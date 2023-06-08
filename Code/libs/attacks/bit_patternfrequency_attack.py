# Bloom filter attack using a frequency set-based approach


MAX_MEMORY_USE = 70000  # In Megabytes

# - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

# Standard library imports
#
import csv
import gzip
import hashlib
import os.path
import sys
import time
import bitarray
import numpy
import random

# PPRL module imports
#
from libs import encoding
from libs import hashing
from libs import hardening

PAD_CHAR = chr(1)   # Used for q-gram padding

BF_HASH_FUNCT1 = hashlib.sha1
BF_HASH_FUNCT2 = hashlib.md5
BF_HASH_FUNCT3 = hashlib.sha224

today_str = time.strftime("%Y%m%d", time.localtime())

# Input variable definitions
#
freq =    'freq'
prob =    'prob'
dynamic = 'dynamic'
static =  'static'



# -----------------------------------------------------------------------------

def align_freq_bf_attr_val(bf_dict, attr_val_freq_dict, min_freq):
  """Align frequent Bloom filters with frequent attribute values and return a
     list of pairs of BF and attribute values and their frequencies.

     Only BFs and attribute values that occur at least 'min_freq' times will be
     considered, and only BFs and attribute values will be added to the list if
     their frequencies are unique.
  """

  print 'Align frequent BF and frequent attribute values'

  # Get frequencies of all Bloom filters and keep those that occur at least
  # 'min_freq' times
  #
  bf_freq_dict = {}

  for this_bf in bf_dict.itervalues():
    bf_freq_dict[this_bf.to01()] = bf_freq_dict.get(this_bf.to01(), 0) + 1

  sorted_bf_list = []

  for (this_bf, this_bf_freq) in bf_freq_dict.iteritems():
    if (this_bf_freq >= min_freq):
      sorted_bf_list.append((this_bf, this_bf_freq))

  sorted_bf_list.sort(key=lambda t: t[1], reverse=True)

  print '  Number of unique BF with a frequency of at least %d: %d' % \
        (min_freq, len(sorted_bf_list))

  # Get list of frequent attribute values that occur at least 'min_freq' times
  #
  sorted_attr_val_list = []

  for (this_attr_val, this_attr_val_freq) in attr_val_freq_dict.iteritems():
    if (this_attr_val_freq >= min_freq):
      sorted_attr_val_list.append((this_attr_val, this_attr_val_freq))

  sorted_attr_val_list.sort(key=lambda t: t[1], reverse=True)

  print '  Number of unique attribute values with a frequency of at least ' + \
        '%d: %d' % (min_freq, len(sorted_attr_val_list))
  print

  # Now align frequent BF and attribute values as long as their frequencies are
  # unique
  #
  freq_bf_attr_val_list = []

  rank = 0

  max_rank = min(len(sorted_bf_list), len(sorted_attr_val_list))

  # No or a single BF or attribute value found for given minimum frequncy
  # (min_freq) (added by Thilina, extended by Peter)
  #
  if (max_rank == 1):
    this_bf =            sorted_bf_list[0][0]
    this_bf_freq =       sorted_bf_list[0][1]

    this_attr_val =      sorted_attr_val_list[0][0]
    this_attr_val_freq = sorted_attr_val_list[0][1]

    freq_bf_attr_val_list.append((this_bf, this_bf_freq, this_attr_val, 
                                  this_attr_val_freq))

  elif (max_rank > 1):  # At least two values
    this_bf =            sorted_bf_list[rank][0]
    this_bf_freq =       sorted_bf_list[rank][1]

    this_attr_val =      sorted_attr_val_list[rank][0]
    this_attr_val_freq = sorted_attr_val_list[rank][1]

    # Loop down the list of BFs and attribute values ordered by frequency
    #
    while (rank < max_rank):
      next_bf_freq =       sorted_bf_list[rank+1][1]
      next_attr_val_freq = sorted_attr_val_list[rank+1][1]

      if ((this_bf_freq == next_bf_freq) or \
          (this_attr_val_freq == next_attr_val_freq)):
        print 'Warning: Two BF or two attribute values have the same ' + \
              'frequency, stop'
        break  # Exit loop (two BF or two attribute values with same frequency)

      freq_bf_attr_val_list.append((this_bf, this_bf_freq, this_attr_val, 
                                    this_attr_val_freq))
      rank += 1
      
      this_bf =            sorted_bf_list[rank][0]
      this_bf_freq =       sorted_bf_list[rank][1]

      this_attr_val =      sorted_attr_val_list[rank][0]
      this_attr_val_freq = sorted_attr_val_list[rank][1]

  print '  Number of frequent BF and attribute values with unique ' + \
        'frequencies: %d' % (len(freq_bf_attr_val_list))
  print

  return freq_bf_attr_val_list

# -----------------------------------------------------------------------------

def analyse_bf_q_gram_freq(freq_bf_attr_val_list, bf_len, q, num_hash_funct):
  """Conduct a frequency and set-based approach to identify which position in
     Bloom filters represent which q-grams.

     Returns a dictionary which for each BF position contains a dictionary of
     possible q-grams at that position, and numerical values of their
     likelihoods.
  """

  start_time = time.time()

  print 'Analyse set of %d frequent Bloom filters and attribute values' % \
        (len(freq_bf_attr_val_list))

  # For all given frequent attribute values get their sets of q-grams
  #
  attr_val_q_gram_dict = {}

  qm1 = q-1

  for (bf, bf_freq, attr_val, attr_val_freq) in freq_bf_attr_val_list:

    attr_val_len = len(attr_val)
    attr_q_gram_list = [attr_val[i:i+q] for i in range(attr_val_len - qm1)]
    attr_q_gram_set =  set(attr_q_gram_list)

    attr_val_q_gram_dict[attr_val] = attr_q_gram_set

  # Step 1: For each BF position, get a set of possible q-grams assigned to
  #         this position (and a value if their likelihoods), as well as a set
  #         of not possible q-grams for this position
  #
  bf_pos_possible_q_gram_dict =     {}
  bf_pos_not_possible_q_gram_dict = {}

  for (bf, bf_freq, attr_val, attr_val_freq) in freq_bf_attr_val_list:

    attr_q_gram_set = attr_val_q_gram_dict[attr_val]
    num_attr_q_gram = len(attr_q_gram_set)

    for pos in range(len(bf)):  # Analyse all bit positions

      assert bf[pos] in ['0','1'], (bf[pos], type(bf[pos]))

      # Set all not possible q-grams for bit positions with value 0
      #
      if (bf[pos] == '0'):
        this_not_poss_q_gram_set = bf_pos_not_possible_q_gram_dict.get(pos,
                                                                       set())
        for q_gram in attr_q_gram_set:
          this_not_poss_q_gram_set.add(q_gram)

        bf_pos_not_possible_q_gram_dict[pos] = this_not_poss_q_gram_set

      else:  # Bit position is 1
        this_poss_q_gram_dict = bf_pos_possible_q_gram_dict.get(pos, {})

        for q_gram in attr_q_gram_set:
          this_poss_q_gram_dict[q_gram] = \
                 this_poss_q_gram_dict.get(q_gram, 0) + 1.0/num_attr_q_gram

        bf_pos_possible_q_gram_dict[pos] = this_poss_q_gram_dict

  # Now remove for each bit position the not possible q-grams from the possible
  # ones
  #
  num_poss_q_gram_list =     []
  num_not_poss_q_gram_list = []

  # The final dictionary with one dictionary per position containing possible
  # q-grams at that position and a numerical value of their likelihood
  #
  poss_q_gram_bf_pos_map_dict = {}

  for pos in range(bf_len):
    not_poss_q_gram_set = bf_pos_not_possible_q_gram_dict.get(pos, set())
    poss_q_gram_dict =    bf_pos_possible_q_gram_dict.get(pos, {})

    num_poss_q_gram_org = len(poss_q_gram_dict)
    num_not_poss_q_gram = len(not_poss_q_gram_set)

    if (num_not_poss_q_gram > 0) and (num_poss_q_gram_org > 0):
      for not_poss_q_gram in not_poss_q_gram_set:
        if not_poss_q_gram in poss_q_gram_dict:
          del poss_q_gram_dict[not_poss_q_gram]  # An impossible q-gram

    poss_q_gram_bf_pos_map_dict[pos] = poss_q_gram_dict

    num_poss_q_gram_filter = len(poss_q_gram_dict)

    num_not_poss_q_gram_list.append(num_not_poss_q_gram)
    num_poss_q_gram_list.append(num_poss_q_gram_filter)

  print '  Not possible number of q-grams per bit position from 0 bits:'
  print '    Minimum: %d, average: %.1f, maximum: %d' % \
        (min(num_not_poss_q_gram_list), numpy.mean(num_not_poss_q_gram_list),
         max(num_not_poss_q_gram_list))
  print '  Possible number of q-grams per bit position from 1 and 0 bits:'
  print '    Minimum: %d, average: %.1f, maximum: %d' % \
        (min(num_poss_q_gram_list), numpy.mean(num_poss_q_gram_list),
         max(num_poss_q_gram_list))
  print

  return poss_q_gram_bf_pos_map_dict

# -----------------------------------------------------------------------------

def reconstruct_attr_val(attr_val_dict, bf_dict, attr_val_freq_dict,
                         use_num_most_freq_attr_val,
                         poss_q_gram_pos_map_dict,
                         analysis_rec_val_id_dict,
                         plain_num_rec):
  """Reconstruct attribute value from Bloom filters and guessed q-grams mapped
     to positions. Only aim to guess the 'use_num_most_freq_attr_val' most
     frequent attribute values.
  """

  # Get the most frequent attribute values
  #
  sorted_attr_val_list = sorted(attr_val_freq_dict.items(),
                 key=lambda t: t[1], reverse=True)[:use_num_most_freq_attr_val]
  freq_attr_val_list = []
  for (attr_val, freq) in sorted_attr_val_list:
    freq_attr_val_list.append(attr_val)

  # For each frequent value get the set of found matching values
  #
  identified_freq_val_dict = {}
  
  # Dictionary for calcualting the attribute and entity reidentification
  # accuracy
  #
  attack_res_dict = {}

  num_no_guess =        0
  num_correct_1_guess = 0
  num_correct_m_guess = 0
  num_wrong_guess =     0

  print 'Reconstruct attribute values from Bloom filters:'
  print '  Aim to reconstruct %d most frequent attribute values:' % \
        (use_num_most_freq_attr_val)
  print '   ', sorted_attr_val_list[:5], '...', sorted_attr_val_list[-5:]

  for (rec_id, rec_bf) in sorted(bf_dict.iteritems()):

    true_attr_val = attr_val_dict[rec_id]

    if (true_attr_val not in freq_attr_val_list):
      continue  # Not a value we know the true status of

    if (true_attr_val in identified_freq_val_dict):
      continue  # Only process each unique frequent attribute value once

    print '  Record %s has true frequent attribute value "%s"' % \
          (rec_id, true_attr_val)

    # Start with all possible frequent attribute values
    #
    cand_attr_val_set = set(freq_attr_val_list)

    for pos in range(len(rec_bf)):

      if (rec_bf[pos] == 1):
        guessed_q_gram_dict = poss_q_gram_pos_map_dict.get(pos, {})

        if (guessed_q_gram_dict != {}):

          # If none of the guessed q-grams at this position occur in an
          # attribute value we can remove the value from the list of
          # candidates
          #
          for cand_attr_val in list(cand_attr_val_set):

            does_occur = False

            for q_gram in guessed_q_gram_dict:

              if (q_gram in cand_attr_val):
                does_occur = True
                break

            # If none of the guessed q-grams occurs in the attribute value we
            # remove it
            #
            if (does_occur == False):
              cand_attr_val_set.remove(cand_attr_val)

        if (len(cand_attr_val_set) == 0):
          num_no_guess += 1
          break

    identified_freq_val_dict[true_attr_val] = cand_attr_val_set

    if (len(cand_attr_val_set) > 0):
      print '    Guessed value(s) for record %s:' % (str(rec_id)), \
            cand_attr_val_set

      if (true_attr_val in cand_attr_val_set):
        if (len(cand_attr_val_set) == 1):  # Exact 1-to-1 guess
          num_correct_1_guess += 1
        else:
          num_correct_m_guess += 1
      else:
        num_wrong_guess += 1
    
    for cand_attr_val in cand_attr_val_set:
      plain_id_set = analysis_rec_val_id_dict[cand_attr_val]
      
      for plain_id in plain_id_set:
        rec_id_tuple = (rec_id, plain_id)
        attack_res_list = attack_res_dict.get(rec_id_tuple, [])
        attack_res_list.append((rec_bf, true_attr_val, cand_attr_val, 1.0))
        attack_res_dict[rec_id_tuple] = attack_res_list
        
  attack_res_tuple = eval_attack_res.calc_attr_ent_reident_res(attack_res_dict, \
                                                               plain_num_rec)
      
    

  print
  print 'Summary of guessing %d most frequenct attribute values:' % \
        (use_num_most_freq_attr_val)
  print '  Number of correct 1-1 guesses:', num_correct_1_guess
  print '  Number of correct 1-m guesses:', num_correct_m_guess
  print '  Number of wrong guesses:      ', num_wrong_guess
  print '  Number of no guesses:         ', num_no_guess
  print

  return num_correct_1_guess, num_correct_m_guess, num_wrong_guess, \
         num_no_guess, attack_res_tuple

# =============================================================================
# Main program
def attack(q, padded, bf_harden, build_bf_dict, bf_encode, hash_type, bf_len, num_hash_funct, res_file_name,
               build_base_data_set_name, analysis_base_data_set_name, build_rec_val_res_tuple,
               analysis_rec_val_res_tuple, min_freq, num_freq_attr_val_list):

    for num_freq_attr_val in num_freq_attr_val_list:
        assert num_freq_attr_val >= 1, num_freq_attr_val_list
    # Read the input data file and load all the record values to a list
    #
    build_rec_val_list      = build_rec_val_res_tuple[0]
    build_rec_val_dict      = build_rec_val_res_tuple[1]
    build_rec_val_id_dict   = build_rec_val_res_tuple[2]
    build_rec_val_freq_dict = build_rec_val_res_tuple[3]
    build_attr_name_list    = build_rec_val_res_tuple[4]

    analysis_rec_val_list         = analysis_rec_val_res_tuple[0]
    analysis_rec_val_dict         = analysis_rec_val_res_tuple[1]
    analysis_rec_val_id_dict      = analysis_rec_val_res_tuple[2]
    analysis_rec_val_freq_dict    = analysis_rec_val_res_tuple[3]
    analysis_guess_attr_name_list = analysis_rec_val_res_tuple[4]

    # -----------------------------------------------------------------------------
    # Step 3: Align frequent Bloom filters with frequent attribute values

    # Align frequent BF to frequent attribute values from analysis (different)
    # data set
    #
    analysis_freq_bf_attr_val_list = align_freq_bf_attr_val(build_bf_dict,
                                                  analysis_rec_val_freq_dict,
                                                  min_freq)
    analysis_num_unique_freq_bf_attr_val = len(analysis_freq_bf_attr_val_list)

    # Check if most frequent BF's frequency is higher than 1
    # if not end the programme
    #
    if(len(analysis_freq_bf_attr_val_list) > 0):

      # -----------------------------------------------------------------------------
      # Now loop over different numbers of most frequent values
      #
      for num_freq_attr_val in num_freq_attr_val_list:

        print 'Analyse BF and attribute values using %d most frequent values only' \
              % (num_freq_attr_val)

        # Limit to the most frequent BFs and attribute values
        #
        if (len(analysis_freq_bf_attr_val_list) > num_freq_attr_val):
          analysis_freq_bf_attr_val_list = \
                                analysis_freq_bf_attr_val_list[:num_freq_attr_val]

        # ---------------------------------------------------------------------------
        # Step 4: Analyse Bloom filters using attribute value frequencies
        #
        start_time = time.time()

        # Now analyse on the analysis data set
        #
        analysis_poss_q_gram_bf_pos_map_dict = \
                             analyse_bf_q_gram_freq(analysis_freq_bf_attr_val_list,
                                                    bf_len, q, num_hash_funct)

        analysis_num_correct_1_guess, analysis_num_correct_m_guess, \
                  analysis_num_wrong_guess, analysis_num_no_guess, \
                  attack_res_tuple = \
                         reconstruct_attr_val(build_rec_val_dict,
                                              build_bf_dict,
                                              analysis_rec_val_freq_dict,
                                              num_freq_attr_val,
                                              analysis_poss_q_gram_bf_pos_map_dict,
                                              analysis_rec_val_id_dict,
                                              len(analysis_rec_val_dict))

        analysis_analyse_time = time.time() - start_time


        attr_reident_res_dict        = attack_res_tuple[0]
        attr_reident_single_res_dict = attack_res_tuple[1]
        ent_reident_res_dict         = attack_res_tuple[2]
        ent_reident_single_res_dict  = attack_res_tuple[3]
        prob_susc_res_dict           = attack_res_tuple[4]
        reident_time                 = attack_res_tuple[5]

        attr_reident_1_1    = attr_reident_res_dict['1-1'] if '1-1' in attr_reident_res_dict else 0
        attr_reident_1_1_p  = attr_reident_res_dict['1-1-p'] if '1-1-p' in attr_reident_res_dict else 0
        attr_reident_1_1_w  = attr_reident_res_dict['1-1-w'] if '1-1-w' in attr_reident_res_dict else 0
        attr_reident_1_m    = attr_reident_res_dict['1-m'] if '1-m' in attr_reident_res_dict else 0
        attr_reident_1_m_p  = attr_reident_res_dict['1-m-p'] if '1-m-p' in attr_reident_res_dict else 0
        attr_reident_1_m_w  = attr_reident_res_dict['1-m-w'] if '1-m-w' in attr_reident_res_dict else 0
        attr_reident_m_1    = attr_reident_res_dict['m-1'] if 'm-1' in attr_reident_res_dict else 0
        attr_reident_m_1_p  = attr_reident_res_dict['m-1-p'] if 'm-1-p' in attr_reident_res_dict else 0
        attr_reident_m_1_w  = attr_reident_res_dict['m-1-w'] if 'm-1-w' in attr_reident_res_dict else 0
        attr_reident_m_m    = attr_reident_res_dict['m-m'] if 'm-m' in attr_reident_res_dict else 0
        attr_reident_m_m_p  = attr_reident_res_dict['m-m-p'] if 'm-m-p' in attr_reident_res_dict else 0
        attr_reident_m_m_w  = attr_reident_res_dict['m-m-w'] if 'm-m-w' in attr_reident_res_dict else 0
        #
        attr_reident_sin_1_1  = attr_reident_single_res_dict['1-1'] if '1-1' in attr_reident_single_res_dict else 0
        attr_reident_sin_1_m  = attr_reident_single_res_dict['1-m'] if '1-m' in attr_reident_single_res_dict else 0
        attr_reident_sin_m_1  = attr_reident_single_res_dict['m-1'] if 'm-1' in attr_reident_single_res_dict else 0
        attr_reident_sin_m_m  = attr_reident_single_res_dict['m-m'] if 'm-m' in attr_reident_single_res_dict else 0
        attr_reident_sin_wrng = attr_reident_single_res_dict['wrng'] if 'wrng' in attr_reident_single_res_dict else 0
        #
        ent_reident_1_1   = ent_reident_res_dict['1-1'] if '1-1' in ent_reident_res_dict else 0
        ent_reident_1_1_p = ent_reident_res_dict['1-1-p'] if '1-1-p' in ent_reident_res_dict else 0
        ent_reident_1_1_w = ent_reident_res_dict['1-1-w'] if '1-1-w' in ent_reident_res_dict else 0
        ent_reident_1_m   = ent_reident_res_dict['1-m'] if '1-m' in ent_reident_res_dict else 0
        ent_reident_1_m_p = ent_reident_res_dict['1-m-p'] if '1-m-p' in ent_reident_res_dict else 0
        ent_reident_1_m_w  = ent_reident_res_dict['1-m-w'] if '1-m-w' in ent_reident_res_dict else 0
        ent_reident_m_1   = ent_reident_res_dict['m-1'] if 'm-1' in ent_reident_res_dict else 0
        ent_reident_m_1_p = ent_reident_res_dict['m-1-p'] if 'm-1-p' in ent_reident_res_dict else 0
        ent_reident_m_1_w = ent_reident_res_dict['m-1-w'] if 'm-1-w' in ent_reident_res_dict else 0
        ent_reident_m_m   = ent_reident_res_dict['m-m'] if 'm-m' in ent_reident_res_dict else 0
        ent_reident_m_m_p = ent_reident_res_dict['m-m-p'] if 'm-m-p' in ent_reident_res_dict else 0
        ent_reident_m_m_w = ent_reident_res_dict['m-m-w'] if 'm-m-w' in ent_reident_res_dict else 0
        #
        ent_reident_sin_1_1  = ent_reident_single_res_dict['1-1'] if '1-1' in ent_reident_single_res_dict else 0
        ent_reident_sin_1_m  = ent_reident_single_res_dict['1-m'] if '1-m' in ent_reident_single_res_dict else 0
        ent_reident_sin_m_1  = ent_reident_single_res_dict['m-1'] if 'm-1' in ent_reident_single_res_dict else 0
        ent_reident_sin_m_m  = ent_reident_single_res_dict['m-m'] if 'm-m' in ent_reident_single_res_dict else 0
        ent_reident_sin_wrng = ent_reident_single_res_dict['wrng'] if 'wrng' in ent_reident_single_res_dict else 0



        # ---------------------------------------------------------------------------
        # Print summary results
        #
        print '#### ---------------------------------------------'
        print '#### Run at:', time.strftime("%Y%m%d %H:%M:%S", time.localtime())
        print '####  ', auxiliary.get_memory_usage()
        print '####   Time used build (load and q-gram gen / BF gen):   ' \
              + '%d / %d sec' % (build_load_time, build_bf_gen_time)
        #
        print '####   Time used analysis (load and q-gram gen / BF gen / ' \
            + 'analysis): %d / -- / %d sec' % (analysis_load_time, \
                                               analysis_analyse_time)
        print '#### Build data set: %s' % (build_base_data_set_name)
        print '####   Number of records: %d' % (len(build_rec_val_dict))
        print '####   Attribute(s) used: %s' % (str(build_attr_name_list))
        #
        print '#### Analysis data set: %s' % (analysis_base_data_set_name)
        print '####   Number of records: %d' % (len(analysis_rec_val_dict))
        print '####   Attribute(s) used: %s' % (str(analysis_guess_attr_name_list))
        print '#### Minimum attribute frequency for analysis: %d' % \
              (min_freq)
        #
        print '#### BF len: %d' % (bf_len)
        print '####   Num hash funct: %d' % (num_hash_funct)

        print '####   q: %d' % (q)
        print '####   BF hardening: %s' % (bf_harden)
        print '####   Hashing type: %s' % \
              ({'dh':'Double hashing', 'rh':'Random hashing',
                'edh':'Enhanced Double hashing', 'th':'Triple hashing'}[hash_type])
        print '#### Number of unique frequent BF and attribute values ' + \
              '(analysis): %d' % (analysis_num_unique_freq_bf_attr_val)

        print '#### Number of most frequent attribute values to reconstruct: %d' % \
              (num_freq_attr_val)
        print '#### Re-identification on analysis data set:'
        print '####   Number of correct 1-1 guesses:', analysis_num_correct_1_guess
        print '####   Number of correct 1-m guesses:', analysis_num_correct_m_guess
        print '####   Number of wrong guesses:      ', analysis_num_wrong_guess
        print '####   Number of no guesses:         ', analysis_num_no_guess
        print '####'

        # ---------------------------------------------------------------------------
        # Write results into a CSV file for analysis

        today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())

        # Generate header line with column names
        #
        header_list = ['today_time_str','q', 'hash_type', 'num_hash_funct', \
                       'bf_len', 'bf_encode', 'padded', \
                       'bf_harden', 'min_freq', 'num_freq_attr_val', \
                       'build_data_set_name', 'build_attr_list', \
                       'analysis_data_set_name', 'analysis_attr_list', \
                       'build_load_time', 'build_bf_gen_time',
                       #
                       'analysis_load_time',
                       'analysis_analyse_time', 'memo_use', \
                       'analysis_num_correct_1', \
                       'analysis_num_correct_m', 'analysis_num_wrong', \
                       'analysis_num_no',]

        attak_res_header = ['max_ps_val_all_assign', 'min_ps_val_all_assign',
                          'mean_ps_val_all_assign', 'median_ps_val_all_assign',
                          'marketer_ps_val_all_assign',
                          #
                          'attr_reident_1_1', 'attr_reident_1_1_p', 'attr_reident_1_1_w',
                          'attr_reident_1_m', 'attr_reident_1_m_p', 'attr_reident_1_m_w',
                          'attr_reident_m_1', 'attr_reident_m_1_p', 'attr_reident_m_1_w',
                          'attr_reident_m_m', 'attr_reident_m_m_p', 'attr_reident_m_m_w',
                          #
                          'attr_reident_sin_1_1', 'attr_reident_sin_1_m',
                          'attr_reident_sin_m_1', 'attr_reident_sin_m_m',
                          'attr_reident_sin_wrng',
                          #
                          'ent_reident_1_1', 'ent_reident_1_1_p', 'ent_reident_1_1_w',
                          'ent_reident_1_m', 'ent_reident_1_m_p', 'ent_reident_1_m_w',
                          'ent_reident_m_1', 'ent_reident_m_1_p', 'ent_reident_m_1_w',
                          'ent_reident_m_m', 'ent_reident_m_m_p', 'ent_reident_m_m_w',
                          #
                          'ent_reident_sin_1_1', 'ent_reident_sin_1_m',
                          'ent_reident_sin_m_1', 'ent_reident_sin_m_m',
                          'ent_reident_sin_wrng',
                          #
                          'res_eval_time']

        header_list += attak_res_header

        # Check if the result file exists, if it does append, otherwise create
        #
        if (not os.path.isfile(res_file_name)):
          csv_writer = csv.writer(open(res_file_name, 'w'))

          csv_writer.writerow(header_list)

        else:  # Append results to an existing file
          csv_writer = csv.writer(open(res_file_name, 'a'))

      #=============================================================================
      #   build_attr_list_str = str(build_attr_list)[1:-1].replace(',','-')
      #   build_attr_list_str = build_attr_list_str.replace(' ', '')
      #
      #   analysis_attr_list_str = str(analysis_attr_list)[1:-1].replace(',','-')
      #   analysis_attr_list_str = analysis_attr_list_str.replace(' ', '')
      #=============================================================================

        res_list = [today_time_str, q, hash_type, num_hash_funct, bf_len,
                    bf_encode, padded, bf_harden,
                    min_freq, num_freq_attr_val, build_base_data_set_name,
                    str(build_attr_name_list), analysis_base_data_set_name,
                    str(analysis_guess_attr_name_list),
                    build_load_time, build_bf_gen_time,
                    #
                    analysis_load_time, analysis_analyse_time,
                    auxiliary.get_memory_usage_val(),
                    analysis_num_correct_1_guess, analysis_num_correct_m_guess,
                    analysis_num_wrong_guess, analysis_num_no_guess,]

        attack_res_list = [prob_susc_res_dict['max-ps'], prob_susc_res_dict['min-ps'],
                           prob_susc_res_dict['avrg-ps'], prob_susc_res_dict['med-ps'],
                           prob_susc_res_dict['makt-ps'],
                           #
                           attr_reident_1_1, attr_reident_1_1_p, attr_reident_1_1_w,
                           attr_reident_1_m, attr_reident_1_m_p, attr_reident_1_m_w,
                           attr_reident_m_1, attr_reident_m_1_p, attr_reident_m_1_w,
                           attr_reident_m_m, attr_reident_m_m_p, attr_reident_m_m_w,
                           #
                           attr_reident_sin_1_1, attr_reident_sin_1_m, attr_reident_sin_m_1,
                           attr_reident_sin_m_m, attr_reident_sin_wrng,
                           #
                           ent_reident_1_1, ent_reident_1_1_p, ent_reident_1_1_w,
                           ent_reident_1_m, ent_reident_1_m_p, ent_reident_1_m_w,
                           ent_reident_m_1, ent_reident_m_1_p, ent_reident_m_1_w,
                           ent_reident_m_m, ent_reident_m_m_p, ent_reident_m_m_w,
                           #
                           ent_reident_sin_1_1, ent_reident_sin_1_m, ent_reident_sin_m_1,
                           ent_reident_sin_m_m, ent_reident_sin_wrng,
                           #
                           reident_time,
                           ]

        res_list += attack_res_list


        assert len(res_list) == len(header_list)

        csv_writer.writerow(res_list)

    else:
      analysis_analyse_time = 0
      analysis_num_correct_1_guess = 0
      analysis_num_correct_m_guess = 0
      analysis_num_wrong_guess = 0
      analysis_num_no_guess = 0

      # ---------------------------------------------------------------------------
      # Print summary results
      #
      print '#### ---------------------------------------------'
      print '#### Run at:', time.strftime("%Y%m%d %H:%M:%S", time.localtime())
      print '####  ', auxiliary.get_memory_usage()
      print '####   Time used build (load and q-gram gen / BF gen):   ' \
            + '%d / %d sec' % (build_load_time, build_bf_gen_time)
      #
      print '####   Time used analysis (load and q-gram gen / BF gen / ' \
          + 'analysis): %d / -- / %d sec' % (analysis_load_time, \
                                             analysis_analyse_time)
      print '#### Build data set: %s' % (build_base_data_set_name)
      print '####   Number of records: %d' % (len(build_rec_val_dict))
      print '####   Attribute(s) used: %s' % (str(build_attr_name_list))
      #
      print '#### Analysis data set: %s' % (analysis_base_data_set_name)
      print '####   Number of records: %d' % (len(analysis_rec_val_dict))
      print '####   Attribute(s) used: %s' % (str(analysis_guess_attr_name_list))
      print '#### Minimum attribute frequency for analysis: %d' % \
            (min_freq)
      #
      print '#### BF len: %d' % (bf_len)
      print '####   Num hash funct: %d' % (num_hash_funct)

      print '####   q: %d' % (q)
      print '####   BF hardening: %s' % (bf_harden)
      print '####   Hashing type: %s' % \
            ({'dh':'Double hashing', 'rh':'Random hashing',
              'edh':'Enhanced double hashing', 'th':'Triple hashing'}[hash_type])
      print '#### Number of unique frequent BF and attribute values ' + \
            '(analysis): %d' % (analysis_num_unique_freq_bf_attr_val)

      print '#### Number of most frequent attribute values to reconstruct: %d' % \
            (num_freq_attr_val)
      print '#### Re-identification on analysis data set:'
      print '####   Number of correct 1-1 guesses:', analysis_num_correct_1_guess
      print '####   Number of correct 1-m guesses:', analysis_num_correct_m_guess
      print '####   Number of wrong guesses:      ', analysis_num_wrong_guess
      print '####   Number of no guesses:         ', analysis_num_no_guess
      print '####'

      # ---------------------------------------------------------------------------
      # Write results into a CSV file for analysis

      today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())

      res_file_name_err = 'bf-attack-results-%s-%s-error.csv' % \
                    (build_base_data_set_name, analysis_base_data_set_name)

      # Generate header line with column names
      #
      header_list = ['today_time_str','q', 'hash_type', 'num_hash_funct', \
                     'bf_len', 'bf_encode',\
                     'bf_harden', 'min_freq', 'num_freq_attr_val', \
                     'build_data_set_name', 'build_attr_list', \
                     'analysis_data_set_name', 'analysis_attr_list', \
                     'build_load_time', 'build_bf_gen_time',
                     #
                     'analysis_load_time',
                     'analysis_analyse_time', 'memo_use', \
                     'analysis_num_correct_1', \
                     'analysis_num_correct_m', 'analysis_num_wrong', \
                     'analysis_num_no']
    #                 'analysis_estim_k1', 'analysis_estim_k2']

      # Check if the result file exists, if it does append, otherwise create
      #
      if (not os.path.isfile(res_file_name_err)):
        csv_writer = csv.writer(open(res_file_name_err, 'w'))

        csv_writer.writerow(header_list)

      else:  # Append results to an existing file
        csv_writer = csv.writer(open(res_file_name_err, 'a'))

    #===============================================================================
    #   build_attr_list_str = str(build_attr_list)[1:-1].replace(',','-')
    #   build_attr_list_str = build_attr_list_str.replace(' ', '')
    #
    #   analysis_attr_list_str = str(analysis_attr_list)[1:-1].replace(',','-')
    #   analysis_attr_list_str = analysis_attr_list_str.replace(' ', '')
    #===============================================================================

      res_list = [today_time_str, q, hash_type, num_hash_funct, bf_len,
                  bf_encode, bf_harden,
                  min_freq, num_freq_attr_val, build_base_data_set_name,
                  str(build_attr_name_list), analysis_base_data_set_name,
                  str(analysis_guess_attr_name_list),
                  build_load_time, build_bf_gen_time,
                  #
                  analysis_load_time, analysis_analyse_time,
                  auxiliary.get_memory_usage_val(),
                  analysis_num_correct_1_guess, analysis_num_correct_m_guess,
                  analysis_num_wrong_guess, analysis_num_no_guess]

      assert len(res_list) == len(header_list)

      csv_writer.writerow(res_list)

    # End.
