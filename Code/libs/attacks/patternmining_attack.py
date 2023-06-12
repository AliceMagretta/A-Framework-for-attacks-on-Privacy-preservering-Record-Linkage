import itertools
import os.path
import csv
import math
import os.path
import random
import sys
import time
import bitarray
import numpy
from libs import fptools
from libs import importing
from libs import bfEncoding

# pma g_variables
NUM_SAMPLE = 1000  # Number of pairs / triplets to sample when calculating
CHECK_POS_TUPLE_SIZE_DIFF_PERC = 20.0

# -----------------------------------------------------------------------------
def gen_q_gram_supp_graph(unique_q_gram_set, q_gram_dict, min_supp=None):
    """From the given set of all unique q-grams and dictionary with q-grams sets
     from records, generate a graph where nodes are q-grams and edges are
     connecting two q-grams if they occur in the same record.

     The attribute values of nodes and edges are their support as the number
     of records they occur in (either a single q-gram for nodes, or pairs of
     q-grams for edges). Edges are directional, with counts according to how
     many times the destination q-gram occurs given the source q-gram occurs.

     If a value is given for 'min_supp' (a float between 0 and 1) then only
     those nodes and edges that have this minimum value (with regard to the
     number of records in the given q-gram dictionary) are kept in the graph
     (dictionaries) returned.

     A second graph is then calculated where the edge values are the
     conditional probabilities that the destination q-gram occurs given the
     source q-gram occurs (in the edge (e_source,e_dest)).

     The function returns three dictionaries, one for nodes (q-grams as keys
     and support counts as values, and the other two for edges (pairs of
     q-grams as keys and either support count or conditional probability as
     values).
  """

    if (min_supp != None):
        assert (0.0 < min_supp) and (1.0 >= min_supp), min_supp

    q_gram_node_dict = {}
    q_gram_edge_dict = {}

    for q_gram in unique_q_gram_set:  # Init count for each unique q-gram
        q_gram_node_dict[q_gram] = 0

    for q_gram_set in q_gram_dict.values():

        for q_gram1 in q_gram_set:  # Increase node support
            q_gram_node_dict[q_gram1] += 1

            for q_gram2 in q_gram_set:

                if (q_gram1 != q_gram2):  # Consider all unique q-gram pairs
                    q_gram_pair = (q_gram1, q_gram2)
                    q_gram_edge_dict[q_gram_pair] = \
                        q_gram_edge_dict.get(q_gram_pair, 0) + 1

    if (min_supp != None):  # Keep only those with minimum support
        num_rec = float(len(q_gram_dict))

        for (q_gram, supp) in q_gram_node_dict.items():
            if (float(supp) / num_rec < min_supp):
                del q_gram_node_dict[q_gram]

        for (q_gram_pair, supp) in q_gram_edge_dict.items():
            if (float(supp) / num_rec < min_supp):
                del q_gram_edge_dict[q_gram_pair]

    # Calculate the conditional probability of the destination q-gram occurring
    # given the source q-gram occurs (i.e. confidence)
    #
    cond_prob_edge_dict = {}
    for (q_gram1, q_gram2) in q_gram_edge_dict.keys():
        q_gram_pair_count = q_gram_edge_dict[(q_gram1, q_gram2)]
        q_gram_count1 = q_gram_node_dict[q_gram1]

        cond_prob = float(q_gram_pair_count) / q_gram_count1
        cond_prob_edge_dict[(q_gram1, q_gram2)] = cond_prob

    return q_gram_node_dict, q_gram_edge_dict, cond_prob_edge_dict


# -----------------------------------------------------------------------------

def gen_bf_col_dict(bf_dict, bf_len):
    """Convert the given BF dictionary into a column-wise format as a list,
       where each column will be a bit array.

       Returns this list of bit arrays as well as a list of how the original
       records refer to elements in bit positions lists (i.e. which entry in a
       bit position list corresponds to which encoded BF.
    """

    num_bf = len(bf_dict)

    bit_col_list = []  # One bit array per position

    bit_col_list = [bitarray.bitarray(num_bf) for _ in range(bf_len)]

    rec_id_list = sorted(list(bf_dict.keys()))

    # Fill newly created bit position arrays
    #
    for (rec_num, rec_id) in enumerate(rec_id_list):
        rec_bf = bf_dict[rec_id]

        for pos in range(bf_len):
            bit_col_list[pos][rec_num] = rec_bf[pos]

    # Check both BF dict and column-wise BF arrays are the same
    #
    rec_id_bf_list = sorted(bf_dict.items())  # One BF per record

    bf_pos_num_1_bit_list = []
    for bit_array in bit_col_list:
        bf_pos_num_1_bit_list.append(int(bit_array.count(1)))

    (100.0 * min(bf_pos_num_1_bit_list) / num_bf,
     100.0 * numpy.mean(bf_pos_num_1_bit_list) / num_bf,
     100.0 * numpy.std(bf_pos_num_1_bit_list) / num_bf,
     100.0 * max(bf_pos_num_1_bit_list) / num_bf)

    return bit_col_list, rec_id_list


# -----------------------------------------------------------------------------

def get_bf_row_col_freq_dist(bf_dict, bit_col_list):
    """Calculate how often each unique BF row and column pattern occurs.

     Return two dictionaries with row and column frequencies of counts of
     occurrences.
  """

    num_bf = len(bf_dict)
    bf_len = len(bit_col_list)

    row_freq_dict = {}
    col_freq_dict = {}

    for bf in bf_dict.values():
        bf_str = bf.to01()
        row_freq_dict[bf_str] = row_freq_dict.get(bf_str, 0) + 1

    for bf_bit_pos in bit_col_list:
        bf_str = bf_bit_pos.to01()
        col_freq_dict[bf_str] = col_freq_dict.get(bf_str, 0) + 1

    row_count_dict = {}  # Now count how often each frequency occurs
    col_count_dict = {}

    for freq in row_freq_dict.values():
        row_count_dict[freq] = row_count_dict.get(freq, 0) + 1
    for freq in col_freq_dict.values():
        col_count_dict[freq] = col_count_dict.get(freq, 0) + 1

    return row_count_dict, col_count_dict


# -----------------------------------------------------------------------------

def check_hamming_weight_bit_positions(bf_bit_pos_list, num_sample):
    """For the given list of bit position bit arrays (column-wise BFs), calculate
       and print the average Hamming weight (HW) for pairs and triplets of
       randomly selected positions using both AND and XOR operations between bit
       arrays.
    """

    bit_pos_pair_and_dict = {}  # Keys are pairs of bit positions
    bit_pos_pair_xor_dict = {}

    bit_pos_triplet_and_dict = {}
    bit_pos_triplet_xor_dict = {}

    bf_len = len(bf_bit_pos_list)
    num_rec = len(bf_bit_pos_list[0])

    bit_pos_list = range(bf_len)  # Position numbers to sample from

    while (len(bit_pos_pair_and_dict) < num_sample):
        bit_pos_pair = tuple(random.sample(bit_pos_list, 2))

        if (bit_pos_pair not in bit_pos_pair_and_dict):  # A new position pair
            pos1, pos2 = bit_pos_pair
            and_bit_array = bf_bit_pos_list[pos1] & bf_bit_pos_list[pos2]  # AND
            xor_bit_array = bf_bit_pos_list[pos1] ^ bf_bit_pos_list[pos2]  # XOR

            bit_pos_pair_and_dict[bit_pos_pair] = int(and_bit_array.count(1))
            bit_pos_pair_xor_dict[bit_pos_pair] = int(xor_bit_array.count(1))

    bit_pos_pair_and_hw_list = list(bit_pos_pair_and_dict.values())
    bit_pos_pair_xor_hw_list = list(bit_pos_pair_xor_dict.values())

    and_hw_mean = numpy.mean(bit_pos_pair_and_hw_list)
    and_hw_std = numpy.std(bit_pos_pair_and_hw_list)
    xor_hw_mean = numpy.mean(bit_pos_pair_xor_hw_list)
    xor_hw_std = numpy.std(bit_pos_pair_xor_hw_list)

    print('Hamming weights between random pairs from %d samples and %d ' % \
          (num_sample, num_rec) + 'records:')
    print('  AND: %d (%.2f%%) average, %d std-dev (%.2f%%)' % \
          (and_hw_mean, 100.0 * and_hw_mean / num_rec,
           and_hw_std, 100.0 * and_hw_std / num_rec))
    print('  XOR: %d (%.2f%%) average, %d std-dev (%.2f%%)' % \
          (xor_hw_mean, 100.0 * xor_hw_mean / num_rec,
           xor_hw_std, 100.0 * xor_hw_std / num_rec))

    while (len(bit_pos_triplet_and_dict) < num_sample):
        bit_pos_triplet = tuple(random.sample(bit_pos_list, 3))

        if (bit_pos_triplet not in bit_pos_triplet_and_dict):  # A new triplet
            pos1, pos2, pos3 = bit_pos_triplet
            and_bit_array = bf_bit_pos_list[pos1] & bf_bit_pos_list[pos2]  # AND
            and_bit_array = and_bit_array & bf_bit_pos_list[pos3]
            xor_bit_array = bf_bit_pos_list[pos1] ^ bf_bit_pos_list[pos2]  # XOR
            xor_bit_array = xor_bit_array ^ bf_bit_pos_list[pos3]

            bit_pos_triplet_and_dict[bit_pos_triplet] = \
                int(and_bit_array.count(1))
            bit_pos_triplet_xor_dict[bit_pos_triplet] = \
                int(xor_bit_array.count(1))

    bit_pos_triplet_and_hw_list = list(bit_pos_triplet_and_dict.values())
    bit_pos_triplet_xor_hw_list = list(bit_pos_triplet_xor_dict.values())

    and_hw_mean = numpy.mean(bit_pos_triplet_and_hw_list)
    and_hw_std = numpy.std(bit_pos_triplet_and_hw_list)
    xor_hw_mean = numpy.mean(bit_pos_triplet_xor_hw_list)
    xor_hw_std = numpy.std(bit_pos_triplet_xor_hw_list)

    print('Hamming weights between random triplets from %d samples and %d ' % \
          (num_sample, num_rec) + 'records:')
    print('  AND: %d (%.2f%%) average, %d std-dev (%.2f%%)' % \
          (and_hw_mean, 100.0 * and_hw_mean / num_rec,
           and_hw_std, 100.0 * and_hw_std / num_rec))
    print('  XOR: %d (%.2f%%) average, %d std-dev (%.2f%%)' % \
          (xor_hw_mean, 100.0 * xor_hw_mean / num_rec,
           xor_hw_std, 100.0 * xor_hw_std / num_rec))
    print()


# -----------------------------------------------------------------------------
# Functions for step 3: Pattern mining to get frequent BF bit positions
# -----------------------------------------------------------------------------


def get_most_freq_other_q_grams(q_gram_dict, must_be_in_rec_q_gram_set,
                                must_not_be_in_rec_q_gram_set):
    """From the given q-gram dictionary and filter q-gram sets, get the frequent
     other q-grams (not in the filter sets), where each q-gram in the
     'must_be_in_rec_q_gram_set' must be in a record q-gram set for the record
     to be counted, and no q-gram in the 'must_not_be_in_rec_q_gram_set' must
     be in a record q-gram set for the record to be counted.

     Returns a list of tuples (q-gram, count) sorted according to their counts
     (most frequent first).
  """

    num_rec = len(q_gram_dict)

    num_rec_part = 0  # Number of records in this partition that are considered

    other_q_gram_freq_dict = {}

    for rec_q_gram_set in q_gram_dict.values():

        # Check if the record q-gram set fulfills the in/out conditions

        # All q-grams in 'must_be_in_rec_q_gram_set' must occur in a record
        #
        all_must_in = must_be_in_rec_q_gram_set.issubset(rec_q_gram_set)

        # No q-gram in 'must_not_be_in_rec_q_gram_set' must occur in record
        #
        if (len(must_not_be_in_rec_q_gram_set.intersection(rec_q_gram_set)) == 0):
            all_must_not_out = True
        else:  # Non-empty intersection, so some q-grams are in both sets
            all_must_not_out = False

        if (all_must_in == True) and (all_must_not_out == True):
            num_rec_part += 1  # Consider this record

            for q_gram in rec_q_gram_set:
                if (q_gram not in must_be_in_rec_q_gram_set):
                    #        if ((q_gram not in must_be_in_rec_q_gram_set) and \
                    #            (q_gram not in must_not_be_in_rec_q_gram_set)):
                    other_q_gram_freq_dict[q_gram] = \
                        other_q_gram_freq_dict.get(q_gram, 0) + 1

    # Get most frequent other q-grams
    #
    freq_q_gram_count_list = sorted(other_q_gram_freq_dict.items(),
                                    key=lambda t: t[1], reverse=True)

    print('Most frequent other q-grams (from records containing %s and not' % \
          (str(must_be_in_rec_q_gram_set)) + ' containing %s):' % \
          (str(must_not_be_in_rec_q_gram_set)))

    # Print 10 most frequent other q-grams
    #
    for (q_gram, count) in freq_q_gram_count_list[:10]:
        print('  %s: %d (%.2f%%, %.2f%%)' % (q_gram, count, 100.0 * count / num_rec,
                                             100.0 * count / num_rec_part))
    print()

    return freq_q_gram_count_list


# -----------------------------------------------------------------------------

def gen_freq_bf_bit_positions_apriori(encode_bf_bit_pos_list, min_count,
                                      col_filter_set=set(),
                                      row_filter_bit_array=None,
                                      verbose=False):
    """Using an Apriori based approach, find all individual, pairs, triplets,
       etc. of bit positions that occur frequently together in the given list of
       bit position arrays (column-wise BFs).

       Only consider bit positions (and pairs and tuples of them) that have a
       Hamming weight of at least 'min_count'.

       If 'col_filter_set' is given (not an empty set), then do not consider
       columns listed in the set.

       If 'row_filter_bit_array' is given (not None), then do not consider the
       rows (BFs) that have a 0-bit.

       Return a dictionary where keys are the longest found tuples made of bit
       positions (integers) and values their counts of occurrences.
    """

    num_bf = len(encode_bf_bit_pos_list[0])

    # If needed generate the row filter bit array - set all rows (BFs) in the
    # filter set to 1 so all are considered
    #
    if (row_filter_bit_array == None):
        row_filter_bit_array = bitarray.bitarray(num_bf)
        row_filter_bit_array.setall(1)

    if (row_filter_bit_array != None):
        part_size = int(row_filter_bit_array.count(1))
    else:
        part_size = num_bf

    # The dictionary with frequent bit position tuples to be returned
    #
    freq_bf_bit_pos_dict = {}

    # First get all bit positions with a HW of at least 'min_count' - - - - - - -
    #
    freq_bit_pos_dict = {}

    max_count = -1

    for (pos, bit_array) in enumerate(encode_bf_bit_pos_list):

        # Only consider columns not given in the column filter set
        #
        if (pos not in col_filter_set):

            # Filter (AND) with row filter bit array
            #
            bit_pos_array_filtered = bit_array & row_filter_bit_array

            bit_pos_hw = int(bit_pos_array_filtered.count(1))
            max_count = max(max_count, bit_pos_hw)
            if (bit_pos_hw >= min_count):
                freq_bit_pos_dict[pos] = bit_pos_hw
                freq_bf_bit_pos_dict[(pos,)] = bit_pos_hw

    # Next get all pairs of bit positions with a HW of at least 'min_count' - -
    #
    freq_bit_pos_pair_dict = {}

    freq_bit_pos_list = sorted(list(freq_bit_pos_dict.keys()))

    for (i, pos1) in enumerate(freq_bit_pos_list[:-1]):
        for pos2 in freq_bit_pos_list[i + 1:]:
            assert pos1 < pos2, (pos1, pos2)

            # Filter (AND) with row filter bit array
            #
            bit_array_pos1_filt = encode_bf_bit_pos_list[pos1] & row_filter_bit_array

            bit_array_pos2 = encode_bf_bit_pos_list[pos2]
            and_bit_pair_array = bit_array_pos1_filt & bit_array_pos2

            and_bit_pos_pair_hw = int(and_bit_pair_array.count(1))

            if (and_bit_pos_pair_hw >= min_count):
                freq_bit_pos_pair_dict[(pos1, pos2)] = and_bit_pos_pair_hw

    if (len(freq_bit_pos_pair_dict) == 0):  # No frequent pairs, return frequent
        return freq_bf_bit_pos_dict  # individuals

    freq_bf_bit_pos_dict = freq_bit_pos_pair_dict  # To be returned

    prev_freq_bit_pos_tuple_dict = freq_bit_pos_pair_dict

    # Now run Apriori for sets of size 3 and more
    #
    curr_len_m1 = 1
    curr_len_p1 = 3

    while (len(prev_freq_bit_pos_tuple_dict) > 1):
        prev_freq_bit_pos_tuple_list = sorted(list(prev_freq_bit_pos_tuple_dict.keys()))

        # Generate candidates of current length plus 1
        #
        cand_bit_pos_tuple_dict = {}

        for (i, pos_tuple1) in enumerate(prev_freq_bit_pos_tuple_list[:-1]):
            pos_tuple1_m1 = pos_tuple1[:curr_len_m1]
            pos_tuple1_last = pos_tuple1[-1]

            for pos_tuple2 in prev_freq_bit_pos_tuple_list[i + 1:]:

                # Check if the two tuples have the same beginning
                #
                if (pos_tuple1_m1 == pos_tuple2[:curr_len_m1]):
                    assert pos_tuple1_last < pos_tuple2[-1], (pos_tuple1, pos_tuple2)
                    cand_pos_tuple = pos_tuple1 + (pos_tuple2[-1],)

                    # Check all sub-tuples are in previous frequent tuple set
                    #
                    all_sub_tuple_freq = True
                    for pos in range(curr_len_p1):
                        check_tuple = tuple(cand_pos_tuple[:pos] + \
                                            cand_pos_tuple[pos + 1:])
                        if (check_tuple not in prev_freq_bit_pos_tuple_dict):
                            all_sub_tuple_freq = False
                            break

                    if (all_sub_tuple_freq == True):  # Get intersection of positions
                        and_bit_tuple_array = row_filter_bit_array
                        for pos in cand_pos_tuple:
                            and_bit_tuple_array = and_bit_tuple_array & \
                                                  encode_bf_bit_pos_list[pos]

                        and_bit_pos_tuple_hw = int(and_bit_tuple_array.count(1))

                        if (and_bit_pos_tuple_hw >= min_count):
                            cand_bit_pos_tuple_dict[cand_pos_tuple] = and_bit_pos_tuple_hw

        if (len(cand_bit_pos_tuple_dict) == 0):
            break  # No more candidates, end Apriori process

        # Set found frequent bit position tuples as final dictionary
        #
        freq_bf_bit_pos_dict = cand_bit_pos_tuple_dict

        curr_len_m1 += 1
        curr_len_p1 += 1

        prev_freq_bit_pos_tuple_dict = cand_bit_pos_tuple_dict

    return freq_bf_bit_pos_dict


# -----------------------------------------------------------------------------

def gen_freq_bf_bit_positions_apriori_memo(encode_bf_bit_pos_list, min_count,
                                           col_filter_set=set(),
                                           row_filter_bit_array=None,
                                           verbose=False):
    """Using an Apriori based approach, find all individual, pairs, triplets,
       etc. of bit positions that occur frequently together in the given list of
       bit position arrays (column-wise BFs).

       Only consider bit positions (and pairs and tuples of them) that have a
       Hamming weight of at least 'min_count'.

       If 'col_filter_set' is given (not an empty set), then do not consider
       columns listed in the set.

       If 'row_filter_bit_array' is given (not None), then do not consider the
       rows (BFs) that have a 0-bit.

       In this version of the function we do keep the actual conjunctions of BFs
       instead of only the set of bit positions, to check if the Apriori
       algorithm runs faster, andhow much more memory is needed.

       Return a dictionary where keys are the longest found tuples made of bit
       positions (integers) and values their counts of occurrences.
    """

    num_bf = len(encode_bf_bit_pos_list[0])

    # If needed generate the row filter bit array - set all rows (BFs) in the
    # filter set to 1 so all are considered
    #
    if (row_filter_bit_array == None):
        row_filter_bit_array = bitarray.bitarray(num_bf)
        row_filter_bit_array.setall(1)

    if (row_filter_bit_array != None):
        part_size = int(row_filter_bit_array.count(1))
    else:
        part_size = num_bf

    print
    'Generate frequent bit position sets with HW of at least %d' % \
    (min_count)
    print
    '  Using the Apriori algorithm (storing all column combination BFs)'
    print
    '  Partiton size: %d Bfs (from %d total BFs)' % (part_size, num_bf)

    # First get all bit positions with a HW of at least 'min_count' - - - - - - -
    #
    freq_bit_pos_dict = {}
    freq_bit_pos_hw_dict = {}  # And a dictionary where we keep their Hamming
    # weights for printing

    max_count = -1

    for (pos, bit_array) in enumerate(encode_bf_bit_pos_list):

        # Only consider columns not given in the column filter set
        #
        if (pos not in col_filter_set):

            # Filter (AND) with row filter bit array
            #
            bit_pos_array_filtered = bit_array & row_filter_bit_array

            bit_pos_hw = int(bit_pos_array_filtered.count(1))
            max_count = max(max_count, bit_pos_hw)
            if (bit_pos_hw >= min_count):
                freq_bit_pos_dict[pos] = bit_pos_array_filtered
                freq_bit_pos_hw_dict[pos] = bit_pos_hw

    # Next get all pairs of bit positions with a HW of at least 'min_count' - -
    #
    freq_bit_pos_pair_dict = {}
    freq_bit_pos_pair_hw_dict = {}  # Keep HW for printing

    freq_bit_pos_list = sorted(list(freq_bit_pos_dict.keys()))

    for (i, pos1) in enumerate(freq_bit_pos_list[:-1]):
        bit_pos_bf1 = freq_bit_pos_dict[pos1]

        for pos2 in freq_bit_pos_list[i + 1:]:
            assert pos1 < pos2, (pos1, pos2)

            # Get the bit-wise AND of the two position BFs
            #
            and_bit_pair_array = bit_pos_bf1 & freq_bit_pos_dict[pos2]

            and_bit_pos_pair_hw = int(and_bit_pair_array.count(1))

            if (and_bit_pos_pair_hw >= min_count):
                freq_bit_pos_pair_dict[(pos1, pos2)] = and_bit_pair_array
                freq_bit_pos_pair_hw_dict[(pos1, pos2)] = and_bit_pos_pair_hw

    # If no frequent pairs then return frequent individual bit positions and
    # their Hamming weights
    #
    if (len(freq_bit_pos_pair_dict) == 0):
        freq_bit_pos_hw_dict = {}  # Generate a dictionary of tuples and their HWs

        for (bit_pos, bit_pos_hw) in freq_bit_pos_hw_dict.items():
            freq_bit_pos_hw_dict[(bit_pos,)] = bit_pos_hw

        return freq_bit_pos_hw_dict

    prev_freq_bit_pos_tuple_dict = freq_bit_pos_pair_dict

    # If no frequent tuples of length 3 or more are found then return the pairs
    #
    freq_bf_bit_pos_dict = freq_bit_pos_pair_dict

    curr_len_m1 = 1  # Now run Apriori for sets of size 3 and more
    curr_len_p1 = 3

    while (len(prev_freq_bit_pos_tuple_dict) > 1):
        prev_freq_bit_pos_tuple_list = sorted(list(prev_freq_bit_pos_tuple_dict.keys()))

        # Generate candidates of current length plus 1
        #
        cand_bit_pos_tuple_dict = {}
        cand_bit_pos_tuple_hw_dict = {}  # Keep HW for printing

        for (i, pos_tuple1) in enumerate(prev_freq_bit_pos_tuple_list[:-1]):
            pos_tuple1_m1 = pos_tuple1[:curr_len_m1]
            pos_tuple1_last = pos_tuple1[-1]

            pos_tuple_bf1 = prev_freq_bit_pos_tuple_dict[pos_tuple1]

            for pos_tuple2 in prev_freq_bit_pos_tuple_list[i + 1:]:

                # Check if the two tuples have the same beginning
                #
                if (pos_tuple1_m1 == pos_tuple2[:curr_len_m1]):
                    assert pos_tuple1_last < pos_tuple2[-1], (pos_tuple1, pos_tuple2)
                    cand_pos_tuple = pos_tuple1 + (pos_tuple2[-1],)

                    # Check all sub-tuples are in previous frequent tuple set
                    #
                    all_sub_tuple_freq = True
                    for pos in range(curr_len_p1):
                        check_tuple = tuple(cand_pos_tuple[:pos] + \
                                            cand_pos_tuple[pos + 1:])
                        if (check_tuple not in prev_freq_bit_pos_tuple_dict):
                            all_sub_tuple_freq = False
                            break

                    if (all_sub_tuple_freq == True):  # Get intersection of positions

                        and_bit_tuple_array = pos_tuple_bf1 & \
                                              prev_freq_bit_pos_tuple_dict[pos_tuple2]

                        and_bit_pos_tuple_hw = int(and_bit_tuple_array.count(1))

                        if (and_bit_pos_tuple_hw >= min_count):
                            cand_bit_pos_tuple_dict[cand_pos_tuple] = and_bit_tuple_array
                            cand_bit_pos_tuple_hw_dict[cand_pos_tuple] = and_bit_pos_tuple_hw

        if (len(cand_bit_pos_tuple_dict) == 0):
            break  # No more candidates, end Apriori process

        # Set found frequent bit position tuples as final dictionary
        #
        freq_bf_bit_pos_dict = cand_bit_pos_tuple_dict

        curr_len_m1 += 1
        curr_len_p1 += 1

        prev_freq_bit_pos_tuple_dict = cand_bit_pos_tuple_dict

    freq_bf_bit_pos_hw_dict = {}

    for (bit_pos_tuple, bit_tuple_array) in freq_bf_bit_pos_dict.items():
        freq_bf_bit_pos_hw_dict[bit_pos_tuple] = int(bit_tuple_array.count(1))

    return freq_bf_bit_pos_hw_dict


# -----------------------------------------------------------------------------

def gen_freq_bf_bit_positions_max_miner(encode_bf_bit_pos_list,
                                        min_count, col_filter_set=set(),
                                        row_filter_bit_array=None,
                                        verbose=False):
    """Using a breath-first based approach as described in "Efficiently Mining
       Long patterns from Databases" (Max-Miner) by R Bayardo, SIGMOD, 1998,
       that applies different pruning techniques to reduce the number of
       candidates sets compared to Apriori.

       Only consider bit positions (and pairs and tuples of them) that have a
       Hamming weight of at least 'min_count'.

       If 'col_filter_set' is given (not an empty set), then do not consider
       columns listed in the set.

       If 'row_filter_bit_array' is given (not None), then do not consider the
       rows (BFs) that have a 0-bit.

       Return a dictionary where keys are the longest found tuples made of bit
       positions (integers) and values their counts of occurrences.
    """

    num_bf = len(encode_bf_bit_pos_list[0])

    # If needed generate the row filter bit array - set all rows (BFs) in the
    # filter set to 1 so all are considered
    #
    if (row_filter_bit_array == None):
        row_filter_bit_array = bitarray.bitarray(num_bf)
        row_filter_bit_array.setall(1)
        part_size = num_bf
    else:
        part_size = int(row_filter_bit_array.count(1))

    print
    'Generate frequent bit position sets with HW of at least %d' % \
    (min_count)
    print
    '  Using the Max-Miner approach'
    print
    '  Partition size: %d Bfs (from %d total BFs)' % (part_size, num_bf)

    # First get all bit positions with a HW of at least 'min_count' - - - - - - -

    # A dictionary with bit positions as keys and their HW as values
    #
    freq_bit_pos_dict = {}

    max_count = -1

    for (pos, bit_array) in enumerate(encode_bf_bit_pos_list):

        # Only consider columns not given in the column filter set
        #
        if (pos not in col_filter_set):

            # Filter (AND) with row filter bit array
            #
            bit_pos_array_filtered = bit_array & row_filter_bit_array

            bit_pos_hw = int(bit_pos_array_filtered.count(1))
            max_count = max(max_count, bit_pos_hw)
            if (bit_pos_hw >= min_count):
                freq_bit_pos_dict[pos] = bit_pos_hw

    print
    '  Found %d bit positions with a HW of at least %d (from %d BFs):' % \
    (len(freq_bit_pos_dict), min_count, num_bf)

    # Check if pairs of bit positions are also frequent, and build dictionary
    # of frequent pairs and their bit arrays and bit position tails (sorted by
    # their Hamming weight)
    #
    freq_bit_pos_list = sorted([item for item in freq_bit_pos_dict],
                               key=freq_bit_pos_dict.get)

    # A dictionary with pairs of bit positions that are frequent as keys, and
    # their bit array and tail (other bit positions) as values
    #
    freq_bit_pos_pair_dict = {}

    tail_len_list = []

    # The set of longest frequent bit position tuples identified
    #
    longest_freq_bit_pos_tuple_set = set()
    longest_freq_bit_pos_tuple_len = -1

    for (i, pos1) in enumerate(freq_bit_pos_list[:-1]):
        pos1_bit_array = encode_bf_bit_pos_list[pos1] & row_filter_bit_array

        for (j, pos2) in enumerate(freq_bit_pos_list[i + 1:]):
            pair_bit_array = pos1_bit_array & encode_bf_bit_pos_list[pos2]

            if (pair_bit_array.count(1) >= min_count):
                head = (pos1, pos2)

                # The tail are all positions after pos2
                #
                tail_bit_pos_list = freq_bit_pos_list[i + j + 2:]

                # If there is a tail get the support of the combined current pair of
                # bit positions plus an element in its tail, and only keep the
                # frequent ones
                #
                if (len(tail_bit_pos_list) > 0):

                    tuple_tail_item_dict = {}

                    full_tail_bit_array = pair_bit_array.copy()
                    tail_freq = True

                    for pos in tail_bit_pos_list:
                        pos_tuple_bit_array = pair_bit_array & encode_bf_bit_pos_list[pos]
                        if (pos_tuple_bit_array.count(1) >= min_count):
                            tuple_tail_item_dict[pos] = pos_tuple_bit_array.count(1)

                            if (tail_freq == True):
                                full_tail_bit_array = full_tail_bit_array & pos_tuple_bit_array

                                if (full_tail_bit_array.count(1) < min_count):
                                    tail_freq = False
                        else:  # Not all positions are frequent
                            tail_freq = False

                    # Sort bit positions according to HW (frequency), smallest first
                    #
                    tail_bit_pos_list = sorted([item for item in tuple_tail_item_dict],
                                               key=tuple_tail_item_dict.get)

                # If there is no tail then this bit position pair cannot be expanded,
                # but it is frequent
                #
                if (len(tail_bit_pos_list) == 0):

                    if (longest_freq_bit_pos_tuple_len == 2):
                        longest_freq_bit_pos_tuple_set.add(head)

                    elif (longest_freq_bit_pos_tuple_len < 2):

                        # A new frequent bit position tuple longer than previous ones
                        #
                        longest_freq_bit_pos_tuple_len = 2
                        longest_freq_bit_pos_tuple_set = set([head])

                # Head concatenated with the full tail is frequent, so add the combined
                # tuple to the set of frequent bit position tuples if it is longest or
                # longer
                #
                elif (tail_freq == True):
                    assert len(tuple_tail_item_dict) == len(tail_bit_pos_list)

                    freq_bit_pos_tuple = head + tuple(tail_bit_pos_list)
                    freq_bit_pos_tuple_len = len(freq_bit_pos_tuple)

                    if (freq_bit_pos_tuple_len == longest_freq_bit_pos_tuple_len):
                        longest_freq_bit_pos_tuple_set.add(freq_bit_pos_tuple)

                    elif (freq_bit_pos_tuple_len > longest_freq_bit_pos_tuple_len):

                        # A new frequent bit position tuple longer than previous ones
                        #
                        longest_freq_bit_pos_tuple_len = freq_bit_pos_tuple_len
                        longest_freq_bit_pos_tuple_set = set([freq_bit_pos_tuple])

                else:  # The frequent bit position pair has a tail, so can be expanded

                    assert freq_bit_pos_list[i + j + 1] == pos2, (freq_bit_pos_list[i + j], pos2)
                    # Assert does not hold anymore due to re-ordering by frequency above
                    # assert freq_bit_pos_list[i+j+2] == tail_bit_pos_list[0]
                    assert pos1 not in tail_bit_pos_list
                    assert pos2 not in tail_bit_pos_list

                    assert head not in freq_bit_pos_pair_dict

                    freq_bit_pos_pair_dict[head] = (pair_bit_array, tail_bit_pos_list)

                    tail_len_list.append(len(tail_bit_pos_list))

    # Now start main loop to generate longer bit position tules - - - - - - - - -
    #
    prev_freq_bit_pos_tuple_dict = freq_bit_pos_pair_dict

    k = 2  # Length of current frequent itemsets

    while (len(prev_freq_bit_pos_tuple_dict) > 0):
        k += 1

        curr_freq_bit_pos_tuple_dict = {}  # New found frequent bit position tuples

        tail_len_list = []

        # Loop over all candidates from the previous iteration
        #
        for (head, tail_pair) in prev_freq_bit_pos_tuple_dict.items():
            head_bit_array, tail_bit_pos_list = tail_pair

            assert head_bit_array.count(1) >= min_count  # The head must be frequent

            # We know the head concatenated with the full tail is not frequent, so
            # expand the head with the individual bit positions from the tail

            # Check for each bit position in the tail if combined with the head it
            # is frequent, and keep a list of tuples with those bit positions in the
            # tail that are frequent in combination with the head, the corresponding
            # bit array, as well as their new tail
            #
            new_tail_bit_pos_list = []

            # Loop over all bit positions in the tail
            #
            for (i, pos) in enumerate(tail_bit_pos_list):
                pos_tuple_bit_array = head_bit_array & encode_bf_bit_pos_list[pos]

                # Only consider an expanded tuple if it is frequent
                #
                if (pos_tuple_bit_array.count(1) >= min_count):
                    new_tail_bit_pos_list.append((pos, pos_tuple_bit_array,
                                                  tail_bit_pos_list[i + 1:]))

            # Given we only include frequent bit position combinations into
            # tails these two lists should be of same length
            #
            assert len(tail_bit_pos_list) == len(new_tail_bit_pos_list)

            # Loop over all frequent expanded bit position tuples
            #
            for (pos, tuple_bit_array, tail_bit_pos_list) in new_tail_bit_pos_list:

                # The new frequent tuple of bit positions
                #
                freq_bit_pos_tuple = head + (pos,)

                # If the tail is empty then the tuple cannot be expanded, so add to
                # the set of frequent bit position tuples if long enough
                #
                if (len(tail_bit_pos_list) == 0):
                    freq_bit_pos_tuple_len = len(freq_bit_pos_tuple)

                    if (freq_bit_pos_tuple_len == longest_freq_bit_pos_tuple_len):
                        longest_freq_bit_pos_tuple_set.add(freq_bit_pos_tuple)

                    elif (freq_bit_pos_tuple_len > longest_freq_bit_pos_tuple_len):

                        # A new frquent bit position tuple longer than previous ones
                        #
                        longest_freq_bit_pos_tuple_len = freq_bit_pos_tuple_len
                        longest_freq_bit_pos_tuple_set = set([freq_bit_pos_tuple])

                else:  # The tail is not empty, so the tuple can be expanded

                    # First check if the length of the head and tail are at least as
                    # long as the so far found longest itemset
                    #
                    head_tail_len = len(freq_bit_pos_tuple) + len(tail_bit_pos_list)

                    if (head_tail_len < longest_freq_bit_pos_tuple_len):
                        continue  # This candidate cannot become the longest

                    # Get the support of the combined current tuple plus an element in
                    # its tail, and only keep the frequent ones
                    #
                    tuple_tail_item_dict = {}

                    full_tail_bit_array = tuple_bit_array.copy()
                    tail_freq = True

                    for pos in tail_bit_pos_list:
                        pos_tuple_bit_array = tuple_bit_array & \
                                              encode_bf_bit_pos_list[pos]
                        if (pos_tuple_bit_array.count(1) >= min_count):
                            tuple_tail_item_dict[pos] = pos_tuple_bit_array.count(1)

                            if (tail_freq == True):
                                full_tail_bit_array = full_tail_bit_array & \
                                                      pos_tuple_bit_array

                                if (full_tail_bit_array.count(1) < min_count):
                                    tail_freq = False
                        else:  # Not all positions are frequent
                            tail_freq = False

                    # Check again if the length of the head and tail are at least as
                    # long as the so far found longest itemset
                    #
                    head_tail_len = len(freq_bit_pos_tuple) + len(tuple_tail_item_dict)
                    if (head_tail_len < longest_freq_bit_pos_tuple_len):
                        continue  # This candidate cannot become the longest

                    # If the tail is empty then the tuple cannot be expanded, so add it
                    # to the set of frequent bit position tuples if long enough
                    #
                    if (len(tuple_tail_item_dict) == 0):
                        freq_bit_pos_tuple_len = len(freq_bit_pos_tuple)

                        if (freq_bit_pos_tuple_len == longest_freq_bit_pos_tuple_len):
                            longest_freq_bit_pos_tuple_set.add(freq_bit_pos_tuple)

                        elif (freq_bit_pos_tuple_len > longest_freq_bit_pos_tuple_len):

                            # A new frquent bit position tuple longer than previous ones
                            #
                            longest_freq_bit_pos_tuple_len = freq_bit_pos_tuple_len
                            longest_freq_bit_pos_tuple_set = set([freq_bit_pos_tuple])

                    elif (tail_freq == True):  # The full tail is frequent

                        assert len(tail_bit_pos_list) == len(tuple_tail_item_dict)
                        assert sorted(tail_bit_pos_list) == \
                               sorted(list(tuple_tail_item_dict.keys()))

                        freq_long_tuple = freq_bit_pos_tuple + tuple(tail_bit_pos_list)
                        freq_long_tuple_len = len(freq_long_tuple)

                        if (freq_long_tuple_len == longest_freq_bit_pos_tuple_len):
                            longest_freq_bit_pos_tuple_set.add(freq_long_tuple)
                        elif (freq_long_tuple_len > longest_freq_bit_pos_tuple_len):
                            longest_freq_bit_pos_tuple_len = freq_long_tuple_len
                            longest_freq_bit_pos_tuple_set = set([freq_long_tuple])

                    else:  # The tail does contain only the frequent bit positions

                        # Sort bit positions according to HW (frequency), smallest first
                        #
                        freq_bit_pos_list = \
                            sorted([item for item in tuple_tail_item_dict],
                                   key=tuple_tail_item_dict.get)

                        # Add new head and tail information into the candiate dictionary
                        #
                        assert freq_bit_pos_tuple not in curr_freq_bit_pos_tuple_dict
                        curr_freq_bit_pos_tuple_dict[freq_bit_pos_tuple] = \
                            (tuple_bit_array, freq_bit_pos_list)

                        tail_len_list.append(len(freq_bit_pos_list))

        prev_freq_bit_pos_tuple_dict = curr_freq_bit_pos_tuple_dict

    # Generate final dictionary of frequent bit position tuples to be returned
    #
    freq_bf_bit_pos_hw_dict = {}

    for freq_bit_pos_tuple in longest_freq_bit_pos_tuple_set:
        bit_tuple_array = row_filter_bit_array.copy()

        for pos in freq_bit_pos_tuple:
            bit_tuple_array = bit_tuple_array & encode_bf_bit_pos_list[pos]

        assert bit_tuple_array.count(1) >= min_count, freq_bit_pos_tuple

        freq_bf_bit_pos_hw_dict[tuple(sorted(freq_bit_pos_tuple))] = \
            int(bit_tuple_array.count(1))

    return freq_bf_bit_pos_hw_dict


# -----------------------------------------------------------------------------

def gen_freq_bf_bit_positions_h_mine(encode_bf_bit_pos_list,
                                     min_count, col_filter_set=set(),
                                     row_filter_bit_array=None,
                                     verbose=False):
    """Using a depth-first based approach similar to Max-Miner, as described in
       "H-Mine: Fast and space-preserving frequent pattern mining in large
       databases" (H-Mine) by J Pei, J Han, H Lu, S Nishio, S Tang, D Yang,
       IIE Transactions, 39(6), 593-605, 2007, which applies pruning techniques
       to reduce the number of candidates sets.

       Only consider bit positions (and pairs and tuples of them) that have a
       Hamming weight of at least 'min_count'.

       If 'col_filter_set' is given (not an empty set), then do not consider
       columns listed in the set.

       If 'row_filter_bit_array' is given (not None), then do not consider the
       rows (BFs) that have a 0-bit.

       Return a dictionary where keys are the longest found tuples made of bit
       positions (integers) and values their counts of occurrences.
    """

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # Recursive H-mine function for depth-first mining frequent bit position sets
    #
    def __h_mine__(head_tuple, head_bit_array, freq_pos_tuple_tail, \
                   prev_maximal_freq_itemset_len, prev_freq_itemset):

        # Remove bit positions with less local minimum support
        #
        assert len(freq_pos_tuple_tail) > 0, len(freq_pos_tuple_tail)

        tail_pos_list = []  # All bit positions in tail that are frequent when
        # combined with the head bit array

        for tail_pos in freq_pos_tuple_tail:
            if ((head_bit_array & freq_bit_pos_dict[tail_pos]).count(1) >= \
                    min_count):
                tail_pos_list.append(tail_pos)

        curr_maximal_freq_itemset_len = prev_maximal_freq_itemset_len
        curr_freq_itemset = prev_freq_itemset

        tail_len = len(tail_pos_list)
        bit_pos_set_len = len(head_tuple)  # Lenth of the head tuple

        # Check if the length of the concatenated head and tail bit position tuples
        # is greater than the maximum length, if not then no need to go down this
        # branch
        #
        if ((tail_len + bit_pos_set_len) >= curr_maximal_freq_itemset_len):

            if (tail_len > 0):  # If the tail bit position list is not empty

                freq_pos_bit_array = head_bit_array
                tail_freq = True

                # Check if the full tail is frequent
                #
                for pos in tail_pos_list:
                    freq_pos_bit_array = freq_pos_bit_array & freq_bit_pos_dict[pos]
                    if (freq_pos_bit_array.count(1) < min_count):
                        tail_freq = False
                        break  # No need to compare further bit positions

                assert tail_freq == (freq_pos_bit_array.count(1) >= min_count)

                if (tail_freq == True):  # The full tail is frequent
                    freq_pos_tuple = head_tuple + tuple(tail_pos_list)
                    freq_pos_tuple_len = len(freq_pos_tuple)

                    if (freq_pos_tuple_len == curr_maximal_freq_itemset_len):
                        curr_freq_itemset.add(freq_pos_tuple)
                        return curr_maximal_freq_itemset_len, curr_freq_itemset
                    elif (freq_pos_tuple_len > curr_maximal_freq_itemset_len):
                        curr_freq_itemset = set([freq_pos_tuple])
                        curr_maximal_freq_itemset_len = freq_pos_tuple_len
                        return curr_maximal_freq_itemset_len, curr_freq_itemset

                    # No else needed because above check ensure only long enough tuples
                    # are investigated

                else:  # The full tail is not frequent do depth-first in branch

                    for (i, pos) in enumerate(tail_pos_list):

                        # Check if each tail bit position is frequent when combined with
                        # the head, if so call function recursively
                        #
                        new_tuple_bit_array = head_bit_array & freq_bit_pos_dict[pos]

                        if (new_tuple_bit_array.count(1) >= min_count):
                            freq_pos_tuple = head_tuple + (pos,)
                            new_tail_pos_list = tail_pos_list[i + 1:]

                            if (len(new_tail_pos_list) > 0):

                                # Resursive call for the h-mine function
                                #
                                curr_maximal_freq_itemset_len, curr_freq_itemset = \
                                    __h_mine__(freq_pos_tuple, \
                                               new_tuple_bit_array,
                                               new_tail_pos_list, \
                                               curr_maximal_freq_itemset_len, \
                                               curr_freq_itemset)

                            else:  # If the new sub-tail has no bit positions
                                freq_pos_tuple_len = len(freq_pos_tuple)
                                if (freq_pos_tuple_len == curr_maximal_freq_itemset_len):
                                    curr_freq_itemset.add(freq_pos_tuple)
                                elif (freq_pos_tuple_len > curr_maximal_freq_itemset_len):
                                    curr_freq_itemset = set([freq_pos_tuple])
                                    curr_maximal_freq_itemset_len = freq_pos_tuple_len

                                return curr_maximal_freq_itemset_len, curr_freq_itemset

            else:  # If tail is empty (has no bit positions)

                # Add head tuple to set of maximal frequent tuples if it is long enough
                #
                if (bit_pos_set_len == curr_maximal_freq_itemset_len):
                    curr_freq_itemset.add(head_tuple)
                    return curr_maximal_freq_itemset_len, curr_freq_itemset

                elif (bit_pos_set_len > curr_maximal_freq_itemset_len):
                    curr_freq_itemset = set([head_tuple])  # New longest results set
                    curr_maximal_freq_itemset_len = bit_pos_set_len
                    return curr_maximal_freq_itemset_len, curr_freq_itemset

                # No else needed because above check ensure only long enough tuples
                # are investigated

        # If the length of the entire bit position list is less than the maximum
        # length then return the previous frequent itemsets and maximal length
        #
        else:
            return curr_maximal_freq_itemset_len, curr_freq_itemset

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    num_bf = len(encode_bf_bit_pos_list[0])

    # If needed generate the row filter bit array - set all rows (BFs) in the
    # filter set to 1 so all are considered
    #
    if (row_filter_bit_array == None):
        row_filter_bit_array = bitarray.bitarray(num_bf)
        row_filter_bit_array.setall(1)
        part_size = num_bf
    else:
        part_size = int(row_filter_bit_array.count(1))

    # First get all bit positions with a HW of at least 'min_count' - - - - - - -

    # A dictionary with bit positions as keys and their bit arrays as values
    #
    freq_bit_pos_dict = {}

    for (pos, bit_array) in enumerate(encode_bf_bit_pos_list):

        # Only consider columns not given in the column filter set
        #
        if (pos not in col_filter_set):

            # Filter (AND) with row filter bit array
            #
            bit_pos_array_filtered = bit_array & row_filter_bit_array

            bit_pos_hw = int(bit_pos_array_filtered.count(1))

            if (bit_pos_hw >= min_count):
                freq_bit_pos_dict[pos] = bit_pos_array_filtered

    print
    '  Found %d bit positions with a HW of at least %d (from %d BFs):' % \
    (len(freq_bit_pos_dict), min_count, num_bf)
    print

    # Re-order bit positions according to their Hamming weights (smallest first)
    #
    freq_bit_pos_list = sorted(list(freq_bit_pos_dict.keys()), \
                               key=lambda v: freq_bit_pos_dict[v].count(1))

    maximal_freq_itemset = set()
    maximal_freq_itemset_len = 0

    # Now loop over all bit positions and generate bit position pairs that - - -
    # are frequent, then recursive call H-mine function for those pairs
    # that have a non-empty tail of frequent bit position
    #
    num_freq_pairs = 0  # keep track of the number of frequent pairs

    for (i, pos1) in enumerate(freq_bit_pos_list):
        pos1_bit_array = freq_bit_pos_dict[pos1]

        for (j, pos2) in enumerate(freq_bit_pos_list[i + 1:]):
            pair_bit_array = pos1_bit_array & freq_bit_pos_dict[pos2]

            # If the bit position pair has the minimum Hamming weight
            #
            if (pair_bit_array.count(1) >= min_count):
                num_freq_pairs += 1
                tail_bit_pos_list = freq_bit_pos_list[i + j + 2:]

                # Check if the concatenated head (pair of bit positions) and tail can
                # potentially lead to a new longest maximal itemset
                #
                total_bit_pos_list_len = len(tail_bit_pos_list) + 2

                if ((total_bit_pos_list_len > 2) and \
                        (total_bit_pos_list_len >= maximal_freq_itemset_len)):

                    # Call H-mine on this pair and its tail
                    #
                    maximal_freq_itemset_len, maximal_freq_itemset = \
                        __h_mine__((pos1, pos2), pair_bit_array, tail_bit_pos_list, \
                                   maximal_freq_itemset_len, maximal_freq_itemset)

                elif (total_bit_pos_list_len == 2):
                    freq_pos_tuple = (pos1, pos2)

                    if (maximal_freq_itemset_len == 2):
                        maximal_freq_itemset.add(freq_pos_tuple)
                    elif (maximal_freq_itemset_len < 2):
                        maximal_freq_itemset = set([freq_pos_tuple])
                        maximal_freq_itemset_len = 2

    if (num_freq_pairs > 0):
        assert len(maximal_freq_itemset) > 0, len(maximal_freq_itemset)

    # Generate final dictionary of frequent bit position tuples to be returned
    #
    freq_bf_bit_pos_hw_dict = {}

    # Loop through the maximum frequent bit position sets and calculate their
    # support (Hamming weight)
    #
    for freq_bit_pos_tuple in maximal_freq_itemset:
        bit_tuple_array = row_filter_bit_array.copy()

        for pos in freq_bit_pos_tuple:
            bit_tuple_array = bit_tuple_array & freq_bit_pos_dict[pos]

        assert bit_tuple_array.count(1) >= min_count, freq_bit_pos_tuple

        freq_bf_bit_pos_hw_dict[tuple(sorted(freq_bit_pos_tuple))] = \
            int(bit_tuple_array.count(1))

    return freq_bf_bit_pos_hw_dict


# -----------------------------------------------------------------------------

def gen_freq_bf_bit_positions_fp_max(encode_bf_bit_pos_list,
                                     min_count, col_filter_set=set(),
                                     row_filter_bit_array=None,
                                     verbose=False):
    """FPtree and FPmax based approach to find all maximal sets of bit positions
       that occur frequently together in the given list of bit position arrays
       (column-wise BFs).

       Only consider bit positions (and pairs and tuples of them) that have a
       Hamming weight of at least 'min_count'.

       If 'col_filter_set' is given (not an empty set), then do not consider
       columns listed in the set.

       If 'row_filter_bit_array' is given (not None), then do not consider the
       rows (BFs) that have a 0-bit.

       Return a dictionary where keys are the longest found tuples made of bit
       positions (integers) and values their counts of occurrences.
    """

    num_bf = len(encode_bf_bit_pos_list[0])
    num_bit_pos = len(encode_bf_bit_pos_list)

    # If needed generate the row filter bit array - set all rows (BFs) in the
    # filter set to 1 so all are considered
    #
    if (row_filter_bit_array == None):
        row_filter_bit_array = bitarray.bitarray(num_bf)
        row_filter_bit_array.setall(1)
        part_size = num_bf
    else:
        part_size = int(row_filter_bit_array.count(1))

    print
    'Generate frequent bit position sets with HW of at least %d' % \
    (min_count)
    print
    '  Using the FPtree and FPmax approach'
    print
    '  Partition size: %d Bfs (from %d total BFs)' % (part_size, num_bf)

    # First get all bit positions with a HW of at least 'min_count' - - - - - - -
    #
    freq_bit_pos_set = set()  # Bit positions with a Hamming weight large enough

    max_count = -1

    for (pos, bit_array) in enumerate(encode_bf_bit_pos_list):

        # Only consider columns not given in the column filter set
        #
        if (pos not in col_filter_set):

            # Filter (AND) with row filter bit array
            #
            bit_pos_array_filtered = bit_array & row_filter_bit_array

            bit_pos_hw = int(bit_pos_array_filtered.count(1))
            max_count = max(max_count, bit_pos_hw)
            if (bit_pos_hw >= min_count):
                freq_bit_pos_set.add(pos)

    print
    '  Found %d bit positions with a HW of at least %d (from %d BFs):' % \
    (len(freq_bit_pos_set), min_count, num_bf)

    # Check if pairs of bit positions are also frequent, and only keep those bit
    # positions that do occur in at least one frequent pair
    #
    freq_bit_pos_list = sorted(freq_bit_pos_set)

    freq_bit_pos_set = set()  # All positions that occur in a frequent pair
    freq_bit_pos_pair_set = set()  # Also keep all frequent pairs

    for (i, pos1) in enumerate(freq_bit_pos_list[:-1]):
        pos1_bit_array = encode_bf_bit_pos_list[pos1] & row_filter_bit_array

        for pos2 in freq_bit_pos_list[i + 1:]:

            pair_bit_array = encode_bf_bit_pos_list[pos2] & pos1_bit_array

            if (pair_bit_array.count(1) >= min_count):
                freq_bit_pos_set.add(pos1)
                freq_bit_pos_set.add(pos2)
                freq_bit_pos_pair_set.add((pos1, pos2))

    for pos in freq_bit_pos_set:
        assert pos in freq_bit_pos_list, pos

    print
    '  Found %d bit positions that occur in frequent pairs' % \
    (len(freq_bit_pos_set)) + ' (from %d frequent bit position pairs)' % \
    (len(freq_bit_pos_pair_set))

    # Check if triplets of bit positions are also frequent, and only keep those
    # bit positions that do occur in at least one frequent triplet
    #
    freq_bit_pos_list = sorted(freq_bit_pos_set)
    num_freq_bit_pos = len(freq_bit_pos_list)

    prev_freq_bit_pos_set = freq_bit_pos_set

    freq_bit_pos_set = set()
    num_freq_bit_pos_triplets = 0

    # Outer-most loop over all positions except the last two ones
    #
    for (i, pos1) in enumerate(freq_bit_pos_list[:-2]):
        pos1_bit_array = encode_bf_bit_pos_list[pos1] & row_filter_bit_array

        # Middle loop from one after i to second last bit position
        #
        for j in range(i + 1, num_freq_bit_pos - 1):
            pos2 = freq_bit_pos_list[j]

            # Check if the bit position pair is frequent
            #
            if (pos1, pos2) in freq_bit_pos_pair_set:
                pair_bit_array = encode_bf_bit_pos_list[pos2] & pos1_bit_array

                # Inner-most loop from one after j to last bit position
                #
                for k in range(j + 1, num_freq_bit_pos):
                    pos3 = freq_bit_pos_list[k]

                    # Check both possible bit position pairs with pos3 are frequent
                    # (Apriori principle)
                    #
                    if (((pos1, pos3) in freq_bit_pos_pair_set) and \
                            ((pos2, pos3) in freq_bit_pos_pair_set)):
                        triplet_bit_array = encode_bf_bit_pos_list[pos3] & pair_bit_array

                        if (pair_bit_array.count(1) >= min_count):
                            freq_bit_pos_set.add(pos1)
                            freq_bit_pos_set.add(pos2)
                            freq_bit_pos_set.add(pos3)
                            num_freq_bit_pos_triplets += 1

    for pos in freq_bit_pos_set:
        assert pos in freq_bit_pos_list, pos

    # If no frequent triples found keep the frequent pairs
    #
    if (len(freq_bit_pos_set) == 0):
        freq_bit_pos_set = prev_freq_bit_pos_set
    else:
        prev_freq_bit_pos_set == set()

    # Now generate the list of transactions (a list of lists) where items are
    # 1-bit positions as integer values
    #

    itemset_list = []

    for bf_row in range(num_bf):

        if (row_filter_bit_array[bf_row] == 1):  # Use this BF

            item_list = []

            for pos in freq_bit_pos_set:  # Only loop over the frequent bit positions
                if (encode_bf_bit_pos_list[pos][bf_row] == 1):
                    item_list.append(pos)

            itemset_list.append(item_list)

    assert len(itemset_list) == row_filter_bit_array.count(1)

    fp_tree, fp_rank = fptools.build_tree(itemset_list, min_count)

    assert len(fp_rank) == len(freq_bit_pos_set), \
        (len(fp_rank), len(freq_bit_pos_set))

    fp_mfit_tree = fptools.MFITree(fp_rank)

    longest_bit_pattern_len = -1

    freq_item_set_set = set()

    for freq_item_list in fptools.fpmax(fp_tree, min_count, fp_mfit_tree):

        freq_item_set_len = len(freq_item_list)

        # Only add to results set if at least as long as longest so far
        #
        if (freq_item_set_len >= longest_bit_pattern_len):
            freq_item_set_set.add(tuple(freq_item_list))

            longest_bit_pattern_len = max(longest_bit_pattern_len, freq_item_set_len)

    freq_bf_bit_pos_hw_dict = {}

    # Now only keep the longest frequent item sets
    #
    for freq_item_tuple in freq_item_set_set:
        if (len(freq_item_tuple) == longest_bit_pattern_len):

            # Get the Hamming weight of this set of bit patterns
            #
            freq_bit_pos_array = row_filter_bit_array.copy()

            for pos in freq_item_tuple:
                freq_bit_pos_array = freq_bit_pos_array & encode_bf_bit_pos_list[pos]

            freq_bit_pos_hw = int(freq_bit_pos_array.count(1))
            assert freq_bit_pos_hw >= min_count, (freq_bit_pos_hw, min_count)

            freq_bf_bit_pos_hw_dict[tuple(sorted(freq_item_tuple))] = freq_bit_pos_hw

    return freq_bf_bit_pos_hw_dict


# -----------------------------------------------------------------------------

def gen_lang_model(lang_model, freq_q_gram_set, q_gram_dict,
                   attr_val_freq_q_gram_dict, min_freq_count):
    """For the given set of frequent q-grams and q-gram dictionary (one q-gram
     set/list per record), generate a language model based on the given
     'lang_model' parameter.

     This will be a dictionary where keys are either a single frequent q-gram
     ('single'), a tuple of frequent q-grams ('tuple'), or tuples of all
     frequent q-grams ('all') split into two tuples of q-grams included and
     excluded in attribute values.

     For each key, we keep the count of how many records have the key, the
     attribute values with that key (based on the attr_val_freq_q_gram_dict),
     and a dictionary with non-frequent q-grams that co-occur with the key and
     their frequencies.

     The function returns one dictionary, where only tuples with a count of at
     least the minimum partition size 'min_freq_count' will be included.
  """

    assert lang_model in ['single', 'tuple', 'all'], lang_model

    # The language model dictionary with keys either:
    # - Single frequent q-grams as keys
    # - Tuples of frequent q-grams as keys (minimum length 2)
    # - Tuples of have / not have icluding all frequent q-grams as keys
    #
    lm_dict = {}

    # A list with the number of frequent and not frequent q-grams per record
    #
    num_freq_q_gram_rec_list = []
    num_not_freq_q_gram_rec_list = []

    # Step 1: Loop over all q-gram sets/lists in the given q-gram dictionary,
    # and identify the frequent and not frequent q-gram, then build the q-gram
    # (tuple) keys for the language model and add the not frequent q-grams to
    # their corresponding q-gram (tuple) keys
    #
    for rec_q_gram_list in q_gram_dict.values():

        # Get all frequent and not frequent q-grams of this record
        #
        rec_freq_q_gram_set = set()
        rec_not_freq_q_gram_set = set()

        for q_gram in rec_q_gram_list:
            if q_gram in freq_q_gram_set:
                rec_freq_q_gram_set.add(q_gram)
            else:
                rec_not_freq_q_gram_set.add(q_gram)

        num_freq_q_gram_rec_list.append(len(rec_freq_q_gram_set))
        num_not_freq_q_gram_rec_list.append(len(rec_not_freq_q_gram_set))

        # Generate the set of keys from the frequent q-grams
        #
        if (lang_model == 'single'):
            # Simply all frequent q-grams that occur in the record
            #
            lm_key_list = list(rec_freq_q_gram_set)

        elif (lang_model == 'tuple'):
            lm_key_list = []  # All subsets of length 2 and longer
            for l in range(2, len(rec_freq_q_gram_set) + 1):
                for q_gram_tuple in itertools.combinations(rec_freq_q_gram_set, l):
                    lm_key_list.append(q_gram_tuple)

        else:  # 'all'
            # Only one tuple (of included / excluded frequent q-grams)
            #
            rec_not_incl_freq_q_gram_set = freq_q_gram_set - rec_freq_q_gram_set

            # Only consider if there is at least one included q-gram
            #
            if (len(rec_freq_q_gram_set) > 0):
                lm_key_list = [(tuple(rec_freq_q_gram_set), \
                                tuple(rec_not_incl_freq_q_gram_set))]
            else:
                lm_key_list = []

        # Now add all not frequent q-grams from this record into the language
        # model dictionary. The values in this dictionary consist of triplets
        # with the count of the frequent tuple, the set of possible attribute
        # values with that tuple (to be generated in the next step below), and
        # the dictionary with not frequent q-grams and their counts
        #
        for q_gram_key in lm_key_list:
            this_q_gram_tuple = lm_dict.get(q_gram_key, (0, set(), {}))
            this_q_gram_count = this_q_gram_tuple[0] + 1
            this_q_gram_dict = this_q_gram_tuple[2]

            for not_freq_q_gram in rec_not_freq_q_gram_set:
                this_q_gram_dict[not_freq_q_gram] = \
                    this_q_gram_dict.get(not_freq_q_gram, 0) + 1

            lm_dict[q_gram_key] = (this_q_gram_count, set(), this_q_gram_dict)

    # Remove all q-gram keys (q-grams / tuples) in the dictionary with a count
    # of less than the minimum frequency
    #
    for q_gram_key in lm_dict.keys():
        this_q_gram_tuple = lm_dict[q_gram_key]
        if (this_q_gram_tuple[0] < min_freq_count):
            del lm_dict[q_gram_key]

    # Step 2: For each q-gram key (q-gram / tuple) find all attribute values from
    # the 'attr_val_freq_q_gram_dict' that have (and have not) the corresponding
    # frequent q-grams
    #
    for attr_val in attr_val_freq_q_gram_dict:
        (attr_val_freq, attr_q_gram_list) = attr_val_freq_q_gram_dict[attr_val]

        # Get all the frequent and not frequent q-grams of this attribute
        #
        attr_val_freq_q_gram_set = set()
        attr_val_not_freq_q_gram_set = set()

        for q_gram in attr_q_gram_list:
            if q_gram in freq_q_gram_set:
                attr_val_freq_q_gram_set.add(q_gram)
            else:
                attr_val_not_freq_q_gram_set.add(q_gram)

        # Generate the set of keys from the frequent q-grams
        #
        if (lang_model == 'single'):
            # Simply all frequent q-grams that occur in the attribute value
            #
            lm_key_list = list(attr_val_freq_q_gram_set)

        elif (lang_model == 'tuple'):
            lm_key_list = []  # All subsets of length 2 and longer
            for l in range(2, len(attr_val_freq_q_gram_set) + 1):
                for q_gram_tuple in itertools.combinations(attr_val_freq_q_gram_set, l):
                    lm_key_list.append(q_gram_tuple)

        else:  # 'all'
            # Only one tuple (of included / excluded frequent q-grams)
            #
            not_incl_freq_q_gram_set = freq_q_gram_set - attr_val_freq_q_gram_set

            # Only consider if there is at least one included q-gram
            #
            if (len(attr_val_freq_q_gram_set) > 0):
                lm_key_list = [(tuple(attr_val_freq_q_gram_set), \
                                tuple(not_incl_freq_q_gram_set))]
            else:
                lm_key_list = []

        num_q_gram_keys_not_in_lm_dict = 0

        # Add the attribute value to the set of possible values of all q-gram keys
        # from the first step
        #
        for q_gram_key in lm_key_list:

            if q_gram_key in lm_dict:
                (this_q_gram_count, this_q_gram_attr_val_set, this_q_gram_dict) = \
                    lm_dict[q_gram_key]
                this_q_gram_attr_val_set.add(attr_val)
                lm_dict[q_gram_key] = (this_q_gram_count, this_q_gram_attr_val_set, \
                                       this_q_gram_dict)
            else:
                num_q_gram_keys_not_in_lm_dict += 1

    # Get statistics of the number of possible attribute values per q-gram key
    # and check how many q-gram keys have no attribute value
    #
    lm_num_attr_val_list = []
    q_gram_keys_without_attr_val_list = []

    for (this_q_gram_key, this_q_gram_tuple) in lm_dict.items():
        q_gram_tuple_num_attr_val = len(this_q_gram_tuple[1])
        lm_num_attr_val_list.append(q_gram_tuple_num_attr_val)
        if (q_gram_tuple_num_attr_val == 0):
            q_gram_keys_without_attr_val_list.append(this_q_gram_key)

    return lm_dict


# -----------------------------------------------------------------------------

def gen_freq_bf_bit_positions_apriori(encode_bf_bit_pos_list, min_count,
                                      col_filter_set=set(),
                                      row_filter_bit_array=None,
                                      verbose=False):
    """Using an Apriori based approach, find all individual, pairs, triplets,
     etc. of bit positions that occur frequently together in the given list of
     bit position arrays (column-wise BFs).

     Only consider bit positions (and pairs and tuples of them) that have a
     Hamming weight of at least 'min_count'.

     If 'col_filter_set' is given (not an empty set), then do not consider
     columns listed in the set.

     If 'row_filter_bit_array' is given (not None), then do not consider the
     rows (BFs) that have a 0-bit.

     Return a dictionary where keys are the longest found tuples made of bit
     positions (integers) and values their counts of occurrences.
  """

    num_bf = len(encode_bf_bit_pos_list[0])

    # If needed generate the row filter bit array - set all rows (BFs) in the
    # filter set to 1 so all are considered
    #
    if (row_filter_bit_array == None):
        row_filter_bit_array = bitarray.bitarray(num_bf)
        row_filter_bit_array.setall(1)

    if (row_filter_bit_array != None):
        part_size = int(row_filter_bit_array.count(1))
    else:
        part_size = num_bf

    # The dictionary with frequent bit position tuples to be returned
    #
    freq_bf_bit_pos_dict = {}

    # First get all bit positions with a HW of at least 'min_count' - - - - - - -
    #
    freq_bit_pos_dict = {}

    max_count = -1

    for (pos, bit_array) in enumerate(encode_bf_bit_pos_list):

        # Only consider columns not given in the column filter set
        #
        if (pos not in col_filter_set):

            # Filter (AND) with row filter bit array
            #
            bit_pos_array_filtered = bit_array & row_filter_bit_array

            bit_pos_hw = int(bit_pos_array_filtered.count(1))
            max_count = max(max_count, bit_pos_hw)
            if (bit_pos_hw >= min_count):
                freq_bit_pos_dict[pos] = bit_pos_hw
                freq_bf_bit_pos_dict[(pos,)] = bit_pos_hw

    # Next get all pairs of bit positions with a HW of at least 'min_count' - -
    #
    freq_bit_pos_pair_dict = {}

    freq_bit_pos_list = sorted(list(freq_bit_pos_dict.keys()))

    for (i, pos1) in enumerate(freq_bit_pos_list[:-1]):
        for pos2 in freq_bit_pos_list[i + 1:]:
            assert pos1 < pos2, (pos1, pos2)

            # Filter (AND) with row filter bit array
            #
            bit_array_pos1_filt = encode_bf_bit_pos_list[pos1] & row_filter_bit_array

            bit_array_pos2 = encode_bf_bit_pos_list[pos2]
            and_bit_pair_array = bit_array_pos1_filt & bit_array_pos2

            and_bit_pos_pair_hw = int(and_bit_pair_array.count(1))

            if (and_bit_pos_pair_hw >= min_count):
                freq_bit_pos_pair_dict[(pos1, pos2)] = and_bit_pos_pair_hw

    if (len(freq_bit_pos_pair_dict) == 0):  # No frequent pairs, return frequent
        return freq_bf_bit_pos_dict  # individuals

    freq_bf_bit_pos_dict = freq_bit_pos_pair_dict  # To be returned

    prev_freq_bit_pos_tuple_dict = freq_bit_pos_pair_dict

    # Now run Apriori for sets of size 3 and more
    #
    curr_len_m1 = 1
    curr_len_p1 = 3

    while (len(prev_freq_bit_pos_tuple_dict) > 1):
        prev_freq_bit_pos_tuple_list = sorted(list(prev_freq_bit_pos_tuple_dict.keys()))

        # Generate candidates of current length plus 1
        #
        cand_bit_pos_tuple_dict = {}

        for (i, pos_tuple1) in enumerate(prev_freq_bit_pos_tuple_list[:-1]):
            pos_tuple1_m1 = pos_tuple1[:curr_len_m1]
            pos_tuple1_last = pos_tuple1[-1]

            for pos_tuple2 in prev_freq_bit_pos_tuple_list[i + 1:]:

                # Check if the two tuples have the same beginning
                #
                if (pos_tuple1_m1 == pos_tuple2[:curr_len_m1]):
                    assert pos_tuple1_last < pos_tuple2[-1], (pos_tuple1, pos_tuple2)
                    cand_pos_tuple = pos_tuple1 + (pos_tuple2[-1],)

                    # Check all sub-tuples are in previous frequent tuple set
                    #
                    all_sub_tuple_freq = True
                    for pos in range(curr_len_p1):
                        check_tuple = tuple(cand_pos_tuple[:pos] + \
                                            cand_pos_tuple[pos + 1:])
                        if (check_tuple not in prev_freq_bit_pos_tuple_dict):
                            all_sub_tuple_freq = False
                            break

                    if (all_sub_tuple_freq == True):  # Get intersection of positions
                        and_bit_tuple_array = row_filter_bit_array
                        for pos in cand_pos_tuple:
                            and_bit_tuple_array = and_bit_tuple_array & \
                                                  encode_bf_bit_pos_list[pos]

                        and_bit_pos_tuple_hw = int(and_bit_tuple_array.count(1))

                        if (and_bit_pos_tuple_hw >= min_count):
                            cand_bit_pos_tuple_dict[cand_pos_tuple] = and_bit_pos_tuple_hw

        if (len(cand_bit_pos_tuple_dict) == 0):
            break  # No more candidates, end Apriori process

        # Set found frequent bit position tuples as final dictionary
        #
        freq_bf_bit_pos_dict = cand_bit_pos_tuple_dict

        curr_len_m1 += 1
        curr_len_p1 += 1

        prev_freq_bit_pos_tuple_dict = cand_bit_pos_tuple_dict

    return freq_bf_bit_pos_dict


# -----------------------------------------------------------------------------
# Functions for step 4: Re-identify attribute values based on frequent bit pos.
# -----------------------------------------------------------------------------

def re_identify_attr_val_setinter(bf_must_have_q_gram_dict,
                                  bf_cannot_have_q_gram_dict,
                                  plain_q_gram_attr_val_dict,
                                  encode_rec_val_dict, max_num_many=10,
                                  verbose=False):
    """Based on the given dictionaries of must have and cannot have q-grams per
     Bloom filter, and the given plain-text and encoded data set's attribute
     values (the latter being the true encoded values for a BF), re-identify
     attribute values from the set of plain-text values that could have been
     encoded in a BF.

     This method implements a simple set intersection approach that only finds
     those attribute values (possibly none) that contain all must have q-grams
     in a Bloom filter.

     Calculate and return the number of:
     - BFs with no guesses
     - BFs with more than 'max_num_many' guesses
     - BFs with 1-to-1 guesses
     - BFs with correct 1-to-1 guesses
     - BFs with partially matching 1-to-1 guesses
     - BFs with 1-to-many guesses
     - BFs with 1-to-many correct guesses
     - BFs with partially matching 1-to-many guesses

     - Accuracy of 1-to-1 partial matching values based on common tokens
     - Accuracy of 1-to-many partial matching values based on common tokens

     Also returns a dictionary with BFs as keys and correctly re-identified
     attribute values as values.
  """

    num_no_guess = 0
    num_too_many_guess = 0
    num_1_1_guess = 0
    num_corr_1_1_guess = 0
    num_part_1_1_guess = 0
    num_1_m_guess = 0
    num_corr_1_m_guess = 0
    num_part_1_m_guess = 0

    acc_part_1_1_guess = 0.0  # Average accuracy of partial matching values based
    acc_part_1_m_guess = 0.0  # on common tokens

    # BFs with correctly re-identified attribute values
    #
    corr_reid_attr_val_dict = {}

    rec_num = 0

    for (enc_rec_id, bf_q_gram_set) in bf_must_have_q_gram_dict.items():

        reid_attr_set_list = []

        for q_gram in bf_q_gram_set:
            reid_attr_set_list.append(plain_q_gram_attr_val_dict[q_gram])

        reid_attr_set_list.sort(key=len)  # Shortest first so smaller intersections

        reid_attr_val_set = set.intersection(*reid_attr_set_list)

        # Remove the attribute values that contain must not have q-grams
        #
        if ((len(reid_attr_val_set) > 0) and \
                (enc_rec_id in bf_cannot_have_q_gram_dict)):
            must_not_have_q_gram_set = bf_cannot_have_q_gram_dict[enc_rec_id]

            checked_reid_attr_val_set = set()

            for attr_val in reid_attr_val_set:
                no_cannot_have_q_gram = True
                for q_gram in must_not_have_q_gram_set:
                    if (q_gram in attr_val):
                        no_cannot_have_q_gram = False
                        break
                if (no_cannot_have_q_gram == True):
                    checked_reid_attr_val_set.add(attr_val)

            reid_attr_val_set = checked_reid_attr_val_set

        num_bf_attr_val_guess = len(reid_attr_val_set)

        # Check if there are possible plain-text values for this BF
        #
        if (num_bf_attr_val_guess == 0):
            num_no_guess += 1
        elif (num_bf_attr_val_guess == 1):
            num_1_1_guess += 1
        elif (num_bf_attr_val_guess > max_num_many):
            num_too_many_guess += 1
        else:
            num_1_m_guess += 1

        # If there is a small number (<= max_num_many) of possible values check if
        # the correct one is included
        #
        if (num_bf_attr_val_guess >= 1) and (num_bf_attr_val_guess <= max_num_many):

            true_encoded_attr_val = encode_rec_val_dict[enc_rec_id]

            if (true_encoded_attr_val in reid_attr_val_set):

                # True attribute value is re-identified
                #
                corr_reid_attr_val_dict[enc_rec_id] = reid_attr_val_set

                if (num_bf_attr_val_guess == 1):
                    num_corr_1_1_guess += 1
                else:
                    num_corr_1_m_guess += 1

            else:  # If no exact match, check if some words / tokens are in common

                true_encoded_attr_val_set = set(true_encoded_attr_val.split())

                # Get maximum number of tokens shared with an encoded attribute value
                #
                max_num_common_token = 0

                for plain_text_attr_val in reid_attr_val_set:
                    plain_text_attr_val_set = set(plain_text_attr_val.split())

                    num_common_token = \
                        len(true_encoded_attr_val_set & plain_text_attr_val_set)
                    max_num_common_token = max(max_num_common_token, num_common_token)

                if (max_num_common_token > 0):  # Add partial accuracy of common tokens
                    num_token_acc = float(max_num_common_token) / \
                                    len(true_encoded_attr_val_set)

                    if (num_bf_attr_val_guess == 1):
                        num_part_1_1_guess += 1
                        acc_part_1_1_guess += num_token_acc
                    else:
                        num_part_1_m_guess += 1
                        acc_part_1_m_guess += num_token_acc

        rec_num += 1

    if (num_part_1_m_guess > 0):
        acc_part_1_m_guess = float(acc_part_1_m_guess) / num_part_1_m_guess
    else:
        acc_part_1_m_guess = 0.0
    if (num_part_1_1_guess > 0):
        acc_part_1_1_guess = float(acc_part_1_1_guess) / num_part_1_1_guess
    else:
        acc_part_1_1_guess = 0.0

    return num_no_guess, num_too_many_guess, num_1_1_guess, num_corr_1_1_guess, \
           num_part_1_1_guess, num_1_m_guess, num_corr_1_m_guess, \
           num_part_1_m_guess, acc_part_1_1_guess, acc_part_1_m_guess, \
           corr_reid_attr_val_dict


# -----------------------------------------------------------------------------

def gen_freq_q_gram_bit_post_dict(q_gram_pos_assign_dict,
                                  true_q_gram_pos_map_dict):
    """Generate two dictionaries which for each identified frequent q-gram
     contain its bit positions (either all or only the correct ones) based on
     the given dictionary of positions and q-grams assigned to them.

     Returns two dictionaries, the first containing all bit positions per
     q-gram while the second only contains correct bit positions (based on the
     given 'true_q_gram_pos_map_dict').
  """

    all_identified_q_gram_pos_dict = {}  # Keys are q-grams, values sets of pos.
    corr_identified_q_gram_pos_dict = {}  # Only correct positions
    num_pos_removed = 0  # For the corrected dictionary

    for (pos, pos_q_gram_set) in q_gram_pos_assign_dict.items():

        for q_gram in pos_q_gram_set:

            # Check if this is a correct position for this q-gram
            #
            if q_gram in true_q_gram_pos_map_dict.get(pos, set()):
                correct_pos = True
            else:
                correct_pos = False

            q_gram_pos_set = all_identified_q_gram_pos_dict.get(q_gram, set())
            q_gram_pos_set.add(pos)
            all_identified_q_gram_pos_dict[q_gram] = q_gram_pos_set

            if (correct_pos == True):
                q_gram_pos_set = corr_identified_q_gram_pos_dict.get(q_gram, set())
                q_gram_pos_set.add(pos)
                corr_identified_q_gram_pos_dict[q_gram] = q_gram_pos_set
            else:
                num_pos_removed += 1

    # Check each q-gram has at least one position in the correct only dictionary
    #
    for q_gram in corr_identified_q_gram_pos_dict.keys():
        if (len(corr_identified_q_gram_pos_dict[q_gram]) == 0):
            del corr_identified_q_gram_pos_dict[q_gram]

    return all_identified_q_gram_pos_dict, corr_identified_q_gram_pos_dict


# -----------------------------------------------------------------------------

def get_matching_bf_sets(identified_q_gram_pos_dict, encode_bf_dict,
                         plain_attr_val_rec_id_dict, bf_must_have_q_gram_dict,
                         bf_cannot_have_q_gram_dict, bf_len,
                         min_q_gram_tuple_size=3):
    """Based on the given identified bit position tuples of frequent q-grams, the
       given BF dictionary (assumed to come from the encoded data set), and the
       given q-gram dictionary (assumed to contain the q-grams from records in
       the plain-text data set), as well as the must have and cannot have q-gram
       sets per BF, for each encoded BF first find all the q-grams that can be
       encoded in this BF (based on the BF's 1-bit pattern), and then find for
       each unique q-gram tuple and its possible BFs the possible matching
       attribute values.

       The function returns a dictionary where frequent q-gram tuples are keys,
       and values are two sets of record identifiers, one of encoded BFs that
       have matching 1-bits in all relevant positions for the q-grams in the
       key, and the second with record identifiers from the plain-text data set
       that contain all the q-grams in the key.
    """

    # The dictionary to be returned with q-gram tuples as keys and two sets of
    # record identifiers (one corresponding to encoded BFs, the other to
    # plain-text values) for each such q-gram tuples.
    #
    q_gram_tuple_rec_id_dict = {}

    # The list of frequent q-grams we have
    #
    freq_q_gram_set = set(identified_q_gram_pos_dict.keys())

    # Step 1: For each BF, find all frequent q-grams that possibly could be
    #         encoded in this BF, not just the must have ones
    #
    q_gram_tuple_enc_rec_set_dict = {}  # Keys are q-gram tuples, values record
    # ID sets from the encoded database

    for (enc_rec_id, rec_bf) in encode_bf_dict.items():
        must_have_q_gram_set = bf_must_have_q_gram_dict.get(enc_rec_id, set())
        cannot_have_q_gram_set = bf_cannot_have_q_gram_dict.get(enc_rec_id, set())

        bf_q_gram_set = must_have_q_gram_set.copy()  # Start with the ones we know

        # Get the set of other q-grams that might be encoded (from all identified
        # ones)
        #
        check_q_gram_set = freq_q_gram_set - must_have_q_gram_set - \
                           cannot_have_q_gram_set

        if (len(check_q_gram_set) > 0):

            for q_gram in check_q_gram_set:
                all_q_gram_pos_1 = True

                for pos in identified_q_gram_pos_dict[q_gram]:
                    if (rec_bf[pos] == 0):
                        all_q_gram_pos_1 = False

                if (all_q_gram_pos_1 == True):
                    # print '    Added "%s" as possible q-gram to encoded BF %s' % \
                    #      (q_gram,enc_rec_id)
                    bf_q_gram_set.add(q_gram)

        if (len(bf_q_gram_set) > 0):
            bf_q_gram_tuple = tuple(bf_q_gram_set)

            bf_q_gram_tuple_set_id_set = \
                q_gram_tuple_enc_rec_set_dict.get(bf_q_gram_tuple, set())
            bf_q_gram_tuple_set_id_set.add(enc_rec_id)
            q_gram_tuple_enc_rec_set_dict[bf_q_gram_tuple] = \
                bf_q_gram_tuple_set_id_set

    # Calculate statistics of the number of encoded BFs / record identifiers per
    # q-gram tuple
    #
    num_enc_rec_id_list = []
    for q_gram_tuple_rec_id_set in q_gram_tuple_enc_rec_set_dict.values():
        num_enc_rec_id_list.append(len(q_gram_tuple_rec_id_set))

    # Remove q-grams tuples that are not long enough
    #
    num_short_tuples_del = 0

    num_many_del = 0

    q_gram_tuple_enc_rec_set_key_list = list(q_gram_tuple_enc_rec_set_dict.keys())
    for q_gram_tuple in q_gram_tuple_enc_rec_set_key_list:
        if (len(q_gram_tuple) < min_q_gram_tuple_size):

            # If the tuple has more than one encoded BF remove it
            #
            if (len(q_gram_tuple_enc_rec_set_dict[q_gram_tuple]) > 1):
                del q_gram_tuple_enc_rec_set_dict[q_gram_tuple]
                num_short_tuples_del += 1

    num_enc_rec_id_list = []
    for q_gram_tuple_rec_id_set in q_gram_tuple_enc_rec_set_dict.values():
        num_enc_rec_id_list.append(len(q_gram_tuple_rec_id_set))

    # Step 2: For each found q-gram tuple which has encoded BFs, get the
    #         plain-text attribute values with these q-grams, and then the
    #         corresponding record identifiers from the plain-text database
    #
    q_gram_tuple_plain_rec_set_dict = {}  # Keys are q-gram tuples, values record
    # ID sets from the plain-text database
    q_gram_tuple_plain_attr_val_dict = {}  # Keys are q-gram tuples, values are
    # plain-text attribute values

    num_no_matching_q_grams = 0
    num_same_length_q_gram_tuple = 0

    q_gram_tuple_len_list = []
    for q_gram_tuple in q_gram_tuple_enc_rec_set_dict.keys():
        q_gram_tuple_len_list.append((q_gram_tuple, len(q_gram_tuple)))

    # Loop over all attribute values from the plain-text database and their
    # record identifiers, and find the q-gram tuples that have all q-grams in an
    # attribute value
    #
    for (attr_val, plain_rec_id_set) in plain_attr_val_rec_id_dict.items():

        # Keep all matching q-gram tuples and their length (number of q-grams)
        #
        attr_val_q_gram_tuple_len_list = []

        for (q_gram_tuple, tuple_len) in q_gram_tuple_len_list:

            all_q_grams_in_val = True

            for q_gram in q_gram_tuple:
                if (q_gram not in attr_val):
                    all_q_grams_in_val = False

            if (all_q_grams_in_val == True):
                attr_val_q_gram_tuple_len_list.append((tuple_len, q_gram_tuple, \
                                                       plain_rec_id_set))

        # Now get the longest tuple with the largest number of q-grams
        #
        if (len(attr_val_q_gram_tuple_len_list) == 1):  # Only one matching tuple

            q_gram_tuple = attr_val_q_gram_tuple_len_list[0][1]

            # There could be several attribute values that match this q-gram tuple
            #
            q_gram_tuple_attr_val_set = \
                q_gram_tuple_plain_attr_val_dict.get(q_gram_tuple, set())
            q_gram_tuple_attr_val_set.add(attr_val)
            q_gram_tuple_plain_attr_val_dict[q_gram_tuple] = \
                q_gram_tuple_attr_val_set
            q_gram_tuple_rec_id_set = \
                q_gram_tuple_plain_rec_set_dict.get(q_gram_tuple, set())
            q_gram_tuple_rec_id_set.update(attr_val_q_gram_tuple_len_list[0][2])
            q_gram_tuple_plain_rec_set_dict[q_gram_tuple] = q_gram_tuple_rec_id_set

        elif (len(attr_val_q_gram_tuple_len_list) > 1):
            attr_val_q_gram_tuple_len_list.sort(reverse=True)  # Longest tuple first

            # Only use the longest q-gram tuple (if there is one longest one)
            #
            if (attr_val_q_gram_tuple_len_list[0][0] > \
                    attr_val_q_gram_tuple_len_list[1][0]):
                q_gram_tuple = attr_val_q_gram_tuple_len_list[0][1]

                q_gram_tuple_attr_val_set = \
                    q_gram_tuple_plain_attr_val_dict.get(q_gram_tuple, set())
                q_gram_tuple_attr_val_set.add(attr_val)
                q_gram_tuple_plain_attr_val_dict[q_gram_tuple] = \
                    q_gram_tuple_attr_val_set
                q_gram_tuple_rec_id_set = \
                    q_gram_tuple_plain_rec_set_dict.get(q_gram_tuple, set())
                q_gram_tuple_rec_id_set.update(attr_val_q_gram_tuple_len_list[0][2])
                q_gram_tuple_plain_rec_set_dict[q_gram_tuple] = q_gram_tuple_rec_id_set

            else:
                num_same_length_q_gram_tuple += 1


        else:
            num_no_matching_q_grams += 1

    # Calculate statistics of the number of plain-text record identifiers per
    # q-gram tuple
    #
    num_plain_rec_id_list = []
    for q_gram_tuple_rec_id_set in q_gram_tuple_plain_rec_set_dict.values():
        num_plain_rec_id_list.append(len(q_gram_tuple_rec_id_set))

    # Generate final dictionary to be returned
    #
    for (q_gram_tuple, enc_q_gram_tuple_rec_id_set) in \
            q_gram_tuple_enc_rec_set_dict.items():
        if (q_gram_tuple in q_gram_tuple_plain_rec_set_dict):
            plain_q_gram_tuple_rec_id_set = \
                q_gram_tuple_plain_rec_set_dict[q_gram_tuple]
            q_gram_tuple_rec_id_dict[q_gram_tuple] = \
                (enc_q_gram_tuple_rec_id_set, plain_q_gram_tuple_rec_id_set)

    return q_gram_tuple_rec_id_dict


# -----------------------------------------------------------------------------

def calc_reident_accuracy(q_gram_tuple_rec_id_dict, encode_rec_val_dict,
                          plain_rec_val_dict, plain_val_num_q_gram_dict,
                          max_num_many, bf_lower_upper_bound_q_gram_dict=None,
                          return_filtered_results=True):
    """Calculate the accuracy of re-identification for the given dictionary that
       contains q-gram tuples as keys and pairs of record identifier sets from
       the encoded data set and values from the plain-text data set, where the
       former are BFs that are believed to encode these q-grams while the latter
       are values that contain these q-grams.

       If the 'bf_lower_upper_bound_q_gram_dict' is provided (with a lower and
       upper number of q-grams for each encoded BF), then only candidate values
       in this interval will be considered.

       Calculate and return the number of:
       - BFs with no guesses
       - BFs with more than 'max_num_many' guesses
       - BFs with 1-to-1 guesses
       - BFs with correct 1-to-1 guesses
       - BFs with partially matching 1-to-1 guesses
       - BFs with 1-to-many guesses
       - BFs with 1-to-many correct guesses
       - BFs with partially matching 1-to-many guesses

       - Accuracy of 1-to-1 partial matching values based on common tokens
       - Accuracy of 1-to-many partial matching values based on common tokens

       If the flag 'return_filtered_results' is set to True (default), then
       these are the results obtained on the length filtered candidate values,
       otherwise the results based on all candidate values will be returned.

       Also returns a dictionary with BFs as keys and correctly re-identified
       attribute values as values.
    """

    # Two counts each (all and length filtered)
    #
    num_no_guess = [0, 0]
    num_too_many_guess = [0, 0]
    num_1_1_guess = [0, 0]
    num_corr_1_1_guess = [0, 0]
    num_part_1_1_guess = [0, 0]
    num_1_m_guess = [0, 0]
    num_corr_1_m_guess = [0, 0]
    num_part_1_m_guess = [0, 0]

    acc_part_1_1_guess = [0.0, 0.0]  # Average accuracy of partial matching values
    acc_part_1_m_guess = [0.0, 0.0]  # based on common tokens

    # Calculate and keep track of the reduction ratio of candidate values
    # in lenth filtering
    #
    lenth_filter_reduction_perc_list = []

    # BFs with correctly re-identified attribute values
    #
    corr_reid_attr_val_dict = {}

    # First get for each encoded BF all the plain-text record identifiers
    #
    encode_plain_rec_id_dict = {}

    for (q_gram_tuple, attr_val_rec_id_sets_pair) in \
            q_gram_tuple_rec_id_dict.items():
        bf_rec_id_set = attr_val_rec_id_sets_pair[0]
        plain_rec_id_set = attr_val_rec_id_sets_pair[1]

        for bf_rec_id in bf_rec_id_set:
            bf_plain_rec_set = encode_plain_rec_id_dict.get(bf_rec_id, set())
            bf_plain_rec_set.update(plain_rec_id_set)
            encode_plain_rec_id_dict[bf_rec_id] = bf_plain_rec_set

    # Now loop over these encoded BFs and their plain-text record identifier sets
    #
    for (bf_rec_id, bf_plain_rec_set) in encode_plain_rec_id_dict.items():

        # First get all the plain-text attribute values from the corresponding
        # records
        #
        q_gram_plain_attr_val_set = set()

        for rec_id in bf_plain_rec_set:
            q_gram_plain_attr_val_set.add(plain_rec_val_dict[rec_id])

        num_plain_val = len(q_gram_plain_attr_val_set)

        # Filter values by length if lower and upper bound dictionary is given
        #
        if (return_filtered_results == True):

            lower_bound, upper_bound = bf_lower_upper_bound_q_gram_dict[bf_rec_id]

            filtered_plain_val_set = set()

            for plain_val in q_gram_plain_attr_val_set:
                plain_num_q_gram = plain_val_num_q_gram_dict[plain_val]

                if ((plain_num_q_gram >= lower_bound) and \
                        (plain_num_q_gram <= upper_bound)):
                    filtered_plain_val_set.add(plain_val)

        if (return_filtered_results == True):
            num_plain_val_filter = len(filtered_plain_val_set)

            if (num_plain_val > 0):
                cand_red_perc = 1.0 - (float(num_plain_val_filter) / num_plain_val)
                lenth_filter_reduction_perc_list.append(cand_red_perc)
            else:
                cand_red_perc = 0.0
        else:
            num_plain_val_filter = 0

        # Now check for the encoded BF record if the plain text values match
        #
        true_encoded_attr_val = encode_rec_val_dict[bf_rec_id]

        if (num_plain_val == 1):
            num_1_1_guess[0] += 1
        elif (num_plain_val > max_num_many):
            num_too_many_guess[0] += 1
        else:
            num_1_m_guess[0] += 1

        if (num_plain_val >= 1) and (num_plain_val <= max_num_many):

            if (true_encoded_attr_val in q_gram_plain_attr_val_set):

                # True attribute value is re-identified
                #
                corr_reid_attr_val_dict[rec_id] = q_gram_plain_attr_val_set

                if (num_plain_val == 1):
                    num_corr_1_1_guess[0] += 1
                else:
                    num_corr_1_m_guess[0] += 1

            else:  # If no exact match, check if some words / tokens are in common
                true_encoded_attr_val_set = set(true_encoded_attr_val.split())

                # Get maximum number of tokens shared with an encoded attribute value
                #
                max_num_common_token = 0

                for plain_text_attr_val in q_gram_plain_attr_val_set:
                    plain_text_attr_val_set = set(plain_text_attr_val.split())

                    num_common_token = \
                        len(true_encoded_attr_val_set & plain_text_attr_val_set)
                    max_num_common_token = max(max_num_common_token, num_common_token)

                if (max_num_common_token > 0):  # Add partial accuracy
                    num_token_acc = float(max_num_common_token) / \
                                    len(true_encoded_attr_val_set)

                    if (num_plain_val == 1):
                        num_part_1_1_guess[0] += 1
                        acc_part_1_1_guess[0] += num_token_acc
                    else:
                        num_part_1_m_guess[0] += 1
                        acc_part_1_m_guess[0] += num_token_acc

        # Also check quality of filtered results
        #
        if (return_filtered_results == True):

            if (num_plain_val_filter == 1):
                num_1_1_guess[1] += 1
            elif (num_plain_val_filter > max_num_many):
                num_too_many_guess[1] += 1
            else:
                num_1_m_guess[1] += 1

            if (num_plain_val_filter >= 1) and (num_plain_val_filter <= max_num_many):

                if (true_encoded_attr_val in filtered_plain_val_set):

                    # True attribute value is re-identified
                    #
                    corr_reid_attr_val_dict[rec_id] = filtered_plain_val_set

                    if (num_plain_val_filter == 1):
                        num_corr_1_1_guess[1] += 1
                    else:
                        num_corr_1_m_guess[1] += 1

                else:  # If no exact match, check if some words / tokens are in common
                    true_encoded_attr_val_set = set(true_encoded_attr_val.split())

                    # Get maximum number of tokens shared with an encoded attribute value
                    #
                    max_num_common_token = 0

                    for plain_text_attr_val in filtered_plain_val_set:
                        plain_text_attr_val_set = set(plain_text_attr_val.split())

                        num_common_token = \
                            len(true_encoded_attr_val_set & plain_text_attr_val_set)
                        max_num_common_token = max(max_num_common_token, num_common_token)

                    if (max_num_common_token > 0):  # Add partial accuracy
                        num_token_acc = float(max_num_common_token) / \
                                        len(true_encoded_attr_val_set)

                        if (num_plain_val_filter == 1):
                            num_part_1_1_guess[1] += 1
                            acc_part_1_1_guess[1] += num_token_acc
                        else:
                            num_part_1_m_guess[1] += 1
                            acc_part_1_m_guess[1] += num_token_acc

    if (num_part_1_m_guess[0] > 0):
        acc_part_1_m_guess[0] = float(acc_part_1_m_guess[0]) / num_part_1_m_guess[0]
    else:
        acc_part_1_m_guess[0] = 0.0
    if (num_part_1_1_guess[0] > 0):
        acc_part_1_1_guess[0] = float(acc_part_1_1_guess[0]) / num_part_1_1_guess[0]
    else:
        acc_part_1_1_guess[0] = 0.0

    if (num_part_1_m_guess[1] > 0):
        acc_part_1_m_guess[1] = float(acc_part_1_m_guess[1]) / \
                                num_part_1_m_guess[1]
    else:
        acc_part_1_m_guess[1] = 0.0
    if (num_part_1_1_guess[1] > 0):
        acc_part_1_1_guess[1] = float(acc_part_1_1_guess[1]) / \
                                num_part_1_1_guess[1]
    else:
        acc_part_1_1_guess[1] = 0.0

    reduction_ratio_mean = numpy.mean(lenth_filter_reduction_perc_list)

    # Now return the final results
    #
    return num_no_guess, num_too_many_guess, num_1_1_guess, \
           num_corr_1_1_guess, num_part_1_1_guess, num_1_m_guess, \
           num_corr_1_m_guess, num_part_1_m_guess, \
           acc_part_1_1_guess, acc_part_1_m_guess, reduction_ratio_mean


def attack(q, padded, bf_harden, encode_attr_list, plain_attr_list, plain_rec_id_col, same_data_attr_flag,
           encode_bf_dict, bf_encode, hash_type, bf_len, num_hash_funct, enc_param_list,res_file_name, ini_start_time,
           harden_param_list, encode_true_q_gram_pos_map_dict,pattern_mine_method_list,encode_base_data_set_name,
           plain_base_data_set_name,mc_chain_len, mc_sel_method, encode_rec_id_col, encode_rec_val_list,
           encode_attr_name_list, plain_rec_val_list, plain_attr_name_list,
           pattern_mine_method_str, stop_iter_perc, stop_iter_perc_lm, min_part_size,
           max_num_many, re_id_method, expand_lang_model, lang_model_min_freq,
           progress_bar):

    # -----------------------------------------------------------------------------
    # stage1 preparation

    # Get five different dictionaries from encode-text in order to measure
    # the accuracy of the attack
    #
    encode_data_analysis_res = importing.get_data_analysis_dict(encode_rec_val_list,
                                                                encode_attr_list, q, padded,
                                                                encode_rec_id_col, bf_harden)

    encode_q_gram_dict = encode_data_analysis_res[0]
    encode_q_gram_attr_val_dict = encode_data_analysis_res[1]
    encode_attr_val_rec_id_dict = encode_data_analysis_res[2]
    encode_rec_val_dict = encode_data_analysis_res[3]
    encode_rec_val_freq_dict = encode_data_analysis_res[4]
    encode_unique_q_gram_set = encode_data_analysis_res[5]
    encode_attr_val_freq_q_gram_dict = encode_data_analysis_res[6]

    if (same_data_attr_flag == False):

        # Get five different dictionaries from plain-text in order to conduct the
        # attack
        #
        plain_data_analysis_res = importing.get_data_analysis_dict(plain_rec_val_list,
                                                                   plain_attr_list, q, padded,
                                                                   plain_rec_id_col, bf_harden)

        plain_q_gram_dict = plain_data_analysis_res[0]
        plain_q_gram_attr_val_dict = plain_data_analysis_res[1]
        plain_attr_val_rec_id_dict = plain_data_analysis_res[2]
        plain_rec_val_dict = plain_data_analysis_res[3]
        plain_rec_val_freq_dict = plain_data_analysis_res[4]
        plain_unique_q_gram_set = plain_data_analysis_res[5]
        plain_attr_val_freq_q_gram_dict = plain_data_analysis_res[6]

        if (encode_attr_name_list != plain_attr_name_list):
            print('*** Warning: Different attributes used to encode BF and plain text:')
            print('***   BF encode: ', encode_attr_name_list)
            print('***   Plain text:', plain_attr_name_list)

    else:  # Set to same as encode

        plain_rec_val_list = encode_rec_val_list
        plain_attr_name_list = encode_attr_name_list
        plain_q_gram_dict = encode_q_gram_dict
        plain_q_gram_attr_val_dict = encode_q_gram_attr_val_dict
        plain_attr_val_rec_id_dict = encode_attr_val_rec_id_dict
        plain_rec_val_dict = encode_rec_val_dict
        plain_rec_val_freq_dict = encode_rec_val_freq_dict
        plain_unique_q_gram_set = encode_unique_q_gram_set
        plain_attr_val_freq_q_gram_dict = encode_attr_val_freq_q_gram_dict

    plain_num_rec = len(plain_rec_val_dict)

    # Find how many attribute values are in common (exactly) across the two data
    # sets (as this gives an upper bound on re-identification accuracy
    #
    encode_attr_val_set = set(encode_attr_val_rec_id_dict.keys())
    plain_attr_val_set = set(plain_attr_val_rec_id_dict.keys())

    common_attr_val_set = encode_attr_val_set & plain_attr_val_set

    print('Number of unique attribute values in data sets and in common:')
    print('  %d in the encoded data set' % (len(encode_attr_val_set)))
    print('  %d in the plain-text data set' % (len(plain_attr_val_set)))
    perc_comm = 200.0 * float(len(common_attr_val_set)) / \
                (len(encode_attr_val_set) + len(plain_attr_val_set))
    print('  %d occur in both data sets (%2.f%%)' % (len(common_attr_val_set),
                                                     perc_comm))
    print()

    progress_bar.setValue(10)
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # Generate the q-gram support graph (a dictionary of nodes (q-grams) and their
    # counts, and a dictionary of edges (q-gram pairs) and their counts
    #
    plain_q_gram_node_dict, plain_q_gram_edge_dict, plain_q_gram_cond_prob_dict = \
        gen_q_gram_supp_graph(plain_unique_q_gram_set,
                                  plain_q_gram_dict)

    encode_num_bf = len(encode_bf_dict)

    if (same_data_attr_flag == False):

        plain_bf_dict, plain_true_q_gram_pos_map_dict = \
            bfEncoding.gen_bloom_filter_dict(plain_rec_val_list, plain_rec_id_col,
                                      bf_encode, hash_type, bf_len,
                                      num_hash_funct, plain_attr_list, q,
                                      padded, bf_harden, enc_param_list,
                                      harden_param_list)

        plain_num_bf = len(plain_bf_dict)

    else:  # Use same as build
        plain_bf_dict = encode_bf_dict
        plain_true_q_gram_pos_map_dict = encode_true_q_gram_pos_map_dict
        plain_num_bf = encode_num_bf

    # Get the true position q-gram set dictionaries from q-gram position set
    # dictionaries
    #
    encode_true_pos_q_gram_dict = {}
    plain_true_pos_q_gram_dict = {}

    for (q_gram, encode_pos_set) in encode_true_q_gram_pos_map_dict.items():
        for pos in encode_pos_set:
            q_gram_set = encode_true_pos_q_gram_dict.get(pos, set())
            q_gram_set.add(q_gram)
            encode_true_pos_q_gram_dict[pos] = q_gram_set
    for (q_gram, plain_pos_set) in plain_true_q_gram_pos_map_dict.items():
        for pos in plain_pos_set:
            q_gram_set = plain_true_pos_q_gram_dict.get(pos, set())
            q_gram_set.add(q_gram)
            plain_true_pos_q_gram_dict[pos] = q_gram_set

    # Calculate the probability that two q-grams are hashed into the same column
    # (using the birthday paradox) assuming each q-gram is hashed 'num_hash_funct'
    # times
    #
    no_same_col_prob = 1.0
    for i in range(1, 2 * num_hash_funct):
        no_same_col_prob *= float(bf_len - i) / bf_len

    # Convert the encoded BF dictionary into column-wise storage
    #
    if (bf_harden == 'balance'):
        encode_bf_bit_pos_list, encode_rec_id_list = \
            gen_bf_col_dict(encode_bf_dict, bf_len * 2)
    elif (bf_harden == 'fold'):
        encode_bf_bit_pos_list, encode_rec_id_list = \
            gen_bf_col_dict(encode_bf_dict, bf_len / 2)
    else:
        encode_bf_bit_pos_list, encode_rec_id_list = \
            gen_bf_col_dict(encode_bf_dict, bf_len)

    # Get the frequency distribution of how often each BF row and column occurs
    #
    row_count_dict, col_count_dict = get_bf_row_col_freq_dist(encode_bf_dict,
                                                                  encode_bf_bit_pos_list)
    most_freq_bf_pattern_count = max(list(row_count_dict.keys()))
    most_freq_bf_bit_pos_pattern_count = max(list(col_count_dict.keys()))

    # Calculate and print the average Hamming weight for pairs and triplets of
    # randomly selected bit positions
    #
    check_hamming_weight_bit_positions(encode_bf_bit_pos_list, NUM_SAMPLE)

    # -----------------------------------------------------------------------------
    # stage 2: Recursively find most frequent q-gram, then BF bit positions that are
    #         frequent, assign q-gram to them, split BF set into two and repeat process.
    progress_bar.setValue(20)
    start_time = time.time()

    # A dictionary of how q-grams have been assigned to bit positions (keys are
    # positions, values are sets of q-grams), to be used for re-identification
    # later on
    #
    q_gram_pos_assign_dict = {}

    # Two dictionaries with sets of the identified frequent q-grams as they must or
    # cannot occur in a BF. The keys in these dictionaries are record identifiers
    # from the encoded data set, while values are sets of q-grams
    #
    bf_must_have_q_gram_dict = {}
    bf_cannot_have_q_gram_dict = {}

    # A set of identified q-grams, once we have a q-gram identified we will not
    # consider it in a smaller partiton later in the process
    #
    identified_q_gram_set = set()

    # Set the initial row filter bit array to all 1-bits (i.e use all rows / BFs)
    #
    row_filter_bit_array = bitarray.bitarray(encode_num_bf)
    row_filter_bit_array.setall(1)  # Bit set to 1: use the corresponding BF

    # Use a queue of tuples, each consisting of:
    # - partition size:       The number of BFs to consider
    # - column filter set:    These are the columns not to consider in the pattern
    #                         mining approach. Will be empty at beginning, so all
    #                         q-grams are considered.
    # - row filter bit array: These are the rows (BFs) to consider (1-bits) or not
    #                         to consider (0-bits) in the pattern mining approach.
    #                         All rows (BFs) are set to 1 at the beginning.
    # - the set of q-grams that must be in record q-grams sets (empty at beginning)
    # - the set of q-grams that must not be in record q-grams sets (empty at
    #                                                               beginning)
    #
    queue_tuple_list = [(encode_num_bf, set(), row_filter_bit_array, set(), set())]

    # Keep the size (number of q-grams) of the most frequent tuple found in each
    # iteration as these sizes should correspond to the number of hash functions
    #
    most_freq_tuple_size_list = []

    # As long as there are tuples in the queue process the next tuple
    #
    iter_num = 0
    while (queue_tuple_list != []):
        iter_num += 1

        # Get first tuple from list and remove it from queue (pop it)
        #
        this_part_size, col_filter_set, row_filter_bit_array, \
        must_be_in_rec_q_gram_set, must_not_be_in_rec_q_gram_set = \
            queue_tuple_list.pop(0)
        print()
        print('Iteration %d: ---------------------------------------------' % \
              (iter_num))
        print('  Number of BFs to consider: %d (%.2f%% of all BFs)' % \
              (this_part_size, 100.0 * this_part_size / encode_num_bf))
        print('  Column filter set contains %d bit positions (bit positions' % \
              (len(col_filter_set)) + ' not to consider)')
        print('  Row (BF) filter has %d of %d BFs set to 1 (BFs to consider)' % \
              (int(row_filter_bit_array.count(1)), len(row_filter_bit_array)))
        print('  Set of q-grams that must be in a record:    ', \
              must_be_in_rec_q_gram_set)
        print('  Set of q-grams that must not be in a record:', \
              must_not_be_in_rec_q_gram_set)
        print()

        # Get the two most frequent q-grams and their counts of occurrence in the
        # plain text data set in the current partition (i.e. with q-gram sets that
        # must be in records or not in records for filtering)
        #
        freq_q_gram_count_list = get_most_freq_other_q_grams(plain_q_gram_dict,
                                                                 must_be_in_rec_q_gram_set,
                                                                 must_not_be_in_rec_q_gram_set)
        most_freq_q_gram1, most_freq_q_gram_count1 = freq_q_gram_count_list[0]
        most_freq_q_gram2, most_freq_q_gram_count2 = freq_q_gram_count_list[1]

        print('  Top most frequent q-gram "%s" occurs %d times' % \
              (most_freq_q_gram1, most_freq_q_gram_count1))
        print('  Second most frequent q-gram "%s" occurs %d times' % \
              (most_freq_q_gram2, most_freq_q_gram_count2))
        print()

        # If the most frequent q-gram has already been identified in an earlier
        # iteration then don't consider it
        #
        if (most_freq_q_gram1 in identified_q_gram_set):
            print('    *** Most frequent q-gram already identified in an earlier ' + \
                  'iteration - no need to re-identify so abort iteration ***')
            print()
            continue

        # Calculate the average frequency between the top two q-grams (to be used as
        # minimum count (minimum support) in the pattern mining algorithm), the idea
        # being that this count should only result in columns of the top most
        # frequent q-gram to be included in the final set of selected columns (bit
        # positions).
        #
        avr_top_count = float(most_freq_q_gram_count1 + most_freq_q_gram_count2) / 2.0

        # To get a suitable minimum count of 1-bits in the Bloom filters, we take the
        # average q-gram count and convert it into a corresponding minimum 1-bit
        # count for the Bloom filter encoded database
        #
        avr_top_q_gram_perc = float(avr_top_count) / plain_num_rec

        # The minimum number of BFs that should have a 1-bit in the columns that
        # possibly can encode the most frequent q-gram
        #
        apriori_bf_min_count = int(math.floor(avr_top_q_gram_perc * encode_num_bf))

        # As stopping criteria check if the difference in counts is large enough
        # (the smaller the difference in count the less clear the pattern mining
        # algorithm will work)
        #
        # Percentage difference between the two most frequent q-grams (in the current
        # partition) relative to each other
        #
        most_freq_count_diff_perc = 100.0 * float(most_freq_q_gram_count1 - \
                                                  most_freq_q_gram_count2) / avr_top_count

        # Check if the difference is large enough to continue recursive splitting
        #
        #
        if (most_freq_count_diff_perc >= stop_iter_perc):  # Large enough
            print('    Difference large enough (>= %.2f%%) ' % (stop_iter_perc) \
                  + 'to continue recursive splitting')
            print()

        else:  # Stop the iterative process (do not append new tuples below)
            print('    *** Difference too small to apply Apriori on this partition,')
            print('abort iteration ***')
            print()

            continue  # Go back and process remaining tuples in the queue

        # Now run all selected pattern mining methods, keep all returned
        # dictionaries with longest maximal frequent bit postion tuples, and if
        # there are several then check the yare all the same
        #
        pattern_mine_res_list = []  # pairs of result dictionaries and time used

        for pattern_mine_method in pattern_mine_method_list:

            pm_start_time = time.time()

            if (pattern_mine_method == 'apriori'):

                # Run the Apriori pattern mining approach, i.e. find set of longest
                # bit positions (BF columns) with a minimum count of common 1-bits)
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_apriori(encode_bf_bit_pos_list,
                                                          apriori_bf_min_count,
                                                          col_filter_set,
                                                          row_filter_bit_array)

            elif (pattern_mine_method == 'mapriori'):

                # Version of Apriori which stores the actual BFs not just Hamming
                # weights, so approach this is faster but needs more memory
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_apriori_memo(encode_bf_bit_pos_list,
                                                               apriori_bf_min_count,
                                                               col_filter_set,
                                                               row_filter_bit_array)

            elif (pattern_mine_method == 'maxminer'):

                # Run the Max-Miner approach (Bayardo, 1998)
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_max_miner(encode_bf_bit_pos_list,
                                                            apriori_bf_min_count,
                                                            col_filter_set,
                                                            row_filter_bit_array)
            elif (pattern_mine_method == 'hmine'):

                # Run the H-mine approach (J Pei, J Han, H Lu, et al., 2007)
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_h_mine(encode_bf_bit_pos_list,
                                                         apriori_bf_min_count,
                                                         col_filter_set,
                                                         row_filter_bit_array)

            elif (pattern_mine_method == 'fpmax'):

                # Run the FP tree and FPmax algorithm
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_fp_max(encode_bf_bit_pos_list,
                                                         apriori_bf_min_count,
                                                         col_filter_set,
                                                         row_filter_bit_array)
            else:
                raise Exception(pattern_mine_method)  # Illegal method

            pm_time = time.time() - pm_start_time

            pattern_mine_res_list.append((pm_freq_bf_bit_pos_dict, pm_time))
        progress_bar.setValue(30)
        # Take the first result dictionary as the main result to use
        #
        freq_bf_bit_pos_dict = pattern_mine_res_list[0][0]
        freq_bf_bit_pos_dict_sorted_list = sorted(freq_bf_bit_pos_dict.items())

        # If more than one pattern mining method was run check if all result the same
        #
        if (len(pattern_mine_method_list) > 1):
            print('  Pattern mining result checks:')

            max_pm_time = -1  # Get maximum time

            for pm_res_tuple in pattern_mine_res_list:
                max_pm_time = max(max_pm_time, pm_res_tuple[1])

            all_same = True

            for (i, pattern_mine_method) in enumerate(pattern_mine_method_list):
                pm_time = pattern_mine_res_list[i][1]
                pm_time_perc = 100.0 * pm_time / max_pm_time

                print('    %10s: %.2f sec (%.2f%%)' % (pattern_mine_method, \
                                                       pm_time, pm_time_perc))
                print('                %s' % \
                      (str(sorted(pattern_mine_res_list[i][0].items()))))

                if (sorted(pattern_mine_res_list[i][0].items()) != \
                        freq_bf_bit_pos_dict_sorted_list):
                    all_same = False

            if (all_same == True):
                print('  All pattern mining methods return same longest maximal ' + \
                      'frequent set of bit positions')
            else:
                print('  *** Pattern mining methods return different longest maximal' + \
                      ' frequent set of bit positions! ***')
                sys.exit()
            print()

        # If no frequent bit position tuple found end the iteration
        #
        if (len(freq_bf_bit_pos_dict) == 0):
            print('## Iteration %d:' % (iter_num))
            print('##   No frequent bit position tuple found!')
            print('##')
            continue

        if (len(freq_bf_bit_pos_dict) == 1):  # Only one longest bit position tuple

            most_freq_pos_tuple, most_freq_count = list(freq_bf_bit_pos_dict.items())[0]
            print('  One single longest bit position tuple of length %d and ' % \
                  (len(most_freq_pos_tuple)) + 'frequency %d identified' % \
                  (most_freq_count))
            print()

        else:  # Several longest bit position tuples

            # Calculate percentage difference of two most frequent bit position tuples,
            # and only keep the most frequent one if this difference is large enough
            #
            sorted_freq_bf_bit_pos_list = sorted(freq_bf_bit_pos_dict.items(),
                                                 key=lambda t: t[1], reverse=True)

            print('  %d longest bit position tuple of length %d identified' % \
                  (len(freq_bf_bit_pos_dict), len(sorted_freq_bf_bit_pos_list[0][0])))

            # Get the two highest frequencies
            #
            most_freq_bit_pos_tuple_count1 = sorted_freq_bf_bit_pos_list[0][1]
            most_freq_bit_pos_tuple_count2 = sorted_freq_bf_bit_pos_list[1][1]
            assert most_freq_bit_pos_tuple_count1 >= most_freq_bit_pos_tuple_count2

            print('    Frequencies of two most frequent bit position tuples: ' + \
                  '%d / %d' % (most_freq_bit_pos_tuple_count1, \
                               most_freq_bit_pos_tuple_count2))

            # Calculate the percentage difference between their frequencies
            #
            avr_top_bit_pos_count = float(most_freq_bit_pos_tuple_count1 + \
                                          most_freq_bit_pos_tuple_count2) / 2.0

            most_freq_bit_pos_count_diff_perc = 100.0 * \
                                                float(most_freq_bit_pos_tuple_count1 - \
                                                      most_freq_bit_pos_tuple_count2) / avr_top_bit_pos_count

            if (most_freq_bit_pos_count_diff_perc >= stop_iter_perc):  # Large enough
                print('    Difference large enough (>= %.2f%%) ' % (stop_iter_perc) \
                      + 'to clearly assign q-gram to bit positions')
                print()

                most_freq_pos_tuple, most_freq_count = sorted_freq_bf_bit_pos_list[0]

            else:  # Stop the iterative process (do not append new tuples below)
                print('    *** Difference too small to clearly assign q-gram to bit ' + \
                      'positions ***')
                print()

                continue  # End iteration, process remaining tuples in the queue

        # If this is not the first iteration then check the number of bit positions
        # identified, if much less than the average found in previous iterations
        # then print a warning
        #
        if (most_freq_tuple_size_list != []):
            num_pos_identified = len(most_freq_pos_tuple)

            avr_num_pos_identified = numpy.mean(most_freq_tuple_size_list)

            max_diff = avr_num_pos_identified * CHECK_POS_TUPLE_SIZE_DIFF_PERC / 100.0

            # Check if enough bit positions were identified
            #
            if (num_pos_identified + max_diff < avr_num_pos_identified):
                print('  *** Warning, most frequent tuple does not contain enough ' + \
                      'bit positions (%d versus %.1f average so far), abort ' % \
                      (num_pos_identified, avr_num_pos_identified) + 'iteration ***')
                print()
                continue

        most_freq_tuple_size_list.append(len(most_freq_pos_tuple))

        assert most_freq_count >= apriori_bf_min_count, \
            (most_freq_count, apriori_bf_min_count)

        # Assign the most frequent q-gram from plain text to the selected positions
        #
        for pos in most_freq_pos_tuple:
            pos_q_gram_set = q_gram_pos_assign_dict.get(pos, set())
            pos_q_gram_set.add(most_freq_q_gram1)
            q_gram_pos_assign_dict[pos] = pos_q_gram_set

        # Add the most frequent q-gram to the set of identified q-grams
        #
        identified_q_gram_set.add(most_freq_q_gram1)

        # Count in how many of the selected bit positions does the most frequent
        # q-gram occur (assume true assignment of q-grams to bit positions is known)
        #
        encode_num_bit_pos_with_most_freq_q_gram = 0
        plain_num_bit_pos_with_most_freq_q_gram = 0

        for pos in most_freq_pos_tuple:
            if (most_freq_q_gram1 in encode_true_pos_q_gram_dict.get(pos, set())):
                encode_num_bit_pos_with_most_freq_q_gram += 1
            if (most_freq_q_gram1 in plain_true_pos_q_gram_dict.get(pos, set())):
                plain_num_bit_pos_with_most_freq_q_gram += 1

        # Print a summary of the iteration and results
        #
        print('## Iteration %d summary:' % (iter_num))
        print('##   Two most frequent q-grams from plain-text and their counts:' \
              + ' ("%s" / %d) and  ("%s" / %d)' % (most_freq_q_gram1,
                                                   most_freq_q_gram_count1, most_freq_q_gram2, most_freq_q_gram_count2))
        print('##   Column filter contains %d bit positions, row bit filter ' % \
              (len(col_filter_set)) + 'has %d of %d 1-bits' % \
              (int(row_filter_bit_array.count(1)), len(row_filter_bit_array)))
        print('##   Set of must / must not occurring record q-grams: %s / %s' % \
              (must_be_in_rec_q_gram_set, must_not_be_in_rec_q_gram_set))
        print('##   Most frequent selected set of %d bit positions %s ' % \
              (len(most_freq_pos_tuple), most_freq_pos_tuple) + 'occurs %d times' \
              % (most_freq_count))
        print('##   Most frequent g-gram "%s" occurs in %d of %d selected bit ' \
              % (most_freq_q_gram1, encode_num_bit_pos_with_most_freq_q_gram,
                 len(most_freq_pos_tuple)) + 'positions for encode BFs')
        print('##   Most frequent g-gram "%s" occurs in %d of %d selected bit ' \
              % (most_freq_q_gram1, plain_num_bit_pos_with_most_freq_q_gram,
                 len(most_freq_pos_tuple)) + 'positions for plain-text BFs')
        print('##')
        print()
        progress_bar.setValue(40)
        # Update the column filter set with the newly assigned columns (we basically
        # assume that once a q-gram has been assigned to a column then do not re-use
        # the column - this is of course not correct
        #
        next_col_filter_set = col_filter_set.union(set(most_freq_pos_tuple))

        # Because q-grams can share bit positions (see birthday paradox probability
        # calculated above), the recursive calls will generate different column
        # filter sets
        #
        print('  Next column filter set:', sorted(next_col_filter_set))
        print()

        # Generate the rows (BFs) where all selected columns have a 1-bit (as the
        # intersection of all BF bit positions that have the most frequent q-gram
        # assigned to them)
        #
        sel_bit_row_filter_bit_array = bitarray.bitarray(encode_num_bf)
        sel_bit_row_filter_bit_array.setall(1)

        for pos in most_freq_pos_tuple:
            sel_bit_row_filter_bit_array = sel_bit_row_filter_bit_array & \
                                           encode_bf_bit_pos_list[pos]

        assert int(sel_bit_row_filter_bit_array.count(1)) >= most_freq_count, \
            (int(sel_bit_row_filter_bit_array.count(1)), most_freq_count)

        # Assign the most frequent q-gram to all BFs that have 1-bits in all selected
        # bit positions (as must have q-gram), and as cannot have q-gram to all to
        # all other BFs
        #
        assert len(sel_bit_row_filter_bit_array) == encode_num_bf
        assert len(encode_rec_id_list) == encode_num_bf

        for i in range(encode_num_bf):
            bf_rec_id = encode_rec_id_list[i]

            # A 1-bit means the most frequent q-gram is assumed to occur in a BF
            #
            if (sel_bit_row_filter_bit_array[i] == 1):
                bf_q_gram_set = bf_must_have_q_gram_dict.get(bf_rec_id, set())
                bf_q_gram_set.add(most_freq_q_gram1)
                bf_must_have_q_gram_dict[bf_rec_id] = bf_q_gram_set

            else:  # A 0-bit means the q-gram is assumed not to occur in the BF
                bf_q_gram_set = bf_cannot_have_q_gram_dict.get(bf_rec_id, set())
                bf_q_gram_set.add(most_freq_q_gram1)
                bf_cannot_have_q_gram_dict[bf_rec_id] = bf_q_gram_set

        # Generate the two row filters for the next two pattern mining calls
        #
        next_row_filter_bit_array = row_filter_bit_array & \
                                    sel_bit_row_filter_bit_array

        sel_bit_row_filter_bit_array.invert()  # Negate all bits
        next_neg_row_filter_bit_array = row_filter_bit_array & \
                                        sel_bit_row_filter_bit_array
        assert (int(row_filter_bit_array.count(1)) == \
                int(next_row_filter_bit_array.count(1)) + \
                int(next_neg_row_filter_bit_array.count(1))), \
            (int(row_filter_bit_array.count(1)), \
             int(next_row_filter_bit_array.count(1)) + \
             int(next_neg_row_filter_bit_array.count(1)))

        # Add the most frequent q-gram to the set of q-grams that must or must not
        # occur in records for the next two iterations (tuples to be added to the
        # queue)
        #
        next_must_be_in_rec_q_gram_set = \
            must_be_in_rec_q_gram_set.union(set([most_freq_q_gram1]))
        next_must_not_be_in_rec_q_gram_set = \
            must_not_be_in_rec_q_gram_set.union(set([most_freq_q_gram1]))

        # Append two new tuples to queue (one for the sub-set of rows with the most
        # frequent q-gram, the other for rows without the most frequent q-grams)
        #
        # Only add a tuple if its corresponding partition (number of rows to
        # consider) is large enough (larger than min_part_size)
        #
        # In the first tuple, add the new found most frequent q-gram to the set of
        # q-grams that must be in a record.
        # In the second tuple, add it to the set of q-grams that must not be in a
        # record.
        #
        pos_part_size = int(next_row_filter_bit_array.count(1))
        neg_part_size = int(next_neg_row_filter_bit_array.count(1))

        if (pos_part_size >= min_part_size):
            queue_tuple_list.append((pos_part_size, next_col_filter_set,
                                     next_row_filter_bit_array,
                                     next_must_be_in_rec_q_gram_set,
                                     must_not_be_in_rec_q_gram_set))
            print('  Added positive tuple with %d BFs to the queue' % (pos_part_size))
            print()

        if (neg_part_size >= min_part_size):
            queue_tuple_list.append((neg_part_size, next_col_filter_set,
                                     next_neg_row_filter_bit_array,
                                     must_be_in_rec_q_gram_set,
                                     next_must_not_be_in_rec_q_gram_set))
            print('  Added negative tuple with %d BFs to the queue' % (neg_part_size))
            print()

        # Sort the queue according to partition size, with largest partition first
        #
        queue_tuple_list.sort(reverse=True)
    progress_bar.setValue(45)
    # ------------------------------------------------------------------------------
    # Check if the pattern mining algorithm failed to identify any frequent patterns
    # from the very 1st iteration. If there are no frequent patterns identified
    # stop the programme and write results to a different file
    #

    if (len(most_freq_tuple_size_list) == 0):

        program_stop_file_name = 'bf-attack-col-pattern-programme-stop-results.csv'
        stop_reason = 'no-freq-bit-pos'

        apriori_time = time.time() - start_time

        today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())

        res_list = [today_time_str, encode_base_data_set_name,
                    len(encode_q_gram_dict),
                    str(encode_attr_name_list), plain_base_data_set_name,
                    len(plain_q_gram_dict), str(plain_attr_name_list),
                    #
                    q, bf_len, num_hash_funct, hash_type, bf_harden,
                    mc_chain_len, mc_sel_method,
                    bf_encode, padded,
                    #
                    stop_iter_perc, min_part_size,
                    #
                    apriori_time, stop_reason
                    ]

        # Generate header line with column names
        #
        header_list = ['today_time_str', 'encode_data_set_name', 'encode_num_rec',
                       'encode_used_attr', 'plain_data_set_name', 'plain_num_rec',
                       'plain_used_attr',
                       #
                       'q', 'bf_len', 'num_hash_funct', 'hash_type', 'bf_harden',
                       'mc_chain_len', 'mc_sel_method',
                       'encode_method', 'padded',
                       #
                       'stop_iter_perc', 'min_part_size',
                       #
                       'apriori_time', 'stop_reason'
                       ]

        if (not os.path.isfile(program_stop_file_name)):
            csv_writer = csv.writer(open(program_stop_file_name, 'w'))

            csv_writer.writerow(header_list)

            print('Created new result file:', program_stop_file_name)

        else:  # Append results to an existing file
            csv_writer = csv.writer(open(program_stop_file_name, 'a'))

            print('Append results to file:', program_stop_file_name)

        csv_writer.writerow(res_list)
        sys.exit()

    # ------------------------------------------------------------------------------

    print('Size of the most frequent tuples found in all iterations:', \
          most_freq_tuple_size_list)

    # Take the mode of this list as estimate of the number of hash functions
    #
    est_num_hash_funct = max(set(most_freq_tuple_size_list), \
                             key=most_freq_tuple_size_list.count)
    print('  Estimated number of hash functions: %d' % (est_num_hash_funct))
    print()

    # Final processing of the sets of must have and cannot have q-gram sets per BF:
    # Remove cannot have q-grams from sets of must have q-grams
    #
    for i in range(encode_num_bf):

        if (i in bf_must_have_q_gram_dict) and (i in bf_cannot_have_q_gram_dict):
            bf_rec_id = encode_rec_id_list[i]

            bf_must_have_q_gram_set = bf_must_have_q_gram_dict[bf_rec_id]
            bf_cannot_have_q_gram_set = bf_cannot_have_q_gram_dict[bf_rec_id]

            # Remove the cannot have q-grams from the must have q-grams
            #
            final_bf_must_have_q_gram_set = \
                bf_must_have_q_gram_set - bf_cannot_have_q_gram_set
            if (final_bf_must_have_q_gram_set != bf_must_have_q_gram_set):
                bf_must_have_q_gram_dict[bf_rec_id] = final_bf_must_have_q_gram_set

    # Output results of Apriori based BF analysis
    #
    print('#### Pattern-mining BF bit position analysis took', iter_num, ' iterations')
    print('####   Encoded data set: ', encode_base_data_set_name)
    print('####     Attributes used:', encode_attr_name_list)
    print('####     Number of records and BFs: %d' % (len(plain_q_gram_dict)))
    if (encode_base_data_set_name == plain_base_data_set_name):
        print('####   Plain-text data set: *** Same as build data set ***')
    else:
        print('####   Plain-text data set:', plain_base_data_set_name)
        print('####     Attributes used:', plain_attr_name_list)
        print('####     Number of records and BFs: %d' % (len(plain_q_gram_dict)))
    print('####   Parameters: q=%d, k=%d, bf_len=%d, hash type=%s, BF harden=%s' \
          % (q, num_hash_funct, bf_len, hash_type, bf_harden))
    print('####     Most frequent BF pattern occurs %d times, most frequent BF ' \
          % (most_freq_bf_pattern_count) + 'bit pattern occurs %d times' % \
          (most_freq_bf_bit_pos_pattern_count))
    print('####')

    # For each identified q-gram first get its true bit positions in the encoded
    # and the plain-text databases
    #
    encode_true_q_gram_pos_dict = encode_true_q_gram_pos_map_dict
    plain_true_q_gram_pos_dict = plain_true_q_gram_pos_map_dict

    encode_bit_pos_q_gram_reca_list = []
    plain_bit_pos_q_gram_reca_list = []

    encode_bit_pos_q_gram_prec_list = []
    plain_bit_pos_q_gram_prec_list = []

    encode_bit_pos_q_gram_false_pos_list = []  # Also keep track of how many wrong
    plain_bit_pos_q_gram_false_pos_list = []  # positions we identified

    assigned_q_gram_pos_dict = {}
    for (pos, pos_q_gram_set) in q_gram_pos_assign_dict.items():
        for q_gram in pos_q_gram_set:
            q_gram_pos_set = assigned_q_gram_pos_dict.get(q_gram, set())
            q_gram_pos_set.add(pos)
            assigned_q_gram_pos_dict[q_gram] = q_gram_pos_set
    print('#### Assignment of BF bit positions to q-grams:')
    for (q_gram, pos_set) in sorted(assigned_q_gram_pos_dict.items()):
        print('####   "%s": %s' % (q_gram, str(sorted(pos_set))))

        encode_true_q_gram_set = encode_true_q_gram_pos_dict[q_gram]
        plain_true_q_gram_set = plain_true_q_gram_pos_dict[q_gram]

        encode_recall = float(len(pos_set.intersection(encode_true_q_gram_set))) / \
                        len(encode_true_q_gram_set)
        plain_recall = float(len(pos_set.intersection(plain_true_q_gram_set))) / \
                       len(plain_true_q_gram_set)

        # Percentage of false identified positions for a q-gram
        #
        encode_false_pos_rate = float(len(pos_set - encode_true_q_gram_set)) / \
                                len(pos_set)
        plain_false_pos_rate = float(len(pos_set - plain_true_q_gram_set)) / \
                               len(pos_set)

        assert (0.0 <= encode_false_pos_rate) and (1.0 >= encode_false_pos_rate), \
            encode_false_pos_rate
        assert (0.0 <= plain_false_pos_rate) and (1.0 >= plain_false_pos_rate), \
            plain_false_pos_rate

        encode_bit_pos_q_gram_reca_list.append(encode_recall)
        plain_bit_pos_q_gram_reca_list.append(plain_recall)

        encode_bit_pos_q_gram_false_pos_list.append(encode_false_pos_rate)
        plain_bit_pos_q_gram_false_pos_list.append(plain_false_pos_rate)

    print('####')
    print('#### Encoding assignment of q-grams to bit position recall:   ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(encode_bit_pos_q_gram_reca_list),
           numpy.mean(encode_bit_pos_q_gram_reca_list),
           max(encode_bit_pos_q_gram_reca_list)))
    print('####   Number and percentage of q-grams with recall 1.0: %d / %.2f%%' \
          % (encode_bit_pos_q_gram_reca_list.count(1.0),
             100.0 * float(encode_bit_pos_q_gram_reca_list.count(1.0)) / \
             (len(identified_q_gram_set) + 0.0001)))
    print('#### Plain-text assignment of q-grams to bit position recall: ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(plain_bit_pos_q_gram_reca_list),
           numpy.mean(plain_bit_pos_q_gram_reca_list),
           max(plain_bit_pos_q_gram_reca_list)))
    print('####   Number and percentage of q-grams with recall 1.0: %d / %.2f%%' \
          % (plain_bit_pos_q_gram_reca_list.count(1.0),
             100.0 * float(plain_bit_pos_q_gram_reca_list.count(1.0)) / \
             (len(identified_q_gram_set) + 0.0001)))
    print('####')
    print('#### Encoding assignment of q-grams to bit position false ' + \
          'positive rate:   %.2f min / %.2f avr / %.2f max' % \
          (min(encode_bit_pos_q_gram_false_pos_list),
           numpy.mean(encode_bit_pos_q_gram_false_pos_list),
           max(encode_bit_pos_q_gram_false_pos_list)))
    print('####   Number and percentage of q-grams with false positive rate' + \
          ' 0.0: %d / %.2f%%' \
          % (encode_bit_pos_q_gram_false_pos_list.count(0.0),
             100.0 * float(encode_bit_pos_q_gram_false_pos_list.count(0.0)) / \
             (len(identified_q_gram_set) + 0.0001)))
    print('#### Plain-text assignment of q-grams to bit position false ' + \
          'positive rate: %.2f min / %.2f avr / %.2f max' % \
          (min(plain_bit_pos_q_gram_false_pos_list),
           numpy.mean(plain_bit_pos_q_gram_false_pos_list),
           max(plain_bit_pos_q_gram_false_pos_list)))
    print('####   Number and percentage of q-grams with false positive rate' + \
          ' 0.0: %d / %.2f%%' \
          % (plain_bit_pos_q_gram_false_pos_list.count(0.0),
             100.0 * float(plain_bit_pos_q_gram_false_pos_list.count(0.0)) / \
             (len(identified_q_gram_set) + 0.0001)))
    print('####')

    # Calculate the precision of the assignment of q-grams to bit positions
    #
    encode_q_gram_to_bit_pos_assign_prec_list = []
    plain_q_gram_to_bit_pos_assign_prec_list = []

    encode_total_num_correct = 0  # Also count how many assignments of q-grams to
    encode_total_num_wrong = 0  # bit positions are wrong and how many correct
    plain_total_num_correct = 0
    plain_total_num_wrong = 0
    progress_bar.setValue(50)
    print('#### Assignment of q-grams to BF bit positions:')
    for (pos, pos_q_gram_set) in sorted(q_gram_pos_assign_dict.items()):
        q_gram_set_str_list = []  # Strings to be printed

        encode_pos_corr = 0  # Correctly assigned q-grams to this bit position
        plain_pos_corr = 0

        for q_gram in pos_q_gram_set:
            if (q_gram in encode_true_pos_q_gram_dict.get(pos, set())):
                assign_str = 'encode correct'
                encode_pos_corr += 1
                encode_total_num_correct += 1
            else:
                assign_str = 'encode wrong'
                encode_total_num_wrong += 1
            if (same_data_attr_flag == False):  # Check analysis BF
                if (q_gram in plain_true_pos_q_gram_dict.get(pos, set())):
                    assign_str += ', plain-text correct'
                    plain_pos_corr += 1
                    plain_total_num_correct += 1
                else:
                    assign_str += ', plain-text wrong'
                    plain_total_num_wrong += 1
            else:  # Encode and plain-text data sets are the same
                if (q_gram in encode_true_pos_q_gram_dict.get(pos, set())):
                    assign_str = 'plain-text correct'
                    plain_pos_corr += 1
                    plain_total_num_correct += 1
                else:
                    assign_str = 'plain-text wrong'
                    plain_total_num_wrong += 1

            q_gram_set_str_list.append('"%s" (%s)' % (q_gram, assign_str))

        encode_pos_proc = float(encode_pos_corr) / len(pos_q_gram_set)
        plain_pos_proc = float(plain_pos_corr) / len(pos_q_gram_set)

        encode_q_gram_to_bit_pos_assign_prec_list.append(encode_pos_proc)
        plain_q_gram_to_bit_pos_assign_prec_list.append(plain_pos_proc)

        print('####   %3d: %s' % (pos, ', '.join(q_gram_set_str_list)))

    print('####')
    print('#### Encoding q-gram to bit position assignment precision:   ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(encode_q_gram_to_bit_pos_assign_prec_list),
           numpy.mean(encode_q_gram_to_bit_pos_assign_prec_list),
           max(encode_q_gram_to_bit_pos_assign_prec_list)))
    print('####   Number and percentage of positions with precison 1.0: ' + \
          '%d / %.2f%%' % (encode_q_gram_to_bit_pos_assign_prec_list.count(1.0),
                           100.0 * float(encode_q_gram_to_bit_pos_assign_prec_list.count(1.0)) / \
                           (len(q_gram_pos_assign_dict) + 0.0001)))
    print('#### Plain-text q-gram to bit position assignment precision: ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(plain_q_gram_to_bit_pos_assign_prec_list),
           numpy.mean(plain_q_gram_to_bit_pos_assign_prec_list),
           max(plain_q_gram_to_bit_pos_assign_prec_list)))
    print('####   Number and percentage of positions with precison 1.0: ' + \
          '%d / %.2f%%' % (plain_q_gram_to_bit_pos_assign_prec_list.count(1.0),
                           100.0 * float(plain_q_gram_to_bit_pos_assign_prec_list.count(1.0)) / \
                           (len(q_gram_pos_assign_dict) + 0.0001)))
    print('#### Encoding total number of correct and wrong assignments:  ' + \
          '%d / %d (%.2f%% correct)' % (encode_total_num_correct,
                                        encode_total_num_wrong, 100.0 * float(encode_total_num_correct) / \
                                        (encode_total_num_correct + encode_total_num_wrong + 0.0001)))
    print('#### Plain-text total number of correct and wrong assignments: ' + \
          '%d / %d (%.2f%% correct)' % (plain_total_num_correct,
                                        plain_total_num_wrong, 100.0 * float(plain_total_num_correct) / \
                                        (plain_total_num_correct + plain_total_num_wrong + 0.0001)))
    print('#### ' + '-' * 80)
    print('####')
    print()

    # Calculate statistics and quality of the must have and cannot have q-gram
    # sets assigned to BFs
    #
    bf_must_have_set_size_list = []
    bf_cannot_have_set_size_list = []

    for q_gram_set in bf_must_have_q_gram_dict.values():
        bf_must_have_set_size_list.append(len(q_gram_set))
    for q_gram_set in bf_cannot_have_q_gram_dict.values():
        bf_cannot_have_set_size_list.append(len(q_gram_set))

    print('#### Summary of q-gram sets assigned to BFs:')
    print('####  %d of %d BF have must have q-grams assigned to them' % \
          (len(bf_must_have_set_size_list), encode_num_bf))
    print('####    Minimum, average and maximum number of q-grams assigned: ' + \
          '%d / %.2f / %d' % (min(bf_must_have_set_size_list),
                              numpy.mean(bf_must_have_set_size_list),
                              max(bf_must_have_set_size_list)))
    print('####  %d of %d BF have cannot have q-grams assigned to them' % \
          (len(bf_cannot_have_set_size_list), encode_num_bf))
    print('####    Minimum, average and maximum number of q-grams assigned: ' + \
          '%d / %.2f / %d' % (min(bf_cannot_have_set_size_list),
                              numpy.mean(bf_cannot_have_set_size_list),
                              max(bf_cannot_have_set_size_list)))
    print('####')

    # Calculate the quality of the identified must / cannot q-gram sets as:
    # - precision of must have q-grams (how many of those identified are in a BF)
    # - precision of cannot have q-grams (how many of those identified are not in
    #   a BF)
    #
    bf_must_have_prec_list = []
    bf_cannot_have_prec_list = []

    for (bf_rec_id, q_gram_set) in bf_must_have_q_gram_dict.items():
        true_q_gram_set = encode_q_gram_dict[bf_rec_id]
        must_have_prec = float(len(q_gram_set & true_q_gram_set)) / len(q_gram_set)

        bf_must_have_prec_list.append(must_have_prec)

    for (bf_rec_id, q_gram_set) in bf_cannot_have_q_gram_dict.items():
        true_q_gram_set = encode_q_gram_dict[bf_rec_id]

        cannot_have_prec = 1.0 - float(len(q_gram_set & true_q_gram_set)) / \
                           len(q_gram_set)

        bf_cannot_have_prec_list.append(cannot_have_prec)
    progress_bar.setValue(55)
    print('#### Precision of q-gram sets assigned to BFs:')
    print('####   Must have q-gram sets minimum, average, maximum precision: ' + \
          '%.2f / %.2f / %.2f' % (min(bf_must_have_prec_list),
                                  numpy.mean(bf_must_have_prec_list),
                                  max(bf_must_have_prec_list)))
    print('####     Ratio of BFs with must have precision 1.0: %.3f' % \
          (float(bf_must_have_prec_list.count(1.0)) / \
           (len(bf_must_have_prec_list) + 0.0001)))
    print('####   Cannot have q-gram sets minimum, average, maximum precision: ' \
          + '%.2f / %.2f / %.2f' % (min(bf_cannot_have_prec_list),
                                    numpy.mean(bf_cannot_have_prec_list),
                                    max(bf_cannot_have_prec_list)))
    print('####     Ratio of BFs with cannot have precision 1.0: %.3f' % \
          (float(bf_cannot_have_prec_list.count(1.0)) / \
           (len(bf_cannot_have_prec_list) + 0.0001)))
    print('####')
    print()

    # -----------------------------------------------------------------------------
    # stage 3: Using a q-gram language model, identify further q-grams that occur
    #         frequently together with one or a set of the the so far identified
    #         frequent q-grams (i.e. there is a high conditional probability that
    #         a new q-gram occurs given one or several frequent does occur in a BF)
    #
    start_time = time.time()

    # First generate the desired language model (with minimum frequency as 1)
    #
    lang_model_dict = gen_lang_model(expand_lang_model, identified_q_gram_set,
                                         plain_q_gram_dict,
                                         plain_attr_val_freq_q_gram_dict,
                                         lang_model_min_freq)

    # For each frequent q-gram (tuple) collect all other q-grams identified and
    # their bit positions
    #
    freq_q_gram_other_q_gram_dict = {}

    # Keep the q-grams identified in this expansion step
    #
    new_q_gram_res_dict = {}

    identified_q_gram_set2 = set()  # New q-grams identified in this step

    # A dictionary of how q-grams have been assigned to bit positions (keys are
    # positions, values are sets of q-grams), to be used for re-identification
    # later on (use q_gram_pos_assign_dict2 as q_gram_pos_assign_dict was used in
    # step 3)
    #
    q_gram_pos_assign_dict2 = {}

    # Two dictionaries with sets of the identified frequent q-grams as they must or
    # cannot occur in a BF. The keys in these dictionaries are record identifiers
    # from the encoded data set, while values are sets of q-grams
    # (use bf_must_have_q_gram_dict2 and bf_cannot_have_q_gram_dict2 as
    # bf_must_have_q_gram_dict and bf_cannot_have_q_gram_dict used in step 3)
    #
    bf_must_have_q_gram_dict2 = {}
    bf_cannot_have_q_gram_dict2 = {}

    # A dictionary with the newly identified q-grams and the positions assigned to
    # them
    #
    assigned_q_gram_pos_dict2 = {}

    # Get the set of the so far considered bit positions, i.e. those to which a
    # frequent q-gram has been assigned to. Only bit positions not in this set
    # will be considered in this expansion step.
    #
    considered_bit_pos_set = set()

    # From the language model get frequency of the frequent q-grams / tuples, and
    # sort them with most frequent first.
    #
    freq_q_gram_tuples_freq_sorted = sorted(lang_model_dict.items(),
                                            key=lambda t: t[1][0], reverse=True)
    # for q_gram_tuple in freq_q_gram_tuples_freq_sorted:
    #  print q_gram_tuple[0], q_gram_tuple[1][0], len(q_gram_tuple[1][1]), \
    #        len(q_gram_tuple[1][1])

    total_corr_num_bfs = 0
    total_wrng_num_bfs = 0

    # Loop over all frequent q-grams / tuples (most frequent first) - - - - - - - -
    #
    progress_bar.setValue(65)
    while (len(freq_q_gram_tuples_freq_sorted) > 0):
        freq_q_gram_tuple = freq_q_gram_tuples_freq_sorted.pop(0)  # Take first

        freq_q_gram_key = freq_q_gram_tuple[0]
        freq_q_gram_key_freq = freq_q_gram_tuple[1][0]
        freq_q_gram_attr_val_set = freq_q_gram_tuple[1][1]
        freq_q_gram_not_freq_dict = freq_q_gram_tuple[1][2]

        print('  Processing frequent q-gram (tuple):', freq_q_gram_key)
        print('    With frequency: %d, %d candidate attribute values and %d not' % \
              (freq_q_gram_key_freq, len(freq_q_gram_attr_val_set),
               len(freq_q_gram_not_freq_dict)) + ' frequent q-grams:')

        # Sort the not-frequent q-grams according to their frequencies
        #
        not_freq_q_gram_list_sorted = sorted(freq_q_gram_not_freq_dict.items(),
                                             key=lambda t: t[1], reverse=True)
        print('     ', not_freq_q_gram_list_sorted[:5], '...')

        # Calculate the conditional probabilities of the not frequent q-grams with
        # regard to the frequent q-gram tuple
        #
        q_gram_cond_prob_list = []

        for (not_freq_q_gram, q_gram_freq) in not_freq_q_gram_list_sorted:
            cond_prob = float(q_gram_freq) / freq_q_gram_key_freq
            assert cond_prob <= 1.0, (cond_prob, q_gram_freq, freq_q_gram_key_freq)
            q_gram_cond_prob_list.append((not_freq_q_gram, cond_prob))

        # Check if conditional probability list is empty
        # if so continue
        if (len(q_gram_cond_prob_list) == 0):
            print('    Conditional probablity list is empty. Continuing the loop...')
            continue

        # Check sorted descending
        #
        if (len(q_gram_cond_prob_list) >= 2):
            assert q_gram_cond_prob_list[0][1] >= q_gram_cond_prob_list[1][1]
            assert q_gram_cond_prob_list[-2][1] >= q_gram_cond_prob_list[-1][1]
        if (len(q_gram_cond_prob_list) >= 3):
            assert q_gram_cond_prob_list[1][1] >= q_gram_cond_prob_list[2][1]
            assert q_gram_cond_prob_list[-3][1] >= q_gram_cond_prob_list[-2][1]

        print('    Conditional probabilities:', q_gram_cond_prob_list[:5], '...')
        progress_bar.setValue(70)
        # List of all other q-grams and their bit positions identified for this
        # frequent q-gram tuple
        #
        freq_q_gram_tuple_other_q_gram_list = []

        # To identify bit positions that can encode any of the not frequent
        # co-occurring q-grams, we use the same pattern mining approach as in step
        # 3, but limited to the BFs we know are encoding the frequent q-gram (tuple)

        # Depending upon the type of the frequent q-gram tuple (which is based on the
        # language model - single, tuple, all), we can identify bit positions that
        # must be all 1 in a BF (or at least one is 0) in order for a BF to be able
        # to encode the frequent q-gram tuple
        # - must have all 1-bits mask: All these bits must be 1 for a BF to be able
        #   to encode a given frequent q-gram
        # - must have one 0-bit mask (for language model 'all' only): At least one
        #   of these bits must be 0 for a BF not to be able to encode a given
        #   frequent q-gram (we need a list of these masks, one per not included
        #   frequent q-gram)
        #
        must_have_all_1_bit_bf = bitarray.bitarray(bf_len)
        must_have_all_1_bit_bf.setall(0)

        must_have_one_0_bit_bf_list = []  # For 'all' only

        # Generate the bit masks depending upon the language model used
        #
        if (expand_lang_model == 'single'):  # One frequent q-gram only
            assert isinstance(freq_q_gram_key, str), freq_q_gram_key  # A single q-gram

            for pos in assigned_q_gram_pos_dict[freq_q_gram_key]:
                must_have_all_1_bit_bf[pos] = 1

        elif (expand_lang_model == 'tuple'):  # Several frequent q-grams
            assert isinstance(freq_q_gram_key, tuple), freq_q_gram_key  # Q-gram tuple

            for freq_q_gram in freq_q_gram_key:
                for pos in assigned_q_gram_pos_dict[freq_q_gram]:
                    must_have_all_1_bit_bf[pos] = 1

        else:  # expand_lang_model == 'all'
            assert len(freq_q_gram_key) == 2
            assert isinstance(freq_q_gram_key[0], tuple), freq_q_gram_key
            assert isinstance(freq_q_gram_key[1], tuple), freq_q_gram_key
            assert len(freq_q_gram_key[0]) + len(freq_q_gram_key[1]) == \
                   len(identified_q_gram_set)

            for freq_q_gram in freq_q_gram_key[0]:  # All must indude frequent q-grams
                for pos in assigned_q_gram_pos_dict[freq_q_gram]:
                    must_have_all_1_bit_bf[pos] = 1

            # We need one BF mask per not included q-gram
            #
            for freq_q_gram in freq_q_gram_key[1]:
                must_have_one_0_bit_bf = bitarray.bitarray(bf_len)
                must_have_one_0_bit_bf.setall(0)

                for pos in assigned_q_gram_pos_dict[freq_q_gram]:
                    must_have_one_0_bit_bf[pos] = 1

                must_have_one_0_bit_bf_list.append(must_have_one_0_bit_bf)

        # Generate the BF bit mask for the pattern mining approach of the BFs to use
        # Only apply pattern mining on the BFs that have 1-bits in the identified
        # bit positions of the frequent q-gram(s)
        #
        sel_bit_row_filter_bit_array = bitarray.bitarray(encode_num_bf)
        sel_bit_row_filter_bit_array.setall(0)
        progress_bar.setValue(75)
        for (i, enc_rec_id) in enumerate(encode_rec_id_list):
            rec_bf = encode_bf_dict[enc_rec_id]

            include_bf = True

            # In order to be able to encode all frequent must include q-gram(s), a BF
            # must have 1-bits in all 1-bits of the masking BF
            #
            if (rec_bf & must_have_all_1_bit_bf != must_have_all_1_bit_bf):
                include_bf = False

            # In order to be able to encode all frequent cannot include q-gram(s), a
            # BF must have at least one 0-bit in the 1-bits of each masking BF
            #
            if (include_bf == True) and (expand_lang_model == 'all'):
                for must_have_one_0_bit_bf in must_have_one_0_bit_bf_list:
                    if (rec_bf & must_have_one_0_bit_bf == must_have_one_0_bit_bf):
                        include_bf = False  # All bits are 1, so this BF might contain a
                        break  # q-gram it should not be able to encode

            if (include_bf == True):
                sel_bit_row_filter_bit_array[i] = 1

        freq_bit_pos_num_bf = int(sel_bit_row_filter_bit_array.count(1))

        if (len(freq_q_gram_attr_val_set) == 0):
            print('    *** Warning: This q-gram (tuple) does not have any possible' + \
                  ' attribute values! ***')

        if (freq_bit_pos_num_bf == 0):
            print('    No BFs for this q-gram tuple - so nothing to expand')
            continue  # No BFs with this pattern, so nothing that can be done

        # Loop over the not frequent q-grams and their conditional probabilities,
        # and process q-grams as long as they have a significantly higher conditional
        # probability compared to the next q-gram in the list
        #
        # for i in range(len(q_gram_cond_prob_list)-1):
        #
        # Quality of later q-grams is not good, so only take first with highest
        # conditional probability
        #
        for i in range(1):

            # Check if condistional probability list has only one other
            # not frequent q-gram
            if (len(q_gram_cond_prob_list) == 1):
                q_gram1, cond_prob1 = q_gram_cond_prob_list[i]
                avrg_cond_prob = cond_prob1

            else:
                q_gram1, cond_prob1 = q_gram_cond_prob_list[i]
                q_gram2, cond_prob2 = q_gram_cond_prob_list[i + 1]

                # Calculate their average conditional probability, and if it is different
                # enough
                #
                avrg_cond_prob = (cond_prob1 + cond_prob2) / 2.0
                cond_prob_perc_diff = 100.0 * (cond_prob1 - cond_prob2) / avrg_cond_prob

                if (cond_prob_perc_diff >= stop_iter_perc_lm):  # Large enough
                    print('    Difference large enough (>= %.2f%%), ' % (stop_iter_perc_lm) \
                          + 'so to try to find bit positions for q-gram "%s"' % (q_gram1))
                    print()
                else:
                    print('    *** Difference too small to try to find bit positions for' + \
                          ' q-gram "%s" ***' % (q_gram1))
                    print()

                    # End loop over not frequent q-grams, go to next frequent q-gram tuple
                    #
                    break

            # Calculate the minimum number of 1-bits each bit position that can encode
            # the selected q-gram (q_gram1) will need to have
            #
            bit_pos_min_supp = avrg_cond_prob * freq_bit_pos_num_bf

            # Call the pattern mining function to get the co-occuring bit positions
            # that can encode the selected q-gram (q_gram1)
            #
            if (pattern_mine_method == 'apriori'):

                # Run the Apriori pattern mining approach, i.e. find set of longest
                # bit positions (BF columns) with a minimum count of common 1-bits)
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_apriori(encode_bf_bit_pos_list,
                                                          bit_pos_min_supp,
                                                          considered_bit_pos_set,
                                                          sel_bit_row_filter_bit_array)
            elif (pattern_mine_method == 'mapriori'):

                # Version of Apriori which stores the actual BFs not just Hamming
                # weights, so approach this is faster but needs more memory
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_apriori_memo(encode_bf_bit_pos_list,
                                                               bit_pos_min_supp,
                                                               considered_bit_pos_set,
                                                               sel_bit_row_filter_bit_array)
            elif (pattern_mine_method == 'maxminer'):

                # Run the Max-Miner approach (Bayardo, 1998)
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_max_miner(encode_bf_bit_pos_list,
                                                            bit_pos_min_supp,
                                                            considered_bit_pos_set,
                                                            sel_bit_row_filter_bit_array)
            elif (pattern_mine_method == 'hmine'):

                # Run the H-mine approach (J Pei, J Han, H Lu, et al., 2007)
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_h_mine(encode_bf_bit_pos_list,
                                                         bit_pos_min_supp,
                                                         considered_bit_pos_set,
                                                         sel_bit_row_filter_bit_array)
            elif (pattern_mine_method == 'fpmax'):

                # Run the FP tree and FPmax algorithm
                #
                pm_freq_bf_bit_pos_dict = \
                    gen_freq_bf_bit_positions_fp_max(encode_bf_bit_pos_list,
                                                         bit_pos_min_supp,
                                                         considered_bit_pos_set,
                                                         sel_bit_row_filter_bit_array)
            else:
                raise Exception(pattern_mine_method)  # Illegal method

            # If no frequent bit position tuple found go to the next q-gram
            #
            if (len(pm_freq_bf_bit_pos_dict) == 0):

                continue

            elif (len(pm_freq_bf_bit_pos_dict) == 1):  # Only one bit position tuple
                most_freq_pos_tuple, most_freq_count = list(pm_freq_bf_bit_pos_dict.items())[0]


            else:  # Several bit position tuples identified

                # Calculate percentage difference of two most frequent bit position
                # tuples, and only keep the most frequent one if this difference is
                # large enough
                #
                sorted_freq_bf_bit_pos_list = sorted(pm_freq_bf_bit_pos_dict.items(),
                                                     key=lambda t: t[1], reverse=True)

                # Get the two highest frequencies
                #
                most_freq_bit_pos_tuple_count1 = sorted_freq_bf_bit_pos_list[0][1]
                most_freq_bit_pos_tuple_count2 = sorted_freq_bf_bit_pos_list[1][1]
                assert most_freq_bit_pos_tuple_count1 >= most_freq_bit_pos_tuple_count2

                # Calculate the percentage difference between their frequencies
                #
                avr_top_bit_pos_count = float(most_freq_bit_pos_tuple_count1 + \
                                              most_freq_bit_pos_tuple_count2) / 2.0

                most_freq_bit_pos_count_diff_perc = 100.0 * \
                                                    float(most_freq_bit_pos_tuple_count1 - \
                                                          most_freq_bit_pos_tuple_count2) / avr_top_bit_pos_count

                if (most_freq_bit_pos_count_diff_perc >= stop_iter_perc_lm):  # Large enough

                    most_freq_pos_tuple, most_freq_count = sorted_freq_bf_bit_pos_list[0]

                else:  # Stop the iterative process (do not append new tuples below)

                    continue  # Go to next q-gram

            # If more than the expected number (estimated number of hash functions) of
            # co-occurring bit positions are found, then discard this result
            #
            if (len(most_freq_pos_tuple) > est_num_hash_funct):
                continue  # Process next q-gram

            # Add the identified bit positions to the result sets
            #
            identified_q_gram_set2.add(q_gram1)

            print('  Frequent q-gram added to the new identified set: %s' % q_gram1)

            # Add the identified bit positions to the considered bit positions
            #
            for pos in most_freq_pos_tuple:
                considered_bit_pos_set.add(pos)

            # We do not add the newly identified q-gram to the list of q-grams to be
            # processed further because their quality is not high enough

            for pos in most_freq_pos_tuple:
                pos_q_gram_set = q_gram_pos_assign_dict2.get(pos, set())
                pos_q_gram_set.add(q_gram1)
                q_gram_pos_assign_dict2[pos] = pos_q_gram_set

            bit_pos_set = assigned_q_gram_pos_dict2.get(q_gram1, set())
            bit_pos_set.update(set(most_freq_pos_tuple))
            assigned_q_gram_pos_dict2[q_gram1] = bit_pos_set

            # Add the q-gram to the must have q-gram sets of all BFs in the partition
            # that have the required 1-bits in all bit positions in most_freq_pos_tuple
            # and to the cannot have q-gram sets of all BFs that do not have 1-bits in
            # all positions in most_freq_pos_tuple.
            #
            q_gram1_mask_bf = bitarray.bitarray(bf_len)
            q_gram1_mask_bf.setall(0)

            for pos in most_freq_pos_tuple:
                q_gram1_mask_bf[pos] = 1

            for (i, bf_rec_id) in enumerate(encode_rec_id_list):
                rec_bf = encode_bf_dict[bf_rec_id]

                # Check if all required bit positions are set to 1
                #
                if (rec_bf & q_gram1_mask_bf == q_gram1_mask_bf):

                    # Check if this is a BF which contains the frequent q-gram
                    #
                    if (sel_bit_row_filter_bit_array[i] == 1):
                        bf_q_gram_set = bf_must_have_q_gram_dict2.get(bf_rec_id, set())
                        bf_q_gram_set.add(q_gram1)
                        bf_must_have_q_gram_dict2[bf_rec_id] = bf_q_gram_set

                else:  # A 0-bit means the q-gram is assumed not to occur in the BF
                    bf_q_gram_set = bf_cannot_have_q_gram_dict2.get(bf_rec_id, set())
                    bf_q_gram_set.add(q_gram1)
                    bf_cannot_have_q_gram_dict2[bf_rec_id] = bf_q_gram_set

            # Calculate accuracy of identified bit positions
            #
            q_gram1_true_bit_pos_set = set()
            for (pos, encode_q_gram_set) in encode_true_pos_q_gram_dict.items():
                if (q_gram1 in encode_q_gram_set):
                    q_gram1_true_bit_pos_set.add(pos)

            true_pos_set = set(most_freq_pos_tuple) & q_gram1_true_bit_pos_set

            prec = float(len(true_pos_set)) / len(most_freq_pos_tuple)
            reca = float(len(true_pos_set)) / len(q_gram1_true_bit_pos_set)

            new_q_gram_res_dict[(freq_q_gram, q_gram1)] = (prec, reca)

            freq_q_gram_tuple_other_q_gram_list.append((q_gram1, most_freq_pos_tuple, \
                                                        prec, reca))

        freq_q_gram_other_q_gram_dict[freq_q_gram_key] = \
            freq_q_gram_tuple_other_q_gram_list

    expand_time = time.time() - start_time
    progress_bar.setValue(90)
    print('#### Number of new q-grams identified: %d (from %d q-grams, %.2f%%)' % \
          (len(identified_q_gram_set2), len(plain_q_gram_node_dict),
           100.0 * float(len(identified_q_gram_set2)) / len(plain_q_gram_node_dict)))
    print('####')

    print('#### Number of correctly identified BFs: %d' % total_corr_num_bfs)
    print('#### Number of wrongly identified BFs: %d' % total_wrng_num_bfs)
    print('####')

    # For each identified q-gram first get its true bit positions in the encoded
    # and the plain-text databases
    #
    encode_true_q_gram_pos_dict2 = {}
    plain_true_q_gram_pos_dict2 = {}

    encode_bit_pos_q_gram_reca_list2 = []
    plain_bit_pos_q_gram_reca_list2 = []

    encode_bit_pos_q_gram_prec_list2 = []
    plain_bit_pos_q_gram_prec_list2 = []

    encode_bit_pos_q_gram_false_pos_list2 = []  # Also keep track of how many wrong
    plain_bit_pos_q_gram_false_pos_list2 = []  # positions we identified

    for (pos, encode_q_gram_set) in encode_true_pos_q_gram_dict.items():
        for q_gram in encode_q_gram_set:
            q_gram_pos_set = encode_true_q_gram_pos_dict.get(q_gram, set())
            q_gram_pos_set.add(pos)
            encode_true_q_gram_pos_dict[q_gram] = q_gram_pos_set
    for (pos, plain_q_gram_set) in plain_true_pos_q_gram_dict.items():
        for q_gram in plain_q_gram_set:
            q_gram_pos_set = plain_true_q_gram_pos_dict.get(q_gram, set())
            q_gram_pos_set.add(pos)
            plain_true_q_gram_pos_dict[q_gram] = q_gram_pos_set

    for (q_gram, pos_set) in sorted(assigned_q_gram_pos_dict2.items()):
        encode_true_q_gram_set = encode_true_q_gram_pos_dict[q_gram]
        plain_true_q_gram_set = plain_true_q_gram_pos_dict[q_gram]

        encode_recall = float(len(pos_set.intersection(encode_true_q_gram_set))) / \
                        len(encode_true_q_gram_set)
        plain_recall = float(len(pos_set.intersection(plain_true_q_gram_set))) / \
                       len(plain_true_q_gram_set)

        encode_prec = float(len(pos_set.intersection(encode_true_q_gram_set))) / \
                      len(pos_set)
        plain_prec = float(len(pos_set.intersection(plain_true_q_gram_set))) / \
                     len(pos_set)

        # Percentage of false identified positions for a q-gram
        #
        encode_false_pos_rate = float(len(pos_set - encode_true_q_gram_set)) / \
                                len(pos_set)
        plain_false_pos_rate = float(len(pos_set - plain_true_q_gram_set)) / \
                               len(pos_set)

        assert (0.0 <= encode_false_pos_rate) and (1.0 >= encode_false_pos_rate), \
            encode_false_pos_rate
        assert (0.0 <= plain_false_pos_rate) and (1.0 >= plain_false_pos_rate), \
            plain_false_pos_rate

        encode_bit_pos_q_gram_reca_list2.append(encode_recall)
        plain_bit_pos_q_gram_reca_list2.append(plain_recall)

        encode_bit_pos_q_gram_prec_list2.append(encode_prec)
        plain_bit_pos_q_gram_prec_list2.append(plain_prec)

        encode_bit_pos_q_gram_false_pos_list2.append(encode_false_pos_rate)
        plain_bit_pos_q_gram_false_pos_list2.append(plain_false_pos_rate)

    # If no results set to 0
    #
    if (len(plain_bit_pos_q_gram_reca_list2) == 0):
        plain_bit_pos_q_gram_reca_list2 = [0.0]
    if (len(plain_bit_pos_q_gram_prec_list2) == 0):
        plain_bit_pos_q_gram_prec_list2 = [0.0]

    if (len(encode_bit_pos_q_gram_reca_list2) == 0):
        encode_bit_pos_q_gram_reca_list2 = [0.0]
    if (len(encode_bit_pos_q_gram_prec_list2) == 0):
        encode_bit_pos_q_gram_prec_list2 = [0.0]

    if (len(encode_bit_pos_q_gram_false_pos_list2) == 0):
        encode_bit_pos_q_gram_false_pos_list2 = [0.0]
    if (len(plain_bit_pos_q_gram_false_pos_list2) == 0):
        plain_bit_pos_q_gram_false_pos_list2 = [0.0]

    print('####')
    print('#### Encoding assignment of q-grams to bit position recall:   ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(encode_bit_pos_q_gram_reca_list2),
           numpy.mean(encode_bit_pos_q_gram_reca_list2),
           max(encode_bit_pos_q_gram_reca_list2)))
    print('####   Number and percentage of q-grams with recall 1.0: ' + \
          '%d / %.2f%%' % (encode_bit_pos_q_gram_reca_list2.count(1.0),
                           100.0 * float(encode_bit_pos_q_gram_reca_list2.count(1.0)) / \
                           (len(identified_q_gram_set2) + 0.0001)))
    print('#### Plain-text assignment of q-grams to bit position recall: ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(plain_bit_pos_q_gram_reca_list2),
           numpy.mean(plain_bit_pos_q_gram_reca_list2),
           max(plain_bit_pos_q_gram_reca_list2)))
    print('####   Number and percentage of q-grams with recall 1.0: %d / %.2f%%' \
          % (plain_bit_pos_q_gram_reca_list2.count(1.0),
             100.0 * float(plain_bit_pos_q_gram_reca_list2.count(1.0)) / \
             (len(identified_q_gram_set2) + 0.0001)))
    print('####')
    print('#### Encoding assignment of q-grams to bit position precision:   ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(encode_bit_pos_q_gram_prec_list2),
           numpy.mean(encode_bit_pos_q_gram_prec_list2),
           max(encode_bit_pos_q_gram_prec_list2)))
    print('####   Number and percentage of q-grams with precision ' + \
          '1.0: %d / %.2f%%' % (encode_bit_pos_q_gram_prec_list2.count(1.0),
                                100.0 * float(encode_bit_pos_q_gram_prec_list2.count(1.0)) / \
                                (len(identified_q_gram_set2) + 0.0001)))
    print('#### Plain-text assignment of q-grams to bit position precision: ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(plain_bit_pos_q_gram_prec_list2),
           numpy.mean(plain_bit_pos_q_gram_prec_list2),
           max(plain_bit_pos_q_gram_prec_list2)))
    print('####   Number and percentage of q-grams with precision 1.0: ' + \
          '%d / %.2f%%' % (plain_bit_pos_q_gram_prec_list2.count(1.0),
                           100.0 * float(plain_bit_pos_q_gram_prec_list2.count(1.0)) / \
                           (len(identified_q_gram_set2) + 0.0001)))
    print('####')
    print('#### Encoding assignment of q-grams to bit position false ' + \
          'positive rate:   %.2f min / %.2f avr / %.2f max' % \
          (min(encode_bit_pos_q_gram_false_pos_list2),
           numpy.mean(encode_bit_pos_q_gram_false_pos_list2),
           max(encode_bit_pos_q_gram_false_pos_list2)))
    print('####   Number and percentage of q-grams with false positive rate' + \
          ' 0.0: %d / %.2f%%' \
          % (encode_bit_pos_q_gram_false_pos_list2.count(0.0),
             100.0 * float(encode_bit_pos_q_gram_false_pos_list2.count(0.0)) / \
             (len(identified_q_gram_set2) + 0.0001)))
    print('#### Plain-text assignment of q-grams to bit position false ' + \
          'positive rate: %.2f min / %.2f avr / %.2f max' % \
          (min(plain_bit_pos_q_gram_false_pos_list2),
           numpy.mean(plain_bit_pos_q_gram_false_pos_list2),
           max(plain_bit_pos_q_gram_false_pos_list2)))
    print('####   Number and percentage of q-grams with false positive rate' + \
          ' 0.0: %d / %.2f%%' \
          % (plain_bit_pos_q_gram_false_pos_list2.count(0.0),
             100.0 * float(plain_bit_pos_q_gram_false_pos_list2.count(0.0)) / \
             (len(identified_q_gram_set2) + 0.0001)))
    print('####')

    # Calculate the precision of the assignment of q-grams to bit positions
    #
    encode_q_gram_to_bit_pos_assign_prec_list2 = []
    plain_q_gram_to_bit_pos_assign_prec_list2 = []

    encode_total_num_correct2 = 0  # Also count how many assignments of q-grams to
    encode_total_num_wrong2 = 0  # bit positions are wrong and how many correct
    plain_total_num_correct2 = 0
    plain_total_num_wrong2 = 0

    print('#### Assignment of q-grams to BF bit positions:')
    for (pos, pos_q_gram_set) in sorted(q_gram_pos_assign_dict2.items()):
        q_gram_set_str_list = []  # Strings to be printed

        encode_pos_corr = 0  # Correctly assigned q-grams to this bit position
        plain_pos_corr = 0

        for q_gram in pos_q_gram_set:
            if (q_gram in encode_true_pos_q_gram_dict.get(pos, set())):
                assign_str = 'encode correct'
                encode_pos_corr += 1
                encode_total_num_correct2 += 1
            else:
                assign_str = 'encode wrong'
                encode_total_num_wrong2 += 1
            if (same_data_attr_flag == False):  # Check analysis BF
                if (q_gram in plain_true_pos_q_gram_dict.get(pos, set())):
                    assign_str += ', plain-text correct'
                    plain_pos_corr += 1
                    plain_total_num_correct2 += 1
                else:
                    assign_str += ', plain-text wrong'
                    plain_total_num_wrong2 += 1
            else:  # Encode and plain-text data sets are the same
                if (q_gram in encode_true_pos_q_gram_dict.get(pos, set())):
                    assign_str = 'plain-text correct'
                    plain_pos_corr += 1
                    plain_total_num_correct2 += 1
                else:
                    assign_str = 'plain-text wrong'
                    plain_total_num_wrong2 += 1

            q_gram_set_str_list.append('"%s" (%s)' % (q_gram, assign_str))

        encode_pos_proc = float(encode_pos_corr) / len(pos_q_gram_set)
        plain_pos_proc = float(plain_pos_corr) / len(pos_q_gram_set)

        encode_q_gram_to_bit_pos_assign_prec_list2.append(encode_pos_proc)
        plain_q_gram_to_bit_pos_assign_prec_list2.append(plain_pos_proc)

        print('####   %3d: %s' % (pos, ', '.join(q_gram_set_str_list)))

    if (len(plain_q_gram_to_bit_pos_assign_prec_list2) == 0):
        plain_q_gram_to_bit_pos_assign_prec_list2 = [0.0]
    if (len(encode_q_gram_to_bit_pos_assign_prec_list2) == 0):
        encode_q_gram_to_bit_pos_assign_prec_list2 = [0.0]

    print('####')
    print('#### Encoding q-gram to bit position assignment precision:   ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(encode_q_gram_to_bit_pos_assign_prec_list2),
           numpy.mean(encode_q_gram_to_bit_pos_assign_prec_list2),
           max(encode_q_gram_to_bit_pos_assign_prec_list2)))
    print('####   Number and percentage of positions with precison 1.0: ' + \
          '%d / %.2f%%' % (encode_q_gram_to_bit_pos_assign_prec_list2.count(1.0),
                           100.0 * float(encode_q_gram_to_bit_pos_assign_prec_list2.count(1.0)) / \
                           (len(q_gram_pos_assign_dict2) + 0.0001)))
    print('#### Plain-text q-gram to bit position assignment precision: ' + \
          '%.2f min / %.2f avr / %.2f max' % \
          (min(plain_q_gram_to_bit_pos_assign_prec_list2),
           numpy.mean(plain_q_gram_to_bit_pos_assign_prec_list2),
           max(plain_q_gram_to_bit_pos_assign_prec_list2)))
    print('####   Number and percentage of positions with precison 1.0: ' + \
          '%d / %.2f%%' % (plain_q_gram_to_bit_pos_assign_prec_list2.count(1.0),
                           100.0 * float(plain_q_gram_to_bit_pos_assign_prec_list2.count(1.0)) / \
                           (len(q_gram_pos_assign_dict2) + 0.0001)))
    print('#### Encoding total number of correct and wrong assignments:  ' + \
          '%d / %d (%.2f%% correct)' % (encode_total_num_correct2,
                                        encode_total_num_wrong2, 100.0 * float(encode_total_num_correct2) / \
                                        (encode_total_num_correct2 + encode_total_num_wrong2 + 0.0001)))
    print('#### Plain-text total number of correct and wrong assignments: ' + \
          '%d / %d (%.2f%% correct)' % (plain_total_num_correct2,
                                        plain_total_num_wrong2, 100.0 * float(plain_total_num_correct2) / \
                                        (plain_total_num_correct2 + plain_total_num_wrong2 + 0.0001)))
    print('#### ' + '-' * 80)
    print('####')
    print()

    # Calculate statistics and quality of the must have and cannot have q-gram
    # sets assigned to BFs
    #
    bf_must_have_set_size_list2 = []
    bf_cannot_have_set_size_list2 = []
    bf_combined_set_size_list2 = []

    for q_gram_set in bf_must_have_q_gram_dict2.values():
        bf_must_have_set_size_list2.append(len(q_gram_set))
    for q_gram_set in bf_cannot_have_q_gram_dict2.values():
        bf_cannot_have_set_size_list2.append(len(q_gram_set))

    all_rec_id_set = set(bf_must_have_q_gram_dict2.keys()) | \
                     set(bf_cannot_have_q_gram_dict2.keys())
    for rec_id in all_rec_id_set:
        comb_set_size = len(bf_must_have_q_gram_dict2.get(rec_id, set()) | \
                            bf_cannot_have_q_gram_dict2.get(rec_id, set()))
        bf_combined_set_size_list2.append(comb_set_size)

    if (len(bf_must_have_set_size_list2) == 0):
        bf_must_have_set_size_list2 = [0]
    if (len(bf_cannot_have_set_size_list2) == 0):
        bf_cannot_have_set_size_list2 = [0]
    if (len(bf_combined_set_size_list2) == 0):
        bf_combined_set_size_list2 = [0]

    print('#### Summary of q-gram sets assigned to BFs:')
    print('####  %d of %d BF have must have q-grams assigned to them' % \
          (len(bf_must_have_set_size_list2), encode_num_bf))
    print('####    Minimum, average and maximum number of q-grams assigned: ' + \
          '%d / %.2f / %d' % (min(bf_must_have_set_size_list2),
                              numpy.mean(bf_must_have_set_size_list2),
                              max(bf_must_have_set_size_list2)))
    print('####    Minimum, average and maximum combined lenth of must plus ' + \
          'cannot have q-gram sets per BF: %d / %.2f / %d' % \
          (min(bf_combined_set_size_list2), numpy.mean(bf_combined_set_size_list2),
           max(bf_combined_set_size_list2)))
    print('####')
    print('####  %d of %d BF have cannot have q-grams assigned to them' % \
          (len(bf_cannot_have_set_size_list2), encode_num_bf))
    print('####    Minimum, average and maximum number of q-grams assigned: ' + \
          '%d / %.2f / %d' % (min(bf_cannot_have_set_size_list2),
                              numpy.mean(bf_cannot_have_set_size_list2),
                              max(bf_cannot_have_set_size_list2)))
    print('####')

    # Calculate the quality of the identified must / cannot q-gram sets as:
    # - precision of must have q-grams (how many of those identified are in a BF)
    # - precision of cannot have q-grams (how many of those identified are not in
    #   a BF)
    # - recall is not relevant as we have only identified a few q-grams so far
    #
    bf_must_have_prec_list2 = []
    bf_cannot_have_prec_list2 = []

    for (bf_rec_id, q_gram_set) in bf_must_have_q_gram_dict2.items():
        true_q_gram_set = set(encode_q_gram_dict[bf_rec_id])
        must_have_prec = float(len(q_gram_set & true_q_gram_set)) / len(q_gram_set)
        bf_must_have_prec_list2.append(must_have_prec)

    for (bf_rec_id, q_gram_set) in bf_cannot_have_q_gram_dict2.items():
        true_q_gram_set = set(encode_q_gram_dict[bf_rec_id])
        cannot_have_prec = 1.0 - float(len(q_gram_set & true_q_gram_set)) / \
                           len(q_gram_set)
        bf_cannot_have_prec_list2.append(cannot_have_prec)

    if (len(bf_must_have_prec_list2) == 0):
        bf_must_have_prec_list2 = [0.0]
    if (len(bf_cannot_have_prec_list2) == 0):
        bf_cannot_have_prec_list2 = [0.0]

    print('#### Precision of q-gram sets assigned to BFs:')
    print('####   Must have q-gram sets minimum, average, maximum precision: ' + \
          '%.3f / %.3f / %.3f' % (min(bf_must_have_prec_list2),
                                  numpy.mean(bf_must_have_prec_list2),
                                  max(bf_must_have_prec_list2)))
    if (len(bf_must_have_prec_list2) > 0):
        print('####     Ratio of BFs with must have precision 1.0: %.5f' % \
              (float(bf_must_have_prec_list2.count(1.0)) / \
               (len(bf_must_have_prec_list2))))
    print('####   Cannot have q-gram sets minimum, average, maximum precision: ' \
          + '%.3f / %.3f / %.3f' % (min(bf_cannot_have_prec_list2),
                                    numpy.mean(bf_cannot_have_prec_list2),
                                    max(bf_cannot_have_prec_list2)))
    if (len(bf_cannot_have_prec_list2) > 0):
        print('####     Ratio of BFs with cannot have precision 1.0: %.5f' % \
              (float(bf_cannot_have_prec_list2.count(1.0)) / \
               (len(bf_cannot_have_prec_list2))))
    print('####')
    print()

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    # stage 4: Length filtering process
    # To enable length filtering for plain-text candidate values, calculate a lower
    # and upper bound of the number of q-grams an encoded BF can contain, and get
    # the number of q-grams for each plain-text value

    # For each BF, based on its Hamming weight and the estimated number of hash
    # functions, calculate an upper and lower bound on how many q-grams this BF
    # can encode
    #
    bf_lower_upper_bound_q_gram_dict = {}

    bound_size_list = []  # Keep the size of each bound for ech BF

    log_len_adj = math.log((1.0 - 1.0 / bf_len))  # Used to calculate upper bound

    # A dictionary with the q-gram estimation results, where keys will be the
    # differences between actual and estimated number of q-grams, and values will
    # be counts of how often these differences occur
    #
    num_corr_diff_dict = {}

    num_q_larger_lower_bound = 0  # Keep track of how many BFs have the true
    num_q_smaller_upper_bound = 0  # number of q-grams within the estimated
    # interval

    if (est_num_hash_funct == 0):
        re_id_method = 'none'

    elif (est_num_hash_funct > 0):
        print('Calculating lower and upper bounds on number of q-grams encoded ' + \
              'in BFs:')

        for (enc_rec_id, rec_bf) in encode_bf_dict.items():
            true_num_q_gram = len(encode_q_gram_dict[enc_rec_id])

            bf_hw = float(rec_bf.count(1))

            if (true_num_q_gram == 0):
                assert bf_hw == 0, bf_hw
                continue

            # Lower bound is if there are no collisions, so each q-gram would generate
            # k (number of hash functions) 1-bits
            #
            bf_lower_bound_q = int(math.floor(bf_hw / est_num_hash_funct))

            if (bf_lower_bound_q > true_num_q_gram):
                print('*** Warning: Lower bound is higher than true number of q-grams:', \
                      (bf_lower_bound_q, true_num_q_gram), 'for record with ID:', \
                      enc_rec_id)

            # Upper bound can be calculated based on the number of expected collisions
            # when hashing k*q elements of a set into a BF of a given length

            # From: https://en.wikipedia.org/wiki/Bloom_filter# \
            #    Approximating_the_number_of_items_in_a_Bloom_filter

            num_0_bit = bf_len - bf_hw
            num_0_bit_frac = float(num_0_bit) / bf_len

            kq = math.log(num_0_bit_frac) / log_len_adj
            assert rec_bf.count(1) <= kq

            bf_est_num_q = kq / est_num_hash_funct  # Mitzenbacher and Upfal

            # Based on Swamidass and Baldi
            #
            bf_est_num_q2 = - (float(bf_len) / est_num_hash_funct) * \
                            math.log(1.0 - bf_hw / bf_len)

            # Check both estimates are very similar
            #
            if (abs(bf_est_num_q - bf_est_num_q2) > 0.1):
                print('xxxx', bf_est_num_q, bf_est_num_q2, abs(bf_est_num_q - bf_est_num_q2))

            # Calculate difference between actual and estimated number of q-grams
            #
            est_diff = true_num_q_gram - int(bf_est_num_q)

            num_corr_diff_dict[est_diff] = num_corr_diff_dict.get(est_diff, 0) + 1

            # Symmetric bound: upper bound is same difference to estimated as lower
            # bound
            #
            bound_size = (bf_est_num_q - bf_lower_bound_q)
            bound_size_list.append(bound_size)

            bf_upper_bound_q = bf_est_num_q + bound_size

            bf_lower_upper_bound_q_gram_dict[enc_rec_id] = (bf_lower_bound_q,
                                                            bf_upper_bound_q)

            # Keep track of accuracy of these estimates
            #
            if (true_num_q_gram >= bf_lower_bound_q):
                num_q_larger_lower_bound += 1
            if (true_num_q_gram <= bf_upper_bound_q):
                num_q_smaller_upper_bound += 1

        print('  Number of estimated q-grams versus correct number of q-grams:')
        print('  (positive means estimated number is smaller, negative means it ' + \
              'is larger)')
        for (est_diff, est_diff_count) in sorted(num_corr_diff_dict.items()):
            print('    %3d: %d (%.2f%%)' % (est_diff, est_diff_count, 100.0 * \
                                            float(est_diff_count) / len(bf_lower_upper_bound_q_gram_dict)))

        print('  Minimum, average and maximum of bound sizes: ' + \
              '%d / %.2f / %d' % (min(bound_size_list), numpy.mean(bound_size_list), \
                                  max(bound_size_list)))

        print('  Number of BFs with estimated q-grams within lower bound: ' + \
              '%d (%.2f%%)' % (num_q_larger_lower_bound, 100.0 * \
                               num_q_larger_lower_bound / len(bf_lower_upper_bound_q_gram_dict)))
        print('  Number of BFs with estimated q-grams within upper bound: ' + \
              '%d (%.2f%%)' % (num_q_smaller_upper_bound, 100.0 * \
                               num_q_smaller_upper_bound / len(bf_lower_upper_bound_q_gram_dict)))
        print()
    progress_bar.setValue(95)
    # -----------------------------------------------------------------------------
    # stage 4: Re-identify plain-text values based on q-grams assigned to bit
    #         positions.

    # For each plain-text value get its number of q-grams
    #
    plain_val_num_q_gram_dict = {}

    for attr_val in plain_attr_val_freq_q_gram_dict:
        (attr_val_freq, attr_q_gram_list) = plain_attr_val_freq_q_gram_dict[attr_val]

        if attr_val not in plain_val_num_q_gram_dict:
            plain_val_num_q_gram_dict[attr_val] = len(attr_q_gram_list)

    # Generate new sets of identified q-grams by combining those from steps 3 and 4
    # and then use these two different versions to re-identify q-grams.
    #
    all_must_have_rec_id_set = set(bf_must_have_q_gram_dict.keys()) | \
                               set(bf_must_have_q_gram_dict2.keys())
    all_cannot_have_rec_id_set = set(bf_cannot_have_q_gram_dict.keys()) | \
                                 set(bf_cannot_have_q_gram_dict2.keys())

    bf_must_have_q_gram_dict_exp = {}  # Expanded dictionaries with newly
    bf_cannot_have_q_gram_dict_exp = {}  # identified q-grams from step 4
    q_gram_pos_assign_dict_exp = {}

    # Merge dictionaries and sets of identified q-grams and sets assigned to BFs
    #
    for rec_id in all_must_have_rec_id_set:
        bf_must_have_q_gram_dict_exp[rec_id] = \
            bf_must_have_q_gram_dict.get(rec_id, set()) | \
            bf_must_have_q_gram_dict2.get(rec_id, set())
    for rec_id in all_cannot_have_rec_id_set:
        bf_cannot_have_q_gram_dict_exp[rec_id] = \
            bf_cannot_have_q_gram_dict.get(rec_id, set()) | \
            bf_cannot_have_q_gram_dict2.get(rec_id, set())

    all_pos_assigned_set = set(q_gram_pos_assign_dict.keys()) | \
                           set(q_gram_pos_assign_dict2.keys())
    for pos in all_pos_assigned_set:
        q_gram_pos_assign_dict_exp[pos] = q_gram_pos_assign_dict.get(pos, set()) | \
                                          q_gram_pos_assign_dict2.get(pos, set())

    # Run each re-identification method
    #
    if (re_id_method == 'all'):
        re_id_method_list = ['bf_tuple', 'set_inter']  # q_gram_tuple, bf_q_gram_tuple
    else:
        re_id_method_list = [re_id_method]

    for re_id_method in re_id_method_list:

        re_id_res_list = []  # Keep results from both re-identification runs

        for (use_q_gram_pos_assign_dict,
             use_bf_must_have_q_gram_dict,
             use_bf_cannot_have_q_gram_dict) in \
                [(q_gram_pos_assign_dict, bf_must_have_q_gram_dict, \
                  bf_cannot_have_q_gram_dict), \
                 (q_gram_pos_assign_dict_exp, bf_must_have_q_gram_dict_exp, \
                  bf_cannot_have_q_gram_dict_exp)]:

            start_time = time.time()

            if (re_id_method == 'set_inter'):
                reid_res_tuple = re_identify_attr_val_setinter(use_bf_must_have_q_gram_dict,
                                                                   use_bf_cannot_have_q_gram_dict,
                                                                   plain_q_gram_attr_val_dict,
                                                                   encode_rec_val_dict,
                                                                   max_num_many)

            elif (re_id_method == 'bf_tuple'):
                # First get sets of bit positions per frequent q-gram
                #
                all_identified_q_gram_pos_dict, corr_identified_q_gram_pos_dict = \
                    gen_freq_q_gram_bit_post_dict(use_q_gram_pos_assign_dict,
                                                      encode_true_pos_q_gram_dict)

                all_bf_q_gram_rec_id_dict = \
                    get_matching_bf_sets(all_identified_q_gram_pos_dict,
                                             encode_bf_dict,
                                             plain_attr_val_rec_id_dict,
                                             use_bf_must_have_q_gram_dict,
                                             use_bf_cannot_have_q_gram_dict, bf_len)

                reid_res_tuple = calc_reident_accuracy(all_bf_q_gram_rec_id_dict,
                                                           encode_rec_val_dict,
                                                           plain_rec_val_dict,
                                                           plain_val_num_q_gram_dict,
                                                           max_num_many,
                                                           bf_lower_upper_bound_q_gram_dict)

            elif (re_id_method == 'none'):  # Don't attempt re-identification
                reid_res_tuple = ([0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], \
                                  [0, 0], [0.0, 0.0], [0.0, 0.0], 0.0)

            else:
                print('*** Should not happen:', re_id_method, '***')
                sys.exit()

            re_id_res_list.append(reid_res_tuple)

        # Results without filtering applied
        #
        num_no_guess = re_id_res_list[0][0][0]
        num_too_many_guess = re_id_res_list[0][1][0]
        num_1_1_guess = re_id_res_list[0][2][0]
        num_corr_1_1_guess = re_id_res_list[0][3][0]
        num_part_1_1_guess = re_id_res_list[0][4][0]
        num_1_m_guess = re_id_res_list[0][5][0]
        num_corr_1_m_guess = re_id_res_list[0][6][0]
        num_part_1_m_guess = re_id_res_list[0][7][0]
        acc_part_1_1_guess = re_id_res_list[0][8][0]
        acc_part_1_m_guess = re_id_res_list[0][9][0]

        # Results with filtering applied
        #
        num_no_guess_filter = re_id_res_list[0][0][1]
        num_too_many_guess_filter = re_id_res_list[0][1][1]
        num_1_1_guess_filter = re_id_res_list[0][2][1]
        num_corr_1_1_guess_filter = re_id_res_list[0][3][1]
        num_part_1_1_guess_filter = re_id_res_list[0][4][1]
        num_1_m_guess_filter = re_id_res_list[0][5][1]
        num_corr_1_m_guess_filter = re_id_res_list[0][6][1]
        num_part_1_m_guess_filter = re_id_res_list[0][7][1]
        acc_part_1_1_guess_filter = re_id_res_list[0][8][1]
        acc_part_1_m_guess_filter = re_id_res_list[0][9][1]
        reduction_ratio_mean = re_id_res_list[0][10]

        # Expanded results without filtering applied
        #
        num_no_guess_exp = re_id_res_list[1][0][0]
        num_too_many_guess_exp = re_id_res_list[1][1][0]
        num_1_1_guess_exp = re_id_res_list[1][2][0]
        num_corr_1_1_guess_exp = re_id_res_list[1][3][0]
        num_part_1_1_guess_exp = re_id_res_list[1][4][0]
        num_1_m_guess_exp = re_id_res_list[1][5][0]
        num_corr_1_m_guess_exp = re_id_res_list[1][6][0]
        num_part_1_m_guess_exp = re_id_res_list[1][7][0]
        acc_part_1_1_guess_exp = re_id_res_list[1][8][0]
        acc_part_1_m_guess_exp = re_id_res_list[1][9][0]

        # Expanded results with filtering applied
        #
        num_no_guess_exp_filter = re_id_res_list[1][0][1]
        num_too_many_guess_exp_filter = re_id_res_list[1][1][1]
        num_1_1_guess_exp_filter = re_id_res_list[1][2][1]
        num_corr_1_1_guess_exp_filter = re_id_res_list[1][3][1]
        num_part_1_1_guess_exp_filter = re_id_res_list[1][4][1]
        num_1_m_guess_exp_filter = re_id_res_list[1][5][1]
        num_corr_1_m_guess_exp_filter = re_id_res_list[1][6][1]
        num_part_1_m_guess_exp_filter = re_id_res_list[1][7][1]
        acc_part_1_1_guess_exp_filter = re_id_res_list[1][8][1]
        acc_part_1_m_guess_exp_filter = re_id_res_list[1][9][1]
        reduction_ratio_mean_exp = re_id_res_list[1][10]

    # ---------------------------------------------------------------------------
    # Print summary results
    #
    today_time_str = time.strftime("%Y%m%d %H:%M:%S", time.localtime())
    consuming_time = time.time() - ini_start_time
    print
    '#### ---------------------------------------------'
    print('####   Time used for this attack: %.2f sec' % (consuming_time))
    print
    '#### Encode data set: %s' % (encode_base_data_set_name)
    print
    '####   Number of records: %d' % (len(encode_q_gram_dict))
    print
    '####   Attribute(s) used: %s' % (str(encode_attr_name_list))
    if (same_data_attr_flag == False):
        print
        '#### Analysis data set: %s' % (plain_base_data_set_name)
        print
        '####   Number of records: %d' % (len(plain_q_gram_dict))
        print
        '####   Attribute(s) used: %s' % (str(plain_attr_name_list))
    print
    '####'

    print
    '#### q: %d' % (q)
    print
    '#### BF len: %d' % (bf_len)
    print
    '#### Num hash funct: %d' % (num_hash_funct)
    print
    '#### Hashing type: %s' % \
    ({'dh': 'Double hashing', 'rh': 'Random hashing', \
      'edh': 'Enhanced double hashing', 'th': 'Triple hashing'}[hash_type])
    print
    '#### BF hardening: %s' % (bf_harden)

    print
    '#### Re-identification method:', re_id_method
    print
    '#### Num no guesses: %d' % (num_no_guess)
    print
    '####   Num > %d guesses: %d' % (max_num_many, num_too_many_guess)
    print
    '####   Num 2 to %d guesses: %d' % (max_num_many, num_1_m_guess)
    print
    '####     Num correct 2 to %d guesses: %d' % \
    (max_num_many, num_corr_1_m_guess)
    if (num_part_1_m_guess > 0):
        print
        '####     Num partially correct 2 to %d guesses: %d' % \
        (max_num_many, num_part_1_m_guess) + \
        ' (average accuracy of common tokens: %.2f)' % (acc_part_1_m_guess)
    else:
        print
        '####     Num partially correct 2 to %d guesses: 0' % (max_num_many)
    print
    '#### Num 1-1 guesses: %d' % (num_1_1_guess)
    print
    '####   Num correct 1-1 guesses: %d' % (num_corr_1_1_guess)
    if (num_part_1_1_guess > 0):
        print
        '####   Num partially correct 1-1 guesses: %d' % \
        (num_part_1_1_guess) + \
        ' (average accuracy of common tokens: %.2f)' % (acc_part_1_1_guess)
    else:
        print
        '####   Num partially correct 1-1 guesses: 0'
    print
    '####'
    print

    print
    '#### Expanded num no guesses: %d' % (num_no_guess_exp)
    print
    '####   Expanded num > %d guesses: %d' % (max_num_many,
                                              num_too_many_guess_exp)
    print
    '####   Expanded num 2 to %d guesses: %d' % (max_num_many,
                                                 num_1_m_guess_exp)
    print
    '####     Expanded num correct 2 to %d guesses: %d' % \
    (max_num_many, num_corr_1_m_guess_exp)
    if (num_part_1_m_guess_exp > 0):
        print
        '####     Expanded num partially correct 2 to %d guesses: %d' % \
        (max_num_many, num_part_1_m_guess_exp) + \
        ' (average accuracy of common tokens: %.2f)' % \
        (acc_part_1_m_guess_exp)
    else:
        print
        '####     Expanded num partially correct 2 to %d guesses: 0' % \
        (max_num_many)
    print
    '#### Expanded num 1-1 guesses: %d' % (num_1_1_guess_exp)
    print
    '####   Expanded num correct 1-1 guesses: %d' % (num_corr_1_1_guess_exp)
    if (num_part_1_1_guess_exp > 0):
        print
        '####   Expanded num partially correct 1-1 guesses: %d' % \
        (num_part_1_1_guess_exp) + \
        ' (average accuracy of common tokens: %.2f)' % \
        (acc_part_1_1_guess_exp)
    else:
        print
        '####   Expanded num partially correct 1-1 guesses: 0'
    print
    '####'
    print

    res_list = [today_time_str, encode_base_data_set_name,
                len(encode_q_gram_dict),
                str(encode_attr_name_list), plain_base_data_set_name,
                len(plain_q_gram_dict), str(plain_attr_name_list),
                #
                consuming_time,
                #
                q, bf_len, num_hash_funct, hash_type, bf_harden,
                mc_chain_len, mc_sel_method,
                bf_encode, padded,
                #
                stop_iter_perc, stop_iter_perc_lm,
                min_part_size, expand_lang_model,
                lang_model_min_freq,
                #
                len(identified_q_gram_set), len(identified_q_gram_set2),
                est_num_hash_funct,
                #
                # Assignment of q-grams to bit position recall:
                min(encode_bit_pos_q_gram_reca_list),
                numpy.mean(encode_bit_pos_q_gram_reca_list),
                max(encode_bit_pos_q_gram_reca_list),
                100.0 * float(encode_bit_pos_q_gram_reca_list.count(1.0)) / \
                (len(identified_q_gram_set) + 0.0001),
                min(plain_bit_pos_q_gram_reca_list),
                numpy.mean(plain_bit_pos_q_gram_reca_list),
                max(plain_bit_pos_q_gram_reca_list),
                100.0 * float(plain_bit_pos_q_gram_reca_list.count(1.0)) / \
                (len(identified_q_gram_set) + 0.0001),
                #
                # Q-gram to bit position assignment precision
                min(encode_q_gram_to_bit_pos_assign_prec_list),
                numpy.mean(encode_q_gram_to_bit_pos_assign_prec_list),
                max(encode_q_gram_to_bit_pos_assign_prec_list),
                100.0 * \
                float(encode_q_gram_to_bit_pos_assign_prec_list.count(1.0)) / \
                (len(q_gram_pos_assign_dict) + 0.0001),
                min(plain_q_gram_to_bit_pos_assign_prec_list),
                numpy.mean(plain_q_gram_to_bit_pos_assign_prec_list),
                max(plain_q_gram_to_bit_pos_assign_prec_list),
                100.0 * \
                float(plain_q_gram_to_bit_pos_assign_prec_list.count(1.0)) / \
                (len(q_gram_pos_assign_dict) + 0.0001),
                #
                # Re-identification quality after filtered
                num_no_guess_filter, num_too_many_guess_filter,
                num_1_1_guess_filter, num_corr_1_1_guess_filter,
                num_part_1_1_guess_filter, num_1_m_guess_filter,
                num_corr_1_m_guess_filter, num_part_1_m_guess_filter,
                acc_part_1_1_guess_filter, acc_part_1_m_guess_filter,
                reduction_ratio_mean,
                #
                # Assignment of expanded (language model) q-grams to bit
                # position recall:
                min(encode_bit_pos_q_gram_reca_list2),
                numpy.mean(encode_bit_pos_q_gram_reca_list2),
                max(encode_bit_pos_q_gram_reca_list2),
                100.0 * float(encode_bit_pos_q_gram_reca_list2.count(1.0)) / \
                (len(identified_q_gram_set2) + 0.0001),
                min(plain_bit_pos_q_gram_reca_list2),
                numpy.mean(plain_bit_pos_q_gram_reca_list2),
                max(plain_bit_pos_q_gram_reca_list2),
                100.0 * float(plain_bit_pos_q_gram_reca_list2.count(1.0)) / \
                (len(identified_q_gram_set2) + 0.0001),
                #
                # Expanded q-gram to bit position assignment precision
                min(encode_bit_pos_q_gram_prec_list2),
                numpy.mean(encode_bit_pos_q_gram_prec_list2),
                max(encode_bit_pos_q_gram_prec_list2),
                100.0 * \
                float(encode_bit_pos_q_gram_prec_list2.count(1.0)) / \
                (len(q_gram_pos_assign_dict2) + 0.0001),
                min(plain_bit_pos_q_gram_prec_list2),
                numpy.mean(plain_bit_pos_q_gram_prec_list2),
                max(plain_bit_pos_q_gram_prec_list2),
                100.0 * \
                float(plain_bit_pos_q_gram_prec_list2.count(1.0)) / \
                (len(q_gram_pos_assign_dict2) + 0.0001),
                #
                # =================================================================
                # # Expanded q-gram to bit position assignment precision
                # min(encode_q_gram_to_bit_pos_assign_prec_list2),
                # numpy.mean(encode_q_gram_to_bit_pos_assign_prec_list2),
                # max(encode_q_gram_to_bit_pos_assign_prec_list2),
                # 100.0* \
                #   float(encode_q_gram_to_bit_pos_assign_prec_list2.count(1.0)) / \
                #   (len(q_gram_pos_assign_dict2)+0.0001),
                # min(plain_q_gram_to_bit_pos_assign_prec_list2),
                # numpy.mean(plain_q_gram_to_bit_pos_assign_prec_list2),
                # max(plain_q_gram_to_bit_pos_assign_prec_list2),
                # 100.0* \
                #   float(plain_q_gram_to_bit_pos_assign_prec_list2.count(1.0)) / \
                #   (len(q_gram_pos_assign_dict2)+0.0001),
                # =================================================================

                # Re-identification quality expanded after filtered
                num_no_guess_exp_filter, num_too_many_guess_exp_filter,
                num_1_1_guess_exp_filter, num_corr_1_1_guess_exp_filter,
                num_part_1_1_guess_exp_filter, num_1_m_guess_exp_filter,
                num_corr_1_m_guess_exp_filter, num_part_1_m_guess_exp_filter,
                acc_part_1_1_guess_exp_filter, acc_part_1_m_guess_exp_filter,
                reduction_ratio_mean_exp
                ]

    # Generate header line with column names
    #
    header_list = ['today_time_str', 'encode_data_set_name', 'encode_num_rec',
                   'encode_used_attr', 'plain_data_set_name', 'plain_num_rec',
                   'plain_used_attr',
                   #
                   'attack_time',
                   #
                   'q', 'bf_len', 'num_hash_funct', 'hash_type', 'bf_harden',
                   'mc_chain_len', 'mc_sel_method',
                   'encode_method', 'padded',
                   #
                   'stop_iter_perc', 'stop_iter_perc_lm',
                   'min_part_size', 'expand_lang_model',
                   'lang_model_min_freq',
                   #
                   'num_identified_freq_q_gram', 'num_identified_extra_q_gram',
                   'est_num_hash_funct',
                   #
                   'encode_min_bit_poss_assign_reca',
                   'encode_avr_bit_poss_assign_reca',
                   'encode_max_bit_poss_assign_reca',
                   'encode_perc_1_bit_poss_assign_reca',
                   'plain_min_bit_poss_assign_reca',
                   'plain_avr_bit_poss_assign_reca',
                   'plain_max_bit_poss_assign_reca',
                   'plain_perc_1_bit_poss_assign_reca',
                   #
                   'encode_min_q_gram_poss_assign_prec',
                   'encode_avr_q_gram_poss_assign_prec',
                   'encode_max_q_gram_poss_assign_prec',
                   'encode_perc_1_q_gram_poss_assign_prec',
                   'plain_min_q_gram_poss_assign_prec',
                   'plain_avr_q_gram_poss_assign_prec',
                   'plain_max_q_gram_poss_assign_prec',
                   'plain_perc_1_q_gram_poss_assign_prec',
                   #
                   'num_no_guess_filter', 'num_too_many_guess_filter',
                   'num_1_1_guess_filter', 'num_corr_1_1_guess_filter',
                   'num_part_1_1_guess_filter', 'num_1_m_guess_filter',
                   'num_corr_1_m_guess_filter', 'num_part_1_m_guess_filter',
                   'acc_part_1_1_guess_filter', 'acc_part_1_m_guess_filter',
                   'reduction_ratio_avrg',
                   #
                   'encode_min_bit_poss_assign_reca_exp',
                   'encode_avr_bit_poss_assign_reca_exp',
                   'encode_max_bit_poss_assign_reca_exp',
                   'encode_perc_1_bit_poss_assign_reca_exp',
                   'plain_min_bit_poss_assign_reca_exp',
                   'plain_avr_bit_poss_assign_reca_exp',
                   'plain_max_bit_poss_assign_reca_exp',
                   'plain_perc_1_bit_poss_assign_reca_exp',
                   #
                   'encode_min_q_gram_poss_assign_prec_exp',
                   'encode_avr_q_gram_poss_assign_prec_exp',
                   'encode_max_q_gram_poss_assign_prec_exp',
                   'encode_perc_1_q_gram_poss_assign_prec_exp',
                   'plain_min_q_gram_poss_assign_prec_exp',
                   'plain_avr_q_gram_poss_assign_prec_exp',
                   'plain_max_q_gram_poss_assign_prec_exp',
                   'plain_perc_1_q_gram_poss_assign_prec_exp',
                   #
                   'num_no_guess_exp_filter', 'num_too_many_guess_exp_filter',
                   'num_1_1_guess_exp_filter', 'num_corr_1_1_guess_exp_filter',
                   'num_part_1_1_guess_exp_filter', 'num_1_m_guess_exp_filter',
                   'num_corr_1_m_guess_exp_filter', 'num_part_1_m_guess_exp_filter',
                   'acc_part_1_1_guess_exp_filter', 'acc_part_1_m_guess_exp_filter',
                   'reduction_ratio_avrg_exp'
                   ]

    # Check if the result file exists, if it does append, otherwise create
    #
    if (not os.path.isfile(res_file_name)):
        write_file = open(res_file_name, 'w')
        csv_writer = csv.writer(write_file)

        csv_writer.writerow(header_list)

        print
        'Created new result file:', res_file_name

    else:  # Append results to an existing file
        write_file = open(res_file_name, 'a')
        csv_writer = csv.writer(write_file)

        print
        'Append results to file:', res_file_name

    csv_writer.writerow(res_list)
    write_file.close()

    print
    '  Written result line:'
    print
    ' ', res_list

    assert len(res_list) == len(header_list)

    print('=' * 80)
    print('end')
