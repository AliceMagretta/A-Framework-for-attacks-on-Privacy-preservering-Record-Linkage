from libs import importing
from libs import bfEncoding
from libs import evaluating
from libs.attacks import patternmining_attack as pma
from libs.attacks import bit_patternfrequency_attack as bpf
from libs.attacks import graph_matching_attack as gma
import csv
import gzip
import math
import hashlib
import os.path
import random
import sys
import time
import bitarray
import numpy

# HW for bit positions

# parameter input

# encoding parameters
q = int(sys.argv[1])
hash_type = sys.argv[2].lower()
num_hash_funct = sys.argv[3]
bf_len = int(sys.argv[4])
bf_harden = sys.argv[5].lower()
bf_encode = sys.argv[6].lower()
padded = eval(sys.argv[7])

# encode dataset parameters
encode_data_set_name = sys.argv[12]
encode_rec_id_col = int(sys.argv[13])
encode_col_sep_char = sys.argv[14]
encode_header_line_flag = eval(sys.argv[15])
encode_attr_list = eval(sys.argv[16])

# plain dataset parameters
plain_data_set_name = sys.argv[17]
plain_rec_id_col = int(sys.argv[18])
plain_col_sep_char = sys.argv[19]
plain_header_line_flag = eval(sys.argv[20])
plain_attr_list = eval(sys.argv[21])

enc_param_list = eval(sys.argv[22])
harden_param_list = eval(sys.argv[23])
attack_method = sys.argv[24].lower()

# valid value check
assert q >= 1, q
assert hash_type in ['dh', 'rh', 'edh', 'th'], hash_type
if num_hash_funct.isdigit():
    num_hash_funct = int(num_hash_funct)
    assert num_hash_funct >= 1, num_hash_funct
else:
    assert num_hash_funct == 'opt', num_hash_funct
assert bf_len > 1, bf_len
assert bf_harden in ['none', 'balance', 'fold', 'rule90', 'mchain', 'salt'], \
    bf_harden

assert encode_rec_id_col >= 0, encode_rec_id_col
assert encode_header_line_flag in [True, False], encode_header_line_flag
assert isinstance(encode_attr_list, list), encode_attr_list
#
assert plain_rec_id_col >= 0, plain_rec_id_col
assert plain_header_line_flag in [True, False], plain_header_line_flag
assert isinstance(plain_attr_list, list), plain_attr_list

#
assert bf_encode in ['abf', 'clk', 'rbf-s', 'clkrbf'], bf_encode
#
assert padded in [True, False], padded

if (bf_harden == 'mchain'):
    mc_chain_len = harden_param_list[0]
    mc_sel_method = harden_param_list[1]
else:
    mc_chain_len = 'None'
    mc_sel_method = 'None'

if (bf_harden == 'fold'):
    if (bf_len % 2 != 0):
        raise Exception('BF hardening approach "fold" needs an even BF length')

if (len(encode_col_sep_char) > 1):
    if (encode_col_sep_char == 'tab'):
        encode_col_sep_char = '\t'
    elif (encode_col_sep_char[0] == '"') and (encode_col_sep_char[-1] == '"') \
            and (len(encode_col_sep_char) == 3):
        encode_col_sep_char = encode_col_sep_char[1]
    else:
        print('Illegal encode data set column separator format:', \
              encode_col_sep_char)

if (len(plain_col_sep_char) > 1):
    if (plain_col_sep_char == 'tab'):
        plain_col_sep_char = '\t'
    elif (plain_col_sep_char[0] == '"') and \
            (plain_col_sep_char[-1] == '"') and \
            (len(plain_col_sep_char) == 3):
        plain_col_sep_char = plain_col_sep_char[1]
    else:
        print('Illegal plain text data set column separator format:', \
              plain_col_sep_char)

# file for saving
encode_base_data_set_name = encode_data_set_name.split('/')[-1]
encode_base_data_set_name = encode_base_data_set_name.replace('.csv', '')
encode_base_data_set_name = encode_base_data_set_name.replace('.gz', '')
assert ',' not in encode_base_data_set_name

plain_base_data_set_name = plain_data_set_name.split('/')[-1]
plain_base_data_set_name = plain_base_data_set_name.replace('.csv', '')
plain_base_data_set_name = plain_base_data_set_name.replace('.gz', '')
assert ',' not in plain_base_data_set_name

# todo: file name
res_file_name = 'bf-attack-col-pattern-results-%s-%s-%s.csv' % \
                (encode_base_data_set_name, plain_base_data_set_name, \
                 time.strftime("%Y%m%d", time.localtime()))
print()
print('Write results into file:', res_file_name)
print()
print('-' * 80)
print()

# Step 1: Load the data sets and extract q-grams for selected attributes

# Check if same data sets and same attributes were given
#
if ((encode_data_set_name == plain_data_set_name) and \
        (encode_attr_list == plain_attr_list)):
    same_data_attr_flag = True
else:
    same_data_attr_flag = False

# Read the input data file and load all the record values to a list
#
encode_rec_val_res_tuple = \
    importing.load_data_set_extract_attr_val(encode_data_set_name,
                                             encode_rec_id_col,
                                             encode_attr_list,
                                             encode_col_sep_char,
                                             encode_header_line_flag)

encode_rec_val_list = encode_rec_val_res_tuple[0]
encode_rec_val_dict = encode_rec_val_res_tuple[1]
encode_rec_val_id_dict = encode_rec_val_res_tuple[2]
encode_rec_val_freq_dict = encode_rec_val_res_tuple[3]
encode_attr_name_list = encode_rec_val_res_tuple[4]

if (same_data_attr_flag == False):

    plain_rec_val_res_tuple = \
        importing.load_data_set_extract_attr_val(plain_data_set_name,
                                                 plain_rec_id_col,
                                                 plain_attr_list,
                                                 plain_col_sep_char,
                                                 plain_header_line_flag)

    plain_rec_val_list = plain_rec_val_res_tuple[0]
    plain_rec_val_dict = plain_rec_val_res_tuple[1]
    plain_rec_val_id_dict = plain_rec_val_res_tuple[2]
    plain_rec_val_freq_dict = plain_rec_val_res_tuple[3]
    plain_attr_name_list = plain_rec_val_res_tuple[4]
else:
    plain_rec_val_list = encode_rec_val_list
    plain_rec_val_dict = encode_rec_val_dict
    plain_rec_val_id_dict = encode_rec_val_id_dict
    plain_rec_val_freq_dict = encode_rec_val_freq_dict
    plain_attr_name_list = encode_attr_name_list

# -----------------------------------------------------------------------------
# Step 2: Generate Bloom filters for records
#

if (num_hash_funct == 'opt'):
    # Get average number of q-grams per record
    #
    enc_avrg_num_q_gram = importing.get_avrg_num_q_grams(encode_rec_val_list,
                                                         encode_attr_list, q, padded)

    # Set number of hash functions to have in average 50% of bits set to 1
    # (reference to published paper? Only in Dinusha's submitted papers)
    # num_hash_funct = int(math.ceil(0.5 * BF_LEN / \
    #                                math.floor(avrg_num_q_gram)))
    #
    num_hash_funct = int(round(numpy.log(2.0) * float(bf_len) /
                               enc_avrg_num_q_gram))

encode_bf_dict, encode_true_q_gram_pos_map_dict = \
    bfEncoding.gen_bloom_filter_dict(encode_rec_val_list, encode_rec_id_col,
                                     bf_encode, hash_type, bf_len,
                                     num_hash_funct, encode_attr_list, q,
                                     padded, bf_harden, enc_param_list,
                                     harden_param_list)

# -----------------------------------------------------------------------------
# Step 3: choose an attack method to conduct

# timer
ini_start_time = time.time()

# bit pattern frequency attack
if (attack_method == 'bfbitpattern'):
    # -----------------------------------------------------------------------------
    # stage1 preparation
    # attack parameters
    min_freq = int(sys.argv[8])
    num_freq_attr_val_list = eval(sys.argv[9])
    #
    assert min_freq >= 1, min_freq

    bpf.attack(q, padded, bf_harden, encode_bf_dict, bf_encode, hash_type, bf_len, num_hash_funct, res_file_name,
               encode_base_data_set_name, plain_base_data_set_name, encode_rec_val_res_tuple,
               plain_rec_val_res_tuple, min_freq, num_freq_attr_val_list)


# pattern mining based attack
elif (attack_method == 'bfcolpattern'):

    # attack parameters
    pattern_mine_method_str = sys.argv[8].lower()
    stop_iter_perc = float(sys.argv[9])
    stop_iter_perc_lm = float(sys.argv[10])
    min_part_size = int(sys.argv[11])

    max_num_many = int(sys.argv[22])
    re_id_method = sys.argv[23]
    expand_lang_model = sys.argv[24]
    lang_model_min_freq = int(sys.argv[25])
    #
    assert pattern_mine_method_str[0] == '[' and \
           pattern_mine_method_str[-1] == ']', pattern_mine_method_str

    pattern_mine_method_list = []
    for pattern_mine_method in pattern_mine_method_str[1:-1].split(','):
        assert pattern_mine_method in ['apriori', 'mapriori', 'maxminer', \
                                       'hmine', 'fpmax']
        pattern_mine_method_list.append(pattern_mine_method)
    #
    assert stop_iter_perc > 0.0 and stop_iter_perc < 100.0, stop_iter_perc
    assert stop_iter_perc_lm > 0.0 and stop_iter_perc_lm < 100.0, stop_iter_perc_lm
    assert min_part_size > 1, min_part_size
    assert max_num_many > 1, max_num_many
    assert re_id_method in ['all', 'set_inter', 'bf_tuple', 'none']
    assert expand_lang_model in ['single', 'tuple', 'all'], expand_lang_model
    assert lang_model_min_freq >= 1, lang_model_min_freq

    pma.attack(q, padded, bf_harden, encode_attr_list, plain_attr_list, plain_rec_id_col, same_data_attr_flag,
               encode_bf_dict, bf_encode, hash_type, bf_len, num_hash_funct, enc_param_list, res_file_name,
               ini_start_time,
               harden_param_list, encode_true_q_gram_pos_map_dict, pattern_mine_method_list, encode_base_data_set_name,
               plain_base_data_set_name, mc_chain_len, mc_sel_method, encode_rec_id_col, encode_rec_val_list,
               encode_attr_name_list, plain_rec_val_list, plain_attr_name_list,
               pattern_mine_method_str, stop_iter_perc, stop_iter_perc_lm, min_part_size,
               max_num_many, re_id_method, expand_lang_model, lang_model_min_freq)


# graph matching based attack
elif (attack_method == 'graphmatching'):
    # attack parameters
    plain_sim_funct_name = sys.argv[15].lower()
    sim_diff_adjust_flag = eval(sys.argv[16])
    encode_sim_funct_name = sys.argv[-1].lower()

    assert plain_sim_funct_name in ['dice', 'jacc'], plain_sim_funct_name
    assert encode_sim_funct_name in ['dice', 'jacc', 'hamm'], encode_sim_funct_name
    sim_diff_adjust_flag in [True, False], sim_diff_adjust_flag

    gma.attack(q, hash_type, num_hash_funct, bf_len, bf_harden, bf_encode, padded, enc_param_list, encode_data_set_name,
               encode_rec_id_col, encode_col_sep_char, encode_header_line_flag, encode_attr_list, plain_data_set_name,
               plain_rec_id_col, plain_col_sep_char, plain_header_line_flag, plain_attr_list,
               plain_sim_funct_name, sim_diff_adjust_flag, encode_sim_funct_name)
