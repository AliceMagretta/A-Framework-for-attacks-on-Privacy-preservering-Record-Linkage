from libs import hashing
from libs import encoding
from libs import hardening
import random
import time
import numpy
import hashlib

BF_HASH_FUNCT1 = hashlib.sha1
BF_HASH_FUNCT2 = hashlib.md5
BF_HASH_FUNCT3 = hashlib.sha224


# -----------------------------------------------------------------------------

def gen_bloom_filter_dict(rec_val_list, rec_id_col, encode_method, hash_type,
                          bf_len, num_hash_funct, use_attr_list, q, padded,
                          bf_harden, enc_param_list=None, harden_param_list=None):
    """Using given record value list generate Bloom filters by encoding specified
       attribute values from each record using given q, bloom filter length, and
       number of hash functions.

       When encoding use the given encode method, hashing type, padding, and
       hardening method.

       Return a dictionary with bit-patterns each of length of the given Bloom
       filter length.
    """

    bf_dict = {}  # One BF per record

    # bf_pos_map_dict = {}  # For each bit position the q-grams mapped to it

    bf_num_1_bit_list = []  # Keep number of bits set to calculate avrg and std

    rec_num = 0

    hash_method_list = []

    # -------------------------------------------------------------------------
    # Define hashing method
    #
    if (hash_type == 'dh'):  # Double Hashing
        if (encode_method == 'clkrbf' and len(use_attr_list) > 1):
            dynamic_num_hash_list = enc_param_list

            for num_hash in dynamic_num_hash_list:
                HASH_METHOD = hashing.DoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                    bf_len, num_hash, True)
                hash_method_list.append(HASH_METHOD)
        else:
            HASH_METHOD = hashing.DoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                bf_len, num_hash_funct, True)
    elif (hash_type == 'rh'):  # Random Hashing
        if (encode_method == 'clkrbf' and len(use_attr_list) > 1):
            dynamic_num_hash_list = enc_param_list

            for num_hash in dynamic_num_hash_list:
                HASH_METHOD = hashing.RandomHashing(BF_HASH_FUNCT1, bf_len,
                                                    num_hash, True)
                hash_method_list.append(HASH_METHOD)
        else:
            HASH_METHOD = hashing.RandomHashing(BF_HASH_FUNCT1, bf_len,
                                                num_hash_funct, True)
    elif (hash_type == 'edh'):  # Enhanced Double Hashing
        if (encode_method == 'clkrbf' and len(use_attr_list) > 1):
            dynamic_num_hash_list = enc_param_list

            for num_hash in dynamic_num_hash_list:
                HASH_METHOD = hashing.EnhancedDoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                            bf_len, num_hash, True)
                hash_method_list.append(HASH_METHOD)
        else:
            HASH_METHOD = hashing.EnhancedDoubleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                        bf_len, num_hash_funct, True)
    else:  # hash_type == 'th' # Triple Hashing
        if (encode_method == 'clkrbf' and len(use_attr_list) > 1):
            dynamic_num_hash_list = enc_param_list

            for num_hash in dynamic_num_hash_list:
                HASH_METHOD = hashing.TripleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                    BF_HASH_FUNCT3, bf_len,
                                                    num_hash, True)
                hash_method_list.append(HASH_METHOD)
        else:
            HASH_METHOD = hashing.TripleHashing(BF_HASH_FUNCT1, BF_HASH_FUNCT2,
                                                BF_HASH_FUNCT3, bf_len,
                                                num_hash_funct, True)

    # -------------------------------------------------------------------------
    # Define encoding method
    #
    if (encode_method == 'abf'):  # Attribute-level Bloom filter
        ENC_METHOD = encoding.AttributeBFEncoding(use_attr_list[0], q, padded,
                                                  HASH_METHOD)
    elif (encode_method == 'clk'):  # Cryptographic Long-term Key
        rec_tuple_list = []

        for att_num in use_attr_list:
            rec_tuple_list.append([att_num, q, padded, HASH_METHOD])

        ENC_METHOD = encoding.CryptoLongtermKeyBFEncoding(rec_tuple_list)

    elif (encode_method.startswith('rbf')):  # Record-level Bloom filter

        num_bits_list = enc_param_list  # List of percentages of number of bits

        rec_tuple_list = []

        for (i, att_num) in enumerate(use_attr_list):
            rec_tuple_list.append([att_num, q, padded, HASH_METHOD,
                                   int(num_bits_list[i] * bf_len)])

        ENC_METHOD = encoding.RecordBFEncoding(rec_tuple_list)

    else:  # encode_method == 'clkrbf'
        rec_tuple_list = []

        for (i, att_num) in enumerate(use_attr_list):
            rec_tuple_list.append([att_num, q, padded, hash_method_list[i]])

        ENC_METHOD = encoding.CryptoLongtermKeyBFEncoding(rec_tuple_list)

    # -------------------------------------------------------------------------
    # Define hardening method
    #
    if (bf_harden == 'balance'):  # Bloom filter Balancing
        input_random_seed = harden_param_list[0]

        if (input_random_seed):
            rand_seed = random.randint(1, 100)
            BFHard = hardening.Balancing(True, rand_seed)
        else:
            BFHard = hardening.Balancing(True)

    elif (bf_harden == 'fold'):  # Bloom filter XOR Folding
        BFHard = hardening.Folding(True)

    elif (bf_harden == 'rule90'):  # Bloom filter Rule 90
        BFHard = hardening.Rule90()

    elif (bf_harden == 'mchain'):  # Bloom filter Markov Chain

        chain_len = harden_param_list[0]
        sel_method = harden_param_list[1]

        # Get a single list of all attribute values
        lang_model_val_list = []

        for rec_val in rec_val_list:
            val_list = []

            for attr_num in use_attr_list:
                val_list.append(rec_val[attr_num])

            rec_str = ' '.join(val_list)

            lang_model_val_list.append(rec_str)

        # Initialize Markov Chain class
        BFHard = hardening.MarkovChain(q, padded, chain_len, sel_method)

        # Calculate transition probability
        BFHard.calc_trans_prob(lang_model_val_list)

    # -------------------------------------------------------------------------
    # Loop over each record and encode relevant attribute values to a
    # Bloom filter
    #
    true_q_gram_pos_dict = {}

    for attr_val_list in rec_val_list:

        # Apply Bloom filter hardening if required
        #
        rec_id = attr_val_list[rec_id_col].strip().lower()  # Get record ID number
        if '-' in rec_id:
            rec_id = rec_id.split('-')[1].strip()

        if (bf_harden in ['balance', 'fold']):
            rec_bf, q_gram_pos_dict = ENC_METHOD.encode(attr_val_list)
            rec_bf, nw_q_gram_pos_dict = BFHard.harden_bf(rec_bf, q_gram_pos_dict)
            q_gram_pos_dict = nw_q_gram_pos_dict.copy()
            del nw_q_gram_pos_dict

        elif (bf_harden in 'rule90'):
            rec_bf, q_gram_pos_dict = ENC_METHOD.encode(attr_val_list)
            rec_bf = BFHard.harden_bf(rec_bf)

        elif (bf_harden == 'mchain'):
            rec_bf, q_gram_pos_dict = ENC_METHOD.encode(attr_val_list, None, BFHard)

        elif (bf_harden == 'salt'):
            salt_str = attr_val_list[5]  # birth year
            if (encode_method == 'abf'):
                rec_bf, q_gram_pos_dict = ENC_METHOD.encode(attr_val_list, salt_str)
            else:
                rec_bf, q_gram_pos_dict = ENC_METHOD.encode(attr_val_list,
                                                            [salt_str for _ in
                                                             range(len(use_attr_list))])

        else:  # bf_harden == 'none'
            rec_bf, q_gram_pos_dict = ENC_METHOD.encode(attr_val_list)

        # Add final Bloom filter to the BF dictionary
        bf_dict[rec_id] = rec_bf

        # Add q-gram positions to the dictionary
        for q_gram, pos_set in q_gram_pos_dict.items():
            all_pos_set = true_q_gram_pos_dict.get(q_gram, set())
            all_pos_set.update(pos_set)
            true_q_gram_pos_dict[q_gram] = all_pos_set

        # Count the number of 1 bits in the Bloom filter
        bf_num_1_bit_list.append(int(rec_bf.count(1)))

    del bf_num_1_bit_list

    return bf_dict, true_q_gram_pos_dict