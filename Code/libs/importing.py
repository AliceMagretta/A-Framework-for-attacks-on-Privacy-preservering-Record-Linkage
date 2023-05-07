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

PAD_CHAR = chr(1)  # Used for q-gram padding


# -----------------------------------------------------------------------------

def load_data_set_extract_attr_val(file_name, rec_id_col, use_attr_list,
                                   col_sep_char, header_line):
    """Load the given file, extract all attributes and get them into a single
       list.

       Returns:
       1) a list of total record values.
       2) a dictionary of record values where keys are record ids and values
          are all the attribute values of that record.
       3) a dictionary of record value frequencies where keys are record
          values and values are frequencies.
       4) and a list of the attribute names used.
    """

    start_time = time.time()

    if (file_name.endswith('gz')):
        f = gzip.open(file_name)
    else:
        f = open(file_name)

    csv_reader = csv.reader(f, delimiter=col_sep_char)

    if (header_line == True):
        h_list = next(csv_reader)
        header_list = h_list[0].split(",")

    use_attr_name_list = []
    if (header_line == True):
        for attr_num in use_attr_list:
            use_attr_name = header_list[attr_num]
            use_attr_name_list.append(use_attr_name)
    print(use_attr_name_list)
    # A list containing all record values
    #
    total_rec_list = []

    # A dictionary of encoded record values in each record
    #
    rec_val_dict = {}

    # A dictionary with record values as keys and record ids as values
    #
    rec_val_id_dict = {}

    # A dictionary of encoded record value frequencies
    #
    rec_val_freq_dict = {}

    # Removed and confidential records. These records do not have any
    # attribute values
    num_rec_with_removed = 0
    num_rec_with_conf = 0

    for rec_list in csv_reader:

        if ('removed' in rec_list):
            num_rec_with_removed += 1
            continue

        if ('confidential' in rec_list):
            num_rec_with_conf += 1
            continue

        # Get record ID
        rec_id = rec_list[rec_id_col].strip().lower()
        if '-' in rec_id:
            rec_id = rec_id.split('-')[1].strip()

        # A list of attribute values per record
        rec_val_list = []

        # A list of attribute values (per record) which will be used for encoding
        use_attr_val_list = []

        # Loop over each attribute value in the record
        for (i, attr_val) in enumerate(rec_list):
            rec_val_list.append(attr_val.strip().lower())

            # Check if current attribute is specified to be encoded
            if (i in use_attr_list):
                use_attr_val_list.append(attr_val.strip().lower())

        total_rec_list.append(rec_val_list)

        # Join all attribute values to a single string
        rec_val = ' '.join(use_attr_val_list)
        rec_val_dict[rec_id] = rec_val

        val_id_set = rec_val_id_dict.get(rec_val, set())
        val_id_set.add(rec_id)
        rec_val_id_dict[rec_val] = val_id_set

        rec_val_freq_dict[rec_val] = rec_val_freq_dict.get(rec_val, 0) + 1

    print('  Number of dismissed records with value \'removed\':', num_rec_with_removed)
    print('  Number of dismissed records with value \'confidential\':', num_rec_with_conf)
    print()

    return total_rec_list, rec_val_dict, rec_val_id_dict, rec_val_freq_dict, use_attr_name_list


# -----------------------------------------------------------------------------

def get_data_analysis_dict(rec_val_list, use_attr_list, q, padded, rec_id_col,
                           bf_harden):
    """ Using a list of records extracted from a dataset generate different
        dictionaries and lists of attribute values, q-grams, etc. for later
        analysations
    """

    # A dictionary of q-grams per each record
    rec_q_gram_dict = {}

    # A dictionary of encoded record values in each record
    rec_val_dict = {}

    # A dictionary of encoded record value frequencies
    rec_val_freq_dict = {}

    # A dictionary of attribute values which contain certian q-grams
    q_gram_attr_val_dict = {}

    # Unique q-gram set
    unique_q_gram_set = set()

    # A dictionary of record ids which has same record value
    attr_val_rec_id_dict = {}

    # Number of records per attribute value as
    # well as the q-gram set for this value
    attr_val_freq_q_gram_dict = {}

    qm1 = q - 1  # Shorthand

    for attr_val_list in rec_val_list:

        # A list of attribute values (per record) which will be used for encoding
        use_attr_val_list = []

        # A set of q-grams per each record
        rec_q_gram_set = set()

        # Get the record ID from the list of attribute values
        rec_id = attr_val_list[rec_id_col].strip().lower()
        if '-' in rec_id:
            rec_id = rec_id.split('-')[1].strip()

        # Loop over each attribute number that is defined to be encoded
        for attr_num in use_attr_list:

            # Get the attribute value and its length
            attr_val = attr_val_list[attr_num]
            attr_val_len = len(attr_val)

            if (padded == True):  # Add padding start and end characters
                attr_val = PAD_CHAR * qm1 + attr_val + PAD_CHAR * qm1
                attr_val_len += 2 * qm1

            # Get the q-gram set for attribute value
            attr_q_gram_set = set([attr_val[i:i + q] for i in
                                   range(attr_val_len - qm1)])

            # Add q-gram set of attribute value to record value q-gram set
            rec_q_gram_set.update(attr_q_gram_set)

            # Add the attribute value to used attribute list
            use_attr_val_list.append(attr_val)

        # Check salting method and add salting string value
        # to each q-gram
        if (bf_harden == 'salt'):
            salt_str = attr_val_list[5]  # birth year
            new_rec_q_gram_set = set()

            for q_gram in rec_q_gram_set:
                new_rec_q_gram_set.add(q_gram + salt_str)

            rec_q_gram_set = new_rec_q_gram_set

        # Add q-gram set of whole record to the dictionary
        rec_q_gram_dict[rec_id] = rec_q_gram_set

        # Update unique q-gram set
        unique_q_gram_set.update(rec_q_gram_set)

        # Join all attribute values to a single string
        rec_val = ' '.join(use_attr_val_list)

        # Add record value to the encoded record value dictionary
        rec_val_dict[rec_id] = rec_val

        rec_val_freq_dict[rec_val] = rec_val_freq_dict.get(rec_val, 0) + 1

        # Add record id to the list of record ids which have the same record value
        rec_id_set = attr_val_rec_id_dict.get(rec_val, set())
        rec_id_set.add(rec_id)
        attr_val_rec_id_dict[rec_val] = rec_id_set

        for q_gram in rec_q_gram_set:
            attr_val_set = q_gram_attr_val_dict.get(q_gram, set())
            attr_val_set.add(rec_val)

            q_gram_attr_val_dict[q_gram] = attr_val_set

        rec_q_gram_list = list(rec_q_gram_set)

        if rec_val in attr_val_freq_q_gram_dict:
            rec_val_freq, dict_attr_q_gram_list = \
                attr_val_freq_q_gram_dict[rec_val]
            assert dict_attr_q_gram_list == rec_q_gram_list
            rec_val_freq += 1
        else:
            rec_val_freq = 1
        attr_val_freq_q_gram_dict[rec_val] = (rec_val_freq, rec_q_gram_list)

    return rec_q_gram_dict, q_gram_attr_val_dict, attr_val_rec_id_dict, \
           rec_val_dict, rec_val_freq_dict, unique_q_gram_set, \
           attr_val_freq_q_gram_dict


# -----------------------------------------------------------------------------

def get_avrg_num_q_grams(rec_val_list, use_attr_list, q, padded):
    """ Using a list of records extracted from dataset calculate the average
        number of q-grams per record
    """

    num_q_gram_per_rec_list = []

    qm1 = q - 1  # Shorthand

    for attr_val_list in rec_val_list:

        rec_q_gram_set = set()

        for attr_num in use_attr_list:
            attr_val = attr_val_list[attr_num]

            attr_val_len = len(attr_val)

            if (padded == True):  # Add padding start and end characters
                attr_val = PAD_CHAR * qm1 + attr_val + PAD_CHAR * qm1
                attr_val_len += 2 * qm1

            attr_q_gram_set = set([attr_val[i:i + q] for i in
                                   range(attr_val_len - qm1)])

            rec_q_gram_set.update(attr_q_gram_set)

        num_q_gram_per_rec_list.append(len(rec_q_gram_set))

    avrg_num_q_gram = numpy.mean(num_q_gram_per_rec_list)

    return avrg_num_q_gram
