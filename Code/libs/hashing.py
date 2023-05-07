# hashing.py - Module that implements several Bloom filter hashing methods
#
# June 2018

# Peter Christen, Thilina Ranbaduge, Sirintra Vaiwsri, and Anushka Vidanage
#
# Contact: peter.christen@anu.edu.au
#
# Research School of Computer Science, The Australian National University,
# Canberra, ACT, 2601
# -----------------------------------------------------------------------------
#
# Copyright 2018 Australian National University and others.
# All Rights reserved.
#
# -----------------------------------------------------------------------------
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
# =============================================================================

import hashlib  # A standard Python library
import random   # For random hashing

import bitarray  # Efficient bit-arrays, available from:
                 # https://pypi.org/project/bitarray/

# =============================================================================

class DoubleHashing():
  """Double-hashing for Bloom filters was proposed and used by:
       - A. Kirsch and M. Mitzenmacher, Less hashing, same performance:
         building a better Bloom filter, ESA, 2006, pp. 456-467.
       - R. Schnell, T. Bachteler, and J. Reiher, Privacy-preserving record
         linkage using Bloom filters, BMC MIDM, vol. 9, no. 1, 2009.
  """

  # ---------------------------------------------------------------------------

  def __init__(self, hash_funct1, hash_funct2, bf_len, num_hash_funct,
               get_q_gram_pos=False):
    """Initialise the double-hashing class by providing the required
       parameters.

       Input arguments:
         - hash_funct1, hash_funct2  Two hash functions.
         - bf_len                    The length in bits of the Bloom filters
                                     to be generated.
         - num_hash_funct            The number of hash functions to be used.
         - get_q_gram_pos            A flag, if set to True then the bit
                                     positions of where q-grams are hash into
                                     are returned in a dictionary.

       Output:
         - This method does not return anything.
    """

    # Initialise the class variables
    #
    self.hash_funct1 = hash_funct1
    self.hash_funct2 = hash_funct2

    assert bf_len > 1, bf_len
    self.bf_len = bf_len

    assert num_hash_funct > 0
    self.num_hash_funct = num_hash_funct

    assert get_q_gram_pos in [True, False]
    self.get_q_gram_pos = get_q_gram_pos

  # ---------------------------------------------------------------------------

  def hash_q_gram_set(self, q_gram_set, salt_str=None):
    """Hash the given q-gram set according to the parameter using when
       initialising the class.

       Input arguments:
         - q_gram_set  The set of q-grams (strings) to be hashed into a Bloom
                       filter.
         - salt_str    An optional string used for salting, if provided this
                       string will be concatenated with every q-gram in the
                       given q-gram set. If set to None no salting will be
                       done.

       Output:
         - bf               A Bloom filter with bits set according to the input
                            q-gram set and double hashing parameters.
         - q_gram_pos_dict  [Only returned if 'get_q_gram_pos' is set to True]
                            A dictionary which has q-grams as keys and where
                            values are sets with the positions these q-grams
                            are hashed to.
    """

    bf_len = self.bf_len  # Short-cuts
    k =      self.num_hash_funct

    get_q_gram_pos = self.get_q_gram_pos
    if (get_q_gram_pos == True):
      q_gram_pos_dict = {}

    # Initialise the Bloom filter to have only 0-bits
    #
    bf = bitarray.bitarray(bf_len)
    bf.setall(0)

    # Hash the q-grams into the Bloom filter
    #
    for q_gram in q_gram_set:

      if (get_q_gram_pos == True):
        q_gram_pos_set = set()

      if (salt_str != None):  # If a salt is given concatenate with q-gram
        q_gram = q_gram + salt_str

      hex_str1 = self.hash_funct1(q_gram).hexdigest()
      int1 =     int(hex_str1, 16)

      hex_str2 = self.hash_funct2(q_gram).hexdigest()
      int2 =     int(hex_str2, 16)

      for i in range(1, k+1):
        pos_i = int1 + i*int2
        pos_i = int(pos_i % bf_len)
        bf[pos_i] = 1

        if (get_q_gram_pos == True):
          q_gram_pos_set.add(pos_i)

      if (get_q_gram_pos == True):
        q_gram_pos_dict[q_gram] = q_gram_pos_set

    if (get_q_gram_pos == True):
      return bf, q_gram_pos_dict
    else:
      return bf

# =============================================================================

class EnhancedDoubleHashing():
  """Enhanced Double-hashing for Bloom filters was proposed and used by:
       - P.C. Dillinger and P. Manolios, Bloom filters in probabilistic
         verification, International Conference on Formal Methods in
         Computer-Aided Design, 2004, pp. 367-381.
       - P.C. Dillinger and P. Manolios, Fast and accurate bitstate
         verification for SPIN, International SPIN Workshop on Model
         Checking of Software, 2004, pp. 57-75.
  """

  # ----------------------------------------------------------------------------

  def __init__(self, hash_funct1, hash_funct2, bf_len, num_hash_funct,
               get_q_gram_pos=False):
    """Initialise the enhanced double-hashing class by providing the required
       parameters.

       Input arguments:
         - hash_funct1, hash_funct2  Two hash functions.
         - bf_len                    The length in bits of the Bloom filters
                                     to be generated.
         - num_hash_funct            The number of hash functions to be used.
         - get_q_gram_pos            A flag, if set to True then the bit
                                     positions of where q-grams are hash into
                                     are returned in a dictionary.

       Output:
         - This method does not return anything.
    """

    # Initialise the class variables
    #
    self.hash_funct1 = hash_funct1
    self.hash_funct2 = hash_funct2

    assert bf_len > 1, bf_len
    self.bf_len = bf_len

    assert num_hash_funct > 0
    self.num_hash_funct = num_hash_funct

    assert get_q_gram_pos in [True, False]
    self.get_q_gram_pos = get_q_gram_pos

  # ---------------------------------------------------------------------------

  def hash_q_gram_set(self, q_gram_set, salt_str=None):
    """Hash the given q-gram set according to the parameter using when
       initialising the class.

       Input arguments:
         - q_gram_set  The set of q-grams (strings) to be hashed into a Bloom
                       filter.
         - salt_str    An optional string used for salting, if provided this
                       string will be concatenated with every q-gram in the
                       given q-gram set. If set to None no salting will be
                       done.

       Output:
         - bf               A Bloom filter with bits set according to the input
                            q-gram set and enhanced double hashing parameters.
         - q_gram_pos_dict  [Only returned if 'get_q_gram_pos' is set to True]
                            A dictionary which has q-grams as keys and where
                            values are sets with the positions these q-grams
                            are hashed to.
    """

    bf_len = self.bf_len  # Short-cuts
    k =      self.num_hash_funct

    get_q_gram_pos = self.get_q_gram_pos
    if (get_q_gram_pos == True):
      q_gram_pos_dict = {}

    # Initialise the Bloom filter to have only 0-bits
    #
    bf = bitarray.bitarray(bf_len)
    bf.setall(0)

    # Hash the q-grams into the Bloom filter
    #
    for q_gram in q_gram_set:

      if (get_q_gram_pos == True):
        q_gram_pos_set = set()

      if (salt_str != None):  # If a salt is given concatenate with q-gram
        q_gram = q_gram + salt_str

      hex_str1 = self.hash_funct1(q_gram).hexdigest()
      int1 =     int(hex_str1, 16)

      hex_str2 = self.hash_funct2(q_gram).hexdigest()
      int2 =     int(hex_str2, 16)

      for i in range(1, k+1):
        pos_i = int1 + i*int2 + int((float(i*i*i) - i) / 6.0)
        pos_i = int(pos_i % bf_len)
        bf[pos_i] = 1

        if (get_q_gram_pos == True):
          q_gram_pos_set.add(pos_i)

      if (get_q_gram_pos == True):
        q_gram_pos_dict[q_gram] = q_gram_pos_set

    if (get_q_gram_pos == True):
      return bf, q_gram_pos_dict
    else:
      return bf

# =============================================================================

class TripleHashing():
  """Triple-hashing for Bloom filters was proposed and used by:
       - P.C. Dillinger and P. Manolios, Bloom filters in probabilistic
         verification, International Conference on Formal Methods in
         Computer-Aided Design, 2004, pp. 367-381.
       - P.C. Dillinger and P. Manolios, Fast and accurate bitstate
         verification for spin, International SPIN Workshop on Model
         Checking of Software, 2004, pp. 57-75.
  """

  # ---------------------------------------------------------------------------

  def __init__(self, hash_funct1, hash_funct2, hash_funct3, bf_len,
               num_hash_funct, get_q_gram_pos=False):
    """Initialise the triple-hashing class by providing the required
       parameters.

       Input arguments:
         - hash_funct1, hash_funct2, hash_funct3  Three hash functions.
         - bf_len                                 The length in bits of the
                                                  Bloom filters to be
                                                  generated.
         - num_hash_funct                         The number of hash functions
                                                  to be used.
         - get_q_gram_pos                         A flag, if set to True then
                                                  the bit positions of where
                                                  q-grams are hash into are
                                                  returned in a dictionary.

       Output:
         - This method does not return anything.
    """

    # Initialise the class variables
    #
    self.hash_funct1 = hash_funct1
    self.hash_funct2 = hash_funct2
    self.hash_funct3 = hash_funct3

    assert bf_len > 1, bf_len
    self.bf_len = bf_len

    assert num_hash_funct > 0
    self.num_hash_funct = num_hash_funct

    assert get_q_gram_pos in [True, False]
    self.get_q_gram_pos = get_q_gram_pos

  # ---------------------------------------------------------------------------

  def hash_q_gram_set(self, q_gram_set, salt_str=None):
    """Hash the given q-gram set according to the parameter using when
       initialising the class.

       Input arguments:
         - q_gram_set  The set of q-grams (strings) to be hashed into a Bloom
                       filter.
         - salt_str    An optional string used for salting, if provided this
                       string will be concatenated with every q-gram in the
                       given q-gram set. If set to None no salting will be
                       done.

       Output:
         - bf               A Bloom filter with bits set according to the input
                            q-gram set and triple hashing parameters.
         - q_gram_pos_dict  [Only returned if 'get_q_gram_pos' is set to True]
                            A dictionary which has q-grams as keys and where
                            values are sets with the positions these q-grams
                            are hashed to.
    """

    bf_len = self.bf_len  # Short-cuts
    k =      self.num_hash_funct

    get_q_gram_pos = self.get_q_gram_pos
    if (get_q_gram_pos == True):
      q_gram_pos_dict = {}

    # Initialise the Bloom filter to have only 0-bits
    #
    bf = bitarray.bitarray(bf_len)
    bf.setall(0)

    # Hash the q-grams into the Bloom filter
    #
    for q_gram in q_gram_set:

      if (get_q_gram_pos == True):
        q_gram_pos_set = set()

      if (salt_str != None):  # If a salt is given concatenate with q-gram
        q_gram = q_gram + salt_str

      hex_str1 = self.hash_funct1(q_gram).hexdigest()
      int1 =     int(hex_str1, 16)

      hex_str2 = self.hash_funct2(q_gram).hexdigest()
      int2 =     int(hex_str2, 16)

      hex_str3 = self.hash_funct3(q_gram).hexdigest()
      int3 =     int(hex_str3, 16)

      for i in range(1, k+1):
        pos_i = int1 + i*int2 + int(float(i*(i-1)/2.0))*int3
        pos_i = int(pos_i % bf_len)
        bf[pos_i] = 1

        if (get_q_gram_pos == True):
          q_gram_pos_set.add(pos_i)

      if (get_q_gram_pos == True):
        q_gram_pos_dict[q_gram] = q_gram_pos_set

    if (get_q_gram_pos == True):
      return bf, q_gram_pos_dict
    else:
      return bf

# =============================================================================

class RandomHashing():
  """Random-hashing for Bloom filters was proposed and used by:
       - R. Schnell and C. Borgs, Randomized response and balanced Bloom
         filters for privacy preserving record linkage, Workshop on Data
         Integration and Applications, held at ICDM, Barcelona, 2016.
  """

  # ---------------------------------------------------------------------------

  def __init__(self, hash_funct, bf_len, num_hash_funct,
               get_q_gram_pos=False):
    """Initialise the random-hashing class by providing the required
       parameters.

       Input arguments:
         - hash_funct      The hash function to be used to encode q-grams.
         - bf_len          The length in bits of the Bloom filters to be
                           generated.
         - num_hash_funct  The number of hash functions to be used.
         - get_q_gram_pos  A flag, if set to True then the bit positions of
                           where q-grams are hash into are returned in a
                           dictionary.

       Output:
         - This method does not return anything.
    """

    # Initialise the class variables
    #
    self.hash_funct = hash_funct

    assert bf_len > 1, bf_len
    self.bf_len = bf_len

    assert num_hash_funct > 0
    self.num_hash_funct = num_hash_funct

    assert get_q_gram_pos in [True, False]
    self.get_q_gram_pos = get_q_gram_pos

  # ---------------------------------------------------------------------------

  def hash_q_gram_set(self, q_gram_set, salt_str=None):
    """Hash the given q-gram set according to the parameter using when
       initialising the class.

       Input arguments:
         - q_gram_set  The set of q-grams (strings) to be hashed into a Bloom
                       filter.
         - salt_str    An optional string used for salting, if provided this
                       string will be concatenated with every q-gram in the
                       given q-gram set. If set to None no salting will be
                       done.

       Output:
         - bf               A Bloom filter with bits set according to the input
                            q-gram set and random hashing parameters.
         - q_gram_pos_dict  [Only returned if 'get_q_gram_pos' is set to True]
                            A dictionary which has q-grams as keys and where
                            values are sets with the positions these q-grams
                            are hashed to.
    """

    bf_len = self.bf_len  # Short-cuts
    k =      self.num_hash_funct

    get_q_gram_pos = self.get_q_gram_pos
    if (get_q_gram_pos == True):
      q_gram_pos_dict = {}

    # Initialise the Bloom filter to have only 0-bits
    #
    bf = bitarray.bitarray(bf_len)
    bf.setall(0)

    # Bloom filter length minus 1 using for position index in Bloom filter
    #
    bf_len_m1 = bf_len - 1

    # Hash the q-grams into the Bloom filter
    #
    for q_gram in q_gram_set:

      if (get_q_gram_pos == True):
        q_gram_pos_set = set()

      if (salt_str != None):  # If a salt is given concatenate with q-gram
        q_gram = q_gram + salt_str

      # Use q-gram itself to see random number generator
      #
      hex_str = self.hash_funct(q_gram).hexdigest()
      random_seed = random.seed(int(hex_str, 16))

      for i in range(k):
        pos_i = random.randint(0, bf_len_m1)
        bf[pos_i] = 1

        if (get_q_gram_pos == True):
          q_gram_pos_set.add(pos_i)

      if (get_q_gram_pos == True):
        q_gram_pos_dict[q_gram] = q_gram_pos_set

    if (get_q_gram_pos == True):
      return bf, q_gram_pos_dict
    else:
      return bf
