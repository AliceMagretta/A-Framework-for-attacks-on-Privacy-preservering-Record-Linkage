"""
A pure python implementation of the FP-growth and FPmax algorithm.
"""

import argparse
import collections
import itertools 

__author__ = "Steve Harenberg <harenbergsd@gmail.com>"


def build_tree(itemsets, minsup):
    """ 
    Creates an FPTree for the given itemsets and minimum support.
    
    Parameters
    ----------
    itemsets : list of lists of strings
    minsup : int
        The minimum support threshold.

    Returns 
    -------
    tree : FPTree
    rank : dictionary
        Maps each item (string) to an int to define an ordering.
    """

    # A dictionary with the frequency of all items (number of transactions an
    # item occurs in)
    #
    count = collections.defaultdict(int)
    for item in itertools.chain.from_iterable([itemset for itemset in itemsets]):
        count[item] += 1

    # Sorted (by frequency and alphabetically) list of all frequent single
    # items    
    #
    items = sorted([item for item in count if count[item] >= minsup],
                    key=count.get)

    # A dictionary with items as keys and their position in items as value
    #
    rank = {item:i for i,item in enumerate(items)}

    # Item sets as in input but only containing frequent individual items
    #
    itemsets = [[item for item in itemset if item in rank] for itemset in itemsets]

#    print count
#    print items
#    print rank
#    print itemsets
    
    tree = FPTree(rank)
    for itemset in itemsets:

        # Sort so most frequent item first
        #
        itemset.sort(key=rank.get, reverse=True)

#        print itemset

        tree.insert_itemset(itemset)
 
    return tree, rank


def itemsets_from_file(filename):
    """
    Returns all the itemsets (as a list of lists of strings) from a given file.

    The text file should have each itemset on one line with spaces between individual items, e.g.:
        1 20 13
        2 5 6 123
        1
        2 3
    """
    with open(filename, "r") as fin:
        itemsets = [[item for item in line.strip().split()] for line in fin]
    return itemsets



def frequent_itemsets(itemsets, minsup):
    """ Initiates the fpgrowth algorithm """
    tree = build_tree(itemsets, minsup)[0]
    for itemset in fpgrowth(tree, minsup):
        yield itemset


def maximal_frequent_itemsets(itemsets, minsup):
    """ Initiates the fpmax algorithm """
    tree, rank = build_tree(itemsets, minsup)
    mfit = MFITree(rank)
    for itemset in fpmax(tree, minsup, mfit):
        yield itemset


def fpgrowth(tree, minsup):
    """
    Performs the fpgrowth algorithm on the given tree to yield all frequent itemsets. 

    Parameters
    ----------
    tree : FPTree
    minsup : int

    Yields
    ------
    lists of strings
        Set of items that has occurred in minsup itemsets.
    """
    items = tree.nodes.keys()
    if tree.is_path:
        for i in range(1, len(items)+1):
            for itemset in itertools.combinations(items, i):
                yield tree.cond_items + list(itemset)
    else:
        for item in items:
            yield tree.cond_items + [item]
            cond_tree = tree.conditional_tree(item, minsup)
            for itemset in fpgrowth(cond_tree, minsup):
                yield itemset


def fpmax(tree, minsup, mfit):
    """
    Performs the fpmax algorithm on the given tree to yield all *maximal* frequent itemsets. 

    Parameters
    ----------
    tree : FPTree
    minsup : int
    mfit : MFITree
        Keeps track of what itemsets have already been output.

    Yields
    ------
    lists of strings
        *Maximal* Set of items that has occurred in minsup itemsets.
    """
    items = list(tree.nodes.keys())
    largest_set = sorted(tree.cond_items+items, key=mfit.rank.get)
    if tree.is_path:
        if not mfit.contains(largest_set):
            largest_set.reverse()
            mfit.cache = largest_set
            mfit.insert_itemset(largest_set)
            yield largest_set
    else:
        # Loop over each item in tree creating another conditional tree
        items.sort(key=tree.rank.get)
        for item in items:
            # Check if the tree will produce a subset already produced
            if mfit.contains(largest_set):
                return 
            largest_set.remove(item)
            cond_tree = tree.conditional_tree(item, minsup)
            for mfi in fpmax(cond_tree, minsup, mfit):
                yield mfi



class FPTree(object):
    def __init__(self, rank=None):
        self.root = FPNode(None)
        self.nodes = collections.defaultdict(list)
        self.cond_items = []
        self.rank = rank
    
    
    def conditional_tree(self, cond_item, minsup):
        """ 
        Creates and returns the subtree of self conditioned on cond_item.
        
        Parameters
        ----------
        cond_item : int | str
            Item that the tree (self) will be conditioned on.
        minsup : int 
            Minimum support threshold.

        Returns
        -------
        cond_tree : FPtree
        """
        # Find all path from root node to nodes for item
        branches = []
        count = collections.defaultdict(int)
        for node in self.nodes[cond_item]:
            branch = node.itempath_from_root()
            branches.append(branch)
            for item in branch:
                count[item] += node.count

        # Define new ordering, otherwise deep trees may have combinatorially explosion
        items = [item for item in count if count[item]>=minsup]
        items.sort(key=count.get)
        rank = {item:i for i,item in enumerate(items)}

   #     items = []      # PC 20171108 ****************
   #     counts.clear()  # PC 20171108 ****************
        
        # Create conditional tree
        cond_tree = FPTree(rank)
        for i,branch in enumerate(branches):
            branch = sorted([item for item in branch if item in rank], key=rank.get, reverse=True)
            cond_tree.insert_itemset(branch, self.nodes[cond_item][i].count)
        cond_tree.cond_items = self.cond_items + [cond_item]

  #      branches = []  # PC 20171108 ****************
        
        return cond_tree

    
    def insert_itemset(self, itemset, count=1):
        """ 
        Inserts a list of items into the tree.
        
        Parameters
        ----------
        itemset : list 
            Items that will be inserted into the tree.
        count : int
            The number of occurrences of the itemset.
        """
        if len(itemset) == 0:
            return
        
        # Follow existing path in tree as long as possible
        index = 0
        node = self.root
        for item in itemset:
            if item in node.children:
                child = node.children[item]
                child.count += count
                node = child
                index += 1
            else:
                break
        
        # Insert any remaining items
        for item in itemset[index:]:
            child_node = FPNode(item, count, node)
            self.nodes[item].append(child_node)
            node = child_node
    

    @property
    def is_path(self):
        if len(self.root.children) > 1:
            return False
        for i in self.nodes:
            if len(self.nodes[i])>1 or len(self.nodes[i][0].children)>1:
                return False
        return True




class FPNode(object):
    def __init__(self, item, count=1, parent=None):
        self.item = item    
        self.count = count
        self.parent = parent
        self.children = collections.defaultdict(FPNode)
        
        if parent != None:
            parent.children[item] = self


    def itempath_from_root(self):
        """ Returns the top-down sequence of items from self to (but not including) the root node. """
        path = []
        if self.item == None:
            return path
        
        node = self.parent
        while node.item != None:
            path.append(node.item)
            node = node.parent
        
        path.reverse()
        return path




class MFITree(object):
    def __init__(self, rank):
        self.root = self.Node(None)
        self.nodes = collections.defaultdict(list)
        self.cache = None
        self.rank = rank
    
    
    def insert_itemset(self, itemset, count=1):
        """ 
        Inserts a list of items into the tree.
        
        Parameters
        ----------
        itemset : list 
            Items that will be inserted into the tree.
        count : int
            The number of occurrences of the itemset.
        """
        if len(itemset) == 0:
            return
        
        # Follow existing path in tree as long as possible
        index = 0
        node = self.root
        for item in itemset:
            if item in node.children:
                child = node.children[item]
                node = child
                index += 1
            else:
                break
        
        # Insert any remaining items
        for item in itemset[index:]:
            child_node = self.Node(item, count, node)
            self.nodes[item].append(child_node)
            node = child_node

    
    def contains(self, itemset):
        """
        Checks if this tree contains itemset in one of its branches. 
        The algorithm assumes that  itemset is sorted according to self.rank.
        """
        if self.cache != None:
            i = 0
            for item in reversed(self.cache):
                if self.rank[itemset[i]] < self.rank[item]:
                    break
                if itemset[i] == item:
                    i += 1
                if i == len(itemset):
                    return True
                
        for basenode in self.nodes[itemset[0]]:
            i=0
            node = basenode
            while node.item != None:
                if self.rank[itemset[i]] < self.rank[node.item]:
                    break
                if itemset[i] == node.item:
                    i += 1
                if i == len(itemset):
                    return True
                node = node.parent
        return False
    
    
    class Node(object):
        def __init__(self, item, count=1, parent=None):
            self.item = item    
            self.parent = parent
            self.children = collections.defaultdict(MFITree.Node)
            
            if parent != None:
                parent.children[item] = self
