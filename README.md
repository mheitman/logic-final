# logic-final

We will be analyzing hash tables using Alloy, exploring the two main ways of implementing them-- via chaining (stores a list of elements in each bucket) and open addressing (stores only one element in each bucket). We have modeled both of these concrete implementations and compared their behaviors. We have also concluded that these strategies are valid HashTables implementations because we were able to create abstraction functions for both implementations. 

While modeling, we decided to abstract out the functionality of hash functions because of their great variety and the number limitations of Alloy.

Properties
AbstractHashTable
	We have modeled a general HashTable as simply a set of key-value pairs. We have also modeled put, delete, and lookup as predicates.
	These predicates uphold the expected behavior of a HashTable
		put - is true if the new KVPair is added to the set of data, or its value is updated if the key is already in the table
		delete - is true if all KVPairs with the provided value is removed from the set of data
		lookup - is true if the value of the KVPair with the matching key in the data set matches the expected value
ChainingTable
	We have modeled the Chaining implementation of HashTables using a set of HashCodes to sequences of KVPairs.
	We then implemented more concrete versions of put, delete, and lookup
		put - if there is already a KVPair with the same key in the seq associated with the key's hashcode, it is removed from the sequence and the new KVPair is added in its place.
			if no KVPair with the same key is in the seq, the provided KVPair is simply appended
		delete - if there is a KVPair with the same key in the seq associated with the key's hashcode, it is removed from the sequence
			if no KVPair with the provided key exists in that seq, the table is unchanged.
		lookup - the value of the key is found by first locating the seq corresponding to the Key's hashcode. The seq is then searched for a KVPair with a matching key. The value of this key is then compared to the expected value. If no key could be found, the expected vlaue should be nothing/empty
	
	We were also able to make the following conclusions about this model and thus the Chaining implementation
		if a put occurs followed by a lookup for the key of the KVPair that was just entered, then the value found always matches the value of the KVPair that was just entered.
		if a key is not found in the HashTable, the value found in a lookup for that key is always empty/null
		if a KVPair will only be found in the sequence of the HashTable that corresponds to it's key's hashcode
		no two KVPairs with the same key can be in the HashTable at the same time
		
Comparisons
	Chaining HashTables have no fixed capacity (depends only on the machine using them), while Open Addressing 
	Chaining HashTables require much more overhead (defining and using LinkedLists, etc.) than Open Addressing

Challenges
	When predicates failed or unexpected examples were being displayed, it was very difficult to find the root of the problem.
	Our biggest challenge overall was deciding what was acceptable to abstract out to best benefit the model.
	In Chaining, we spent a long time figuring out how the progression of functions on HashTables. Although out first thought was Events, using them would ruin our abstraction checking.


This project was both interesting to model and informative. We have gained a deeper understanding of this fundamental data structure.