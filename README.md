# logic-final

We will be analyzing hash tables using Alloy, exploring the two main ways of implementing them-- via chaining (stores a list of elements in each bucket) and open addressing (stores only one element in each bucket). We have modeled both of these concrete implementations and compared their behaviors. We have also hoped to conclude that these strategies are valid HashTables implementations because we were able to create abstraction functions for both implementations. We could make this affirmation about Chaining and OpenAddressing; however, because of some concerns for OpenAddressing, described below, we feel less sure about making the same conclusions for this strategy.

While modeling, we decided to abstract out the functionality of hash functions because of their great variety and the number limitations of Alloy.
Additionally, we chose to represent HashCodes as a sig, rather than Integers because of the limitations of Alloy.

For both models, we put an ordering on the Tables so that we could ensure that values in the tables were only changed under the proper parameters.

Properties
AbstractHashTable
	We have modeled a general HashTable as simply a set of key-value pairs. We have also modeled put, delete, and lookup as predicates.
	These predicates uphold the expected behavior of a HashTable
		put - is true if the new KVPair is added to the set of data, or its value is updated if the key is already in the table
		delete - is true if all KVPairs with the provided value is removed from the set of data
		lookup - is true if the value of the KVPair with the matching key in the data set matches the expected value
ChainingTable
	We have modeled the Chaining implementation of HashTables using a set of HashCodes to sequences of KVPairs.
	Because of the limitations of Alloy with regards to Integers, for the purpose of this model we decided to abstract out ensuring that an entered KVPair hits a bucket. Typically, one would mod the HashCode by the size of the table. We instead just assume that any key's hashcode is a valid bucket, and adjust its sequence accordingly.
	We then implemented more concrete versions of put, delete, and lookup
		put - if there is already a KVPair with the same key in the seq associated with the key's hashcode, it is removed from the sequence and the new KVPair is added in its place.
			if no KVPair with the same key is in the seq, the provided KVPair is simply appended
		delete - if there is a KVPair with the same key in the seq associated with the key's hashcode, it is removed from the sequence
			if no KVPair with the provided key exists in that seq, the table is unchanged.
		lookup - the value of the key is found by first locating the seq corresponding to the Key's hashcode. The seq is then searched for a KVPair with a matching key. The value of this key is then compared to the expected value. If no key could be found, the expected value should be nothing/empty
	We were also able to make the following conclusions about this model and thus the Chaining implementation
		if a put occurs followed by a lookup for the key of the KVPair that was just entered, then the value found always matches the value of the KVPair that was just entered.
		if a key is not found in the HashTable, the value found in a lookup for that key is always empty/null
		if a KVPair will only be found in the sequence of the HashTable that corresponds to it's key's hashcode
		no two KVPairs with the same key can be in the HashTable at the same time
Open Addressing
	We have modeled the Open Addressing implementation of the HashTables using an ordered sig with the following properties:
		map - the set of data, models as a set of indices to KVPairs
		hashFunction - not a "hashFunction", used to find the smallest available index for insertion (map HashCodes to their proper indices in the "array")
		empty - a set of available indices to insert a value
		capacity - indicates the number of KVPairs the table can hold, because in open addressing the number of elements is restricted to the size of the table)
    We did make a probe function that essentially returned what the result of actually probing would be-- we did not use isDeleted flags or nulls, as they would require loops, but this seemed like a good option in terms of modeling what doing the actual process would return.
	Because while loops are not possible in Alloy, our model was constrained far more than we originally anticipated; therefore, our implementations of lookup and delete do not very closely resemble the steps made by a true implementation. 
	We can also conclude that Open Addressing is a valid strategy for implementing HashTables.
	
Comparisons
	Chaining HashTables have no fixed capacity (depends only on the machine using them), while Open Addressing did. We will elaborate more during the presentation. One of the more significant differences mainly came in the form of what was possible to model in Alloy-- again, since Alloy does not support while loops, which are pretty necessary in a search for OpenAddressing, it was difficult to abstract out this functionality. 
    Chaining HashTables require much more overhead (defining and using LinkedLists, etc.) than Open Addressing

Challenges
	When predicates failed or unexpected examples were being displayed, it was very difficult to find the root of the problem.
	One challenge we continually faced was whether it was acceptable to abstract out specific functionality to best benefit the model.
	Our biggest challenge overall was with OpenAddressing was attempting to closely model the actual algorithm. 
	In Chaining, we spent a long time figuring out how the progression of functions on HashTables. Although out first thought was Events, using them would ruin our abstraction checking.

This project was both interesting to model and informative. We have gained a deeper understanding of this fundamental data structure. Through this model, we were able to confirm and support many of the known properties and behaviors of HashTable implementations.
