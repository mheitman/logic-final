sig HashCode {}
sig Key {
	hash : HashCode
}{
	one hash
}
sig Value {}

sig HashTable {
	// Each value has one key, represents all the KV Pairs in the table
	data: Key one -> Value
}

// Assert that if keys are equal, so are their hashvalues???
fact EqualHashCode{
	all k1,k2 : Key | {
		kv1.k = kv2.k implies kv1.hash = kv2.hash
	}
}

pred init [h: HashTable] {
	no h.data
}

pred put [h, h': HashTable, k: Key, v: Value] {
	h'.data = h.data ++ k -> v
}

pred delete [h, h': HashTable, k: Key] {
	// Any pair with the provided key should be removed
	h'.data = h.data - k -> Value
}

//????
//fun lookup [h: HashTable, k: Key, v : Value] {
//	let v' = h.data [k] | some v' implies v = v'
//	}

// This command should not find any counterexample
//PutLookup: check {
//	all h, h': HashTable, k: Key, v1, v2: Value |
//		put [h, h', k, v1] and lookup [h', k, v2] => v1 = v2
//	}
