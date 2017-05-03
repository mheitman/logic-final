open basicDefinitions

sig HashTable {
	data: set KVPair
}


// If 2 KVPairs are in the Hashtable, their keys are different
fact NoKVPairsWithSameKey {
	all h : HashTable | {
		all disj kv1,kv2 : KVPair | {
			(kv1 in h.data and kv2 in h.data) implies kv1.key != kv2.key
		}
	}
}

pred init [h: HashTable] {
	no h.data
}

pred put [h, h': HashTable, kv : KVPair] {
	// If the key is already in the HashTable it's value should be overridden
	kv.key in h.data.key implies {
		one kv2 : h.data | {
			kv2.key = kv.key
			h'.data = (h.data - kv2) + kv
		}
	}
	// Otherwise the KVPair is added
	kv.key not in h.data.key implies {
		h'.data = h.data + kv
	}
}

pred delete [h, h': HashTable, k: Key] {
	// If the key is in the HashTable any pairs with that key should be removed
	k in h.data.key implies {
		one kv2 : h.data | {
			kv2.key = k
			h'.data = h.data - kv2
		}
	}
	// Otherwise, the data should remain unchanged
	k not in h.data.key implies {
		h'.data = h.data
	}
}

pred lookup [h: HashTable, k: Key, v : Value] {
	// If the key is in the HashTable its value should equal v
	k in h.data.key implies {
		one kv : h.data | {
			kv.key = k
			kv.val = v
		}
	}
	// Otherwise, v should be empty/null
	k not in h.data.key implies {
		no v
	}
}

// This command should not find any counterexample
PutLookup: check {
	all h, h': HashTable, kv: KVPair, v2: Value | {
		put [h, h', kv] and lookup [h', kv.key, v2] => kv.val = v2
	}
}

