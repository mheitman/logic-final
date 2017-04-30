open basicDefinitions
open util/sequniv

open util/ordering[ChainingTable]

sig Chain {
	elements: seq KVPair
}
sig ChainingTable {
	map: HashCode one -> Chain
}

fact trace {
    all c: ChainingTable - last| {
	one kv : KVPair | {
		put [c, c.next, kv]
    	} or one k: Key | {
		delete [c, c.next, k]
	}
    }
}

fact init {
	// Every HashCode is mapped to an empty list
	no HashCode.(first.map).elements
}

pred put [c, c': ChainingTable, kv : KVPair] {
	let hc = kv.key.hash | {
	let list =hc.(c.map).elements | {
		// If the key is already in its hashcode's list its value should be overridden
		kv.key in Int.list.key implies {
			one kv2 : Int.list | {
				let i = list.indsOf[kv2] | {
					hc.(c'.map).elements = (list.delete[i]).insert[i, kv]
				}
			}
		}
		// Otherwise the KVPair is added
		kv.key not in Int.list.key implies {
			hc.(c'.map).elements = list.add[kv]
		}
	}
	}
}

pred delete [c, c': ChainingTable, k: Key] {
	let hc = k.hash | {
	let list =hc.(c.map).elements | {
		// If the key is already in its hashcode's list its should be removed
		k in Int.list.key implies {
			one kv2 : Int.list | {
				let i = list.indsOf[kv2] | {
					hc.(c'.map).elements = list.delete[i]
				}
			}
		}
		// Otherwise the list is unchanged
		k not in Int.list.key implies {
			hc.(c'.map).elements = list
		}
	}
	}
}

pred lookup [c: ChainingTable, k: Key, v : Value] {
	let hc = k.hash | {
	let list =hc.(c.map).elements | {
		// If the key is already in its hashcode's list its should be removed
		k in Int.list.key implies {
			one kv2 : Int.list | {
				kv2.val = v
			}
		}
		// Otherwise, v should be empty/null
		k not in Int.list.key implies {
			no v
		}
	}
	}
}

// This command should not find any counterexample
PutLookup: check {
	all c, c': ChainingTable, kv: KVPair, v2: Value | {
		put [c, c', kv] and lookup [c', kv.key, v2] => kv.val = v2
	}
}

NoKVPairsWithSameKey: check {
	all c : ChainingTable | {
		all disj kv1,kv2 : KVPair | {
			(kv1 in Int.(HashCode.(c.map).elements) and kv2 in Int.(HashCode.(c.map).elements)) implies kv1.key != kv2.key
		}
	}
}

/*
pred putOK {
	some disj h1,h2 : HashTable | {
		some kv : KVPair | {
			put[h1,h2,kv]
		}
	}
}
run putOK for exactly 2 KVPair, exactly 2 HashCode, exactly 1 Key, exactly 2 Value, exactly 2 HashTable

pred deleteOK {
	some disj h1,h2 : HashTable | {
		some k : Key | {
			delete[h1,h2,k]
		}
	}
}
run deleteOK for exactly 3 KVPair, exactly 2 HashCode, exactly 2 Key, exactly 3 Value, exactly 2 HashTable
*/
