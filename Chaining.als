open basicDefinitions
open util/sequniv

sig Chain {
	elements: seq KVPair
}
sig ChainingSystem {
	map: HashCode one -> Chain
}

/*
NOT WORKING BECAUSE HASH TABLE STARTS WITH VALUES?
SWITCH TO USING EVENTS??
*/

pred init [c: ChainingSystem] {
	// Every HashCode is mapped to an empty list
	all hc : HashCode | {
		no hc.(c.map).elements
	}
}

pred put [c, c': ChainingSystem, kv : KVPair] {
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
			hc.(c'.map).elements = list.delete[list.indsOf[kv]]
		}
	}
	}
}

pred delete [c, c': ChainingSystem, k: Key] {
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

pred lookup [c: ChainingSystem, k: Key, v : Value] {
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
	all c, c': ChainingSystem, kv: KVPair, v2: Value | {
		put [c, c', kv] and lookup [c', kv.key, v2] => kv.val = v2
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
