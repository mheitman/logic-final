open basicDefinitions
open util/sequniv

open util/ordering[ChainingTable]

sig ChainingTable {
	map: HashCode -> (seq KVPair)
}

fact trace {
    all c: ChainingTable - last| {
	one kv : KVPair | {
		put [c, c.next, kv]
    	} or some k: Key | {
		delete [c, c.next, k]
	}
    }
}

fact init {
	// Every HashCode is mapped to an empty list
	no HashCode.(first.map)
}

pred put [c, c': ChainingTable, kv : KVPair] {
	let hc = kv.key.hash | {
	let list = hc.(c.map) | {
		// If the key is already in its hashcode's set its value should be overridden
		kv.key in list.elems.key implies {
			one kv2 : list.elems | {
				kv2.key = kv.key
				let i = list.indsOf[kv2] | {
					hc.(c'.map) = (list.delete[i]).insert[i,kv]
				}
			}
		}
		// Otherwise the KVPair is added
		kv.key not in list.elems.key implies {
			hc.(c'.map) = list.add[kv]
		}
	}
	// All other sequences remain unchanged
	all otherhash : HashCode - hc | {
		otherhash.(c'.map) = otherhash.(c.map)
	}
	}
}

pred delete [c, c': ChainingTable, k: Key] {
	let hc = k.hash | {
	let list = hc.(c.map) | {
		// If the key is already in its hashcode's list its should be removed
		k in list.elems.key implies {
			one kv2 : list.elems | {
				kv2.key = k
				let i = list.indsOf[kv2] | {
					hc.(c'.map) = (list.delete[i])
				}
			}
		}
		// Otherwise the list is unchanged
		k not in list.elems.key implies {
			hc.(c'.map) = list
		}
	}
	// All other sequences remain unchanged
	all otherhash : HashCode - hc | {
		otherhash.(c'.map) = otherhash.(c.map)
	}
	}
}

pred lookup [c: ChainingTable, k: Key, v : Value] {
	let hc = k.hash | {
	let list =hc.(c.map) | {
		// If the key is already in its hashcode's list its should be removed
		k in list.elems.key implies {
			one kv2 : list.elems | {
				kv2.key = k
				kv2.val = v
			}
		}
		// Otherwise, v should be empty/null
		k not in list.elems.key implies {
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
			(kv1 in HashCode.(c.map).elems) and kv2 in (HashCode.(c.map).elems) implies kv1.key != kv2.key
		}
	}
}

pred putOK {
	some disj c1,c2 : ChainingTable | {
		some kv : KVPair | {
			put[c1,c2,kv]
		}
	}
}
run putOK for exactly 2 KVPair, 3 HashCode, exactly 2 Key, exactly 2 Value, 3 ChainingTable

pred deleteOK {
	some disj c1,c2 : ChainingTable | {
		some k : Key | {
			delete[c1,c2,k]
		}
	}
}
run deleteOK for 3 KVPair, 3 HashCode, 3 Key, 3 Value, 3 ChainingTable
