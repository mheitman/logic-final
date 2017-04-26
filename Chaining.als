module abstractHashTable [Key, Value]
open util/sequniv

sig KVPair {
	key: Key,
	val: Value
}{
	one key
	one val
}

sig Chain {
	elements: seq KVPair
}
sig ChainingSystem {
	map: HashCode one -> Chain
}

pred init [c: ChainingSystem] {
	// Every HashCode is mapped to an empty list?
	all hc : HashCode | {
		no hc.map.elements
	}
}

pred put [c, c': ChainingSystem, k: Key, v : Value] {
	let hc = k.hash | {
		one kv : KVPair | {
			kv.key = k
			kv.val = v
			no elems : hc.c.map.elems | {
				elems.key = k
			} implies hc.c'.map =  hc.c.map.append[kv]
			one elems : hc.c.map.elems | {
				elems.key = k
			} implies hc.c'.map =  hc.c.map.append[kv] // FIX????
		}
	}
}

// ???????
fun update[sq1, Chain, kv : KVPair, v1 : Value] {
	let removed = s.delete[s.indsOf[kv]] | {
		one kv : KVPair | {
			removed.append
		}
	}
	removed
}

// ???????
pred delete [h, h': HashTable, k: Key] {
	// Any pair with the provided key should be removed
	let currlist = hc.c.map.elems
	hc.c'.map.elems.key = hc.c.map.elems.key - k
	}

// ???????
pred lookup [h: HashTable, k: Key, v : Value] {
	let v' = h.data [k] | some v' implies v = v'
	}

// Check properties???

