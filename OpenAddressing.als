open basicDefinitions
open util/sequniv

open util/ordering[OATable]

sig OATable {
	map: Int lone -> KVPair,
	hashFunction: seq HashCode,
	empty: set Int,
	capacity: Int
}

fact trace {
    all oat: OATable - last| {
	one kv : KVPair | {
		put [oat, oat.next, kv]
    	} or some k: Key | {
		delete [oat, oat.next, k]
	}
    }
}

fact init {
	first.capacity > 0
	#(first.hashFunction.elems) = first.capacity
	#first.empty = first.capacity
	no Int.(first.map)
	first.empty = first.hashFunction.inds
}

pred put [oat, oat': OATable, kv: KVPair] {
	no oat.empty => {
		no kv 
		oat'.map = oat.map
		oat'.empty = oat.empty
		oat'.hashFunction = oat.hashFunction
		oat'.capacity = oat.capacity
	} else {
		kv.key.hash in oat.hashFunction.elems
		let ind = oat.hashFunction.idxOf [kv.key.hash] {
			// Already in map, just needs to be updated
			kv.key in Int.(oat.map).key => {
				one kv2: Int.(oat.map) | {
				kv2.key = kv.key
				let ind2 = oat.map.kv2 {
					oat'.map = oat.map - (ind2 -> KVPair) + (ind2 -> kv)
					oat'.empty = oat.empty
					oat'.hashFunction = oat.hashFunction
					oat'.capacity = oat.capacity
				}
			}
			} else {
				// Insert into map
				let loc = probe[oat, ind] | {
					oat'.map = oat.map + loc -> kv
					oat'.empty = oat.empty - loc
					oat'.hashFunction = oat.hashFunction
					oat'.capacity = oat.capacity
				}
			}
		}
	}
}

pred delete [oat, oat': OATable, k: Key] {
	k in Int.(oat.map).key => {
		one kv: Int.(oat.map) | {
			kv.key = k
			let loc =  oat.map.kv | {
				oat'.map = oat.map - (loc -> loc.(oat.map))
				oat'.empty = oat.empty + loc
				oat'.hashFunction = oat.hashFunction
				oat'.capacity = oat.capacity
			}
		}
	} else {
		no k
		oat'.map = oat.map
		oat'.empty = oat.empty
		oat'.hashFunction = oat.hashFunction
		oat'.capacity = oat.capacity
	}
}

pred lookup [oat: OATable, k: Key, v : Value] {
	k in Int.(oat.map).key => {
		one kv: Int.(oat.map) | {
			kv.key = k
			kv.val = v
		}
	} else no v
}

// Finds the next available index to insert at
fun probe [oat: OATable, idx: Int]: Int {
	let avail = {n: oat.empty | n >= idx} | {
		some avail => min [avail]
		else {
			min [{n: oat.empty | n < idx}]
		}
	}
}

run {} for 2 KVPair, exactly 2 HashCode, exactly 2 Key, exactly 2 Value, 2 OATable




