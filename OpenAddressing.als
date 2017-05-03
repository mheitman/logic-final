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
	some kv : KVPair | {
		put [oat, oat.next, kv]
    	} or some kv: KVPair | {
		delete [oat, oat.next, kv]
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
			-- Already in map, just needs to be updated
			kv.key in Int.(oat.map).key => {
				let ind2 = oat.map.kv {
					oat'.map - (ind2 -> ind2.(oat.map)) = oat.map - (ind2 -> ind2.(oat.map))
					ind2 -> kv in oat'.map
					oat'.empty = oat.empty
					oat'.hashFunction = oat.hashFunction
					oat'.capacity = oat.capacity
				}
			} else {
				-- Insert into map
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

pred delete [oat, oat': OATable, kv: KVPair] {
	kv.key in Int.(oat.map).key => {
		let loc =  oat.map.kv | {
			oat'.map = oat.map - (loc -> loc.(oat.map))
			oat'.empty = oat.empty + loc
			oat'.hashFunction = oat.hashFunction
			oat'.capacity = oat.capacity
		}
	} else {
		no kv
		oat'.map = oat.map
		oat'.empty = oat.empty
		oat'.hashFunction = oat.hashFunction
		oat'.capacity = oat.capacity
	}
}

fun probe [oat: OATable, idx: Int]: Int {
	let avail = {n: oat.empty | n >= idx} | {
		some avail => min [avail]
		else {
			min [{n: oat.empty | n < idx}]
		}
	}
}

run {} for 2 KVPair, exactly 2 HashCode, exactly 2 Key, exactly 2 Value, 2 OATable




