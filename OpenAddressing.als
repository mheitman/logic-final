open basicDefinitions
open util/sequniv
--open util/ordering[HashCode]

abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}
/*sig OATable {
	map: HashCode one -> OAPair,
	ordering: seq HashCode,
	empty: seq HashCode,
	capacity: Int
}*/

sig OATable {
	map: Int one -> OAPair,
	hashFunction: seq HashCode,
	empty: seq Int,
	capacity: Int
}

--fact { some OATable.map2 }

sig OAPair extends KVPair {
	isDeleted: Bool
}{
	isDeleted = False
}

pred init [oat: OATable] {
	oat.capacity > 0
	#HashCode = oat.capacity
	all hc : HashCode | {
		no hc.(oat.map)
		hc in (oat.empty).elems
		hc in (oat.hashFunction).elems
	}
}

fun probe [oat: OATable, hc: HashCode]: seq HashCode {
	let ind = oat.empty.idxOf [hc] | 
		oat.empty.subseq [ind, oat.empty.lastIdx]
}

pred put [oat, oat': OATable, oa : OAPair] {
--	let mapp = Int.(oat.map) | {
	let hc = oa.key.hash | {
		oa.key in HashCode.(oat.map).key => {
			let newhc = oat.map.oa | newhc.(oat'.map) = oa
			--oat'.map
		} else {
			let avail = probe [oat, hc] | {
				some avail => {
					oat'.empty = 
						oat.empty.delete [oat.empty.idxOf [avail.first]]
					oat'.map = oat.map + (avail.first -> oa)
				} else {
					let more = probe [oat, oat.empty.first] | {
						some more => {
							oat'.empty = 
								oat.empty.delete [oat.empty.idxOf [more.first]]
							oat'.map = oat.map + (more.first -> oa)
						} else {
							oat' = oat and no oa
						}
					}
				}
			}
		}
	}
--	}
}

/*pred delete [oat, oat': OATable, k: Key] {
	let ind = probe2 [oat, k.hash] |
		
}*/

run {} for exactly 2 KVPair, 2 OAPair, exactly 2 HashCode, exactly 1 Key, exactly 2 Value, exactly 1 OATable

-- CHECK THERE'S SOMETHING BEFORE PROBING
fun probe2 [oat: OATable, hc: HashCode]: HashCode {
	let ind = oat.empty.idxOf [hc] | 
		let avail = oat.empty.subseq [ind, oat.empty.lastIdx] |
			some avail => avail.first
			else probe2 [oat, oat.empty.first]
}

pred lookup [c: OATable, k: Key, v : Value] {}

