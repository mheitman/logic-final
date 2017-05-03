open basicDefinitions
open OpenAddressing as OA
open abstractHashTable as absHT

fun alpha [oat: OATable]: HashTable {
	{h: HashTable | {
		h.data = HashCode.(oat.map).elems
	}}
}

// This check should not produce a counterexample
PutOK: check {
	all oat: OATable, kv : KVPair, h,h': HashTable |
		oat/put [c, c', kv] and h = alpha [oat]  and h' = alpha [oat'] => absHT/put [h, h', kv]
}

// This check should not produce a counterexample
DeleteOK: check {
	all oat,oat': ChainingTable, k : Key, h,h': HashTable |
		oat/delete [c, c', k] and h = alpha [oat]  and h' = alpha [oat'] => absHT/delete [h, h', k]
}

// This check should not produce a counterexample
LookupOK: check {
	all oat: OATable, k : Key, v : Value, h: HashTable |
		oat/lookup [oat, k, v] and h = alpha [oat] => absHT/lookup [h, k, v]
}
