open basicDefinitions
open OpenAddressing as OA
open abstractHashTable as absHT

fun alpha [oat: OATable]: HashTable {
	{h: HashTable | {
		h.data = Int.(oat.map)
	}}
}

// This check should not produce a counterexample
PutOK: check {
	all oat, oat': OATable, kv : KVPair, h,h': HashTable |
		OA/put [oat, oat', kv] and h = alpha [oat]  and h' = alpha [oat'] => absHT/put [h, h', kv]
}

// This check should not produce a counterexample
DeleteOK: check {
	all oat, oat': OATable, k : Key, h,h': HashTable |
		OA/delete [oat, oat', k] and h = alpha [oat]  and h' = alpha [oat'] => absHT/delete [h, h', k]
}

// This check should not produce a counterexample
LookupOK: check {
	all oat: OATable, k : Key, v : Value, h: HashTable |
		OA/lookup [oat, k, v] and h = alpha [oat] => absHT/lookup [h, k, v]
}
