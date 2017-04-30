open basicDefinitions
open Chaining as chaining
open abstractHashTable as absHT

fun alpha [c: ChainingTable]: HashTable {
	{h: HashTable | {
		h.data = Int.(HashCode.(c.map).elements)
	}}
}

// This check should not produce a counterexample
PutOK: check {
	all c,c': ChainingTable, kv : KVPair, h,h': HashTable |
		chaining/put [c, c', kv] and h = alpha [c]  and h' = alpha [c'] => absHT/put [h, h', kv]
}

// This check should not produce a counterexample
DeleteOK: check {
	all c,c': ChainingTable, k : Key, h,h': HashTable |
		chaining/delete [c, c', k] and h = alpha [c]  and h' = alpha [c'] => absHT/delete [h, h', k]
}

// This check should not produce a counterexample
LookupOK: check {
	all c: ChainingTable, k : Key, v : Value, h: HashTable |
		chaining/lookup [c, k, v] and h = alpha [c] => absHT/lookup [h, k, v]
}
