sig HashCode {}
sig Key {
	hash : HashCode
}
sig Value {}
sig KVPair {
	key: Key,
	val: Value
}

// Assert that if keys are equal, so are their hashvalues
fact EqualHashCode {
	all kv1, kv2 : KVPair | {
		kv1.key = kv2.key implies kv1.key.hash = kv2.key.hash
	}
}


// Assert that if two KVPairs' key and values are equal, they are the same pair
fact EqualKVPair {
	all kv1,kv2 : KVPair | {
		kv1.key = kv2.key and kv1.val = kv2.val implies kv1 = kv2
	}
}
