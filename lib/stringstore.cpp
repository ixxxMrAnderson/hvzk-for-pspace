
struct Stringstore {
    Hashmap<Offset<u8>> strings;
    Array_dyn<u8> string_data;
    u64 mask = 1ull << 63;
};

void stringstore_free(Stringstore* store) {
    hashmap_free(&store->strings);
    array_free(&store->string_data);
}

u64 stringstore_get_id(Stringstore* store, Array_t<u8> str) {
    for (u64 adj = 0;; ++adj) {
        u64 hash = (hash_str(str) + adj) | store->mask;
        auto* ptr = hashmap_getcreate(&store->strings, hash, {0, -1});
        if (ptr->size == -1) {
            *ptr = array_append(&store->string_data, str);
            return hash;
        } else {
            auto str_stored = array_suboffset(store->string_data, *ptr);
            if (array_equal(str_stored, str)) return hash;
        }
    }
}

Array_t<u8> stringstore_get_str(Stringstore* store, u64 id) {
    auto offset = hashmap_get(&store->strings, id);
    return array_suboffset(store->string_data, offset);
}
