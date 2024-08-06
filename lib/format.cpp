
bool global_format_ignore_units;

s64 _format_split(u64 n, Array_t<u64> muls, Array_t<u64> into) {
    assert(muls.size+1 == into.size);
    array_memset(&into);
    for (s64 i = 0; i < muls.size; ++i) {
        into[i] = n % muls[i];
        n /= muls[i];
        if (n == 0) return i;
    }
    into[muls.size] = n;
    return muls.size;
}

Array_t<u8> format_bytes(u64 bytes, Array_dyn<u8>* into) {
    if (global_format_ignore_units) {
        return array_printf(into, "%llu", bytes);
    }
    u64 _buf[7];
    Array_t<u64> split {_buf, (s64)(sizeof(_buf) / sizeof(_buf[0]))};
    s64 type = _format_split(bytes, {1024, 1024, 1024, 1024, 1024, 1024}, split);
    if (type < 7 and split[type] >= 1000) ++type;
    
    if (type == 0) {
        return array_printf(into, "%llu B", split[0]);
    } else {
        return array_printf(into, "%llu.%02llu %ciB", split[type], split[type-1] * 100/1024, " KMGTPE"[type]);
    }
}

Array_t<u8> format_time(u64 ns, Array_dyn<u8>* into) {
    if (global_format_ignore_units) {
        return array_printf(into, "%llu.%09llu", ns / 1000000000ull, ns % 1000000000ull);
    }
    u64 _buf[8];
    Array_t<u64> split {_buf, (s64)(sizeof(_buf) / sizeof(_buf[0]))};
    s64 type = _format_split(ns, {1000, 1000, 1000, 60, 60, 24, 365}, split);

    switch (type) {
    case 0: return array_printf(into, "%lluns", split[0]);
    case 1: return array_printf(into, "%llu.%02lluus", split[1], split[0] / 10);
    case 2: return array_printf(into, "%llu.%02llums", split[2], split[1] / 10);
    case 3: return array_printf(into, "%llu.%02llus",  split[3], split[2] / 10);
    case 4: return array_printf(into, "%llum%02llu.%02llus",  split[4], split[3], split[2] / 10);
    case 5: return array_printf(into, "%lluh%02llum%02llus",  split[5], split[4], split[3]);
    case 6: return array_printf(into, "%llud%02lluh%02llum",  split[6], split[5], split[4]);
    case 7: return array_printf(into, "%lluy%03llud%02lluh",  split[7], split[6], split[5]);
    default: assert_false;
    }
}

Array_t<u8> format_uint(s64 val, Array_dyn<u8>* into, u8 base=10) {
    static char const alph[] = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    assert(base < sizeof(alph));
    s64 index = into->size;
    while (true) {
        array_push_back(into, alph[val % base]);
        val /= base;
        if (not val) break;
    }
    auto arr = array_subarray(*into, index);
    for (s64 i = 0; 2*i < arr.size-1; ++i)
        simple_swap(&arr[i], &arr[arr.size-1 - i]);
    return arr;
}
Array_t<u8> format_int(s64 val, Array_dyn<u8>* into) {
    if (val < 0) {
        array_push_back(into, '-');
        s64 index = into->size;
        format_uint(-val, into);
        return array_subarray(*into, index);
    } else {
        return format_uint(val, into);
    }
}



