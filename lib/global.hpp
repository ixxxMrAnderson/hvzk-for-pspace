
#pragma once

// I usually do not pay attention to assertions with side-effects, so let us define them here to
// execute the expressions regardless. Also, if the compiler cannot figure out that assert(false)
// means unreachable, so just search-replace all of those with assert_false once going to release.
#ifndef NDEBUG
#include <cassert>
#define assert_false assert(false)
#else
#define assert(x) (void)__builtin_expect(not (x), 0)
#define assert_false __builtin_unreachable()
#endif

#include <cerrno>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
//#include <cstdio>
#include <cctype>

#include <initializer_list>

// Replacements for <algorithm>
template <typename T>
void simple_swap(T* a, T* b) {
    T tmp = *a;
    *a = *b;
    *b = tmp;
}
// template <typename T> T min(T a, T b) { return a < b ? a : b; }
// template <typename T> T max(T a, T b) { return a > b ? a : b; }

// Defer macro. The idea is based on Jonathan Blow's code at https://pastebin.com/3YvWQa5c, although
// the code has been written from scratch.
template <typename T>
struct Deferrer {
    T t;
    Deferrer(T const& t): t{t} {}
    ~Deferrer() { t(); }
};
struct Deferrer_helper {
    template <typename T>
    auto operator+ (T const& t) { return Deferrer<T> {t}; }
};
#define DEFER_NAME1(x, y) x##y
#define DEFER_NAME(x) DEFER_NAME1(_defer, x)
#define defer auto DEFER_NAME(__LINE__) = Deferrer_helper{} + [&]


// Standard integer types
#define DEFINED_SHORT_INTS
using s128 = __int128;
using u128 = unsigned __int128;
using s64 = long long; // gcc and emcc (well, their shipped standard libraries) have different opinions about using long long or just long as 64-bit integer types. But for printf I just want to write one of them. Yay.
using u64 = unsigned long long;
//using s64 = std::int64_t;
//using u64 = std::uint64_t;
using s32 = std::int32_t;
using u32 = std::uint32_t;
using s16 = std::int16_t;
using u16 = std::uint16_t;
using s8 = std::int8_t;
using u8 = std::uint8_t;

// General data structures

// Array_t is just a pointer with a size, and Array_dyn a pointer with a size and capacity. They
// conform to my personal data structure invariants: Can be initialised by zeroing the memory, can
// be copied using memcpy. Obviously, this means that there is no hidden allocation happening in
// here, that is all done by the call-site. Also, no const.

template <typename T_>
struct Array_t {
    using T = T_;
    T* data;
    s64 size;

    constexpr Array_t(T* data = nullptr, s64 size = 0):
        data{data}, size{size} {}
    
    constexpr Array_t(std::initializer_list<T> lst):
        data{(T*)lst.begin()}, size{lst.end() - lst.begin()} {}
    
    T& operator[] (int pos) {
		assert(0 <= pos and pos < size);
		return data[pos];
	}

    // See the E macro below.
    //T& dbg(int pos, int line) {
    //    if (not (0 <= pos and pos < size)) {
    //        printf("line: %d\n", line);
    //        abort();
    //    }
	//	return data[pos];
	//}

    T* begin() { return data; }
	T* end()   { return data + size; }
    T& back()  { assert(size > 0); return data[size-1]; }
};

template <typename T_>
struct Array_dyn: public Array_t<T_> {
    using T = T_;
    bool do_not_reallocate : 1;
    s64 capacity : 63;

    Array_dyn(T* data = nullptr, s64 size = 0, s64 capacity = 0, bool norealloc = false):
        Array_t<T>::Array_t{data, size},
        do_not_reallocate{norealloc},
        capacity{capacity} {}
    
    explicit Array_dyn(Array_t<T> arr) :
        Array_t<T>::Array_t{arr.data, arr.size},
        do_not_reallocate{false},
        capacity{arr.size} {
            capacity ^= (capacity - capacity);
        }
    
    T& operator[] (int pos) {
		assert(0 <= pos and pos < Array_t<T>::size);
		return Array_t<T>::data[pos];
	}

    // See the E macro below.
    //T& dbg (int pos, int line) {
    //    if (0 <= pos and pos < Array_t<T>::size) {
    //        return Array_t<T>::data[pos];
    //    } else {
    //        printf("out of bounds, index %d size %lld, line %d\n", pos, Array_t<T>::size, line);
    //        abort();
    //    }
    //}

    T* begin() const { return (T*)Array_t<T>::data; }
	T* end()   const { return (T*)(Array_t<T>::data + Array_t<T>::size); }
    T& back()  const { assert(Array_t<T>::size > 0); return (T&)(Array_t<T>::data[Array_t<T>::size-1]); }
};




// Experimental: Offset types

template <typename T>
struct Offset {
    s64 beg = 0, size = 0;
};

template <typename T>
Array_t<T> array_suboffset(Array_t<T> arr, Offset<T> off) {
    return array_subarray(arr, off.beg, off.beg + off.size);
}

template <typename T>
Offset<T> array_makeoffset(Array_t<T> arr, Array_t<T> sub) {
    assert(arr.data <= sub.data and sub.end() <= arr.end());
    return {sub.data - arr.data, sub.size};
}
template <typename T>
Offset<T> array_makeoffset(Array_t<T> arr, s64 start, s64 end) {
    assert(0 <= start and start <= end and end <= arr.size);
    return {start, end - start};
}
template <typename T>
Offset<T> array_makeoffset(Array_t<T> arr, s64 start) {
    assert(0 <= start and start <= arr.size);
    return {start, arr.size - start};
}


// This is to help debugging if the stacktraces stop working. (Which, for some reason, they do.) As
// ~90% of runtime errors are out-of-bounds accesses, I often want to know precisely which one. To
// this end, replace arr[pos] by E(arr,pos) in the places you want to monitor.
//#define E(x, y) ((x).dbg((y), __LINE__))


// Allocation. Returns zeroed memory.
template <typename T>
Array_t<T> array_create(s64 size) {
    return {(T*)calloc(sizeof(T), size), size};
}

// Take some bytes from an already existing memory location. Advance p by the number of bytes used.
template <typename T>
Array_t<T> array_create_from(u8** p, s64 size) {
    Array_t<T> result = {(T*)*p, size};
    *p += sizeof(T) * size;
    return result;
}

// For convenience
Array_t<u8> operator "" _arr(const char* str, long unsigned int len) {
    return {(u8*)str, (s64)len};
}
Array_t<u8> array_create_str(const char* str) {
    return {(u8*)str, (s64)strlen(str)};
}


// Free the memory, re-initialise the array.
template <typename T>
void array_free(Array_t<T>* arr) {
    assert(arr);
    free(arr->data);
    arr->data = nullptr;
    arr->size = 0;
}
template <typename T>
void array_free(Array_dyn<T>* arr) {
    assert(arr and not arr->do_not_reallocate);
    free(arr->data);
    arr->data = nullptr;
    arr->size = 0;
    arr->capacity = 0;
}

// Ensure that there is space for at least count elements.
template <typename T>
void array_reserve(Array_dyn<T>* into, s64 count) {
    if (count > into->capacity) {
        assert(not into->do_not_reallocate);
        s64 capacity_new = 2 * into->capacity;
        if (capacity_new < count) {
            capacity_new = count;
        }
        into->data = (T*)realloc(into->data, capacity_new * sizeof(T));
        assert(into->data);
        into->capacity = capacity_new;
        assert(into->data);
    }
}

// Set the array's size to count, reallocate if necessary.
template <typename T>
void array_resize(Array_t<T>* arr, s64 count) {
    if (arr->size == count) return;
    arr->data = (T*)realloc(arr->data, count * sizeof(T));
    if (arr->size < count) {
        memset(arr->data + arr->size, 0, (count - arr->size) * sizeof(T));
    }
    arr->size = count;
}
template <typename T>
void array_resize(Array_dyn<T>* arr, s64 count) {
    array_reserve(arr, count);
    if (arr->size < count) {
        memset(arr->data + arr->size, 0, (count - arr->size) * sizeof(T));
    }
    arr->size = count;
}

// Add element to the end of an array, reallocate if necessary.
template <typename T>
void array_push_back(Array_dyn<T>* into, T elem) {
    array_reserve(into, into->size + 1);
    ++into->size;
    into->data[into->size-1] = elem;
}
template <typename T, typename T_>
void array_push_back(Array_dyn<T>* into, T_ elem) {
    array_reserve(into, into->size + 1);
    ++into->size;
    into->data[into->size-1] = elem;
}

// Insert an element into the array, such that its position is index. Reallocate if necessary.
template <typename T>
void array_insert(Array_dyn<T>* into, s64 index, T elem) {
    assert(into and 0 <= index and index <= into->size);
    array_reserve(into, into->size + 1);
    memmove(into->data + (index+1), into->data + index, (into->size - index) * sizeof(T));
    ++into->size;
    into->data[index] = elem;
}

// Append a number of elements to the array.
template <typename T>
Offset<T> array_append(Array_dyn<T>* into, Array_t<T> data) {
    if (data.size == 0) return {};
    array_reserve(into, into->size + data.size);
    memcpy(into->end(), data.data, data.size * sizeof(T));
    into->size += data.size;
    return {into->size - data.size, data.size};
}
template <typename T>
Offset<T> array_append(Array_dyn<T>* into, std::initializer_list<T> data) {
    array_reserve(into, into->size + data.size());
    memcpy(into->end(), data.begin(), data.size() * sizeof(T));
    into->size += data.size();
    return {(s64)(into->size - data.size()), (s64)data.size()};
}

// Append a number of zero-initialised elements to the array.
template <typename T>
Offset<T> array_append_zero(Array_dyn<T>* into, s64 size) {
    array_reserve(into, into->size + size);
    memset(into->end(), 0, size * sizeof(T));
    into->size += size;
    return {into->size - size, size};
}

// Return an array that represents the sub-range [start, end). start == end is fine (but the result
// will use a nullptr).
template <typename T>
Array_t<T> array_subarray(Array_t<T> arr, s64 start, s64 end) {
    assert(0 <= start and start <= arr.size);
    assert(0 <= end   and end   <= arr.size);
    assert(start <= end);
    if (start == end)
        return {nullptr, 0};
    else
        return {arr.data + start, end - start};
}
template <typename T>
Array_t<T> array_subarray(Array_t<T> arr, s64 start) {
    return array_subarray(arr, start, arr.size);
}

template <typename T>
Array_t<T> array_subindex(Array_t<s64> indices, Array_t<T> data, s64 el) {
    return array_subarray(data, indices[el], indices[el+1]);
}

template <typename... Args>
Array_t<u8> array_printf(Array_dyn<u8>* arr, char const* fmt, Args... args) {
    assert(arr);
    array_reserve(arr, arr->size + snprintf(0, 0, fmt, args...)+1);
    s64 n = snprintf((char*)arr->end(), arr->capacity - arr->size, fmt, args...);
    arr->size += n;
    return array_subarray(*arr, arr->size-n);
}
Array_t<u8> array_printf(Array_dyn<u8>* arr, char const* str) {
    assert(arr);
    s64 n = strlen(str);
    array_append(arr, {(u8*)str, n + 1});
    --arr->size;
    return array_subarray(*arr, arr->size-n);
}


template <typename... Args>
void array_printa(Array_dyn<u8>* arr, char const* fmt, Args... args) {
    s64 count = 0;
    for (s64 i = 0; fmt[i]; ++i) {
        count += fmt[i] == '%';
    }
    assert(sizeof...(args) == count);
    
    auto args_arr = {args...};

    s64 j = 0;
    for (s64 i = 0; fmt[i]; ++i) {
        if (fmt[i] == '%') {
            array_append(arr, args_arr.begin()[j++]);
        } else {
            array_push_back(arr, fmt[i]);
        }
    }
}

template <typename T>
bool array_equal(Array_t<T> a, Array_t<T> b) {
    return a.size == b.size and memcmp(a.data, b.data, a.size * sizeof(T)) == 0;
}
bool array_equal_str(Array_t<u8> a, char const* str) {
    return a.size == (s64)strlen(str) and memcmp(a.data, str, a.size) == 0;
}
template <typename T>
int array_cmp(Array_t<T> a, Array_t<T> b) {
    s64 size = min(a.size, b.size);
    s64 cmp = memcmp(a.data, b.data, a.size * sizeof(T));
    return cmp ? cmp : (a.size > b.size) - (a.size < b.size);
}

template <typename T> void array_swap(Array_t  <T>* a, Array_t  <T>* b) { simple_swap(a, b); }
template <typename T> void array_swap(Array_dyn<T>* a, Array_dyn<T>* b) { simple_swap(a, b); }
template <typename T>
void array_swap(Array_t <T>* a, Array_dyn<T>* b) {
    simple_swap(&a->data, &b->data);
    simple_swap(&a->size, &b->size);
    b->capacity = b->size;
}
template <typename T> void array_swap(Array_dyn<T>* a, Array_t<T>* b) { array_swap(b, a); };

// These two functions implement a bitset.
void bitset_set(Array_t<u64>* bitset, u64 bit, u8 val) {
    u64 index  = bit / 64;
    u64 offset = bit % 64;
    (*bitset)[index] ^= (((*bitset)[index] >> offset & 1) ^ val) << offset;
}
bool bitset_get(Array_t<u64> bitset, u64 bit) {
    u64 index  = bit / 64;
    u64 offset = bit % 64;
    return bitset[index] >> offset & 1;
}

template <typename T>
void array_memcpy(Array_t<T>* arr, Array_t<T> from) {
    assert(arr->size == from.size);
    memcpy(arr->data, from.data, arr->size * sizeof(T));
}
template <typename T>
void array_memmove(Array_t<T>* arr, Array_t<T> from) {
    assert(arr->size == from.size);
    memmove(arr->data, from.data, arr->size * sizeof(T));
}
template <typename T>
void array_memset(Array_t<T>* arr, u8 val=0) {
    memset(arr->data, val, arr->size * sizeof(T));
}
template <typename T>
void array_pop_front(Array_dyn<T>* arr, s64 n) {
    assert(n <= arr->size);
    memmove(arr->data, arr->data+n, (arr->size-n) * sizeof(T));
    arr->size -= n;
}
template <typename T>
void array_prepend_zero(Array_dyn<T>* arr, s64 n) {
    array_reserve(arr, arr->size + n);
    memmove(arr->data + n, arr->data, arr->size * sizeof(T));
    memset(arr->data, 0, n * sizeof(T));
    arr->size += n;
}

// Decode the first unicode codepoint in buf, return the number of bytes it is long. The result
// value of the codepoint is written into c_out .
s64 utf8_decode(Array_t<u8> buf, u32* c_out = nullptr, bool* err = nullptr) {
    u32 c = buf[0];
    s64 c_bytes = c&128 ? c&64 ? c&32 ? c&16 ? 4 : 3 : 2 : -1 : 1;
    if (buf.size < c_bytes) c_bytes = -1;
    
    if (c_bytes == 1) {
        // nothing
    } else if (c_bytes == 2) {
        c = (buf[0]&0x1f) << 6 | (buf[1]&0x3f);
    } else if (c_bytes == 3) {
        c = (buf[0]&0xf) << 12 | (buf[1]&0x3f) << 6 | (buf[2]&0x3f);
    } else if (c_bytes == 4) {
        c = (buf[0]&0x7) << 18 | (buf[1]&0x3f) << 12 | (buf[2]&0x3f) << 6 | (buf[3]&0x3f);
    } else {
        if (err) *err = true;
        else assert_false;
        c = '?';
        c_bytes = 1;
    }
    if (c_out) *c_out = c;
    return c_bytes;
}

template <typename T, typename Func>
void array_sort_insertion(Array_t<T>* arr, Func&& key) {
    for (s64 i = 1; i < arr->size; ++i) {
        T i_el = (*arr)[i];
        auto i_key = key(i_el);
        
        s64 target = i;
        while (target > 0 and key((*arr)[target-1]) > i_key) --target;
        
        for (s64 j = i; j > target; --j) {
            (*arr)[j] = (*arr)[j-1];
        }
        (*arr)[target] = i_el;
    }
}

// key must return integers in the range [0, key_upper)
template <typename T, typename Func>
void array_sort_counting(Array_t<T>* arr, Func&& key, s64 key_upper) {
    Array_t<s64> counts = array_create<s64>(key_upper);
    Array_t<T> temp = array_create<T>(arr->size);
    defer {
        array_free(&counts);
        array_free(&temp);
    };
    
    for (T i: *arr) ++counts[key(i)];

    s64 sum = 0;
    for (s64 i = 0; i < key_upper; ++i) {
        s64 tmp = counts[i]; counts[i] = sum; sum += tmp;
    }
    
    for (T i: *arr) temp[counts[key(i)]++] = i;
    array_memcpy(arr, temp);
}

template <typename T>
void array_reverse(Array_t<T>* arr) {
    for (s64 i = 0; 2*i < arr->size-1; ++i) {
        simple_swap(&(*arr)[i], &(*arr)[arr->size-1 - i]);
    }
}
