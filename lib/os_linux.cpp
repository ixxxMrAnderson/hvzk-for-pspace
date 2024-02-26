
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

namespace Os_codes {

enum Open_flags: u64 {
    OPEN_READ  = 1,
    OPEN_WRITE = 2,
    OPEN_CREATE = 4,
    OPEN_APPEND = 8,
    OPEN_TRUNCATE = 16
};

enum General_code: s64 {
    SUCCESS = 0,
    ERROR = 1,
    SKIPPED = -1, // Skipped due to existing error code
};
    
enum Write_all_code: s64 {
    WRITE_ERROR = 101,
    WRITE_EOF = 102,
    WRITE_WOULDBLOCK = 103
};

enum Read_all_code: s64 {
    READ_ERROR = 201,
    READ_EOF = 202,
    READ_WOULDBLOCK = 203
};

enum Seek_whence: u8 {
    P_SEEK_SET,
    P_SEEK_CUR,
    P_SEEK_END
};

enum Access_flags: u8 {
    ACCESS_EXISTS = 1,
    ACCESS_READ = 2,
    ACCESS_WRITE = 4,
    ACCESS_EXECUTE = 8
};

};

struct Status {
    s64 code = 0;
    Array_dyn<u8> error_buf;

    bool good() const { return code == 0; }
    bool bad()  const { return code != 0; }
};

// Only necessary to call if an error occurred
void os_status_free(Status* status) {
    array_free(&status->error_buf);
}

struct Os_data {
    bool initialized;
    timespec t_start; // Time of program start
    Status status;
};

Os_data global_os;

void os_init() {
    clock_gettime(CLOCK_MONOTONIC_RAW, &global_os.t_start);
    global_os.initialized = true;
}

u64 os_now() {
    assert(global_os.initialized);
    timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (ts.tv_sec - global_os.t_start.tv_sec) * 1000000000ull
        + (ts.tv_nsec - global_os.t_start.tv_nsec);
}

bool os_status_initp(Status** statusp) {
    if (*statusp == nullptr) *statusp = &global_os.status;
    return (**statusp).bad();
}

template <typename... T>
void os_error_printf(Status* status, s64 code, char const* fmt, T... args) {
    assert(fmt);
    status->code = code;
    if (fmt && fmt[0] == '$') {
        array_printf(&status->error_buf, "%s\n", strerror(errno));
        ++fmt;
        fmt += fmt[0] == ' ';
    }
    array_printf(&status->error_buf, fmt, args...);
}

int os_open(Array_t<u8> path, u64 flags, u32 mode=0, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return -1;
    
    using namespace Os_codes;
    assert(not (flags & ~(OPEN_READ | OPEN_WRITE | OPEN_CREATE | OPEN_APPEND | OPEN_TRUNCATE)));
    
    char* tmp = (char*)alloca(path.size + 1);
    memcpy(tmp, path.data, path.size);
    tmp[path.size] = 0;

    int f = 0;
    u64 flagsrw = flags & (OPEN_READ | OPEN_WRITE);
    f |= flagsrw == (OPEN_READ | OPEN_WRITE) ? O_RDWR : 0;
    f |= flagsrw == OPEN_READ ? O_RDONLY : 0;
    f |= flagsrw == OPEN_WRITE ? O_WRONLY : 0;
    assert(flagsrw);
    
    f |= flags & OPEN_CREATE ? O_CREAT : 0;
    f |= flags & OPEN_APPEND ? O_APPEND : 0;
    f |= flags & OPEN_TRUNCATE ? O_TRUNC : 0;
    
    int fd = open(tmp, f, (mode_t)mode);

    if (fd == -1) {
        os_error_printf(status, ERROR, "$ while opening file '%s'\n", tmp);
        return -1;
    }

    return fd;
}
void os_close(int fd, Status* status = nullptr) {
    if (os_status_initp(&status)) return;
    int code = close(fd);
    if (code) os_error_printf(status, 221206101, "$ while calling close()\n");
}

bool os_read(int fd, Array_dyn<u8>* buf, s64 n, Status* status = nullptr) {
    if (os_status_initp(&status)) return false;
    
    array_reserve(buf, buf->size + n);
        
    s64 bytes_read = read(fd, buf->data + buf->size, n);
    if (bytes_read == -1) {
        bool wouldblock = errno == EWOULDBLOCK || errno == EAGAIN;
        s64 code = wouldblock ? Os_codes::READ_WOULDBLOCK : Os_codes::READ_ERROR;
        os_error_printf(status, code, "$ while calling read()");
        return false;
    }
    buf->size += bytes_read;

    return bytes_read > 0;
}

void os_read_fixed(int fd, Array_t<u8> buf, Status* status = nullptr) {
    if (os_status_initp(&status)) return;
    
    while (buf.size > 0) {
        s64 bytes_read = read(fd, buf.data, buf.size);
        if (bytes_read == -1) {
            s64 code = errno == EWOULDBLOCK or errno == EAGAIN ? Os_codes::READ_WOULDBLOCK : Os_codes::READ_ERROR;
            return os_error_printf(status, code, "$ while calling read()");
        }
        if (bytes_read == 0) {
            /* Note that buf.size > 0 due to loop condition */
            return os_error_printf(status, Os_codes::READ_EOF, "unexpected eof (%ld bytes left to read)\n", (long)buf.size);
        }
        buf = array_subarray(buf, bytes_read, buf.size);
    }
}

void os_write_fixed(int fd, Array_t<u8> buf, Status* status = nullptr) {
    if (os_status_initp(&status)) return;
    
    while (buf.size > 0) {
        s64 bytes_written = write(fd, buf.data, buf.size);
        if (bytes_written == -1) {
            if (errno == EPIPE) {
                return os_error_printf(status, Os_codes::WRITE_EOF, "eof while writing bytes (%ld left to write)\n", (long)buf.size);
            } else {
                s64 code = errno == EWOULDBLOCK or errno == EAGAIN ? Os_codes::WRITE_WOULDBLOCK : Os_codes::WRITE_ERROR;
                return os_error_printf(status, code, "$ while calling write()");
            }
        }
        assert(bytes_written > 0);
        buf = array_subarray(buf, bytes_written, buf.size);
    }
    return;
}


s64 os_seek(int fd, u64 offset, u8 whence, Status* status = nullptr) {
    if (os_status_initp(&status)) return 0;
    
    int w = SEEK_SET;
    switch (whence) {
    case Os_codes::P_SEEK_SET: w = SEEK_SET; break;
    case Os_codes::P_SEEK_CUR: w = SEEK_CUR; break;
    case Os_codes::P_SEEK_END: w = SEEK_END; break;
    default: assert_false;
    }
    
    off_t r = lseek(fd, offset, w);
    if (r == (off_t)-1) {
        os_error_printf(status, 221206001, "$ while calling lseek()");
        return -1;
    }
    s64 rr = r;
    if (rr != r) {
        os_error_printf(status, 221206002, "seek offset does not fit into an s64");
        return -1;
    }
    
    return r;
}

Array_t<u8> os_read_file(Array_t<u8> path, Status* status = nullptr) {
    if (os_status_initp(&status)) return {};

    int fd = os_open(path, Os_codes::OPEN_READ, 0, status);
    s64 length = os_seek(fd, 0, Os_codes::P_SEEK_END, status);
    os_seek(fd, 0, Os_codes::P_SEEK_SET, status);
    
    if (status->bad()) return {};

    Array_t<u8> result = array_create<u8>((s64)length);
    os_read_fixed(fd, result, status);
    os_close(fd, status);
    
    return result;
}
void os_write_file(Array_t<u8> path, Array_t<u8> data, Status* status = nullptr) {
    if (os_status_initp(&status)) return;

    int fd = os_open(path, Os_codes::OPEN_WRITE | Os_codes::OPEN_CREATE | Os_codes::OPEN_TRUNCATE, 0660, status);
    os_write_fixed(fd, data, status);
    os_close(fd, status);
}

bool os_access(Array_t<u8> path, u8 flags) {
    using namespace Os_codes;
    int mode = 0;
    mode |= flags & ACCESS_EXISTS  ? F_OK : 0;
    mode |= flags & ACCESS_READ    ? R_OK : 0;
    mode |= flags & ACCESS_WRITE   ? W_OK : 0;
    mode |= flags & ACCESS_EXECUTE ? X_OK : 0;

    char* tmp = (char*)alloca(path.size + 1);
    memcpy(tmp, path.data, path.size);
    tmp[path.size] = 0;
    
    return access(tmp, mode) != -1;
}

void os_error_output(Array_t<u8> prefix = "Error"_arr, Status* status = nullptr) {
    if (not status) status = &global_os.status;

    Status temp_status;
    s64 last = 0;
    for (s64 i = 0; i < status->error_buf.size; ++i) {
        if (status->error_buf[i] == '\n') {
            os_write_fixed(STDERR_FILENO, prefix, &temp_status);
            os_write_fixed(STDERR_FILENO, ": "_arr, &temp_status);
            os_write_fixed(STDERR_FILENO, array_subarray(status->error_buf, last, i), &temp_status);
            os_write_fixed(STDERR_FILENO, "\n"_arr, &temp_status);
            last = i+1;
        }
    }
    status->error_buf.size = 0;

    if (temp_status.bad()) {
        // Encountering an error while trying to print an error message is not a good sign
        abort();
    }
}

void os_error_panic(Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->bad()) {
        os_error_output("Error"_arr, status);
        exit(2);
    }
}

bool os_error_clear(Status* status = nullptr) {
    if (not status) status = &global_os.status;
    status->error_buf.size = 0;
    bool result = status->code;
    status->code = 0;
    return result;
}

Array_t<u8> array_load_from_file(Array_t<u8> path) {
    Array_t<u8> result = os_read_file(path);
    os_error_panic();
    return result;
}
void array_write_to_file(Array_t<u8> path, Array_t<u8> data) {
    os_write_file(path, data);
    os_error_panic();
}
void array_fwrite(Array_t<u8> str, int fd = STDOUT_FILENO) {
    os_write_fixed(fd, str);
    os_error_panic();
}
void array_puts(Array_t<u8> str, int fd = STDOUT_FILENO) {
    os_write_fixed(fd, str);
    os_write_fixed(fd, "\n"_arr);
    os_error_panic();
}


// Old functions below
#if 0

int os_request_lock_try(int fd, bool* out_success, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return Os_codes::SKIPPED;
    
    int code = flock(fd, LOCK_EX | LOCK_NB);

    bool succ = true;
    if (code) {
        if (errno == EWOULDBLOCK) {
            succ = false;
        } else {
            os_error_printf(status, "$ while trying to acquire lock\n");
            return 1;
        }
    }
    
    if (out_success) *out_success = succ;
    return 0;
}


int os_read_try(int fd, Array_t<u8> buf, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return Os_codes::SKIPPED;
    
    while (buf.size > 0) {
        s64 bytes_read = read(fd, buf.data, buf.size);
        if (bytes_read == -1) {
            bool wouldblock = errno == EWOULDBLOCK || errno == EAGAIN;
            os_error_printf(status, "$ while calling read()");
            return wouldblock ? Os_codes::READ_WOULDBLOCK : Os_codes::READ_ERROR;
        }
        if (bytes_read == 0) {
            /* Note that buf.size > 0 due to loop condition */
            array_printf(&status->error_buf, "unexpected eof (%ld bytes left to read)\n", (long)buf.size);
            return Os_codes::READ_EOF;
        }
        buf = array_subarray(buf, bytes_read, buf.size);
    }
    
    assert(buf.size == 0);
    return 0;
}

int os_read_all_try(int fd, Array_dyn<u8>* buf, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return Os_codes::SKIPPED;
    
    while (true) {
        if (buf->capacity < buf->size + 256) {
            array_reserve(buf, buf->size + 256);
        }
        
        s64 bytes_read = read(fd, buf->data + buf->size, buf->capacity - buf->size);
        if (bytes_read == -1) {
            bool wouldblock = errno == EWOULDBLOCK || errno == EAGAIN;
            os_error_printf(status, "$ while calling read()");
            return wouldblock ? Os_codes::READ_WOULDBLOCK : Os_codes::READ_ERROR;
        }
        buf->size += bytes_read;

        if (buf->size < buf->capacity) break;
    }
    
    return 0;
}
int os_truncate_try(int fd, u64 size, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return Os_codes::SKIPPED;
    
    int code = ftruncate(fd, size);
    if (code) {
        os_error_printf(status, "$ while calling ftruncate()");
        return 1;
    }
    return 0;
}

int os_chmod_try(int fd, u32 mode, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return Os_codes::SKIPPED;
    
    int code = fchmod(fd, mode);
    if (code) {
        os_error_printf(status, "$ while calling fchmod()\n");
        return 1;
    }
    return 0;
}

Array_t<u8> os_read_whole_file(Array_t<u8> path, Status* status = nullptr) {
    if (not status) status = &global_os.status;
    if (status->code) return {};
    
    int fd;
    if (os_open_try(path, Os_codes::OPEN_READ, 0, &fd, status)) goto error_nocontext;

    {u64 size;
    if (os_seek_try(fd, 0, Os_codes::P_SEEK_END, &size, status)) goto error;
    if (os_seek_try(fd, 0, Os_codes::P_SEEK_SET, status)) goto error;

    {Array_t<u8> result = array_create<u8>(size);

    if (os_read_try(fd, result, status)) goto error;    
    if (os_close_try(fd, status)) goto error;    
    
    return result;}}

  error:
    array_printf(&status->error_buf, "while reading file at '");
    array_append(&status->error_buf, path);
    array_printf(&status->error_buf, "'\n");
  error_nocontext:
    os_error_print(status);
    exit(6);
}
#endif


