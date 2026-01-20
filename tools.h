/*
  tools.h - A collection of useful tools and data structures.
  This is HEAVILY insprired by [TOOLS.h](https://github.com/tsoding/TOOLS.h)
  ^ Alexey's youtube channel: https://www.youtube.com/c/tsoding
  I've reimplemented many of the same things to improve my own understanding of
  the tools + put my own spin on some things where i felt like it.
*/
#ifndef TOOLS_H_
#define TOOLS_H_

#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

// =====================================================
// ================= Replaceable macros ================
// =====================================================

#ifndef TOOLS_DEF
#define TOOLS_DEF
#endif // TOOLS_DEF

#ifndef TOOLS_REALLOC
#include <stdlib.h>
#define TOOLS_REALLOC(ptr, size) realloc((ptr), (size))
#endif // TOOLS_REALLOC

#ifndef TOOLS_ASSERT
#include <assert.h>
#define TOOLS_ASSERT(expr) assert(expr)
#endif // TOOLS_ASSERT

#ifndef TOOLS_FREE
#include <stdlib.h>
#define TOOLS_FREE(ptr) free((ptr))
#endif // TOOLS_FREE

// =====================================================
// =============== END Replaceable macros ==============
// =====================================================

// Helpers
#define TOOLS_UNUSED(value) (void)(value)
#define TOOLS_TODO(message)                                                                                            \
  do {                                                                                                                 \
    fprintf(stderr, "%s:%d: TODO: %s\n", __FILE__, __LINE__, message);                                                 \
    abort();                                                                                                           \
  } while (0)
#define TOOLS_UNREACHABLE(message, ...)                                                                                \
  do {                                                                                                                 \
    fprintf(stderr, "%s:%d: UNREACHABLE: " message "\n", __FILE__, __LINE__ __VA_OPT__(, ) __VA_ARGS__);               \
    abort();                                                                                                           \
  } while (0)

#define TOOLS_AS_ARRAY(Type, n, ...) ((Type[(n)]){__VA_ARGS__})
#define TOOLS_ARRAY_LEN(array) (sizeof(array) / sizeof((array)[0]))
#define TOOLS_ARRAY_GET(array, index) (TOOLS_ASSERT((size_t)(index) < TOOLS_ARRAY_LEN(array)), array[(size_t)(index)])

#define TOOLS_COMBINE1(X, Y) X##Y
#define TOOLS_COMBINE(X, Y) TOOLS_COMBINE1(X, Y)
#define TOOLS_UNIQUE_VAR(prefix) TOOLS_COMBINE(__, TOOLS_COMBINE(prefix, TOOLS_COMBINE(_, TOOLS_COMBINE(__LINE__, __))))

#define DEPAREN(...) ESC(ISH __VA_ARGS__)
#define ISH(...) ISH __VA_ARGS__
#define ESC(...) ESC_(__VA_ARGS__)
#define ESC_(...) VAN##__VA_ARGS__
#define VANISH

#define TOOLS_NARGS(...) TOOLS_NARGS_PP_ARG_N_IMPL(__VA_ARGS__, TOOLS_NARGS_PP_RSEQ_N())
#define TOOLS_NARGS_PP_ARG_N_IMPL(...) TOOLS_NARGS_PP_ARG_N(__VA_ARGS__)
#define TOOLS_NARGS_PP_ARG_N(_1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19,     \
                             _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31, _32, _33, _34, _35, _36, _37, \
                             _38, _39, _40, _41, _42, _43, _44, _45, _46, _47, _48, _49, _50, _51, _52, _53, _54, _55, \
                             _56, _57, _58, _59, _60, _61, _62, _63, N, ...)                                           \
  N
#define TOOLS_NARGS_PP_RSEQ_N()                                                                                        \
  63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35,  \
      34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6,  \
      5, 4, 3, 2, 1, 0

/* NEW_CHECK(default, maybe_blank) */
#define TOOLS_MAYBE_DEFAULT(...) TOOLS_MAYBE_DEFAULT_M_(__VA_ARGS__)
/* delay expansion of M once to perform TOOLS_MAYBE_DEFAULT_Q */
#define TOOLS_MAYBE_DEFAULT_M_(D, ...) TOOLS_MAYBE_DEFAULT_F(D, TOOLS_MAYBE_DEFAULT_Q(__VA_ARGS__))
/* TOOLS_MAYBE_DEFAULT_Q(maybe_blank): if __VA_ARGS__ is non-blank, __VA_ARGS__. Otherwise, TOOLS_MAYBE_DEFAULT_SPACE */
#define TOOLS_MAYBE_DEFAULT_Q(...) TOOLS_MAYBE_DEFAULT_FIRST_ONE(dummy, ##__VA_ARGS__, TOOLS_MAYBE_DEFAULT_SPACE)
/* Given a dummy and >=1 arguments, expand to the first argument */
#define TOOLS_MAYBE_DEFAULT_FIRST_ONE(dummy, a1, ...) a1
/* TOOLS_MAYBE_DEFAULT_SPACE just expands into two arguments so that we can differentiate between was-blank (2 args) and
 * non-blank (1 arg) */
#define TOOLS_MAYBE_DEFAULT_SPACE 0, 0
/* TOOLS_MAYBE_DEFAULT_F(default, one-or-two-arguments) */
#define TOOLS_MAYBE_DEFAULT_F(...) TOOLS_MAYBE_DEFAULT_F_(__VA_ARGS__)
#define TOOLS_MAYBE_DEFAULT_F_(...) TOOLS_MAYBE_DEFAULT_F__(__VA_ARGS__)
/* delay expansion of TOOLS_MAYBE_DEFAULT_F twice, for performing TOOLS_MAYBE_DEFAULT_Q and TOOLS_MAYBE_DEFAULT_SPACE */
#define TOOLS_MAYBE_DEFAULT_F__(D, ...) TOOLS_MAYBE_DEFAULT_H(NARGS(__VA_ARGS__), D, __VA_ARGS__)
/* TOOLS_MAYBE_DEFAULT_H(1 or 2, default, maybe_blank) */
#define TOOLS_MAYBE_DEFAULT_H(...) TOOLS_MAYBE_DEFAULT_H_(__VA_ARGS__)
/* delay expansion once, for performing NARGS */
#define TOOLS_MAYBE_DEFAULT_H_(N, D, ...) TOOLS_MAYBE_DEFAULT_DO##N(D, __VA_ARGS__)
/* based on NARGS, pick correct result */
#define TOOLS_MAYBE_DEFAULT_DO1(D, ...) __VA_ARGS__
#define TOOLS_MAYBE_DEFAULT_DO2(D, ...) D

// Expression value will be the shifted value
#define shift(ptr, size) (TOOLS_ASSERT((size) > 0 && "shift on empty array"), (size)--, *(ptr)++)

#define return_defer_named(result, value, defer_label)                                                                 \
  do {                                                                                                                 \
    result = value;                                                                                                    \
    goto defer_label;                                                                                                  \
  } while (0)
#define return_defer(value) return_defer_named(result, value, defer)

// =====================================================
// ====================== Memory =======================
// =====================================================

void *memdup_impl(void *src, size_t n);
#define memdup(src) memdup_impl((src), sizeof(*(src)));

// =====================================================
// ==================== END Memory =====================
// =====================================================

// =====================================================
// ======================= Span ========================
// =====================================================

#define SPAN_FIELDS(type)                                                                                              \
  size_t size;                                                                                                         \
  type *data

#define span_lit(Type, ...)                                                                                            \
  { .size = TOOLS_NARGS(__VA_ARGS__), .data = ((Type[TOOLS_NARGS(__VA_ARGS__)]){__VA_ARGS__}) }

#define span_ptr(span, index) ((span)->data + (index))
#define span_at(span, index) (*span_ptr((span), (index)))
#define span_last(span) ((span)->data[(TOOLS_ASSERT((span)->size > 0), (span)->size - 1)])

#define span_shift(span) shift((span)->data, (span)->size)
#define span_chop_one span_shift
#define span_chop_back(span, n) (TOOLS_ASSERT((size_t)(n) <= (span)->size), (span)->size -= (n))
#define span_chop_front(span, n) (span_chop_back((span), (n)), (span)->data += (n))

#define span_eq(a, b) ((a).size == (b).size && memcmp((a).data, (b).data, (a).size * sizeof(*(a).data)) == 0)

#define span_for_each(Type, it, span) for (Type *it = (span).data; it < ((span).data + (span).size); ++it)

// =====================================================
// ===================== END Span ======================
// =====================================================

// =====================================================
// =================== Dynamic Array ===================
// =====================================================

#define DA_INIT_CAP 8
#define DA_GROWTH_FACTOR 2

#define DA_FIELDS(type)                                                                                                \
  SPAN_FIELDS(type);                                                                                                   \
  size_t capacity

#define da_reserve(da, cap)                                                                                            \
  do {                                                                                                                 \
    size_t new_cap = (cap);                                                                                            \
    if ((da)->capacity < new_cap) {                                                                                    \
      (da)->capacity = (da)->capacity <= 0 ? DA_INIT_CAP : (da)->capacity;                                             \
      while ((da)->capacity < new_cap) { (da)->capacity *= DA_GROWTH_FACTOR; }                                         \
      (da)->data = TOOLS_REALLOC((da)->data, (da)->capacity * sizeof(*(da)->data));                                    \
      TOOLS_ASSERT((da)->data && "get good");                                                                          \
    }                                                                                                                  \
  } while (0)
#define da_free(da) ((da)->data ? TOOLS_FREE((da)->data) : 0, (da)->capacity = 0, (da)->size = 0);

#define da_push(da, item) (({ da_reserve((da), (da)->size + 1); }), (da)->data[(da)->size++] = (item))
#define da_push_n(da, items, n)                                                                                        \
  do {                                                                                                                 \
    da_reserve((da), (da)->size + (n));                                                                                \
    memcpy((da)->data + (da)->size, (items), (n) * sizeof(*(da)->data));                                               \
    (da)->size += (n);                                                                                                 \
  } while (0)
#define da_concat(da, other) da_push_n((da), (other)->data, (other)->size)

#define da_last(da) ((da)->data[(TOOLS_ASSERT((da)->size > 0), (da)->size - 1)])

#define da_resize(da, new_size) da_reserve((da), (da)->size = (new_size))
#define da_clear(da) da_resize((da), 0)
#define da_remove_unordered(da, i)                                                                                     \
  (da)->data[(size_t)(i)] = (da)->data[(TOOLS_ASSERT((size_t)(i) < (da)->size), --(da)->size)];

#define da_eq span_eq

#define da_for_each span_for_each

// =====================================================
// ================= END Dynamic Array =================
// =====================================================

// =====================================================
// ============ StringBuilder / StringView =============
// =====================================================

typedef struct SB {
  DA_FIELDS(char);
} StringBuilder;
typedef struct SV {
  SPAN_FIELDS(char);
} StringView;

#define sv_at(sv, index) ((sv).data[(index)])
#define sv_len(sv) ((sv).size)

#define sb_append da_push
#define sb_concat da_push_n
#define sb_append_sv(sb, sv) sb_concat((sb), (sv).data, (sv).size)
#define sb_append_cstr(sb, cstr)                                                                                       \
  do {                                                                                                                 \
    const char *TOOLS_UNIQUE_VAR(s) = cstr;                                                                            \
    sb_concat((sb), TOOLS_UNIQUE_VAR(s), strlen(TOOLS_UNIQUE_VAR(s)));                                                 \
  } while (0)
#define sb_append_null(sb) sb_append((sb), '\0')
TOOLS_DEF size_t sb_appendf(StringBuilder *sb, const char *fmt, ...);
TOOLS_DEF size_t sb_align_with(StringBuilder *sb, size_t alignment, char fill);
#define sb_align(sb, alignment) sb_align_with((sb), (alignment), ' ')
#define sv_extend_to_endof(sv, other) ((sv)->size = &span_last(&(other)) - (sv)->data)

#define sb_to_cstr(sb) strndup((sb).data, (sb).size)

#define sb_free da_free
#define sb_clear da_clear

TOOLS_DEF StringView sv_new(char *data, size_t size);
#define sv_from_parts sv_new
TOOLS_DEF StringView sv_from_cstr(const char *cstr);
TOOLS_DEF StringView sv_prefix(StringView sv, size_t n);
#define sv_from_da(da) sv_new((da).data, (da).size)
#define da2sv sv_from_da
#define sv_from_sb sv_from_da
#define sb2sv sv_from_sb

TOOLS_DEF bool sv_eq(StringView a, StringView b);
#define sv_eq_cstr(sv, cstr) (sv_eq((sv), sv_from_cstr((cstr))))
TOOLS_DEF bool sv_starts_with(StringView sv, const char *prefix);
TOOLS_DEF bool sv_ends_with(StringView sv, const char *suffix);

#define sv_chop_front_ignore span_chop_front
TOOLS_DEF StringView sv_chop_front(StringView *sv, size_t n);
#define sv_chop_left sv_chop_front
TOOLS_DEF StringView sv_chop_by_delim(StringView *sv, char delim);
TOOLS_DEF StringView sv_chop_back(StringView *sv, size_t n);
#define sv_chop_right sv_chop_back

TOOLS_DEF StringView sv_trim_start(StringView sv);
#define sv_trim_left sv_trim_start
TOOLS_DEF StringView sv_trim_end(StringView sv);
#define sv_trim_right sv_trim_end
TOOLS_DEF StringView sv_trim(StringView sv);

#define sv_for_each(it, sv) span_for_each(char, (it), (sv))

// printf macros for StringView
#ifndef SV_Fmt
#define SV_Fmt "%.*s"
#endif // SV_Fmt
#ifndef SV_Arg
#define SV_Arg(sv) (int)(sv).size, (sv).data
#endif // SV_Arg
#define SB_Fmt SV_Fmt
#define SB_Arg SV_Arg
// USAGE:
//   String_View name = ...;
//   printf("Name: "SV_Fmt"\n", SV_Arg(name));

// =====================================================
// ========== END StringBuilder / StringView ===========
// =====================================================

// =====================================================
// =================== Struct Error ====================
// =====================================================

#define SERROR_FIELDS StringBuilder error

// internal definitions
#define serrorf(s, fmt, ...) ((void)sb_appendf(&(s)->error, fmt __VA_OPT__(, ) __VA_ARGS__), false)
#define serror_forwardf(to, from, bridgetext, fmt, ...)                                                                \
  serrorf((to), "[%s:%-4d] " fmt bridgetext SB_Fmt, __FILE__, __LINE__,                                                \
          __VA_ARGS__ __VA_OPT__(, ) SB_Arg((from)->error))
#define serror_causedf(s, fmt, ...)                                                                                    \
  serrorf((s), "\n\tCaused [%s:%-4d]: " fmt, __FILE__, __LINE__ __VA_OPT__(, ) __VA_ARGS__)
#define serror_exists(s) ((s)->error.size > 0)
#define serror_clear(s) sb_clear(&(s)->error)

// =====================================================
// ================= END Struct Error ==================
// =====================================================

// =====================================================
// ==================== Files / IO =====================
// =====================================================

TOOLS_DEF bool read_file(const char *filepath, StringBuilder *sb);
TOOLS_DEF bool write_file(const char *filepath, char *data, size_t size);
#define write_file_sv(filepath, sv) write_file((filepath), (sv).data, (sv).size)
#define write_file_sb write_file_sv

// =====================================================
// ================== END Files / IO ===================
// =====================================================

// =====================================================
// ====================== Logging ======================
// =====================================================

typedef enum { TOOLS_TRACE, TOOLS_DEBUG, TOOLS_INFO, TOOLS_WARN, TOOLS_ERROR, TOOLS_NO_LOGS } ToolsLogLevel;
typedef struct ToolsLogOpts {
  const char *prefix;
  const char *debug_label;
  bool omit_prefix; // level + log_location
  bool omit_level;
  bool omit_log_location;
  bool omit_newline;
  const char *file;
  int line;
} ToolsLogOpts;

typedef void(tools_log_handler)(ToolsLogLevel level, ToolsLogOpts opts, const char *fmt, va_list args);

TOOLS_DEF void tools_set_log_handler(tools_log_handler *handler);
TOOLS_DEF tools_log_handler *tools_get_log_handler(void);

extern ToolsLogLevel tools_logging_min_log_level;
TOOLS_DEF tools_log_handler tools_default_log_handler;

TOOLS_DEF void tools_log_opt(ToolsLogLevel level, ToolsLogOpts opts, const char *fmt, ...);
#define tools_logx(lvl, opts, fmt, ...)                                                                                \
  tools_log_opt(lvl, ((ToolsLogOpts){.file = __FILE__, .line = __LINE__, DEPAREN(opts)}),                              \
                (fmt)__VA_OPT__(, ) __VA_ARGS__)
#define tools_log(lvl, fmt, ...) tools_logx(lvl, (), (fmt)__VA_OPT__(, ) __VA_ARGS__)

// =====================================================
// ==================== END Logging ====================
// =====================================================

#endif // TOOLS_H_

#ifdef TOOLS_IMPL

void *memdup_impl(void *src, size_t n) { return memcpy(calloc(1, n), src, n); }

size_t sb_appendf(StringBuilder *sb, const char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  int n = vsnprintf(NULL, 0, fmt, args);
  va_end(args);

  // NOTE: the new_capacity needs to be +1 because of the null terminator.
  // However, further below we increase sb->count by n, not n + 1.
  // This is because we don't want the sb to include the null terminator. The user can always sb_append_null() if they
  // want it
  da_reserve(sb, sb->size + n + 1);
  va_start(args, fmt);
  vsnprintf(sb->data + sb->size, n + 1, fmt, args);
  va_end(args);

  sb->size += n;

  return (size_t)n;
}
size_t sb_align_with(StringBuilder *sb, size_t alignment, char fill) {
  size_t padding = (alignment - (sb->size % alignment)) % alignment;
  for (size_t i = 0; i < padding; ++i) { sb_append(sb, fill); }
  return padding;
}
StringView sv_new(char *data, size_t size) { return (StringView){.data = data, .size = (size_t)size}; }
StringView sv_from_cstr(const char *cstr) { return sv_new((char *)cstr, strlen(cstr)); }
#define sv_from_cstr_lit(cstr) ((StringView){.data = (char *)(cstr), .size = (TOOLS_ARRAY_LEN((cstr)) - 1)})
StringView sv_prefix(StringView sv, size_t n) {
  if (n > sv.size) { n = sv.size; }
  return sv_new(sv.data, n);
}
bool sv_eq(StringView a, StringView b) { return a.size == b.size && (memcmp(a.data, b.data, a.size) == 0); }
bool sv_starts_with(StringView sv, const char *prefix) {
  StringView prefix_sv = sv_from_cstr(prefix);
  return sv_eq(prefix_sv, sv_prefix(sv, prefix_sv.size));
}
bool sv_ends_with(StringView sv, const char *suffix) {
  StringView suffix_sv = sv_from_cstr(suffix);
  return sv_eq(suffix_sv, sv_chop_back(&sv, suffix_sv.size));
}
StringView sv_chop_front(StringView *sv, size_t n) {
  if (n > sv->size) { n = sv->size; }
  StringView result = {.data = sv->data, .size = n};
  span_chop_front(sv, n);
  return result;
}
StringView sv_chop_by_delim(StringView *sv, char delim) {
  size_t i = 0;
  while (i < sv->size && sv->data[i] != delim) { ++i; }
  StringView result = sv_chop_front(sv, i);
  if (sv->size > 0 && sv->data[0] == delim) {
    span_chop_front(sv, 1); // chop the delim
  }
  return result;
}
StringView sv_chop_back(StringView *sv, size_t n) {
  if (n > sv->size) { n = sv->size; }
  StringView result = {.data = sv->data + (sv->size - n), .size = n};
  span_chop_back(sv, n);
  return result;
}
StringView sv_trim_start(StringView sv) {
  size_t start = 0;
  while (start < sv.size && isspace(sv.data[start])) { ++start; }
  return sv_chop_front(&sv, start);
}
StringView sv_trim_end(StringView sv) {
  size_t end = sv.size;
  while (end > 0 && isspace(sv.data[end - 1])) { --end; }
  return sv_chop_back(&sv, sv.size - end);
}
StringView sv_trim(StringView sv) { return sv_trim_end(sv_trim_start(sv)); }
bool read_file(const char *filepath, StringBuilder *sb) {
  bool result = true;

  FILE *file = fopen(filepath, "rb");
  if (!file) return_defer(false);

  if (fseek(file, 0, SEEK_END)) return_defer(false);
  size_t file_size = ftell(file);
  if (file_size < 0) return_defer(false);
  if (fseek(file, 0, SEEK_SET)) return_defer(false);

  da_reserve(sb, sb->size + file_size);
  size_t read_size = fread(sb->data + sb->size, file_size, 1, file);
  if (read_size != 1 || (errno = ferror(file))) return_defer(false);
  sb->size += file_size;

defer:
  if (!result)
    tools_logx(TOOLS_ERROR, .omit_log_location = true, "Failed to read file: %s. Got error: %s\n", filepath,
               strerror(errno));
  if (file) fclose(file);
  return result;
}
bool write_file(const char *filepath, char *data, size_t size) {
  bool result = true;

  FILE *file = fopen(filepath, "wb");
  if (!file) return_defer(false);

  size_t write_size = fwrite(data, size, 1, file);
  if (write_size != 1 || (errno = ferror(file))) return_defer(false);

defer:
  if (!result)
    tools_logx(TOOLS_ERROR, .omit_log_location = true, "Failed to write file: %s. Got error: %s\n", filepath,
               strerror(errno));
  if (file) fclose(file);
  return result;
}

static tools_log_handler *tools__log_handler = &tools_default_log_handler;
void tools_set_log_handler(tools_log_handler *handler) { tools__log_handler = handler; }
tools_log_handler *tools_get_log_handler(void) { return tools__log_handler; }

ToolsLogLevel tools_logging_min_log_level = TOOLS_INFO;
char *tools_logging_debug_label = "ALL";
void tools_default_log_handler(ToolsLogLevel level, ToolsLogOpts opts, const char *fmt, va_list args) {
  if (level < tools_logging_min_log_level) { return; }

  if (level == TOOLS_DEBUG && tools_logging_debug_label != NULL && opts.debug_label != NULL &&
      strcmp(tools_logging_debug_label, "ALL") != 0 && strcmp(tools_logging_debug_label, opts.debug_label) != 0) {
    return;
  }

  if (!opts.omit_level && !opts.omit_prefix) {
    switch (level) {
    case TOOLS_TRACE: fprintf(stderr, "[TRACE] ");
    case TOOLS_DEBUG: fprintf(stderr, "[DEBUG] "); break;
    case TOOLS_INFO: fprintf(stderr, "[INFO]  "); break;
    case TOOLS_WARN: fprintf(stderr, "[WARN]  "); break;
    case TOOLS_ERROR: fprintf(stderr, "[ERROR] "); break;
    case TOOLS_NO_LOGS: return;
    }
  }
  if (!opts.omit_log_location && !opts.omit_prefix) {
    char *fname = opts.file ? (char *)opts.file : "unknown_file";
    if (strlen(fname) > 20) { fname += strlen(fname) - 20; }
    fprintf(stderr, "[%s:%-4d] ", fname, opts.line);
  }

  if (opts.prefix) { fprintf(stderr, "[%s] ", opts.prefix); }

  vfprintf(stderr, fmt, args);
  if (!opts.omit_newline) fprintf(stderr, "\n");
}

void tools_log_opt(ToolsLogLevel level, ToolsLogOpts opts, const char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  tools__log_handler(level, opts, fmt, args);
  va_end(args);
}

#endif // TOOLS_IMPL

#ifndef TOOLS_STRIP_PREFIX_GUARD_
#define TOOLS_STRIP_PREFIX_GUARD_

#ifndef TOOLS_DONT_STRIP_PREFIXES
#define UNUSED TOOLS_UNUSED
#define TODO TOOLS_TODO
#define UNREACHABLE TOOLS_UNREACHABLE
#define AS_ARRAY TOOLS_AS_ARRAY
#define ARRAY_LEN TOOLS_ARRAY_LEN
#define ARRAY_GET TOOLS_ARRAY_GET
#define COMBINE TOOLS_COMBINE
#define UNIQUE_VAR TOOLS_UNIQUE_VAR
#define NARGS TOOLS_NARGS
#define MAYBE_DEFAULT TOOLS_MAYBE_DEFAULT
#define LogLevel ToolsLogLevel
#define TRACE TOOLS_TRACE
#define DEBUG TOOLS_DEBUG
#define INFO TOOLS_INFO
#define WARN TOOLS_WARN
#define ERROR TOOLS_ERROR
#define NO_LOGS TOOLS_NO_LOGS
#define LogOpts ToolsLogOpts
#define log_handler tools_log_handler
#define set_log_handler tools_set_log_handler
#define default_log_handler tools_default_log_handler
#define log_opt tools_log_opt
#define logx tools_logx
#define log tools_log
#endif // TOOLS_DONT_STRIP_PREFIXES

#endif // TOOLS_STRIP_PREFIX_GUARD_