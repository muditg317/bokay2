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
#define TOOLS_UNREACHABLE(message)                                                                                     \
  do {                                                                                                                 \
    fprintf(stderr, "%s:%d: UNREACHABLE: %s\n", __FILE__, __LINE__, message);                                          \
    abort();                                                                                                           \
  } while (0)

#define TOOLS_ARRAY_LEN(array) (sizeof(array) / sizeof(array[0]))
#define TOOLS_ARRAY_GET(array, index) (TOOLS_ASSERT((size_t)(index) < TOOLS_ARRAY_LEN(array)), array[(size_t)(index)])

#define TOOLS_COMBINE1(X, Y) X##Y
#define TOOLS_COMBINE(X, Y) TOOLS_COMBINE1(X, Y)
#define TOOLS_UNIQUE_VAR(prefix) TOOLS_COMBINE(prefix, TOOLS_COMBINE(_, __LINE__))

// Expression value will be the shifted value
#define shift(ptr, size) (TOOLS_ASSERT((size) > 0 && "shift on empty array"), (size)--, *(ptr)++)

#define return_defer_named(result, value, defer_label)                                                                 \
  do {                                                                                                                 \
    result = value;                                                                                                    \
    goto defer_label;                                                                                                  \
  } while (0)
#define return_defer(value) return_defer_named(result, value, defer)

// =====================================================
// ======================= Span ========================
// =====================================================

#define SPAN_FIELDS(type)                                                                                              \
  type *data;                                                                                                          \
  size_t size;

#define span_at(span, index) ((span)->data[(index)])
#define span_last(span) ((span)->data[(TOOLS_ASSERT((span)->size > 0), (span)->size - 1)])

#define span_shift(span) shift((span)->data, (span)->size)
#define span_chop_one(span) span_shift((span))
#define span_chop_back(span, n) (TOOLS_ASSERT((size_t)(n) <= (span)->size), (span)->size -= (n))
#define span_chop_front(span, n) (span_chop_back((span), (n)), (span)->data += (n))

#define span_for_each(Type, it, span) for (Type *it = (span).data, *end = (span).data + (span).size; it != end; ++it)

// =====================================================
// ===================== END Span ======================
// =====================================================

// =====================================================
// =================== Dynamic Array ===================
// =====================================================

#define DA_INIT_CAP 8
#define DA_GROWTH_FACTOR 2

#define DA_FIELDS(type)                                                                                                \
  SPAN_FIELDS(type)                                                                                                    \
  size_t capacity;

#define da_reserve(da, cap)                                                                                            \
  do {                                                                                                                 \
    if ((da)->capacity < (cap)) {                                                                                      \
      (da)->capacity = (da)->capacity <= 0 ? DA_INIT_CAP : (da)->capacity;                                             \
      while ((da)->capacity < (cap)) {                                                                                 \
        (da)->capacity *= DA_GROWTH_FACTOR;                                                                            \
      }                                                                                                                \
      (da)->data = TOOLS_REALLOC((da)->data, (da)->capacity * sizeof(*(da)->data));                                    \
      TOOLS_ASSERT((da)->data && "get good");                                                                          \
    }                                                                                                                  \
  } while (0)
#define da_free(da) (TOOLS_FREE((da)->data), (da)->capacity = 0, (da)->size = 0);

#define da_push(da, item)                                                                                              \
  do {                                                                                                                 \
    da_reserve((da), (da)->size + 1);                                                                                  \
    (da)->data[(da)->size++] = (item);                                                                                 \
  } while (0)
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

#define da_for_each(Type, it, da) span_for_each((Type), (it), (da))

// =====================================================
// ================= END Dynamic Array =================
// =====================================================

// =====================================================
// ============ StringBuilder / StringView =============
// =====================================================

typedef struct {
  DA_FIELDS(char)
} StringBuilder;
typedef struct {
  SPAN_FIELDS(char)
} StringView;

#define sb_append(sb, c) da_push((sb), (c))
#define sb_concat(sb, data, n) da_push_n((sb), (data), (n))
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

#define sb_free(sb) da_free((sb))
#define sb_clear(sb) da_clear((sb))

TOOLS_DEF StringView sv_new(char *data, size_t size);
#define sv_from_parts(data, size) sv_new((data), (size))
TOOLS_DEF StringView sv_from_cstr(const char *cstr);
#define sv_from_sb(sb) sv_new((sb)->data, (sb)->size)
#define sb2sv(sb) sv_from_sb(sb)
#define sv_from_da(da) sv_new((da)->data, (da)->size)
#define da2sv(da) sv_from_da(da)

TOOLS_DEF bool sv_eq(StringView a, StringView b);
TOOLS_DEF bool sv_starts_with(StringView sv, const char *prefix);
TOOLS_DEF bool sv_ends_with(StringView sv, const char *suffix);

TOOLS_DEF StringView sv_chop_front(StringView *sv, size_t n);
#define sv_chop_left(sv, n) sv_chop_front((sv), (n))
TOOLS_DEF StringView sv_chop_by_delim(StringView *sv, char delim);
TOOLS_DEF StringView sv_chop_back(StringView *sv, size_t n);
#define sv_chop_right(sv, n) sv_chop_back((sv), (n))

TOOLS_DEF StringView sv_trim_start(StringView sv);
#define sv_trim_left(sv) sv_trim_start(sv)
TOOLS_DEF StringView sv_trim_end(StringView sv);
#define sv_trim_right(sv) sv_trim_end(sv)
TOOLS_DEF StringView sv_trim(StringView sv);

#define sv_for_each(it, sv) span_for_each(char, (it), (sv))

// printf macros for StringView
#ifndef SV_Fmt
#define SV_Fmt "%.*s"
#endif // SV_Fmt
#ifndef SV_Arg
#define SV_Arg(sv) (int)(sv).size, (sv).data
#endif // SV_Arg
// USAGE:
//   String_View name = ...;
//   printf("Name: "SV_Fmt"\n", SV_Arg(name));

// =====================================================
// ========== END StringBuilder / StringView ===========
// =====================================================

// =====================================================
// ==================== Files / IO =====================
// =====================================================

TOOLS_DEF bool read_file(const char *filepath, StringBuilder *sb);
TOOLS_DEF bool write_file(const char *filepath, char *data, size_t size);
#define write_file_sv(filepath, sv) write_file((filepath), (sv).data, (sv).size)
#define write_file_sb(filepath, sb) write_file_sv((filepath), (sb))

// =====================================================
// ================== END Files / IO ===================
// =====================================================

#endif // TOOLS_H_

#ifdef TOOLS_IMPLEMENTATION

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
  for (size_t i = 0; i < padding; ++i) {
    sb_append(sb, fill);
  }
  return padding;
}
StringView sv_new(char *data, size_t size) { return (StringView){.data = data, .size = (size_t)size}; }
StringView sv_from_cstr(const char *cstr) { return sv_new((char *)cstr, strlen(cstr)); }
bool sv_eq(StringView a, StringView b) { return a.size == b.size && (memcmp(a.data, b.data, a.size) == 0); }
bool sv_starts_with(StringView sv, const char *prefix) {
  StringView prefix_sv = sv_from_cstr(prefix);
  return sv_eq(prefix_sv, sv_chop_front(&sv, prefix_sv.size));
}
bool sv_ends_with(StringView sv, const char *suffix) {
  StringView suffix_sv = sv_from_cstr(suffix);
  return sv_eq(suffix_sv, sv_chop_back(&sv, suffix_sv.size));
}
StringView sv_chop_front(StringView *sv, size_t n) {
  if (n > sv->size) {
    n = sv->size;
  }
  StringView result = {.data = sv->data, .size = n};
  span_chop_front(sv, n);
  return result;
}
StringView sv_chop_by_delim(StringView *sv, char delim) {
  size_t i = 0;
  while (i < sv->size && sv->data[i] != delim) {
    ++i;
  }
  StringView result = sv_chop_front(sv, i);
  if (sv->size > 0 && sv->data[0] == delim) {
    span_chop_front(sv, 1); // chop the delim
  }
  return result;
}
StringView sv_chop_back(StringView *sv, size_t n) {
  if (n > sv->size) {
    n = sv->size;
  }
  StringView result = {.data = sv->data + (sv->size - n), .size = n};
  span_chop_back(sv, n);
  return result;
}
StringView sv_trim_start(StringView sv) {
  size_t start = 0;
  while (start < sv.size && isspace(sv.data[start])) {
    ++start;
  }
  return sv_chop_front(&sv, start);
}
StringView sv_trim_end(StringView sv) {
  size_t end = sv.size;
  while (end > 0 && isspace(sv.data[end - 1])) {
    --end;
  }
  return sv_chop_back(&sv, sv.size - end);
}
StringView sv_trim(StringView sv) { return sv_trim_end(sv_trim_start(sv)); }
bool read_file(const char *filepath, StringBuilder *sb) {
  bool result = true;

  FILE *file = fopen(filepath, "rb");
  if (!file)
    return_defer(false);

  if (fseek(file, 0, SEEK_END))
    return_defer(false);
  size_t file_size = ftell(file);
  if (file_size < 0)
    return_defer(false);
  if (fseek(file, 0, SEEK_SET))
    return_defer(false);

  da_reserve(sb, sb->size + file_size);
  size_t read_size = fread(sb->data + sb->size, file_size, 1, file);
  if (read_size != 1 || (errno = ferror(file)))
    return_defer(false);
  sb->size += file_size;

defer:
  if (!result)
    printf("Failed to read file: %s. Got error: %s\n", filepath, strerror(errno));
  if (file)
    fclose(file);
  return result;
}
bool write_file(const char *filepath, char *data, size_t size) {
  bool result = true;

  FILE *file = fopen(filepath, "wb");
  if (!file)
    return_defer(false);

  size_t write_size = fwrite(data, size, 1, file);
  if (write_size != 1 || (errno = ferror(file)))
    return_defer(false);

defer:
  if (!result)
    printf("Failed to write file: %s. Got error: %s\n", filepath, strerror(errno));
  if (file)
    fclose(file);
  return result;
}

#endif // TOOLS_IMPLEMENTATION