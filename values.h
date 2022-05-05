#ifndef VALUES_H
#define VALUES_H

#include <stdint.h>

/* any abstract value */
typedef int64_t val_t;

typedef enum type_t {
  T_INVALID = -1,
  /* immediates */
  T_INT,
  T_BOOL,
  T_CHAR,
  T_EOF,  
  T_VOID,
  T_EMPTY,
  /* pointers */
  T_BOX,
  T_CONS,
  T_VECT,
  T_STR,
  T_SYMB,
  T_PROC,
  T_STRUCT,
} type_t;

typedef struct thunk_t {
} thunk_t;

val_t eval_thunk(thunk_t *t);

typedef uint32_t val_char_t;
typedef struct val_box_t {
  thunk_t *val;
} val_box_t;
typedef struct val_cons_t {
  thunk_t *snd;
  thunk_t *fst;
} val_cons_t;
typedef struct val_vect_t {
  uint64_t len;
  val_t elems[];
} val_vect_t;
typedef struct val_str_t {
  uint64_t len;
  val_char_t codepoints[];
} val_str_t;
typedef struct val_symb_t {
  uint64_t len;
  val_char_t codepoints[];
} val_symb_t;
typedef struct val_struct_t {
  val_t name;
  val_t* vals;
} val_struct_t;
/* return the type of x */
type_t val_typeof(val_t x);

/**
 * Wrap/unwrap values
 *
 * The behavior of unwrap functions are undefined on type mismatch.
 */
int64_t val_unwrap_int(val_t x);
val_t val_wrap_int(int64_t i);

int val_unwrap_bool(val_t x);
val_t val_wrap_bool(int b);

val_char_t val_unwrap_char(val_t x);
val_t val_wrap_char(val_char_t b);

val_t val_wrap_eof();

val_t val_wrap_void();

val_box_t* val_unwrap_box(val_t x);
val_t val_wrap_box(val_box_t* b);

val_cons_t* val_unwrap_cons(val_t x);
val_t val_wrap_cons(val_cons_t* c);

val_vect_t* val_unwrap_vect(val_t x);
val_t val_wrap_vect(val_vect_t* c);

val_str_t* val_unwrap_str(val_t x);
val_t val_wrap_str(val_str_t* c);

val_symb_t* val_unwrap_symb(val_t x);
val_t val_wrap_symb(val_symb_t* c);

val_struct_t* val_unwrap_struct(val_t x);
val_t val_wrap_struct(val_struct_t* c);

#endif
