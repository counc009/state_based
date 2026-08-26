#include <stdlib.h>

#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#define fabs_f(x) (x < 0.0f ? - x : x)

union int_float { float f; int32_t i; };

static inline float float_of_int(int32_t i) {
  union int_float x = { .i = i };
  return x.f;
}

static inline int32_t int_of_float(float f) {
  union int_float x = { .f = f };
  return x.i;
}

#define F32_val(v)  (float_of_int(Int32_val(v)))
#define F32_copy(f) (caml_copy_int32(int_of_float(f)))

CAMLprim value f32_add(value x, value y) {
  CAMLparam2(x, y);
  CAMLreturn (F32_copy (F32_val(x) + F32_val(y)));
}

CAMLprim value f32_sub(value x, value y) {
  CAMLparam2(x, y);
  CAMLreturn (F32_copy (F32_val(x) - F32_val(y)));
}

CAMLprim value f32_mul(value x, value y) {
  CAMLparam2(x, y);
  CAMLreturn (F32_copy (F32_val(x) * F32_val(y)));
}

CAMLprim value f32_div(value x, value y) {
  CAMLparam2(x, y);
  CAMLreturn (F32_copy (F32_val(x) / F32_val(y)));
}

CAMLprim value f32_abs(value x) {
  CAMLparam1(x);
  CAMLreturn (F32_copy (fabs_f(F32_val(x))));
}

CAMLprim value f32_neg(value x) {
  CAMLparam1(x);
  CAMLreturn (F32_copy (- F32_val(x)));
}

CAMLprim value f32_of_double(value x) {
  CAMLparam1(x);
  CAMLreturn (F32_copy((float) Double_val(x)));
}

CAMLprim value f32_to_double(value x, value y) {
  CAMLparam2(x, y);
  CAMLreturn (caml_copy_double((double) F32_val(x)));
}
