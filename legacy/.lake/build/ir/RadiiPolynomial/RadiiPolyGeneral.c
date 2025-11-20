// Lean compiler output
// Module: RadiiPolynomial.RadiiPolyGeneral
// Imports: public import Init public import Mathlib.Analysis.Calculus.Deriv.Mul public import Mathlib.Analysis.Calculus.FDeriv.Basic public import Mathlib.Analysis.Calculus.MeanValue public import Mathlib.Topology.MetricSpace.Contracting
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_simpleRadiiPolynomial___closed__0;
LEAN_EXPORT lean_object* l_NewtonLikeMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_radiiPolynomial(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Z__bound(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_I__F(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Z__bound__general(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_generalRadiiPolynomial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NormedAddCommGroup_toNormedAddGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_I__E(lean_object*, lean_object*, lean_object*);
static lean_object* l_I__E___closed__0;
LEAN_EXPORT lean_object* l_NewtonLikeMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NewtonLikeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_simpleRadiiPolynomial(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Real_definition_00___x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_npowRec___at___00generalRadiiPolynomial_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_I__F___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_I__E___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_npowRec___at___00generalRadiiPolynomial_spec__0(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_I__E___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_I__E(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_I__E___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_I__E___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_I__E(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_I__F(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_I__E___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_I__F___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_I__F(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_NewtonLikeMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_NormedAddCommGroup_toNormedAddGroup___redArg(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
lean_inc(x_4);
x_8 = lean_apply_1(x_3, x_4);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_apply_2(x_7, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_NewtonLikeMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_NewtonLikeMap___redArg(x_3, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_NewtonLikeMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_NewtonLikeMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_npowRec___at___00generalRadiiPolynomial_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Real_definition_00___x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_inc(x_2);
x_8 = l_npowRec___at___00generalRadiiPolynomial_spec__0(x_7, x_2);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_generalRadiiPolynomial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_5);
x_6 = lean_apply_1(x_4, x_5);
x_7 = lean_unsigned_to_nat(2u);
lean_inc(x_5);
x_8 = l_npowRec___at___00generalRadiiPolynomial_spec__0(x_7, x_5);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Real_definition_00___x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_13, 0, x_3);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_5);
x_16 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_npowRec___at___00generalRadiiPolynomial_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_npowRec___at___00generalRadiiPolynomial_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Z__bound__general(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_inc(x_4);
x_6 = lean_apply_1(x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_radiiPolynomial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_4);
x_5 = lean_apply_1(x_3, x_4);
x_6 = lean_unsigned_to_nat(2u);
lean_inc(x_4);
x_7 = l_npowRec___at___00generalRadiiPolynomial_spec__0(x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Real_definition_00___x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
x_10 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_4);
x_13 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Z__bound(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_simpleRadiiPolynomial___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Real_definition_00___x40_Mathlib_Data_Real_Basic_6358291____hygCtx___hyg_2_;
x_2 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_simpleRadiiPolynomial(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_simpleRadiiPolynomial___closed__0;
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_alloc_closure((void*)(l_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Analysis_Calculus_Deriv_Mul(uint8_t builtin);
lean_object* initialize_Mathlib_Analysis_Calculus_FDeriv_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Analysis_Calculus_MeanValue(uint8_t builtin);
lean_object* initialize_Mathlib_Topology_MetricSpace_Contracting(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RadiiPolynomial_RadiiPolyGeneral(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_Deriv_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_FDeriv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Calculus_MeanValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_MetricSpace_Contracting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_I__E___closed__0 = _init_l_I__E___closed__0();
lean_mark_persistent(l_I__E___closed__0);
l_simpleRadiiPolynomial___closed__0 = _init_l_simpleRadiiPolynomial___closed__0();
lean_mark_persistent(l_simpleRadiiPolynomial___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
