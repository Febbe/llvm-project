; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -mtriple riscv32 -mattr=+d,+zvfh,+v < %s \
; RUN:    -verify-machineinstrs | FileCheck %s
; RUN: llc -mtriple riscv64 -mattr=+d,+zvfh,+v < %s \
; RUN:    -verify-machineinstrs | FileCheck %s
; RUN: llc -mtriple riscv32 -mattr=+d,+zvfh,+v,+unaligned-vector-mem < %s \
; RUN:    -verify-machineinstrs | FileCheck --check-prefix=FAST %s
; RUN: llc -mtriple riscv64 -mattr=+d,+zvfh,+v,+unaligned-vector-mem < %s \
; RUN:    -verify-machineinstrs | FileCheck --check-prefix=FAST %s


define <vscale x 1 x i32> @unaligned_load_nxv1i32_a1(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv1i32_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vsetvli a1, zero, e8, mf2, ta, ma
; CHECK-NEXT:    vle8.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv1i32_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vsetvli a1, zero, e32, mf2, ta, ma
; FAST-NEXT:    vle32.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i32>, ptr %ptr, align 1
  ret <vscale x 1 x i32> %v
}

define <vscale x 1 x i32> @unaligned_load_nxv1i32_a2(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv1i32_a2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vsetvli a1, zero, e8, mf2, ta, ma
; CHECK-NEXT:    vle8.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv1i32_a2:
; FAST:       # %bb.0:
; FAST-NEXT:    vsetvli a1, zero, e32, mf2, ta, ma
; FAST-NEXT:    vle32.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i32>, ptr %ptr, align 2
  ret <vscale x 1 x i32> %v
}

define <vscale x 1 x i32> @aligned_load_nxv1i32_a4(ptr %ptr) {
; CHECK-LABEL: aligned_load_nxv1i32_a4:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vsetvli a1, zero, e32, mf2, ta, ma
; CHECK-NEXT:    vle32.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_load_nxv1i32_a4:
; FAST:       # %bb.0:
; FAST-NEXT:    vsetvli a1, zero, e32, mf2, ta, ma
; FAST-NEXT:    vle32.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i32>, ptr %ptr, align 4
  ret <vscale x 1 x i32> %v
}

define <vscale x 1 x i64> @unaligned_load_nxv1i64_a1(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv1i64_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl1r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv1i64_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vl1re64.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i64>, ptr %ptr, align 1
  ret <vscale x 1 x i64> %v
}

define <vscale x 1 x i64> @unaligned_load_nxv1i64_a4(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv1i64_a4:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl1r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv1i64_a4:
; FAST:       # %bb.0:
; FAST-NEXT:    vl1re64.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i64>, ptr %ptr, align 4
  ret <vscale x 1 x i64> %v
}

define <vscale x 1 x i64> @aligned_load_nxv1i64_a8(ptr %ptr) {
; CHECK-LABEL: aligned_load_nxv1i64_a8:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl1re64.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_load_nxv1i64_a8:
; FAST:       # %bb.0:
; FAST-NEXT:    vl1re64.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i64>, ptr %ptr, align 8
  ret <vscale x 1 x i64> %v
}

define <vscale x 2 x i64> @unaligned_load_nxv2i64_a1(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv2i64_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv2i64_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re64.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 2 x i64>, ptr %ptr, align 1
  ret <vscale x 2 x i64> %v
}

define <vscale x 2 x i64> @unaligned_load_nxv2i64_a4(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv2i64_a4:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv2i64_a4:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re64.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 2 x i64>, ptr %ptr, align 4
  ret <vscale x 2 x i64> %v
}

define <vscale x 2 x i64> @aligned_load_nxv2i64_a8(ptr %ptr) {
; CHECK-LABEL: aligned_load_nxv2i64_a8:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2re64.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_load_nxv2i64_a8:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re64.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 2 x i64>, ptr %ptr, align 8
  ret <vscale x 2 x i64> %v
}

; Masks should always be aligned
define <vscale x 1 x i1> @unaligned_load_nxv1i1_a1(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv1i1_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vsetvli a1, zero, e8, mf8, ta, ma
; CHECK-NEXT:    vlm.v v0, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv1i1_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vsetvli a1, zero, e8, mf8, ta, ma
; FAST-NEXT:    vlm.v v0, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 1 x i1>, ptr %ptr, align 1
  ret <vscale x 1 x i1> %v
}

define <vscale x 4 x float> @unaligned_load_nxv4f32_a1(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv4f32_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv4f32_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re32.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 4 x float>, ptr %ptr, align 1
  ret <vscale x 4 x float> %v
}

define <vscale x 4 x float> @unaligned_load_nxv4f32_a2(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv4f32_a2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv4f32_a2:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re32.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 4 x float>, ptr %ptr, align 2
  ret <vscale x 4 x float> %v
}

define <vscale x 4 x float> @aligned_load_nxv4f32_a4(ptr %ptr) {
; CHECK-LABEL: aligned_load_nxv4f32_a4:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2re32.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_load_nxv4f32_a4:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re32.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 4 x float>, ptr %ptr, align 4
  ret <vscale x 4 x float> %v
}

define <vscale x 8 x half> @unaligned_load_nxv8f16_a1(ptr %ptr) {
; CHECK-LABEL: unaligned_load_nxv8f16_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_load_nxv8f16_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re16.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 8 x half>, ptr %ptr, align 1
  ret <vscale x 8 x half> %v
}

define <vscale x 8 x half> @aligned_load_nxv8f16_a2(ptr %ptr) {
; CHECK-LABEL: aligned_load_nxv8f16_a2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vl2re16.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_load_nxv8f16_a2:
; FAST:       # %bb.0:
; FAST-NEXT:    vl2re16.v v8, (a0)
; FAST-NEXT:    ret
  %v = load <vscale x 8 x half>, ptr %ptr, align 2
  ret <vscale x 8 x half> %v
}

define void @unaligned_store_nxv4i32_a1(<vscale x 4 x i32> %x, ptr %ptr) {
; CHECK-LABEL: unaligned_store_nxv4i32_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vs2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_store_nxv4i32_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vs2r.v v8, (a0)
; FAST-NEXT:    ret
  store <vscale x 4 x i32> %x, ptr %ptr, align 1
  ret void
}

define void @unaligned_store_nxv4i32_a2(<vscale x 4 x i32> %x, ptr %ptr) {
; CHECK-LABEL: unaligned_store_nxv4i32_a2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vs2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_store_nxv4i32_a2:
; FAST:       # %bb.0:
; FAST-NEXT:    vs2r.v v8, (a0)
; FAST-NEXT:    ret
  store <vscale x 4 x i32> %x, ptr %ptr, align 2
  ret void
}

define void @aligned_store_nxv4i32_a4(<vscale x 4 x i32> %x, ptr %ptr) {
; CHECK-LABEL: aligned_store_nxv4i32_a4:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vs2r.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_store_nxv4i32_a4:
; FAST:       # %bb.0:
; FAST-NEXT:    vs2r.v v8, (a0)
; FAST-NEXT:    ret
  store <vscale x 4 x i32> %x, ptr %ptr, align 4
  ret void
}

define void @unaligned_store_nxv1i16_a1(<vscale x 1 x i16> %x, ptr %ptr) {
; CHECK-LABEL: unaligned_store_nxv1i16_a1:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vsetvli a1, zero, e8, mf4, ta, ma
; CHECK-NEXT:    vse8.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: unaligned_store_nxv1i16_a1:
; FAST:       # %bb.0:
; FAST-NEXT:    vsetvli a1, zero, e16, mf4, ta, ma
; FAST-NEXT:    vse16.v v8, (a0)
; FAST-NEXT:    ret
  store <vscale x 1 x i16> %x, ptr %ptr, align 1
  ret void
}

define void @aligned_store_nxv1i16_a2(<vscale x 1 x i16> %x, ptr %ptr) {
; CHECK-LABEL: aligned_store_nxv1i16_a2:
; CHECK:       # %bb.0:
; CHECK-NEXT:    vsetvli a1, zero, e16, mf4, ta, ma
; CHECK-NEXT:    vse16.v v8, (a0)
; CHECK-NEXT:    ret
;
; FAST-LABEL: aligned_store_nxv1i16_a2:
; FAST:       # %bb.0:
; FAST-NEXT:    vsetvli a1, zero, e16, mf4, ta, ma
; FAST-NEXT:    vse16.v v8, (a0)
; FAST-NEXT:    ret
  store <vscale x 1 x i16> %x, ptr %ptr, align 2
  ret void
}
