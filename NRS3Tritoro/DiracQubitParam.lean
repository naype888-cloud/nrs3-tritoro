/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.DiracQubit

/-!
# The Dirac qubit: the state of every speed, and the fastest one

For `0 ≤ t ≤ r = √(1 + m²) − |m|`, `speedParam t m` is the root `a` of
`a² − (1 − t²) a + t² m² = 0`; the upper eigenstate `speedState a m` with `s = −√(1 − a)` moves
exactly at `t`. At `t = r` the root is `a = |m| r`, and no other `a` reaches `r`.

## Main results

- `DiracQubit.velocity_speedState_param` : the state of speed `t`, for every `0 ≤ t ≤ r`.
- `DiracQubit.speedParam_speedLimit`, `DiracQubit.eq_of_velocity_eq_speedLimit` : the limit is
  reached at `a = |m| r`, and only there.
-/

@[expose] public noncomputable section

namespace DiracQubit

/-- For `0 ≤ t ≤ r`, the root `a = ((1 − t²) − √((1 − t²)² − 4t²m²))/2`. -/
def speedParam (t m : ℝ) : ℝ :=
  ((1 - t ^ 2) - Real.sqrt ((1 - t ^ 2) ^ 2 - 4 * t ^ 2 * m ^ 2)) / 2

section Param

variable {t m : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.sqrt (1 + m ^ 2) - |m|)
include ht0 ht

theorem one_sub_sq_ge : 2 * t * |m| ≤ 1 - t ^ 2 := by
  have hr := DiracSpeed.speedLimit_sq m
  have hr0 := DiracSpeed.speedLimit_nonneg m
  have hm0 := abs_nonneg m
  nlinarith only [hr, ht, ht0, hm0, hr0, mul_nonneg (sub_nonneg.2 ht) (add_nonneg hr0 ht0)]

theorem disc_nonneg : 0 ≤ (1 - t ^ 2) ^ 2 - 4 * t ^ 2 * m ^ 2 := by
  have h := one_sub_sq_ge ht0 ht
  have hm0 := abs_nonneg m
  have h2 : 0 ≤ 1 - t ^ 2 + 2 * t * |m| := by nlinarith only [h, ht0, hm0]
  have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  rw [hm2]
  nlinarith only [mul_nonneg (sub_nonneg.2 h) h2]

theorem speedParam_nonneg : 0 ≤ speedParam t m := by
  have h := one_sub_sq_ge ht0 ht
  have hd := disc_nonneg ht0 ht
  have hle : Real.sqrt ((1 - t ^ 2) ^ 2 - 4 * t ^ 2 * m ^ 2) ≤ 1 - t ^ 2 := by
    have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith only [h, ht0, abs_nonneg m]
    calc Real.sqrt ((1 - t ^ 2) ^ 2 - 4 * t ^ 2 * m ^ 2) ≤ Real.sqrt ((1 - t ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (t * m)])
      _ = 1 - t ^ 2 := Real.sqrt_sq h1
  unfold speedParam; linarith

omit ht0 ht in
theorem speedParam_le_one : speedParam t m ≤ 1 := by
  have := Real.sqrt_nonneg ((1 - t ^ 2) ^ 2 - 4 * t ^ 2 * m ^ 2)
  unfold speedParam; nlinarith only [this, sq_nonneg t]

/-- The root: `a (1 − a) = t² (a + m²)`. -/
theorem speedParam_root :
    speedParam t m * (1 - speedParam t m) = t ^ 2 * (speedParam t m + m ^ 2) := by
  have hd := Real.sq_sqrt (disc_nonneg ht0 ht)
  unfold speedParam
  linear_combination (-1 / 4 : ℝ) * hd

/-- **The state of speed `t`**: at `a = speedParam t m`, `s = −√(1 − a)`, the upper eigenstate
moves exactly at `t`. -/
theorem velocity_speedState_param (hm : m ≠ 0) :
    velocity (-Real.sqrt (1 - speedParam t m)) (speedState (speedParam t m) m) = t := by
  have ha := speedParam_nonneg ht0 ht
  have ha1 := speedParam_le_one (t := t) (m := m)
  have hroot := speedParam_root ht0 ht
  rw [velocity_speedState ha hm, neg_neg]
  set a := speedParam t m
  have hE := energy_sq (m := m) ha
  have hE0 : 0 < energy a m := Real.sqrt_pos.2 (by have := sq_pos_of_ne_zero hm; linarith)
  have hv0 : 0 ≤ Real.sqrt (1 - a) * Real.sqrt a / energy a m := by positivity
  have hv2 : (Real.sqrt (1 - a) * Real.sqrt a / energy a m) ^ 2 = t ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt ha, hE,
      div_eq_iff (by have := sq_pos_of_ne_zero hm; linarith)]
    linarith only [hroot]
  nlinarith only [hv0, hv2, ht0, sq_nonneg (Real.sqrt (1 - a) * Real.sqrt a / energy a m - t)]

end Param

/-- **The speed limit is reached at `a = |m| r`**. -/
theorem speedParam_speedLimit (m : ℝ) :
    speedParam (Real.sqrt (1 + m ^ 2) - |m|) m = |m| * (Real.sqrt (1 + m ^ 2) - |m|) := by
  have hr := DiracSpeed.speedLimit_sq m
  set r := Real.sqrt (1 + m ^ 2) - |m|
  have hd : (1 - r ^ 2) ^ 2 - 4 * r ^ 2 * m ^ 2 = 0 := by
    have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
    rw [hm2]
    have h1 : 1 - r ^ 2 = 2 * |m| * r := by linarith only [hr]
    rw [h1]; ring
  unfold speedParam
  rw [hd, Real.sqrt_zero]
  linarith only [hr]

/-- **And only there**: if the state at `a` moves at the limit `r`, then `a = |m| r`. -/
theorem eq_of_velocity_eq_speedLimit {a m : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hm : m ≠ 0)
    (h : velocity (-Real.sqrt (1 - a)) (speedState a m) = Real.sqrt (1 + m ^ 2) - |m|) :
    a = |m| * (Real.sqrt (1 + m ^ 2) - |m|) := by
  have hr := DiracSpeed.speedLimit_sq m
  set r := Real.sqrt (1 + m ^ 2) - |m|
  rw [velocity_speedState ha hm, neg_neg] at h
  have hE := energy_sq (m := m) ha
  have hE0 : 0 < energy a m := Real.sqrt_pos.2 (by have := sq_pos_of_ne_zero hm; linarith)
  have h2 : (1 - a) * a = r ^ 2 * (a + m ^ 2) := by
    have := congrArg (· ^ 2) h
    simp only [div_pow, mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 - a),
      Real.sq_sqrt ha, hE] at this
    rw [div_eq_iff (by have := sq_pos_of_ne_zero hm; linarith)] at this
    linarith only [this]
  have hm2 : |m| ^ 2 = m ^ 2 := sq_abs m
  have key : (a - |m| * r) ^ 2 = 0 := by linear_combination -h2 - a * hr + r ^ 2 * hm2
  nlinarith only [key, sq_nonneg (a - |m| * r)]

end DiracQubit
