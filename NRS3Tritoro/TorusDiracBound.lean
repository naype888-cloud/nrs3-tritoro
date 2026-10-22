/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusDirac
public import NRS3Tritoro.TorusUniverseIsolation
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The speed limit of a massive Dirac state

On the axis of the universe (`L` even) let `D_m ψ = E ψ` with `m ≠ 0` and `a = ‖T°ψ‖²`. Then
`T°² ψ = a ψ`, `K² ψ = (1 − a) ψ` and `E² = a + m²`. The staggered sign reverses the velocity, and
`m Σψ = (E − T°)ψ`, so `E ⟨K⟩ = ⟨K T°⟩`; with `‖K T° ψ‖² = a (1 − a)`,

  `(a + m²) ⟨K⟩² ≤ a (1 − a)`.

Put `r = √(1 + m²) − |m|`, so `r² + 2|m| r = 1`. Then `r² (a + m²) − a (1 − a) = (a − |m| r)²`, and

  `|⟨K⟩| ≤ √(1 + m²) − |m| < 1`:

the mass sets how far below the cone a stationary state stays. At `m = 1/2` the limit is
`√5/2 − 1/2 = 1/φ`; at `m = 1` it is `√2 − 1`.

## Main results

- `TorusUniverse.transport_current`, `TorusUniverse.transport_sq_add_current_sq` : `T°` and `K`
  commute, and `T°² + K² = 1`.
- `TorusUniverse.abs_velocity_le_of_dirac` : `|⟨K⟩| ≤ √(1 + m²) − |m|` for an eigenvector of
  `D_m`.
- `TorusUniverse.speedLimit_half`, `TorusUniverse.abs_velocity_le_inv_goldenRatio` : mass `1/2`,
  speed at most `1/φ`.
- `TorusUniverse.speedLimit_one`, `TorusUniverse.abs_velocity_le_sqrt_two_sub_one` : mass `1`,
  speed at most `√2 − 1`.
-/

@[expose] public noncomputable section

open Complex

namespace TorusUniverse

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
/-- `T°` and `K` commute. -/
theorem transport_current (ψ : HU L) : transport (current ψ) = current (transport ψ) := by
  ext j
  simp only [transport_apply, current_apply, add_sub_cancel_right, sub_add_cancel]
  ring

omit [NeZero L] in
/-- **`T°² + K² = 1`**, as operators. -/
theorem transport_sq_add_current_sq (ψ : HU L) :
    transport (transport ψ) + current (current ψ) = ψ := by
  ext j
  simp only [PiLp.add_apply, transport_apply, current_apply, add_sub_cancel_right, sub_add_cancel]
  linear_combination ((ψ (j + 1 + 1) + ψ (j - 1 - 1)) / 4 - ψ j / 2) * Complex.I_sq

theorem current_isSymmetric : (current : HU L →ₗ[ℂ] HU L).IsSymmetric := by
  intro φ ψ
  rw [current_eq, current_eq, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    inner_shift, inner_shiftInv]
  simp only [map_div₀, Complex.conj_I, map_ofNat]
  ring

/-- `r = √(1 + m²) − |m|` solves `r² + 2|m| r = 1`. -/
theorem speedLimit_sq (m : ℝ) :
    (Real.sqrt (1 + m ^ 2) - |m|) ^ 2 + 2 * |m| * (Real.sqrt (1 + m ^ 2) - |m|) = 1 := by
  have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + m ^ 2)
  have hm : |m| ^ 2 = m ^ 2 := sq_abs m
  nlinarith only [h, hm]

theorem speedLimit_nonneg (m : ℝ) : 0 ≤ Real.sqrt (1 + m ^ 2) - |m| := by
  rw [sub_nonneg, ← Real.sqrt_sq (abs_nonneg m), sq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **The speed limit of a massive Dirac state**: an eigenvector of `D_m`, `m ≠ 0`, moves at
most at `√(1 + m²) − |m|`. -/
theorem abs_velocity_le_of_dirac (h2 : 2 ∣ L) {m : ℝ} (hm : m ≠ 0) {E : ℝ} {ψ : HU L}
    (hψ : ‖ψ‖ = 1) (hE : dirac m ψ = (E : ℂ) • ψ) :
    |velocity ψ| ≤ Real.sqrt (1 + m ^ 2) - |m| := by
  set v := velocity ψ
  set a := ‖transport ψ‖ ^ 2 with ha_def
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  -- `T°² ψ = (E² − m²) ψ` and `a = E² − m²`
  have hTT : transport (transport ψ) = ((E ^ 2 - m ^ 2 : ℝ) : ℂ) • ψ := by
    have h := dirac_sq h2 m ψ
    rw [hE, map_smul, hE, smul_smul] at h
    have h' : transport (transport ψ) = ((E : ℂ) * E) • ψ - ((m : ℂ) ^ 2) • ψ := by
      rw [h]; abel
    rw [h', ← sub_smul]
    push_cast
    ring_nf
  have ha : a = E ^ 2 - m ^ 2 := by
    have h1 : (inner ℂ (transport ψ) (transport ψ)).re = a := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← h1, transport_isSymmetric, hTT, inner_smul_right, hψψ, mul_one, Complex.ofReal_re]
  have hE2 : E ^ 2 = a + m ^ 2 := by linarith
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    have := norm_transport_le ψ
    rw [hψ] at this
    nlinarith only [this, norm_nonneg (transport ψ)]
  -- the velocity is odd under `Σ`, and `m Σψ = Eψ − T°ψ`
  have hmS : (m : ℂ) • stagger ψ = (E : ℂ) • ψ - transport ψ := by
    have h : dirac m ψ = transport ψ + (m : ℂ) • stagger ψ := rfl
    rw [hE] at h
    rw [h]; abel
  set z := inner ℂ ψ (current (transport ψ))
  have hTK : inner ℂ (transport ψ) (current ψ) = z := by
    rw [transport_isSymmetric, transport_current]
  have hTKT : inner ℂ (transport ψ) (current (transport ψ)) =
      ((E ^ 2 - m ^ 2 : ℝ) : ℂ) * inner ℂ ψ (current ψ) := by
    rw [transport_isSymmetric, transport_current, hTT, map_smul, inner_smul_right]
  have hodd : m ^ 2 * (-v) = E ^ 2 * v - 2 * E * z.re + (E ^ 2 - m ^ 2) * v := by
    have h1 : velocity ((m : ℂ) • stagger ψ) = m ^ 2 * (-v) := by
      rw [velocity_smul, velocity_stagger h2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [← h1, hmS, velocity]
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, hTK, hTKT]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, v, velocity]
    ring
  have hE0 : E ≠ 0 := by
    rintro rfl
    have : 0 < m ^ 2 := by positivity
    linarith
  have hw : z.re = E * v := by
    have h : 2 * E * z.re = 2 * E * (E * v) := by linear_combination hodd
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hE0) h
  -- `‖K T° ψ‖² = a (1 − a)`
  have hKKT : current (current (transport ψ)) = ((1 - a : ℝ) : ℂ) • transport ψ := by
    have h := transport_sq_add_current_sq (transport ψ)
    rw [hTT, map_smul] at h
    calc current (current (transport ψ))
        = transport ψ - ((E ^ 2 - m ^ 2 : ℝ) : ℂ) • transport ψ := by
          rw [eq_sub_iff_add_eq, add_comm]; exact h
      _ = ((1 - a : ℝ) : ℂ) • transport ψ := by rw [ha]; push_cast; module
  have hnorm : ‖current (transport ψ)‖ ^ 2 = a * (1 - a) := by
    have h1 : (inner ℂ (current (transport ψ)) (current (transport ψ))).re =
        ‖current (transport ψ)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← h1, current_isSymmetric, hKKT, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    norm_cast
    simp only [← ha_def]
    rw [mul_comm]
    rfl
  have hz : z.re ^ 2 ≤ a * (1 - a) := by
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ψ (current (transport ψ))
    rw [hψ, one_mul] at h1
    have h2 := Complex.abs_re_le_norm z
    rw [← hnorm, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h2.trans h1) 2
  -- the scalar step: a perfect square
  have hv : (a + m ^ 2) * v ^ 2 ≤ a * (1 - a) := by
    rw [← hE2, show E ^ 2 * v ^ 2 = z.re ^ 2 by rw [hw]; ring]
    exact hz
  have hr := speedLimit_sq m
  have hr0 := speedLimit_nonneg m
  set r := Real.sqrt (1 + m ^ 2) - |m|
  have hsq : a * (1 - a) ≤ r ^ 2 * (a + m ^ 2) := by
    have hm2 : |m| ^ 2 = m ^ 2 := sq_abs m
    have key : r ^ 2 * (a + m ^ 2) - a * (1 - a) = (a - |m| * r) ^ 2 := by
      linear_combination a * hr - r ^ 2 * hm2
    linarith only [key, sq_nonneg (a - |m| * r)]
  have hpos : 0 < a + m ^ 2 := by positivity
  have hvr : v ^ 2 ≤ r ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hpos
    calc (a + m ^ 2) * v ^ 2 ≤ a * (1 - a) := hv
      _ ≤ r ^ 2 * (a + m ^ 2) := hsq
      _ = (a + m ^ 2) * r ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (abs_nonneg v) hr0 two_ne_zero).1 (by rw [sq_abs]; exact hvr)

/-- **At mass `1/2` the speed limit is `1/φ`**: `√(1 + 1/4) − 1/2 = (√5 − 1)/2`. -/
theorem speedLimit_half {m : ℝ} (hm : |m| = 1 / 2) :
    Real.sqrt (1 + m ^ 2) - |m| = Real.goldenRatio⁻¹ := by
  have hm2 : m ^ 2 = 1 / 4 := by rw [← sq_abs, hm]; norm_num
  have h5 : Real.sqrt (1 + m ^ 2) = Real.sqrt 5 / 2 := by
    rw [hm2, show (1 + 1 / 4 : ℝ) = (Real.sqrt 5 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  rw [h5, hm, Real.inv_goldenRatio, Real.goldenConj]
  ring

/-- At mass `1` the speed limit is `√2 − 1`. -/
theorem speedLimit_one {m : ℝ} (hm : |m| = 1) : Real.sqrt (1 + m ^ 2) - |m| = Real.sqrt 2 - 1 := by
  have hm2 : m ^ 2 = 1 := by rw [← sq_abs, hm]; norm_num
  rw [hm2, hm]
  norm_num

/-- **Mass `1/2`, speed `1/φ`**: an eigenvector of `D_m` with `|m| = 1/2` moves at most at
`1/φ`. -/
theorem abs_velocity_le_inv_goldenRatio (h2 : 2 ∣ L) {m : ℝ} (hm : |m| = 1 / 2) {E : ℝ}
    {ψ : HU L} (hψ : ‖ψ‖ = 1) (hE : dirac m ψ = (E : ℂ) • ψ) :
    |velocity ψ| ≤ Real.goldenRatio⁻¹ := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  rw [← speedLimit_half hm]
  exact abs_velocity_le_of_dirac h2 hm0 hψ hE

/-- Mass `1`, speed `√2 − 1`. -/
theorem abs_velocity_le_sqrt_two_sub_one (h2 : 2 ∣ L) {m : ℝ} (hm : |m| = 1) {E : ℝ}
    {ψ : HU L} (hψ : ‖ψ‖ = 1) (hE : dirac m ψ = (E : ℂ) • ψ) :
    |velocity ψ| ≤ Real.sqrt 2 - 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  rw [← speedLimit_one hm]
  exact abs_velocity_le_of_dirac h2 hm0 hψ hE

end TorusUniverse
