/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The speed limit of a Dirac state, in any Hilbert space

`TorusDiracBound` proves the speed limit on one closed axis, where the mass term is `m Σ` and
`(m Σ)² = m²`. The argument works for any symmetric `B` that anticommutes with the transport
`A` of the axis and with its velocity `V`, as long as `B` is never smaller than the mass,
`‖Bχ‖² ≥ m² ‖χ‖²`. Let

  `A V = V A`,  `V B = −B V`,  `A B = −B A`,  `V² + A² = 1`,  `(A + B) ψ = E ψ`,  `‖ψ‖ = 1`.

* `‖(A + B)χ‖² = ‖Aχ‖² + ‖Bχ‖²`, so with `a = ‖Aψ‖²`, `E² = a + ‖Bψ‖² ≥ a + m²`.
* `⟨ψ, (V B + B V) ψ⟩ = 0` and `Bψ = Eψ − Aψ` give `E ⟨V⟩ = ⟨V A⟩`.
* `‖V A ψ‖² = ‖Aψ‖² − ‖A²ψ‖² ≤ a − a² = a (1 − a)`, by Cauchy–Schwarz `‖A²ψ‖ ≥ ⟨ψ, A²ψ⟩ = a`.

So `(a + m²) ⟨V⟩² ≤ E² ⟨V⟩² ≤ a (1 − a)` and `|⟨V⟩| ≤ √(1 + m²) − |m|`, for every eigenvector:
no condition on `A²`. The other axes only make `B` larger, and they slow the state down further.
At `|m| = 1/2` the limit is `1/φ`, at `|m| = 1` it is `√2 − 1`.

## Main results

- `DiracSpeed.speedLimit_sq`, `DiracSpeed.speedLimit_half`, `DiracSpeed.speedLimit_one` :
  `r = √(1 + m²) − |m|` solves `r² + 2|m| r = 1`; `r = 1/φ` at `|m| = 1/2`, `√2 − 1` at `|m| = 1`.
- `DiracSpeed.speedLimit_eq_inv_iff` : `r = ρ⁻¹ ↔ ρ − ρ⁻¹ = 2m`.
- `DiracSpeed.speedLimit_sinh`, `DiracSpeed.sinh_log_goldenRatio` : at `m = sinh θ`, `r = e^{−θ}`;
  the mass `1/2` is the rapidity `log φ`.
- `DiracSpeed.norm_sq_add_of_anticomm` : `‖(A + B)χ‖² = ‖Aχ‖² + ‖Bχ‖²` for anticommuting
  symmetric `A`, `B`.
- `DiracSpeed.abs_energy_ge` : if `‖Bχ‖² ≥ m² ‖χ‖²`, every eigenvalue of `A + B` has `|E| ≥ |m|`.
- `DiracSpeed.abs_velocity_le` : `|⟨V⟩| ≤ √(1 + m²) − |m|` for every unit eigenvector of `A + B`.
- `DiracSpeed.norm_sq_ge_of_sq_eq` : a symmetric `S` with `S² = (1 + S)/2` has `‖Sχ‖² ≥ ‖χ‖²/4`.
-/

@[expose] public noncomputable section

open Complex

namespace DiracSpeed

/-! ## 1. The scalar limit -/

/-- `r = √(1 + m²) − |m|` solves `r² + 2|m| r = 1`. -/
theorem speedLimit_sq (m : ℝ) :
    (Real.sqrt (1 + m ^ 2) - |m|) ^ 2 + 2 * |m| * (Real.sqrt (1 + m ^ 2) - |m|) = 1 := by
  have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + m ^ 2)
  have hm : |m| ^ 2 = m ^ 2 := sq_abs m
  nlinarith only [h, hm]

theorem speedLimit_nonneg (m : ℝ) : 0 ≤ Real.sqrt (1 + m ^ 2) - |m| := by
  rw [sub_nonneg, ← Real.sqrt_sq (abs_nonneg m), sq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

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

/-- **The speed limit is the inverse of `ρ` exactly when `ρ − ρ⁻¹ = 2m`**: for `ρ > 0`,
`m ≥ 0`, `√(1 + m²) − m = ρ⁻¹ ↔ ρ − ρ⁻¹ = 2m`. -/
theorem speedLimit_eq_inv_iff {m ρ : ℝ} (hm : 0 ≤ m) (hρ : 0 < ρ) :
    Real.sqrt (1 + m ^ 2) - |m| = ρ⁻¹ ↔ ρ - ρ⁻¹ = 2 * m := by
  rw [abs_of_nonneg hm]
  have hρ' : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ.ne'
  constructor
  · intro h
    have hr := speedLimit_sq m
    rw [abs_of_nonneg hm, h] at hr
    have h2 : (ρ⁻¹ ^ 2 + 2 * m * ρ⁻¹) * ρ = ρ := by rw [hr, one_mul]
    linear_combination (-1 : ℝ) * h2 + (ρ⁻¹ + 2 * m) * hρ'
  · intro h
    have hsq : 1 + m ^ 2 = (ρ⁻¹ + m) ^ 2 := by
      have hm2 : 2 * m * ρ⁻¹ = 1 - ρ⁻¹ ^ 2 := by
        rw [← h]; linear_combination hρ'
      nlinarith only [hm2]
    rw [hsq, Real.sqrt_sq (by positivity)]
    ring

/-- **Rapidity form**: at mass `m = sinh θ`, `θ ≥ 0`, the speed limit is `e^{−θ}`. -/
theorem speedLimit_sinh {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sqrt (1 + Real.sinh θ ^ 2) - |Real.sinh θ| = Real.exp (-θ) := by
  have hs : 0 ≤ Real.sinh θ := by
    rw [Real.sinh_eq]
    have := Real.exp_le_exp.2 (by linarith : -θ ≤ θ)
    linarith
  rw [abs_of_nonneg hs, add_comm, ← Real.cosh_sq, Real.sqrt_sq (Real.cosh_pos θ).le,
    Real.cosh_sub_sinh]

/-- `sinh (log φ) = 1/2`: the mass `1/2` is the rapidity `log φ`. -/
theorem sinh_log_goldenRatio : Real.sinh (Real.log Real.goldenRatio) = 1 / 2 := by
  rw [Real.sinh_eq, Real.exp_log Real.goldenRatio_pos, Real.exp_neg, Real.exp_log
    Real.goldenRatio_pos, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

/-- The scalar step: `(a + m²) v² ≤ a (1 − a)` gives `|v| ≤ √(1 + m²) − |m|`. -/
theorem abs_le_speedLimit {a m v : ℝ} (hm : m ≠ 0) (ha0 : 0 ≤ a)
    (hv : (a + m ^ 2) * v ^ 2 ≤ a * (1 - a)) : |v| ≤ Real.sqrt (1 + m ^ 2) - |m| := by
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

/-! ## 2. Dirac operators -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {A B V : H →ₗ[ℂ] H}

/-- Anticommuting symmetric operators are orthogonal on every state:
`‖(A + B)χ‖² = ‖Aχ‖² + ‖Bχ‖²`. -/
theorem norm_sq_add_of_anticomm (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : ∀ χ, A (B χ) = -B (A χ)) (χ : H) :
    ‖A χ + B χ‖ ^ 2 = ‖A χ‖ ^ 2 + ‖B χ‖ ^ 2 := by
  have h0 : (inner ℂ (A χ) (B χ)).re = 0 := by
    have h1 : inner ℂ (A χ) (B χ) = inner ℂ χ (A (B χ)) := hA χ (B χ)
    have h2 : inner ℂ (B χ) (A χ) = inner ℂ χ (B (A χ)) := hB χ (A χ)
    have h3 : inner ℂ (B χ) (A χ) = (starRingEnd ℂ) (inner ℂ (A χ) (B χ)) :=
      (inner_conj_symm (B χ) (A χ)).symm
    rw [hAB, inner_neg_right, ← h2, h3] at h1
    have := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  rw [norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex, h0]
  ring

/-- **The mass gap**: if `‖Bχ‖² ≥ m² ‖χ‖²` for every `χ`, every eigenvalue of `A + B` has
`|E| ≥ |m|`. -/
theorem abs_energy_ge (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : ∀ χ, A (B χ) = -B (A χ)) {m : ℝ} (hBm : ∀ χ, m ^ 2 * ‖χ‖ ^ 2 ≤ ‖B χ‖ ^ 2)
    {E : ℝ} {ψ : H} (hψ : ψ ≠ 0) (hE : A ψ + B ψ = (E : ℂ) • ψ) : |m| ≤ |E| := by
  have h := norm_sq_add_of_anticomm hA hB hAB ψ
  rw [hE, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow] at h
  have hn : 0 < ‖ψ‖ ^ 2 := by positivity
  have h2 : m ^ 2 * ‖ψ‖ ^ 2 ≤ |E| ^ 2 * ‖ψ‖ ^ 2 := by
    nlinarith only [h, hBm ψ, sq_nonneg ‖A ψ‖]
  have h3 : |m| ^ 2 ≤ |E| ^ 2 := by
    rw [sq_abs]; exact le_of_mul_le_mul_right h2 hn
  exact (pow_le_pow_iff_left₀ (abs_nonneg m) (abs_nonneg E) two_ne_zero).1 h3

/-- **A ring of three is never smaller than `1/2`**: if `S` is symmetric with `S² = (1 + S)/2`
(eigenvalues `1` and `−1/2`), then `‖Sχ‖² ≥ ‖χ‖²/4`. -/
theorem norm_sq_ge_of_sq_eq {S : H →ₗ[ℂ] H} (hS : S.IsSymmetric)
    (h : ∀ χ, S (S χ) = ((1 / 2 : ℝ) : ℂ) • (χ + S χ)) (χ : H) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖S χ‖ ^ 2 := by
  have hre : ∀ η : H, (inner ℂ η η).re = ‖η‖ ^ 2 := fun η => by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) η
  set t := (inner ℂ χ (S χ)).re
  have hT2 : ‖S χ‖ ^ 2 = 1 / 2 * (‖χ‖ ^ 2 + t) := by
    rw [← hre, hS, h, inner_smul_right, Complex.re_ofReal_mul, inner_add_right, Complex.add_re,
      hre]
  have hpos := sq_nonneg ‖S χ + ((1 / 2 : ℝ) : ℂ) • χ‖
  rw [norm_add_sq (𝕜 := ℂ), norm_smul, Complex.norm_real, inner_smul_right,
    RCLike.re_to_complex, Complex.re_ofReal_mul, hS] at hpos
  norm_num at hpos
  nlinarith only [hpos, hT2]

/-- **The speed limit of a Dirac state**: every unit eigenvector of `A + B` moves at most at
`√(1 + m²) − |m|`. -/
theorem abs_velocity_le (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hV : V.IsSymmetric)
    (hAV : ∀ χ, A (V χ) = V (A χ)) (hVB : ∀ χ, V (B χ) = -B (V χ))
    (hAB : ∀ χ, A (B χ) = -B (A χ)) (hVV : ∀ χ, V (V χ) + A (A χ) = χ)
    {m : ℝ} (hm : m ≠ 0) (hBm : ∀ χ, m ^ 2 * ‖χ‖ ^ 2 ≤ ‖B χ‖ ^ 2)
    {E : ℝ} {ψ : H} (hψ : ‖ψ‖ = 1) (hE : A ψ + B ψ = (E : ℂ) • ψ) :
    |(inner ℂ ψ (V ψ)).re| ≤ Real.sqrt (1 + m ^ 2) - |m| := by
  set v := (inner ℂ ψ (V ψ)).re
  set a := ‖A ψ‖ ^ 2
  have hre : ∀ χ : H, (inner ℂ χ χ).re = ‖χ‖ ^ 2 := fun χ => by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) χ
  -- `E² = a + ‖Bψ‖² ≥ a + m²`
  have hE2 : E ^ 2 = a + ‖B ψ‖ ^ 2 := by
    have h := norm_sq_add_of_anticomm hA hB hAB ψ
    rwa [hE, norm_smul, Complex.norm_real, Real.norm_eq_abs, hψ, mul_one, sq_abs] at h
  have hb : m ^ 2 ≤ ‖B ψ‖ ^ 2 := by simpa [hψ] using hBm ψ
  -- `E ⟨V⟩ = ⟨V A⟩`
  set z := inner ℂ ψ (V (A ψ))
  have hBψ : B ψ = (E : ℂ) • ψ - A ψ := by rw [← hE]; abel
  have hw : (E : ℂ) * inner ℂ ψ (V ψ) = z := by
    have h1 : inner ℂ ψ (V (B ψ)) = -inner ℂ (B ψ) (V ψ) := by rw [hVB, inner_neg_right, hB]
    rw [hBψ, map_sub, map_smul, inner_sub_right, inner_smul_right, inner_sub_left,
      inner_smul_left, Complex.conj_ofReal, hA, hAV] at h1
    linear_combination h1 / 2
  have hzre : z.re = E * v := by
    rw [← hw, Complex.re_ofReal_mul]
  -- `‖V A ψ‖² = a − ‖A²ψ‖² ≤ a (1 − a)`
  have hnorm : ‖V (A ψ)‖ ^ 2 = a - ‖A (A ψ)‖ ^ 2 := by
    have h2 : V (V (A ψ)) = A ψ - A (A (A ψ)) := eq_sub_of_add_eq (hVV (A ψ))
    rw [← hre, hV, h2, inner_sub_right, Complex.sub_re, hre, ← hA (A ψ) (A (A ψ)), hre]
  have hA2 : a ^ 2 ≤ ‖A (A ψ)‖ ^ 2 := by
    have h1 : a = (inner ℂ ψ (A (A ψ))).re := by rw [← hA, hre]
    have h2 := norm_inner_le_norm (𝕜 := ℂ) ψ (A (A ψ))
    rw [hψ, one_mul] at h2
    have h3 := (Complex.abs_re_le_norm (inner ℂ ψ (A (A ψ)))).trans h2
    rw [← h1] at h3
    rw [← sq_abs a]
    exact pow_le_pow_left₀ (abs_nonneg a) h3 2
  have hz : z.re ^ 2 ≤ ‖V (A ψ)‖ ^ 2 := by
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ψ (V (A ψ))
    rw [hψ, one_mul] at h1
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((Complex.abs_re_le_norm z).trans h1) 2
  have ha0 : 0 ≤ a := by positivity
  have hv : (a + m ^ 2) * v ^ 2 ≤ a * (1 - a) := by
    have h1 : E ^ 2 * v ^ 2 = z.re ^ 2 := by rw [hzre]; ring
    nlinarith only [h1, hz, hnorm, hA2, hE2, hb, sq_nonneg v]
  exact abs_le_speedLimit hm ha0 hv

end DiracSpeed
