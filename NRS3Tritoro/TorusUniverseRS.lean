/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusUniverse

/-!
# Robertson–Schrödinger on the axis of the universe

On the axis `ZMod L` of the universe take the transport `T°` and a coordinate `X` (`chart x`).
Both are symmetric: `T° = (S + S⁻¹)/2` with the shift `S` unitary, `X` real diagonal. The
Robertson–Schrödinger surplus

  `Var T° · Var X − Cov² − (⟨i[T°, X]⟩/2)²`

is the Cauchy–Schwarz gap `‖T̃ψ‖² ‖X̃ψ‖² − |⟨T̃ψ, X̃ψ⟩|²` of the two fluctuations, so it is never
negative, and it vanishes with `X̃ψ ≠ 0` exactly when `T̃ψ = κ X̃ψ` for some `κ ∈ ℂ` (`D23`).

## Main results

- `TorusUniverse.transport_isSymmetric`, `TorusUniverse.chart_isSymmetric` : `T°`, `X` symmetric.
- `TorusUniverse.surplus_eq` : the surplus is the Cauchy–Schwarz gap.
- `TorusUniverse.surplus_nonneg` : Robertson–Schrödinger on the axis of the universe.
- `TorusUniverse.exists_parallel_of_surplus_eq_zero` : saturation is `T̃ψ = κ X̃ψ`.
-/

@[expose] public noncomputable section

open Complex PathGraph3DNRS SpectralExtremal

namespace TorusUniverse

variable {L : ℕ}

/-! ## 1. The shift -/

/-- The shift `(Sψ)_j = ψ_{j+1}`. -/
def shift : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun j => ψ (j + 1)
  map_add' ψ φ := by ext j; simp only [PiLp.add_apply]
  map_smul' c ψ := by ext j; simp only [PiLp.smul_apply, RingHom.id_apply]

/-- The inverse shift `(S⁻¹ψ)_j = ψ_{j−1}`. -/
def shiftInv : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun j => ψ (j - 1)
  map_add' ψ φ := by ext j; simp only [PiLp.add_apply]
  map_smul' c ψ := by ext j; simp only [PiLp.smul_apply, RingHom.id_apply]

theorem shift_apply (ψ : HU L) (j : ZMod L) : shift ψ j = ψ (j + 1) := rfl

theorem shiftInv_apply (ψ : HU L) (j : ZMod L) : shiftInv ψ j = ψ (j - 1) := rfl

theorem shift_shiftInv (ψ : HU L) : shift (shiftInv ψ) = ψ := by
  ext j; simp only [shift_apply, shiftInv_apply, add_sub_cancel_right]

theorem transport_eq (ψ : HU L) : transport ψ = (1 / 2 : ℂ) • (shift ψ + shiftInv ψ) := by
  ext j
  simp only [transport_apply, PiLp.smul_apply, PiLp.add_apply, shift_apply, shiftInv_apply,
    smul_eq_mul]
  ring

theorem current_eq (ψ : HU L) : current ψ = (I / 2) • (shift ψ - shiftInv ψ) := by
  ext j
  simp only [current_apply, PiLp.smul_apply, PiLp.sub_apply, shift_apply, shiftInv_apply,
    smul_eq_mul]

variable [NeZero L]

theorem inner_shift (φ ψ : HU L) : inner ℂ φ (shift ψ) = inner ℂ (shiftInv φ) ψ := by
  simp only [PiLp.inner_apply, shift_apply, shiftInv_apply]
  rw [← sum_sub_one fun j => inner ℂ (φ j) (ψ (j + 1))]
  simp only [sub_add_cancel]

theorem inner_shiftInv (φ ψ : HU L) : inner ℂ φ (shiftInv ψ) = inner ℂ (shift φ) ψ := by
  simp only [PiLp.inner_apply, shift_apply, shiftInv_apply]
  rw [← sum_add_one fun j => inner ℂ (φ j) (ψ (j - 1))]
  simp only [add_sub_cancel_right]

/-- **The shift is unitary**: `‖Sψ‖ = ‖ψ‖`. -/
theorem norm_shift (ψ : HU L) : ‖shift ψ‖ = ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [shift_apply]
  rw [sum_add_one fun j => ‖ψ j‖ ^ 2]

/-! ## 2. Transport and coordinate are symmetric -/

theorem transport_isSymmetric : (transport : HU L →ₗ[ℂ] HU L).IsSymmetric := by
  intro φ ψ
  rw [transport_eq, transport_eq, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, inner_shift, inner_shiftInv]
  simp only [map_div₀, map_one, map_ofNat]
  ring

theorem chart_isSymmetric (x : ZMod L → ℝ) : (chart x : HU L →ₗ[ℂ] HU L).IsSymmetric := by
  intro φ ψ
  simp only [PiLp.inner_apply, chart_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## 3. The surplus is a Cauchy–Schwarz gap -/

/-- The Robertson–Schrödinger surplus of `(T°, X)`. -/
def surplus (x : ZMod L → ℝ) (ψ : HU L) : ℝ :=
  varianceG transport ψ * varianceG (chart x) ψ - covarianceG transport (chart x) ψ ^ 2 -
    (tensionG transport (chart x) ψ / 2) ^ 2

/-- For symmetric `A`, `B` and a unit state, `|⟨Ãψ, B̃ψ⟩|² = Cov² + (⟨i[A, B]⟩/2)²`. -/
theorem norm_sq_inner_centered {A B : HU L →ₗ[ℂ] HU L} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    ‖inner ℂ (centeredG A ψ) (centeredG B ψ)‖ ^ 2 =
      covarianceG A B ψ ^ 2 + (tensionG A B ψ / 2) ^ 2 := by
  set z := inner ℂ (A ψ) (B ψ)
  have hAψ : inner ℂ (A ψ) ψ = (meanG A ψ : ℂ) := by
    apply Complex.ext
    · rw [meanG, ← inner_conj_symm, Complex.conj_re, Complex.ofReal_re]
    · have h := hA.im_inner_apply_self ψ
      rw [RCLike.im_to_complex] at h
      rw [h, Complex.ofReal_im]
  have hBψ : inner ℂ ψ (B ψ) = (meanG B ψ : ℂ) := by
    apply Complex.ext
    · rw [meanG, Complex.ofReal_re]
    · have h := hB.im_inner_self_apply ψ
      rw [RCLike.im_to_complex] at h
      rw [h, Complex.ofReal_im]
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hc : inner ℂ (centeredG A ψ) (centeredG B ψ) = z - (meanG A ψ * meanG B ψ : ℝ) := by
    simp only [centeredG, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hAψ, hBψ, hψψ, Complex.conj_ofReal]
    push_cast
    ring
  have ht : tensionG A B ψ = -2 * z.im := by
    have h1 : inner ℂ ψ (A (B ψ)) = z := (hA ψ (B ψ)).symm
    have h2 : inner ℂ ψ (B (A ψ)) = (starRingEnd ℂ) z := by
      rw [← hB ψ (A ψ), inner_conj_symm]
    simp only [tensionG, observableTension, opCommutator, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_right, inner_sub_right, h1, h2,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [covarianceG, hc, ht, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The surplus is the Cauchy–Schwarz gap** of the two fluctuations. -/
theorem surplus_eq (x : ZMod L → ℝ) {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    surplus x ψ = ‖centeredG transport ψ‖ ^ 2 * ‖centeredG (chart x) ψ‖ ^ 2 -
      ‖inner ℂ (centeredG transport ψ) (centeredG (chart x) ψ)‖ ^ 2 := by
  rw [norm_sq_inner_centered transport_isSymmetric (chart_isSymmetric x) hψ, surplus,
    varianceG, varianceG]
  ring

/-- **Robertson–Schrödinger on the axis of the universe**: the surplus is never negative. -/
theorem surplus_nonneg (x : ZMod L → ℝ) {ψ : HU L} (hψ : ‖ψ‖ = 1) : 0 ≤ surplus x ψ := by
  rw [surplus_eq x hψ, ← mul_pow]
  have := norm_inner_le_norm (𝕜 := ℂ) (centeredG transport ψ) (centeredG (chart x) ψ)
  have h0 := norm_nonneg (inner ℂ (centeredG transport ψ) (centeredG (chart x) ψ))
  nlinarith

/-- **Saturation is parallel fluctuations**: a vanishing surplus with `X̃ψ ≠ 0` gives
`T̃ψ = κ X̃ψ`. -/
theorem exists_parallel_of_surplus_eq_zero (x : ZMod L → ℝ) {ψ : HU L} (hψ : ‖ψ‖ = 1)
    (hs : surplus x ψ = 0) (hX : centeredG (chart x) ψ ≠ 0) :
    ∃ κ : ℂ, centeredG transport ψ = κ • centeredG (chart x) ψ := by
  rw [surplus_eq x hψ, ← mul_pow, sub_eq_zero] at hs
  have h := (pow_left_inj₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hs
  rw [← norm_inner_symm, mul_comm] at h
  rcases ((norm_inner_eq_norm_tfae (𝕜 := ℂ) (centeredG (chart x) ψ)
    (centeredG transport ψ)).out 1 3).1 h.symm with h0 | h1
  · exact absurd h0 hX
  · exact h1

end TorusUniverse
