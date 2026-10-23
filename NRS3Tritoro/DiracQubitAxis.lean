/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.DiracQubit
public import NRS3Tritoro.FiberDiracAxis

/-!
# The Dirac qubit is the two-wave block of the axis of the universe

On the axis `ZMod L` (`L` even) take a lattice momentum `u`, `u^L = 1`, `|u| = 1`, and the waves
`e_u`, `e_{−u}`. Then `T° e_u = (Re u) e_u`, `K e_u = −(Im u) e_u`, `Σ e_u = e_{−u}`, and the
embedding

  `ι χ = χ₀ e_u + χ₁ e_{−u}`

carries the Dirac qubit at `c = Re u`, `s = Im u` (`DiracQubit`) into the axis exactly: it is an
isometry, `D_m (ι χ) = ι (H χ)` and the velocity of `ι χ` is the velocity of `χ`. With the
rotating mode of the fiber, `ι χ ⊗ v` is an eigenstate of the Dirac operator of the axis with the
fiber (`FiberDiracAxis`) whenever `χ` is an eigenstate of the qubit of mass `−1/2`.

The momenta of a finite axis are the roots of unity; the qubit takes every momentum.

## Main results

- `DiracQubitAxis.transport_wave`, `DiracQubitAxis.current_wave` : `T° = Re u`, `K = −Im u` on
  `e_u`.
- `DiracQubitAxis.norm_embed` : `ι` is an isometry.
- `DiracQubitAxis.dirac_embed` : `D_m (ι χ) = ι (H χ)`.
- `DiracQubitAxis.velocity_embed` : `⟨K⟩_{ι χ} = ⟨V⟩_χ`.
- `DiracQubitAxis.fiberDirac_tensor_embed` : `ι χ ⊗ v` is an eigenstate of `D` of the axis with
  the fiber.
-/

@[expose] public noncomputable section

open Complex TorusUniverse

namespace DiracQubitAxis

variable {L : ℕ} [NeZero L] {u : ℂ} (hL : u ^ L = 1) (hn : ‖u‖ = 1)

/-! ## 1. Waves of any lattice momentum -/

section Wave

include hL in
theorem pow_val_add_one (j : ZMod L) : u ^ (j + 1).val = u * u ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hL, pow_add, ZMod.val_one_eq_one_mod,
    ← pow_eq_pow_mod _ hL, pow_one, mul_comm]

include hn in
theorem ne_zero : u ≠ 0 := by
  rintro rfl; simp at hn

include hL hn in
theorem pow_val_sub_one (j : ZMod L) : u ^ (j - 1).val = u⁻¹ * u ^ j.val := by
  have h := pow_val_add_one hL (j - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (ne_zero hn), one_mul]

include hn in
theorem inv_eq_conj : u⁻¹ = (starRingEnd ℂ) u := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp

include hL hn in
/-- `T° e_u = (Re u) e_u`. -/
theorem transport_wave : transport (wave L u) = (u.re : ℂ) • wave L u := by
  ext j
  simp only [transport_apply, wave_apply, PiLp.smul_apply, smul_eq_mul, pow_val_add_one hL,
    pow_val_sub_one hL hn, inv_eq_conj hn]
  have h := Complex.add_conj u
  push_cast at h
  linear_combination (u ^ j.val / (Real.sqrt L : ℂ) / 2) * h

include hL hn in
/-- `K e_u = −(Im u) e_u`. -/
theorem current_wave : current (wave L u) = (-(u.im : ℂ)) • wave L u := by
  ext j
  simp only [current_apply, wave_apply, PiLp.smul_apply, smul_eq_mul, pow_val_add_one hL,
    pow_val_sub_one hL hn, inv_eq_conj hn]
  have h := Complex.sub_conj u
  push_cast at h
  linear_combination (I / 2 * (u ^ j.val / (Real.sqrt L : ℂ))) * h +
    ((u.im : ℂ) * (u ^ j.val / (Real.sqrt L : ℂ))) * Complex.I_sq

include hn in
theorem norm_wave : ‖wave L u‖ = 1 := by
  have h : ‖wave L u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [wave_apply, norm_div, norm_pow, hn, one_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    field_simp
  nlinarith [norm_nonneg (wave L u)]

include hn in
/-- The waves `e_{−u}` and `e_u` are orthogonal when `L` is even. -/
theorem inner_wave_neg (h2 : 2 ∣ L) : inner ℂ (wave L (-u)) (wave L u) = 0 := by
  obtain ⟨k, hk⟩ := h2
  have hu : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hterm : ∀ j : ZMod L, inner ℂ (wave L (-u) j) (wave L u j) = (-1) ^ j.val / L := by
    intro j
    rw [RCLike.inner_apply, wave_apply, wave_apply, map_div₀, map_pow, map_neg,
      Complex.conj_ofReal, ← sqrt_mul_sqrt (L := L)]
    have h1 : u ^ j.val * (starRingEnd ℂ) u ^ j.val = 1 := by rw [← mul_pow, hu, one_pow]
    field_simp [sqrt_ne_zero]
    rw [neg_pow]
    linear_combination (-1 : ℂ) ^ j.val * ((Real.sqrt L : ℂ))⁻¹ ^ 2 * h1
  rw [PiLp.inner_apply]
  simp only [hterm]
  rw [sum_val (fun k => (-1 : ℂ) ^ k / L), ← Finset.sum_div, hk, sum_neg_one_pow, zero_div]

omit [NeZero L] in
include hL in
theorem neg_pow_eq_one (h2 : 2 ∣ L) : (-u) ^ L = 1 := by
  rw [neg_pow, hL, mul_one, Even.neg_one_pow (even_iff_two_dvd.2 h2)]

include hn in
theorem norm_neg_u : ‖-u‖ = 1 := by rw [_root_.norm_neg, hn]

end Wave

/-! ## 2. The embedding -/

/-- `ι χ = χ₀ e_u + χ₁ e_{−u}`. -/
def embed (L : ℕ) [NeZero L] (u : ℂ) (χ : DiracQubit.Q) : HU L :=
  χ 0 • wave L u + χ 1 • wave L (-u)

variable (h2 : 2 ∣ L)
include hL hn h2

omit hL hn h2 in
theorem embed_smul (z : ℂ) (χ : DiracQubit.Q) : embed L u (z • χ) = z • embed L u χ := by
  simp only [embed, PiLp.smul_apply, smul_eq_mul, smul_add, smul_smul]

omit hL in
/-- **`ι` is an isometry.** -/
theorem norm_embed (χ : DiracQubit.Q) : ‖embed L u χ‖ = ‖χ‖ := by
  have h11 : inner ℂ (wave L u) (wave L u) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_wave hn]; simp
  have h22 : inner ℂ (wave L (-u)) (wave L (-u)) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_wave (norm_neg_u hn)]; simp
  have h21 := inner_wave_neg hn h2
  have h12 : inner ℂ (wave L u) (wave L (-u)) = 0 := by
    rw [← inner_conj_symm, h21, map_zero]
  have h : ‖embed L u χ‖ ^ 2 = ‖χ‖ ^ 2 := by
    rw [DiracQubit.norm_sq_eq, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    simp only [embed, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h11,
      h22, h21, h12, mul_zero, mul_one, add_zero, zero_add]
    rw [RCLike.re_to_complex, Complex.add_re, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  nlinarith [norm_nonneg (embed L u χ), norm_nonneg χ]

/-- **`D_m (ι χ) = ι (H χ)`**: the qubit is the two-wave block of the axis. -/
theorem dirac_embed (m : ℝ) (χ : DiracQubit.Q) :
    TorusUniverse.dirac m (embed L u χ) = embed L u (DiracQubit.dirac u.re m χ) := by
  simp only [TorusUniverse.dirac, embed, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, transport_wave hL hn, transport_wave (neg_pow_eq_one hL h2) (norm_neg_u hn),
    stagger_wave, neg_neg, DiracQubit.dirac, DiracQubit.opA_apply, DiracQubit.opB_apply,
    PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.neg_re, Complex.ofReal_neg]
  module

/-- **`⟨K⟩_{ι χ} = ⟨V⟩_χ`** with `s = Im u`. -/
theorem velocity_embed (χ : DiracQubit.Q) :
    TorusUniverse.velocity (embed L u χ) = DiracQubit.velocity u.im χ := by
  have h11 : inner ℂ (wave L u) (wave L u) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_wave hn]; simp
  have h22 : inner ℂ (wave L (-u)) (wave L (-u)) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_wave (norm_neg_u hn)]; simp
  have h21 := inner_wave_neg hn h2
  have h12 : inner ℂ (wave L u) (wave L (-u)) = 0 := by
    rw [← inner_conj_symm, h21, map_zero]
  rw [DiracQubit.velocity_eq, TorusUniverse.velocity]
  simp only [embed, map_add, map_smul, current_wave hL hn,
    current_wave (neg_pow_eq_one hL h2) (norm_neg_u hn), Complex.neg_im, Complex.ofReal_neg,
    neg_neg, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h11, h22, h21,
    h12, mul_zero, mul_one, add_zero, zero_add]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [NeZero L] hL hn h2 in
theorem tensor_smul (z : ℂ) (ψ : HU L) (v : HU 3) :
    FiberDiracAxis.tensor (z • ψ) v = z • FiberDiracAxis.tensor ψ v := by
  ext p; simp only [FiberDiracAxis.tensor, PiLp.smul_apply, smul_eq_mul]; ring

/-- **The qubit with the fiber**: if `χ` is an eigenstate of the qubit of mass `−1/2` at
`c = Re u`, then `ι χ ⊗ v_rot` is an eigenstate of the Dirac operator of the axis with the
fiber. -/
theorem fiberDirac_tensor_embed {E : ℝ} {χ : DiracQubit.Q}
    (hE : DiracQubit.dirac u.re (-1 / 2) χ = (E : ℂ) • χ) :
    FiberDiracAxis.dirac (FiberDiracAxis.tensor (embed L u χ) FiberDiracAxis.rotating) =
      (E : ℂ) • FiberDiracAxis.tensor (embed L u χ) FiberDiracAxis.rotating := by
  rw [FiberDiracAxis.dirac_tensor FiberDiracAxis.transport_rotating, dirac_embed hL hn h2, hE,
    embed_smul, tensor_smul]

end DiracQubitAxis
