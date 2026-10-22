/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusDiracBound

/-!
# The speed limit of a Dirac state, in any Hilbert space

`TorusDiracBound` proves the speed limit on one closed axis, where the mass term is `m Σ` and
`(m Σ)² = m²`. The same argument works when the rest of the Dirac operator is any symmetric `B`
that anticommutes with the transport `A` of the axis and with its velocity `V`, as long as `B`
is never smaller than the mass: `‖Bχ‖² ≥ m² ‖χ‖²`. Let

  `A V = V A`,  `V B = −B V`,  `A B = −B A`,  `V² + A² = 1`,

`(A + B) ψ = E ψ` and `A² ψ = a ψ`. Then `‖(A + B)χ‖² = ‖Aχ‖² + ‖Bχ‖²`, so `E² = a + ‖Bψ‖²`,
and as on the axis `E ⟨V⟩ = ⟨V A⟩` with `‖V A ψ‖² = a (1 − a)`:

  `(a + m²) ⟨V⟩² ≤ (a + ‖Bψ‖²) ⟨V⟩² ≤ a (1 − a)`,  `|⟨V⟩| ≤ √(1 + m²) − |m|`.

The other axes only make `B` larger, and they slow the state down further.

## Main results

- `DiracSpeed.norm_sq_add_of_anticomm` : `‖(A + B)χ‖² = ‖Aχ‖² + ‖Bχ‖²` for anticommuting
  symmetric `A`, `B`.
- `DiracSpeed.abs_energy_ge` : if `‖Bχ‖² ≥ m² ‖χ‖²`, every eigenvalue of `A + B` has `|E| ≥ |m|`.
- `DiracSpeed.abs_velocity_le` : `|⟨V⟩| ≤ √(1 + m²) − |m|` for a unit eigenvector of `A + B`
  that is also an eigenvector of `A²`.
-/

@[expose] public noncomputable section

open Complex

namespace DiracSpeed

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

/-- **The speed limit of a Dirac state**: a unit eigenvector of `A + B` that is also an
eigenvector of `A²` moves at most at `√(1 + m²) − |m|`. -/
theorem abs_velocity_le (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hV : V.IsSymmetric)
    (hAV : ∀ χ, A (V χ) = V (A χ)) (hVB : ∀ χ, V (B χ) = -B (V χ))
    (hAB : ∀ χ, A (B χ) = -B (A χ)) (hVV : ∀ χ, V (V χ) + A (A χ) = χ)
    {m : ℝ} (hm : m ≠ 0) (hBm : ∀ χ, m ^ 2 * ‖χ‖ ^ 2 ≤ ‖B χ‖ ^ 2)
    {E a : ℝ} {ψ : H} (hψ : ‖ψ‖ = 1) (hE : A ψ + B ψ = (E : ℂ) • ψ)
    (ha : A (A ψ) = (a : ℂ) • ψ) :
    |(inner ℂ ψ (V ψ)).re| ≤ Real.sqrt (1 + m ^ 2) - |m| := by
  set v := (inner ℂ ψ (V ψ)).re
  set b := ‖B ψ‖ ^ 2
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  -- `a = ‖Aψ‖²`, `1 − a = ‖Vψ‖²`, `E² = a + b`
  have hna : ‖A ψ‖ ^ 2 = a := by
    have h1 : (inner ℂ (A ψ) (A ψ)).re = ‖A ψ‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [← h1, hA, ha, inner_smul_right, hψψ, mul_one, Complex.ofReal_re]
  have hnv : ‖V ψ‖ ^ 2 = 1 - a := by
    have h1 : (inner ℂ (V ψ) (V ψ)).re = ‖V ψ‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h2 : V (V ψ) = ψ - (a : ℂ) • ψ := by rw [← ha]; exact eq_sub_of_add_eq (hVV ψ)
    rw [← h1, hV, h2, inner_sub_right, inner_smul_right, hψψ]
    simp
  have hE2 : E ^ 2 = a + b := by
    have h := norm_sq_add_of_anticomm hA hB hAB ψ
    rw [hE, norm_smul, Complex.norm_real, Real.norm_eq_abs, hψ, mul_one, sq_abs, hna] at h
    exact h
  have hb : m ^ 2 ≤ b := by simpa [hψ] using hBm ψ
  have ha0 : 0 ≤ a := by rw [← hna]; positivity
  have ha1 : a ≤ 1 := by nlinarith only [hnv, sq_nonneg ‖V ψ‖]
  have hE0 : E ≠ 0 := by
    rintro rfl
    have : 0 < m ^ 2 := by positivity
    nlinarith only [hE2, ha0, hb, this]
  -- `B²ψ = bψ` and `Bψ = Eψ − Aψ`
  have hBB : B (B ψ) = ((E ^ 2 - a : ℝ) : ℂ) • ψ := by
    have h : A (A ψ + B ψ) + B (A ψ + B ψ) = ((E : ℂ) * E) • ψ := by
      rw [hE, map_smul, map_smul, ← smul_add, hE, smul_smul]
    rw [map_add, map_add, hAB, ha] at h
    have h' : B (B ψ) = ((E : ℂ) * E) • ψ - (a : ℂ) • ψ := by rw [← h]; abel
    rw [h', ← sub_smul]
    push_cast
    ring_nf
  have hBψ : B ψ = (E : ℂ) • ψ - A ψ := by rw [← hE]; abel
  -- the velocity of `Bψ` is `−(E² − a) v`
  have hvB : (inner ℂ (B ψ) (V (B ψ))).re = -(E ^ 2 - a) * v := by
    rw [hVB, inner_neg_right, ← hB, hBB, inner_smul_left, Complex.conj_ofReal]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, v]
    ring
  set z := inner ℂ ψ (V (A ψ))
  have hAVψ : inner ℂ (A ψ) (V ψ) = z := by rw [hA, hAV]
  have hAVA : inner ℂ (A ψ) (V (A ψ)) = (a : ℂ) * inner ℂ ψ (V ψ) := by
    rw [hA, hAV, ha, map_smul, inner_smul_right]
  have hexp : (inner ℂ (B ψ) (V (B ψ))).re = E ^ 2 * v - 2 * E * z.re + a * v := by
    rw [hBψ]
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, hAVψ, hAVA]
    have hz : inner ℂ ψ (V (A ψ)) = z := rfl
    rw [hz]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, v]
    ring
  have hw : z.re = E * v := by
    have h : 2 * E * z.re = 2 * E * (E * v) := by linear_combination -(hexp.symm.trans hvB)
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hE0) h
  -- `‖V A ψ‖² = a (1 − a)`
  have hnorm : ‖V (A ψ)‖ ^ 2 = a * (1 - a) := by
    have h1 : (inner ℂ (V (A ψ)) (V (A ψ))).re = ‖V (A ψ)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have h3 : A (A (A ψ)) = (a : ℂ) • A ψ := by rw [ha, map_smul]
    have h2 : V (V (A ψ)) = A ψ - (a : ℂ) • A ψ := by
      rw [← h3]; exact eq_sub_of_add_eq (hVV (A ψ))
    have hAA : inner ℂ (A ψ) (A ψ) = (a : ℂ) := by rw [hA, ha, inner_smul_right, hψψ, mul_one]
    rw [← h1, hV, h2, inner_sub_right, inner_smul_right, hAA, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  have hz : z.re ^ 2 ≤ a * (1 - a) := by
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ψ (V (A ψ))
    rw [hψ, one_mul] at h1
    have h2 := Complex.abs_re_le_norm z
    rw [← hnorm, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h2.trans h1) 2
  -- the scalar step, as on the axis
  have hv : (a + m ^ 2) * v ^ 2 ≤ a * (1 - a) := by
    have h1 : E ^ 2 * v ^ 2 = z.re ^ 2 := by rw [hw]; ring
    nlinarith only [h1, hz, hE2, hb, sq_nonneg v]
  have hr := TorusUniverse.speedLimit_sq m
  have hr0 := TorusUniverse.speedLimit_nonneg m
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

end DiracSpeed
