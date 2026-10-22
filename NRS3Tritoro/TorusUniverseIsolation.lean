/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusUniverseWave

/-!
# Saturating states of the universe stay away from the fastest waves

Let `4 ∣ L` and `u = ±i`. A unit state near the wave `e_u` is `ψ = a e_u + b e_{−u} + ζ` with `b`,
`ζ` small. Then `T° ψ = T° ζ`, so `|⟨T°⟩| ≤ ‖ζ‖²`. Saturation `T̃ψ = κ X̃ψ`, read on `e_{−u}`,
is `−⟨T°⟩ b = κ (−a/2 + …)`, because `X` couples the two waves with `−1/2`: so `|κ| ≲ ‖ζ‖² |b|`.
Read in norm it is `‖T° ζ‖ ≤ ‖ζ‖² + 2L |κ|`, and `T°` is bounded below on `ζ`. Together they force
`ζ = 0`, then `T° ψ = 0` and `Var T° = 0`. So no saturating state with fluctuating transport comes
near the wave: `‖(S − u)ψ‖` stays above a fixed `c > 0`.

## Main results

- `TorusUniverse.exists_transport_gap` : `T°` is bounded below off the two waves.
- `TorusUniverse.isolation` : saturating states with `Var T° > 0` stay away from the waves.
-/

@[expose] public noncomputable section

open Complex PathGraph3DNRS

namespace TorusUniverse

variable {L : ℕ} [NeZero L]

/-! ## 1. Bounds -/

theorem norm_chart_le (ψ : HU L) : ‖chart (univChart L) ψ‖ ≤ L * ‖ψ‖ := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have h : ‖chart (univChart L) ψ‖ ^ 2 ≤ (L * ‖ψ‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [chart_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, univChart]
    have h0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    have h1 : (j.val : ℝ) ≤ L := by exact_mod_cast (ZMod.val_lt j).le
    gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem norm_transport_le (ψ : HU L) : ‖transport ψ‖ ≤ ‖ψ‖ := by
  have h := norm_sq_transport_add_norm_sq_current ψ
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg ‖current ψ‖])

theorem abs_meanG_le (A : HU L →ₗ[ℂ] HU L) {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    |meanG A ψ| ≤ ‖A ψ‖ := by
  have := norm_inner_le_norm (𝕜 := ℂ) ψ (A ψ)
  rw [hψ, one_mul] at this
  exact (Complex.abs_re_le_norm _).trans this

/-- **`T°` is bounded below off the two waves** (`4 ∣ L`): `‖T°ζ‖ = ‖(S − u)(S + u)ζ‖/2`. -/
theorem exists_transport_gap (h4 : 4 ∣ L) {u : ℂ} (hu : u = I ∨ u = -I) :
    ∃ G > 0, ∀ ζ : HU L, inner ℂ (wave L u) ζ = 0 → inner ℂ (wave L (-u)) ζ = 0 →
      G * ‖ζ‖ ≤ ‖transport ζ‖ := by
  obtain ⟨g, hg, hgap⟩ := exists_gap_wave (L := L) hu
  obtain ⟨g', hg', hgap'⟩ := exists_gap_wave (L := L) (neg_of hu)
  refine ⟨g * g' / 2, by positivity, fun ζ he hω => ?_⟩
  set w := shift ζ - (-u) • ζ
  have hw : inner ℂ (wave L u) w = 0 := by
    rw [inner_sub_right, inner_smul_right, he, inner_shift, shiftInv_wave hu h4,
      inner_smul_left, he]
    simp
  have hSw : shift w - u • w = (2 : ℂ) • shift (transport ζ) := by
    ext j
    simp only [w, map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, shift_apply,
      transport_apply, add_sub_cancel_right]
    linear_combination (-ζ j) * sq_of hu
  have h1 := hgap w hw
  have h2 := hgap' ζ hω
  rw [hSw, norm_smul, norm_shift] at h1
  have h22 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h22] at h1
  nlinarith

/-! ## 2. Saturating states stay away from the waves -/

/-- **Isolation of the wave** (`4 ∣ L`): a saturating state with fluctuating transport keeps a
fixed distance from the eigenvector `e_u` of the shift, measured by `‖(S − u)ψ‖`. -/
theorem isolation (h4 : 4 ∣ L) {u : ℂ} (hu : u = I ∨ u = -I) :
    ∃ c > 0, ∀ ψ : HU L, ‖ψ‖ = 1 → 0 < varianceG transport ψ →
      (∃ κ : ℂ, centeredG transport ψ = κ • centeredG (chart (univChart L)) ψ) →
        c ≤ ‖shift ψ - u • ψ‖ := by
  obtain ⟨g, hg, hgap⟩ := exists_gap_wave (L := L) hu
  obtain ⟨G, hG, hTgap⟩ := exists_transport_gap h4 hu
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set δ : ℝ := min G 1 / (16 * L) with hδ
  have hm0 : 0 < min G 1 := lt_min hG one_pos
  have hδ0 : 0 < δ := by positivity
  have hδG : δ ≤ G / 16 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [min_le_left G 1, hL1, hG]
  have hδL : 16 * L * δ ≤ 1 := by
    rw [hδ, mul_div_assoc', div_le_one (by positivity)]
    nlinarith only [min_le_right G 1, hL1]
  have hδ16 : 16 * δ ≤ 1 := by nlinarith only [hδL, hL1, hδ0]
  have hδ1 : δ ≤ 1 := by linarith only [hδ16, hδ0]
  refine ⟨g * δ, by positivity, fun ψ hψ hT ⟨κ, hκ⟩ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set e := wave L u
  set ω := wave L (-u)
  set X := chart (univChart L)
  have he : ‖e‖ = 1 := norm_wave hu
  have hω : ‖ω‖ = 1 := norm_wave (neg_of hu)
  have hωe : inner ℂ ω e = 0 := inner_wave_neg hu h4
  have heω : inner ℂ e ω = 0 := by rw [← inner_conj_symm, hωe, map_zero]
  have hee : inner ℂ e e = 1 := by rw [inner_self_eq_norm_sq_to_K, he]; simp
  have hωω : inner ℂ ω ω = 1 := by rw [inner_self_eq_norm_sq_to_K, hω]; simp
  -- the decomposition `ψ = a e + b ω + ζ`
  set a := inner ℂ e ψ
  set η := ψ - a • e
  have heη : inner ℂ e η = 0 := by
    simp only [η, inner_sub_right, inner_smul_right, hee, mul_one, a, sub_self]
  have hSη : shift η - u • η = shift ψ - u • ψ := by
    simp only [η, map_sub, map_smul, e, shift_wave hu h4, smul_sub, smul_comm u a]
    abel
  have hηδ : ‖η‖ < δ := by
    have := hgap η heη
    rw [hSη] at this
    exact lt_of_mul_lt_mul_left (this.trans_lt hlt) hg.le
  set b := inner ℂ ω ψ
  have hb : b = inner ℂ ω η := by
    simp only [η, inner_sub_right, inner_smul_right, hωe, mul_zero, sub_zero, b]
  set ζ := η - b • ω
  have hωζ : inner ℂ ω ζ = 0 := by
    simp only [ζ, inner_sub_right, inner_smul_right, hωω, mul_one, ← hb, sub_self]
  have heζ : inner ℂ e ζ = 0 := by
    simp only [ζ, inner_sub_right, inner_smul_right, heω, heη, mul_zero, sub_self]
  have hpy : ‖η‖ * ‖η‖ = ‖b • ω‖ * ‖b • ω‖ + ‖ζ‖ * ‖ζ‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (b • ω) ζ
      (by rw [inner_smul_left, hωζ, mul_zero])
    rwa [show b • ω + ζ = η by simp [ζ]] at h
  rw [norm_smul, hω, mul_one] at hpy
  have hζη : ‖ζ‖ ≤ ‖η‖ := by
    nlinarith only [hpy, norm_nonneg ζ, norm_nonneg b, norm_nonneg η]
  have hbη : ‖b‖ ≤ ‖η‖ := by
    nlinarith only [hpy, norm_nonneg ζ, norm_nonneg b, norm_nonneg η]
  have hζδ : ‖ζ‖ < δ := hζη.trans_lt hηδ
  have hbδ : ‖b‖ < δ := hbη.trans_lt hηδ
  have hpa : 1 = ‖a‖ * ‖a‖ + ‖η‖ * ‖η‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a • e) η
      (by rw [inner_smul_left, heη, mul_zero])
    rwa [show a • e + η = ψ by simp [η], hψ, norm_smul, he, mul_one, mul_one] at h
  have ha1 : ‖a‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) e ψ
    rwa [he, hψ, one_mul] at this
  have ha : 1 - δ ≤ ‖a‖ := by
    nlinarith only [hpa, ha1, hηδ, hδ1, hδ0, norm_nonneg a, norm_nonneg η]
  have hdec : ψ = a • e + b • ω + ζ := by simp [ζ, η]
  -- transport only sees `ζ`
  have hTψ : transport ψ = transport ζ := by
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul, e, ω, transport_wave hu h4, transport_wave (neg_of hu) h4,
      smul_zero, zero_add]
  set mT := meanG transport ψ
  set mX := meanG X ψ
  have hTζ : ‖transport ζ‖ ≤ ‖ζ‖ := norm_transport_le ζ
  have hmT : |mT| ≤ ‖ζ‖ ^ 2 := by
    have h1 : inner ℂ ψ (transport ψ) = inner ℂ (transport ζ) ζ := by
      rw [hTψ, ← transport_isSymmetric ψ ζ, hTψ]
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (transport ζ) ζ
    have h3 : |mT| ≤ ‖inner ℂ (transport ζ) ζ‖ := by
      rw [← h1]; exact Complex.abs_re_le_norm _
    calc |mT| ≤ ‖transport ζ‖ * ‖ζ‖ := h3.trans h2
      _ ≤ ‖ζ‖ * ‖ζ‖ := mul_le_mul_of_nonneg_right hTζ (norm_nonneg _)
      _ = ‖ζ‖ ^ 2 := (sq _).symm
  have hκ' : transport ζ - (mT : ℂ) • ψ = κ • (X ψ - (mX : ℂ) • ψ) := by
    rw [← hTψ]; exact hκ
  -- read the saturation on `ω`
  have hTω : transport ω = 0 := transport_wave (neg_of hu) h4
  have hωT : inner ℂ ω (transport ζ) = 0 := by
    rw [← transport_isSymmetric ω ζ, hTω, inner_zero_left]
  have hXψ : inner ℂ ω (X ψ) =
      a * (-1 / 2) + b * inner ℂ ω (X ω) + inner ℂ ω (X ζ) := by
    conv_lhs => rw [hdec]
    simp only [map_add, map_smul, inner_add_right, inner_smul_right, ω, X, e,
      inner_wave_chart hu h4]
  set W := -a / 2 + b * (inner ℂ ω (X ω) - mX) + inner ℂ ω (X ζ)
  have hproj : -((mT : ℂ) * b) = κ * W := by
    have := congrArg (inner ℂ ω) hκ'
    simp only [inner_sub_right, inner_smul_right, hωT] at this
    rw [show inner ℂ ω ψ = b from rfl] at this
    simp only [W]
    linear_combination this + κ * hXψ
  -- bounds on `W`
  have hXω : ‖X ω‖ ≤ L := by simpa [hω] using norm_chart_le ω
  have hXψn : ‖X ψ‖ ≤ L := by simpa [hψ] using norm_chart_le ψ
  have hXζ : ‖X ζ‖ ≤ L * ‖ζ‖ := norm_chart_le ζ
  have hmX : |mX| ≤ L := (abs_meanG_le X hψ).trans hXψn
  have hq : ‖inner ℂ ω (X ω) - mX‖ ≤ 2 * L := by
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ω (X ω)
    rw [hω, one_mul] at h1
    have h2 : ‖(mX : ℂ)‖ = |mX| := Complex.norm_real _
    calc _ ≤ ‖inner ℂ ω (X ω)‖ + ‖(mX : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * L := by rw [h2]; linarith only [h1, hXω, hmX]
  have hr : ‖inner ℂ ω (X ζ)‖ ≤ L * ‖ζ‖ := by
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ω (X ζ)
    rw [hω, one_mul] at h1
    exact h1.trans hXζ
  have hW : 1 / 4 ≤ ‖W‖ := by
    have h1 : ‖-a / 2‖ ≤ ‖W‖ + ‖b * (inner ℂ ω (X ω) - mX)‖ + ‖inner ℂ ω (X ζ)‖ := by
      have : -a / 2 = W - b * (inner ℂ ω (X ω) - mX) - inner ℂ ω (X ζ) := by
        simp only [W]; ring
      rw [this]
      exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    rw [norm_div, norm_neg, norm_mul] at h1
    have h22 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h22] at h1
    have hbq : ‖b‖ * ‖inner ℂ ω (X ω) - mX‖ ≤ δ * (2 * L) :=
      mul_le_mul hbδ.le hq (norm_nonneg _) hδ0.le
    have hrr : ‖inner ℂ ω (X ζ)‖ ≤ L * δ :=
      hr.trans (mul_le_mul_of_nonneg_left hζδ.le (by positivity))
    linarith only [h1, hbq, hrr, ha, hδL, hδ16]
  have hκb : ‖κ‖ * (1 / 4) ≤ ‖ζ‖ ^ 2 * δ := by
    have h1 := congrArg norm hproj
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
    calc ‖κ‖ * (1 / 4) ≤ ‖κ‖ * ‖W‖ := by gcongr
      _ = |mT| * ‖b‖ := h1.symm
      _ ≤ ‖ζ‖ ^ 2 * δ := by gcongr
  -- read the saturation in norm
  have hnorm : ‖transport ζ‖ ≤ ‖ζ‖ ^ 2 + ‖κ‖ * (2 * L) := by
    have h1 : transport ζ = (mT : ℂ) • ψ + κ • (X ψ - (mX : ℂ) • ψ) := by
      rw [← hκ']; abel
    have h2 : ‖X ψ - (mX : ℂ) • ψ‖ ≤ 2 * L := by
      calc _ ≤ ‖X ψ‖ + ‖(mX : ℂ) • ψ‖ := norm_sub_le _ _
        _ ≤ 2 * L := by
          rw [norm_smul, hψ, mul_one, Complex.norm_real, Real.norm_eq_abs]
          linarith only [hXψn, hmX]
    rw [h1]
    calc _ ≤ ‖(mT : ℂ) • ψ‖ + ‖κ • (X ψ - (mX : ℂ) • ψ)‖ := norm_add_le _ _
      _ ≤ ‖ζ‖ ^ 2 + ‖κ‖ * (2 * L) := by
        rw [norm_smul, norm_smul, hψ, mul_one, Complex.norm_real, Real.norm_eq_abs]
        gcongr
  have hgapζ := hTgap ζ heζ hωζ
  have hζ0 : ‖ζ‖ = 0 := by
    have hk4 : ‖κ‖ ≤ 4 * δ * ‖ζ‖ ^ 2 := by linarith only [hκb]
    have hk2 : ‖κ‖ * (2 * L) ≤ 1 / 2 * ‖ζ‖ ^ 2 :=
      calc ‖κ‖ * (2 * L) ≤ 4 * δ * ‖ζ‖ ^ 2 * (2 * L) :=
            mul_le_mul_of_nonneg_right hk4 (by positivity)
        _ = (8 * L * δ) * ‖ζ‖ ^ 2 := by ring
        _ ≤ 1 / 2 * ‖ζ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith only [hδL]) (sq_nonneg _)
    have h4 : ‖ζ‖ ^ 2 ≤ δ * ‖ζ‖ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hζδ.le (norm_nonneg _)
    have h5 : δ * ‖ζ‖ ≤ G / 16 * ‖ζ‖ := mul_le_mul_of_nonneg_right hδG (norm_nonneg _)
    have h6 : G * ‖ζ‖ ≤ G * 0 := by linarith only [hgapζ, hnorm, hk2, h4, h5]
    exact le_antisymm (le_of_mul_le_mul_left h6 hG) (norm_nonneg _)
  -- then the transport does not fluctuate
  have hζ : ζ = 0 := norm_eq_zero.1 hζ0
  have hT0 : transport ψ = 0 := by rw [hTψ, hζ, map_zero]
  have hm0 : mT = 0 := by simp [mT, meanG, hT0]
  have : varianceG transport ψ = 0 := by
    simp [varianceG, centeredG, hT0, show meanG transport ψ = 0 from hm0]
  exact absurd this hT.ne'

end TorusUniverse
