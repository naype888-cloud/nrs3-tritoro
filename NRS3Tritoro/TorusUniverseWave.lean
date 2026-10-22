/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusUniverseRS

/-!
# The two fastest waves of the axis of the universe

For `u = ±i` the plane wave `u^j/√L` is the state that `abs_velocity_le` lets reach the cone. When
`4 ∣ L` it is an eigenvector of the shift, `S e_u = u e_u`, with `T° e_u = 0`; the two waves are
orthogonal and the coordinate of the universe couples them with `⟨e_{−u}, X e_u⟩ = −1/2`. The
eigenvectors of `S` for `u` are the multiples of `e_u` (none when `4 ∤ L`), so `S − u` is bounded
below off `e_u`: there is `g > 0` with `g ‖η‖ ≤ ‖(S − u) η‖` for `η ⊥ e_u`, and for every `η`
when `4 ∤ L`.

## Main results

- `TorusUniverse.shift_wave`, `TorusUniverse.transport_wave` : `S e_u = u e_u`, `T° e_u = 0`.
- `TorusUniverse.inner_wave_neg`, `TorusUniverse.inner_wave_chart` : the two waves are
  orthogonal, and `X` couples them with `−1/2`.
- `TorusUniverse.exists_gap_wave`, `TorusUniverse.exists_gap` : `S − u` is bounded below.
- `TorusUniverse.norm_sq_shift_sub_I`, `TorusUniverse.norm_sq_shift_add_I` :
  `‖(S ∓ i)ψ‖² = 2 ± 2⟨K⟩`.
-/

@[expose] public noncomputable section

open Complex

namespace TorusUniverse

variable {L : ℕ} [NeZero L]

/-- The coordinate of the universe: positions counted from the closing link. -/
def univChart (L : ℕ) [NeZero L] : ZMod L → ℝ := fun j => (j.val : ℝ)

/-- The plane wave `u^j/√L`. -/
def wave (L : ℕ) [NeZero L] (u : ℂ) : HU L :=
  WithLp.toLp 2 fun j => u ^ j.val / (Real.sqrt L : ℂ)

theorem wave_apply (u : ℂ) (j : ZMod L) : wave L u j = u ^ j.val / (Real.sqrt L : ℂ) := rfl

/-! ## 1. Sums over the axis -/

theorem sum_val {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ j : ZMod L, f j.val = ∑ k ∈ Finset.range L, f k :=
  Finset.sum_bij' (fun j _ => j.val) (fun k _ => (k : ZMod L))
    (fun j _ => Finset.mem_range.2 (ZMod.val_lt j)) (fun _ _ => Finset.mem_univ _)
    (fun j _ => ZMod.natCast_zmod_val j)
    (fun _ hk => ZMod.val_cast_of_lt (Finset.mem_range.1 hk)) fun _ _ => rfl

theorem sum_neg_one_pow (m : ℕ) : ∑ k ∈ Finset.range (2 * m), ((-1 : ℂ) ^ k) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      pow_succ, pow_mul]
    norm_num

theorem sum_neg_one_pow_mul (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), ((-1 : ℂ) ^ k * k) = -m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      pow_succ, pow_mul]
    push_cast
    ring

/-! ## 2. The waves -/

omit [NeZero L] in
theorem sqrt_mul_sqrt : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = L := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp

theorem sqrt_ne_zero : (Real.sqrt L : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt L := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L))
  exact_mod_cast this.ne'


section Waves

variable {u : ℂ} (hu : u = I ∨ u = -I)
include hu

theorem pow_four_of : u ^ 4 = 1 := by
  rcases hu with rfl | rfl
  · exact Complex.I_pow_four
  · rw [neg_pow, Complex.I_pow_four]; norm_num

theorem sq_of : u ^ 2 = -1 := by
  rcases hu with rfl | rfl <;> simp

theorem conj_of : (starRingEnd ℂ) u = -u := by
  rcases hu with rfl | rfl <;> simp

theorem norm_of : ‖u‖ = 1 := by
  rcases hu with rfl | rfl <;> simp

theorem neg_of : -u = I ∨ -u = -I := by
  rcases hu with rfl | rfl <;> simp

theorem pow_val_add_one (h4 : 4 ∣ L) (j : ZMod L) : u ^ (j + 1).val = u * u ^ j.val := by
  have hL : 4 ≤ L := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) h4
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < L),
    pow_eq_pow_mod _ (pow_four_of hu), Nat.mod_mod_of_dvd _ h4,
    ← pow_eq_pow_mod _ (pow_four_of hu), pow_succ, mul_comm]

theorem pow_val_sub_one (h4 : 4 ∣ L) (j : ZMod L) : u ^ (j - 1).val = u ^ 3 * u ^ j.val := by
  have h := pow_val_add_one hu h4 (j - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, show u ^ 3 * u = 1 by rw [← pow_succ]; exact pow_four_of hu, one_mul]

/-- `S e_u = u e_u`. -/
theorem shift_wave (h4 : 4 ∣ L) : shift (wave L u) = u • wave L u := by
  ext j
  simp only [shift_apply, wave_apply, PiLp.smul_apply, smul_eq_mul, pow_val_add_one hu h4]
  ring

/-- `S⁻¹ e_u = u³ e_u`. -/
theorem shiftInv_wave (h4 : 4 ∣ L) : shiftInv (wave L u) = u ^ 3 • wave L u := by
  ext j
  simp only [shiftInv_apply, wave_apply, PiLp.smul_apply, smul_eq_mul, pow_val_sub_one hu h4]
  ring

/-- **The fastest wave does not fluctuate in transport**: `T° e_u = 0`. -/
theorem transport_wave (h4 : 4 ∣ L) : transport (wave L u) = 0 := by
  ext j
  simp only [transport_apply, wave_apply, PiLp.zero_apply, pow_val_add_one hu h4,
    pow_val_sub_one hu h4]
  linear_combination (u * u ^ j.val / (Real.sqrt L : ℂ) / 2) * sq_of hu

/-- `e_u` is a unit vector. -/
theorem norm_wave : ‖wave L u‖ = 1 := by
  have h : ‖wave L u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [wave_apply, norm_div, norm_pow, norm_of hu, one_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    field_simp
  nlinarith [norm_nonneg (wave L u)]

end Waves

omit [NeZero L] in
/-- An eigenvector of the shift is a geometric sequence: `ψ_j = u^j ψ_0`. -/
theorem eq_pow_of_shift {u : ℂ} {ψ : HU L} (h : shift ψ = u • ψ) (k : ℕ) :
    ψ (k : ZMod L) = u ^ k * ψ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := congrArg (fun φ : HU L => φ (k : ZMod L)) h
    simp only [shift_apply, PiLp.smul_apply, smul_eq_mul] at hk
    rw [Nat.cast_succ, hk, ih, pow_succ]
    ring

/-- A unit-lifted bound below on a subspace where `A` has no kernel (finite dimension). -/
theorem exists_gap_of (A : HU L →ₗ[ℂ] HU L) (W : Submodule ℂ (HU L))
    (h : ∀ η ∈ W, A η = 0 → η = 0) : ∃ g > 0, ∀ η ∈ W, g * ‖η‖ ≤ ‖A η‖ := by
  obtain ⟨K, hK0, hK⟩ := (A ∘ₗ W.subtype).exists_antilipschitzWith
    (LinearMap.ker_eq_bot'.2 fun η hη => Subtype.ext (h η η.2 hη))
  have hK' : (0 : ℝ) < K := NNReal.coe_pos.2 hK0
  refine ⟨1 / K, by positivity, fun η hη => ?_⟩
  have hb := ZeroHomClass.bound_of_antilipschitz (A ∘ₗ W.subtype) hK ⟨η, hη⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hb
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hK', mul_comm]
  exact hb

variable {u : ℂ} (hu : u = I ∨ u = -I)
include hu

/-- **The two fastest waves are orthogonal**: `⟨e_{−u}, e_u⟩ = 0`. -/
theorem inner_wave_neg (h4 : 4 ∣ L) : inner ℂ (wave L (-u)) (wave L u) = 0 := by
  obtain ⟨m, hm⟩ : 2 ∣ L := (by norm_num : 2 ∣ 4).trans h4
  have hterm : ∀ j : ZMod L, inner ℂ (wave L (-u) j) (wave L u j) = (-1) ^ j.val / L := by
    intro j
    rw [RCLike.inner_apply, wave_apply, wave_apply, map_div₀, map_pow, map_neg, conj_of hu,
      neg_neg, Complex.conj_ofReal, ← sqrt_mul_sqrt (L := L), ← sq_of hu]
    field_simp [sqrt_ne_zero]
    ring
  rw [PiLp.inner_apply]
  simp only [hterm]
  rw [sum_val (fun k => (-1 : ℂ) ^ k / L), ← Finset.sum_div, hm, sum_neg_one_pow, zero_div]

/-- **The coordinate couples the two waves**: `⟨e_{−u}, X e_u⟩ = −1/2`. -/
theorem inner_wave_chart (h4 : 4 ∣ L) :
    inner ℂ (wave L (-u)) (chart (univChart L) (wave L u)) = -1 / 2 := by
  obtain ⟨m, hm⟩ : 2 ∣ L := (by norm_num : 2 ∣ 4).trans h4
  have hterm : ∀ j : ZMod L, inner ℂ (wave L (-u) j) (chart (univChart L) (wave L u) j) =
      (-1) ^ j.val * j.val / L := by
    intro j
    rw [RCLike.inner_apply, chart_apply, wave_apply, wave_apply, map_div₀, map_pow, map_neg,
      conj_of hu, neg_neg, Complex.conj_ofReal, ← sqrt_mul_sqrt (L := L), ← sq_of hu, univChart]
    push_cast
    field_simp [sqrt_ne_zero]
    ring
  rw [PiLp.inner_apply]
  simp only [hterm]
  rw [sum_val (fun k => (-1 : ℂ) ^ k * k / L), ← Finset.sum_div, hm, sum_neg_one_pow_mul]
  have : (m : ℂ) ≠ 0 := by
    rintro h
    have : m = 0 := by exact_mod_cast h
    exact NeZero.ne L (by omega)
  push_cast
  field_simp

/-! ## 3. `S − u` is bounded below off the wave -/

/-- `⟨e_u, ψ⟩ = √L ψ_0` for an eigenvector `ψ` of the shift (`4 ∣ L`). -/
theorem inner_wave_of_shift {η : HU L} (hs : shift η = u • η) :
    inner ℂ (wave L u) η = η 0 * (Real.sqrt L : ℂ) := by
  have key : ∀ n : ℕ, (-u) ^ n * u ^ n = 1 := fun n => by
    rw [← mul_pow, show -u * u = 1 by linear_combination -(sq_of hu), one_pow]
  have hterm : ∀ j : ZMod L, inner ℂ (wave L u j) (η j) = η 0 / (Real.sqrt L : ℂ) := by
    intro j
    rw [RCLike.inner_apply, wave_apply, ← ZMod.natCast_zmod_val j, eq_pow_of_shift hs,
      ZMod.natCast_zmod_val j, map_div₀, map_pow, conj_of hu, Complex.conj_ofReal]
    calc _ = η 0 * ((-u) ^ j.val * u ^ j.val) / (Real.sqrt L : ℂ) := by ring
      _ = _ := by rw [key, mul_one]
  rw [PiLp.inner_apply]
  simp only [hterm, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← sqrt_mul_sqrt (L := L)]
  field_simp [sqrt_ne_zero]

/-- **Off the wave, `S − u` is bounded below** (`4 ∣ L`). -/
theorem exists_gap_wave :
    ∃ g > 0, ∀ η : HU L, inner ℂ (wave L u) η = 0 → g * ‖η‖ ≤ ‖shift η - u • η‖ := by
  have hker : ∀ η ∈ (ℂ ∙ wave L u)ᗮ,
      (shift - u • LinearMap.id : HU L →ₗ[ℂ] HU L) η = 0 → η = 0 := by
    intro η hη h0
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hη
    have hs : shift η = u • η := by simpa [sub_eq_zero] using h0
    have h0' := (inner_wave_of_shift hu hs).symm.trans hη
    have : η 0 = 0 := (mul_eq_zero.1 h0').resolve_right sqrt_ne_zero
    ext j
    rw [← ZMod.natCast_zmod_val j, eq_pow_of_shift hs, this, mul_zero, PiLp.zero_apply]
  obtain ⟨g, hg, hgap⟩ := exists_gap_of (shift - u • LinearMap.id) _ hker
  refine ⟨g, hg, fun η hη => ?_⟩
  have := hgap η (Submodule.mem_orthogonal_singleton_iff_inner_right.2 hη)
  simpa using this

/-- **With `4 ∤ L` the shift has no eigenvector for `u`**: `S − u` is bounded below. -/
theorem exists_gap (h4 : ¬ 4 ∣ L) : ∃ g > 0, ∀ η : HU L, g * ‖η‖ ≤ ‖shift η - u • η‖ := by
  have hL : u ^ L ≠ 1 := by
    rw [pow_eq_pow_mod _ (pow_four_of hu)]
    have h1 : L % 4 ≠ 0 := fun h => h4 (Nat.dvd_of_mod_eq_zero h)
    have h2 : L % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize L % 4 = r at h1 h2
    interval_cases r <;> rcases hu with rfl | rfl <;> norm_num [pow_succ, Complex.ext_iff] at *
  have hker : ∀ η ∈ (⊤ : Submodule ℂ (HU L)),
      (shift - u • LinearMap.id : HU L →ₗ[ℂ] HU L) η = 0 → η = 0 := by
    intro η _ h0
    have hs : shift η = u • η := by simpa [sub_eq_zero] using h0
    have h00 : η 0 = u ^ L * η 0 := by
      rw [← eq_pow_of_shift hs, ZMod.natCast_self]
    have : η 0 = 0 := by
      have : (1 - u ^ L) * η 0 = 0 := by linear_combination h00
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hL))
    ext j
    rw [← ZMod.natCast_zmod_val j, eq_pow_of_shift hs, this, mul_zero, PiLp.zero_apply]
  obtain ⟨g, hg, hgap⟩ := exists_gap_of (shift - u • LinearMap.id) ⊤ hker
  exact ⟨g, hg, fun η => by simpa using hgap η Submodule.mem_top⟩

omit hu

/-! ## 4. The distance to the waves is the velocity -/

theorem velocity_eq_im (ψ : HU L) : velocity ψ = (inner ℂ (shift ψ) ψ).im := by
  rw [velocity, current_eq, inner_smul_right, inner_sub_right, inner_shiftInv,
    ← inner_conj_symm (shift ψ) ψ]
  simp only [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  norm_num
  ring

/-- `‖(S − i)ψ‖² = 2 + 2⟨K⟩` for unit states. -/
theorem norm_sq_shift_sub_I {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    ‖shift ψ - I • ψ‖ ^ 2 = 2 + 2 * velocity ψ := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_shift, norm_smul, Complex.norm_I, hψ, inner_smul_right,
    RCLike.re_to_complex, velocity_eq_im]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

/-- `‖(S + i)ψ‖² = 2 − 2⟨K⟩` for unit states. -/
theorem norm_sq_shift_add_I {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    ‖shift ψ - (-I) • ψ‖ ^ 2 = 2 - 2 * velocity ψ := by
  rw [norm_sub_sq (𝕜 := ℂ), norm_shift, norm_smul, norm_neg, Complex.norm_I, hψ,
    inner_smul_right, RCLike.re_to_complex, velocity_eq_im]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

end TorusUniverse
