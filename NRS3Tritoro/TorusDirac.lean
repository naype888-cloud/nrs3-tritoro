/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusUniverseWave

/-!
# The doublers of the axis of the universe and Dirac's square root

On the closed axis `ZMod L` (`L` even) the two fastest waves `e_{±i}` move at `∓1`: they are a
right mover and a left mover, the doubled pair that a closed momentum circle forces on every
local transport (Nielsen–Ninomiya). They are exchanged by the staggered sign

  `(Σψ)_j = (−1)^j ψ_j`,

which anticommutes with the transport and with the current. So the doubler is not a second
particle: it is the second component of one Dirac field, and `Σ` is Dirac's `β`. With a mass `m`
the operator `D_m = T° + m Σ` squares to

  `D_m² = T°² + m²`,

Dirac's square root of the relativistic relation, with `c` one position per step. The mass
couples the two movers, and no stationary state of `D_m` reaches the cone: `|⟨K⟩| < 1` for every
eigenvector of `D_m` with `m ≠ 0`.

## Main results

- `TorusUniverse.transport_stagger`, `TorusUniverse.current_stagger` : `Σ` anticommutes with
  `T°` and with `K`.
- `TorusUniverse.stagger_wave` : `Σ e_u = e_{−u}`, the doublers are exchanged.
- `TorusUniverse.dirac_sq` : `D_m² = T°² + m²`.
- `TorusUniverse.abs_velocity_lt_one_of_dirac` : a massive stationary state moves strictly below
  the cone.
-/

@[expose] public noncomputable section

open Complex PathGraph3DNRS

namespace TorusUniverse

variable {L : ℕ} [NeZero L]

/-- The staggered sign `(Σψ)_j = (−1)^j ψ_j`. -/
def stagger : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun j => (-1) ^ j.val * ψ j
  map_add' ψ φ := by ext j; simp only [PiLp.add_apply]; ring
  map_smul' c ψ := by
    ext j; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [NeZero L] in
theorem stagger_apply (ψ : HU L) (j : ZMod L) : stagger ψ j = (-1) ^ j.val * ψ j := rfl

theorem neg_one_pow_val_add_one (h2 : 2 ∣ L) (j : ZMod L) :
    (-1 : ℂ) ^ (j + 1).val = -(-1) ^ j.val := by
  have hL : 2 ≤ L := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) h2
  have h1 : (-1 : ℂ) ^ 2 = 1 := by norm_num
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < L),
    pow_eq_pow_mod _ h1, Nat.mod_mod_of_dvd _ h2, ← pow_eq_pow_mod _ h1, pow_succ]
  ring

theorem neg_one_pow_val_sub_one (h2 : 2 ∣ L) (j : ZMod L) :
    (-1 : ℂ) ^ (j - 1).val = -(-1) ^ j.val := by
  have h := neg_one_pow_val_add_one h2 (j - 1)
  rw [sub_add_cancel] at h
  rw [h, neg_neg]

/-! ## 1. The staggered sign -/

omit [NeZero L] in
theorem stagger_stagger (ψ : HU L) : stagger (stagger ψ) = ψ := by
  ext j
  rw [stagger_apply, stagger_apply, ← mul_assoc, ← mul_pow]
  norm_num

/-- **`Σ` anticommutes with the transport**: `T° Σ = −Σ T°`. -/
theorem transport_stagger (h2 : 2 ∣ L) (ψ : HU L) :
    transport (stagger ψ) = -stagger (transport ψ) := by
  ext j
  simp only [transport_apply, stagger_apply, PiLp.neg_apply, neg_one_pow_val_add_one h2,
    neg_one_pow_val_sub_one h2]
  ring

/-- **`Σ` anticommutes with the current**: `K Σ = −Σ K`. -/
theorem current_stagger (h2 : 2 ∣ L) (ψ : HU L) :
    current (stagger ψ) = -stagger (current ψ) := by
  ext j
  simp only [current_apply, stagger_apply, PiLp.neg_apply, neg_one_pow_val_add_one h2,
    neg_one_pow_val_sub_one h2]
  ring

/-- `Σ` is symmetric. -/
theorem inner_stagger_left (φ ψ : HU L) :
    inner ℂ (stagger φ) ψ = inner ℂ φ (stagger ψ) := by
  simp only [PiLp.inner_apply, stagger_apply, RCLike.inner_apply, map_mul, map_pow, map_neg,
    map_one]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `Σ` is unitary. -/
theorem inner_stagger (φ ψ : HU L) : inner ℂ (stagger φ) (stagger ψ) = inner ℂ φ ψ := by
  rw [inner_stagger_left, stagger_stagger]

/-- **`Σ` exchanges the doublers**: `Σ e_u = e_{−u}`. -/
theorem stagger_wave (u : ℂ) : stagger (wave L u) = wave L (-u) := by
  ext j
  rw [stagger_apply, wave_apply, wave_apply, neg_pow u]
  ring

/-! ## 2. Dirac's square root -/

/-- The massive Dirac operator `D_m = T° + m Σ`. -/
def dirac (m : ℝ) : HU L →ₗ[ℂ] HU L := transport + (m : ℂ) • stagger

/-- **Dirac's square root**: `D_m² = T°² + m²`. -/
theorem dirac_sq (h2 : 2 ∣ L) (m : ℝ) (ψ : HU L) :
    dirac m (dirac m ψ) = transport (transport ψ) + ((m : ℂ) ^ 2) • ψ := by
  simp only [dirac, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    transport_stagger h2, stagger_stagger]
  module

/-! ## 3. The mass keeps every stationary state below the cone -/

theorem velocity_smul (s : ℂ) (ψ : HU L) : velocity (s • ψ) = ‖s‖ ^ 2 * velocity ψ := by
  rw [velocity, velocity, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

/-- **The velocity is odd under `Σ`**. -/
theorem velocity_stagger (h2 : 2 ∣ L) (ψ : HU L) : velocity (stagger ψ) = -velocity ψ := by
  rw [velocity, velocity, current_stagger h2, inner_neg_right, inner_stagger, Complex.neg_re]

/-- **A massive stationary state moves strictly below the cone**: if `D_m ψ = E ψ` with
`m ≠ 0`, then `|⟨K⟩| < 1`. -/
theorem abs_velocity_lt_one_of_dirac (h2 : 2 ∣ L) {m : ℝ} (hm : m ≠ 0) {E : ℂ} {ψ : HU L}
    (hψ : ‖ψ‖ = 1) (hE : dirac m ψ = E • ψ) : |velocity ψ| < 1 := by
  by_contra hv
  have hv1 : |velocity ψ| = 1 := le_antisymm (abs_velocity_le hψ) (not_lt.1 hv)
  have hv2 : velocity ψ ^ 2 = 1 := by rw [← sq_abs, hv1, one_pow]
  have hs := statistics_sum hψ
  have hK0 : 0 ≤ varianceG current ψ := by unfold varianceG; positivity
  have hT0 : 0 ≤ varianceG transport ψ := by unfold varianceG; positivity
  have hmean : meanG transport ψ = 0 := by
    nlinarith only [hs, hv2, hK0, hT0, sq_nonneg (meanG transport ψ)]
  have hvar : varianceG transport ψ = 0 := by
    nlinarith only [hs, hv2, hK0, hT0, sq_nonneg (meanG transport ψ)]
  -- the transport does not move `ψ`, so `ψ` is an eigenvector of `Σ`
  have hTψ : transport ψ = 0 := by
    have hc : centeredG transport ψ = 0 := by
      rw [varianceG, sq_eq_zero_iff, norm_eq_zero] at hvar
      exact hvar
    simpa [centeredG, hmean] using hc
  have hSt : (m : ℂ) • stagger ψ = E • ψ := by
    simpa [dirac, hTψ] using hE
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hs' : stagger ψ = (E / m) • ψ := by
    rw [div_eq_inv_mul, ← smul_smul, ← hSt, smul_smul, inv_mul_cancel₀ hm', one_smul]
  -- `Σ` is unitary, so the eigenvalue has modulus `1`
  have hn : ‖E / m‖ = 1 := by
    have h1 : ‖stagger ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_stagger]
    rw [hs', norm_smul, hψ, mul_one] at h1
    nlinarith only [h1, norm_nonneg (E / m)]
  -- the velocity is odd under `Σ` and even under a phase: it vanishes
  have h0 : velocity ψ = -velocity ψ := by
    rw [← velocity_stagger h2, hs', velocity_smul, hn, one_pow, one_mul]
  have : velocity ψ = 0 := by linarith
  rw [this, abs_zero] at hv1
  exact zero_ne_one hv1

end TorusUniverse
