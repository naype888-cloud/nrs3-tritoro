/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic
public import NavaRobertsonIndependent.Mathematics.D37_PathGraph3D

/-!
# The axis of the universe: the current link by link

The universe is one three-torus covered by `M` cubes per axis, `d` positions each. An axis of the
universe is the closed axis `ZMod L`, `L = M d`: finite, with no end (`TorusCover`). Its transport
is `(T°ψ)_j = (ψ_{j+1} + ψ_{j−1})/2`, every link alike, the closing link included.

The current is measured link by link, every link moves one position:

  `(Kψ)_j = (i/2)(ψ_{j+1} − ψ_{j−1})`.

* Inside a cube `K` is the commutator of `D38`: if a coordinate `x` moves the same step `s` on the
  two links at `j`, then `(i[T°, X]ψ)_j = s (Kψ)_j`. With the step `h = 2/(d − 1)` of the cube,
  `⟨K⟩` is the velocity `((d − 1)/2) ⟨K_d⟩` of `D38`.
* No coordinate does it on the whole axis. The steps of a coordinate add up to `0` around the
  axis, so if all links but one move `s`, the last one moves `−(L − 1) s`. For one cube closed on
  itself (`L = d`, `s = 2/(d − 1)`) this is the jump `−2` of the seam of `P_d`: the jump, not the
  state, is what gave tensions above `1` on the closed axis.
* Nothing moves more than one position per step: `|⟨K⟩| ≤ 1` for unit states. The phase mode
  `i^j` reaches `−1` when `4 ∣ L`, but `T° i^j = 0`: its transport does not fluctuate.
* Transport and current share the unit. The shift `S` is unitary, `T° = (S + S⁻¹)/2`,
  `K = i(S − S⁻¹)/2`, so `T°² + K² = 1` and for every unit state

    `⟨T°⟩² + Var T° + ⟨K⟩² + Var K = 1`.

  A variance `0` would be a perfect estimate. With `Var T° > 0`, `|⟨K⟩| < 1`: the cone is a
  limit that no state with fluctuating transport reaches.

## Main results

- `TorusUniverse.commutator_apply_of_steps` : inside a cube, `i[T°, X] = s K`.
- `TorusUniverse.closing_step` : all links but one move `s`, the last one `−(L − 1) s`.
- `TorusUniverse.step_eq_zero` : no coordinate moves the same nonzero step on every link.
- `TorusUniverse.abs_velocity_le` : `|⟨K⟩| ≤ 1` for unit states.
- `TorusUniverse.current_phaseMode`, `TorusUniverse.transport_phaseMode` : the phase mode moves at
  `−1` with `T° i^j = 0`, for `4 ∣ L`.
- `TorusUniverse.statistics_sum` : `⟨T°⟩² + Var T° + ⟨K⟩² + Var K = 1`.
- `TorusUniverse.abs_velocity_lt_one` : `Var T° > 0` gives `|⟨K⟩| < 1`.
-/

@[expose] public noncomputable section

open Complex

namespace TorusUniverse

variable {L : ℕ}

/-- The states on an axis of `L` positions of the universe. -/
abbrev HU (L : ℕ) := EuclideanSpace ℂ (ZMod L)

/-- The transport of the closed axis, `(T°ψ)_j = (ψ_{j+1} + ψ_{j−1})/2`. -/
def transport : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun j => (ψ (j + 1) + ψ (j - 1)) / 2
  map_add' ψ φ := by ext j; simp only [PiLp.add_apply]; ring
  map_smul' c ψ := by
    ext j; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The current link by link, `(Kψ)_j = (i/2)(ψ_{j+1} − ψ_{j−1})`. -/
def current : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun j => I / 2 * (ψ (j + 1) - ψ (j - 1))
  map_add' ψ φ := by ext j; simp only [PiLp.add_apply]; ring
  map_smul' c ψ := by
    ext j; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- A coordinate on the axis: multiplication by `x_j`. -/
def chart (x : ZMod L → ℝ) : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun j => (x j : ℂ) * ψ j
  map_add' ψ φ := by ext j; simp only [PiLp.add_apply]; ring
  map_smul' c ψ := by
    ext j; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem transport_apply (ψ : HU L) (j : ZMod L) :
    transport ψ j = (ψ (j + 1) + ψ (j - 1)) / 2 := rfl

theorem current_apply (ψ : HU L) (j : ZMod L) :
    current ψ j = I / 2 * (ψ (j + 1) - ψ (j - 1)) := rfl

theorem chart_apply (x : ZMod L → ℝ) (ψ : HU L) (j : ZMod L) :
    chart x ψ j = (x j : ℂ) * ψ j := rfl

/-! ## 1. Inside a cube the commutator is the link current -/

/-- The commutator with a coordinate,
`(i[T°, X]ψ)_j = (i/2)((x_{j+1} − x_j) ψ_{j+1} + (x_{j−1} − x_j) ψ_{j−1})`. -/
theorem commutator_apply (x : ZMod L → ℝ) (ψ : HU L) (j : ZMod L) :
    (I • (transport ∘ₗ chart x - chart x ∘ₗ transport)) ψ j =
      I / 2 * (((x (j + 1) - x j : ℝ) : ℂ) * ψ (j + 1) +
        ((x (j - 1) - x j : ℝ) : ℂ) * ψ (j - 1)) := by
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul, transport_apply, chart_apply]
  push_cast
  ring

/-- **Inside a cube the commutator is the link current**: if the coordinate moves the same step
`s` on the two links at `j`, then `(i[T°, X]ψ)_j = s (Kψ)_j`. -/
theorem commutator_apply_of_steps {x : ZMod L → ℝ} {s : ℝ} {j : ZMod L}
    (h₁ : x (j + 1) - x j = s) (h₀ : x j - x (j - 1) = s) (ψ : HU L) :
    (I • (transport ∘ₗ chart x - chart x ∘ₗ transport)) ψ j = (s : ℂ) * current ψ j := by
  rw [commutator_apply, current_apply, h₁, show x (j - 1) - x j = -s by linarith]
  push_cast
  ring

/-! ## 2. No coordinate does it on the whole axis -/

variable [NeZero L]

theorem sum_add_one {M : Type*} [AddCommMonoid M] (f : ZMod L → M) :
    ∑ j, f (j + 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl

theorem sum_sub_one {M : Type*} [AddCommMonoid M] (f : ZMod L → M) :
    ∑ j, f (j - 1) = ∑ j, f j :=
  Fintype.sum_equiv (Equiv.subRight 1) _ _ fun _ => rfl

/-- The steps of a coordinate add up to `0` around the closed axis. -/
theorem sum_steps (x : ZMod L → ℝ) : ∑ j, (x (j + 1) - x j) = 0 := by
  rw [Finset.sum_sub_distrib, sum_add_one, sub_self]

/-- **The closing step**: if every link but the one at `j₀` moves `s`, that one moves
`−(L − 1) s`. -/
theorem closing_step {x : ZMod L → ℝ} {s : ℝ} (j₀ : ZMod L)
    (h : ∀ j, j ≠ j₀ → x (j + 1) - x j = s) :
    x (j₀ + 1) - x j₀ = -(((L : ℝ) - 1) * s) := by
  have hs := sum_steps x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
    Finset.sum_congr rfl fun j hj => h j (Finset.ne_of_mem_erase hj), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at hs
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne L)), Nat.cast_one] at hs
  linarith

/-- **No coordinate moves the same step on every link**: equal steps `s` give `L s = 0`. -/
theorem step_eq_zero {x : ZMod L → ℝ} {s : ℝ} (h : ∀ j, x (j + 1) - x j = s) : s = 0 := by
  have hs := sum_steps x
  simp only [h, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hs
  exact (mul_eq_zero.1 hs).resolve_left (by exact_mod_cast NeZero.ne L)

/-! ## 3. Nothing moves more than one position per step -/

/-- The velocity `⟨K⟩`, in positions per step. -/
def velocity (ψ : HU L) : ℝ := (inner ℂ ψ (current ψ)).re

theorem inner_current (ψ : HU L) :
    inner ℂ ψ (current ψ) =
      ∑ j, (starRingEnd ℂ) (ψ j) * (I / 2 * (ψ (j + 1) - ψ (j - 1))) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, current_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **`|⟨K⟩| ≤ ‖ψ‖²`**: every link carries at most one position per step. -/
theorem abs_velocity_le_norm_sq (ψ : HU L) : |velocity ψ| ≤ ‖ψ‖ ^ 2 := by
  calc |velocity ψ| ≤ ‖inner ℂ ψ (current ψ)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j, ‖ψ j‖ * ((‖ψ (j + 1)‖ + ‖ψ (j - 1)‖) / 2) := by
        rw [inner_current]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, Complex.norm_conj, norm_mul, norm_div, Complex.norm_I]
        have := norm_sub_le (ψ (j + 1)) (ψ (j - 1))
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2]
        gcongr
        linarith
    _ ≤ ∑ j, ((‖ψ j‖ ^ 2 + ‖ψ (j + 1)‖ ^ 2) / 4 + (‖ψ j‖ ^ 2 + ‖ψ (j - 1)‖ ^ 2) / 4) := by
        gcongr with j
        nlinarith [sq_nonneg (‖ψ j‖ - ‖ψ (j + 1)‖), sq_nonneg (‖ψ j‖ - ‖ψ (j - 1)‖)]
    _ = ‖ψ‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Finset.sum_add_distrib, ← Finset.sum_div]
        rw [sum_add_one (fun j => ‖ψ j‖ ^ 2), sum_sub_one (fun j => ‖ψ j‖ ^ 2)]
        ring

/-- **Nothing moves more than one position per step**: `|⟨K⟩| ≤ 1` for unit states. -/
theorem abs_velocity_le {ψ : HU L} (hψ : ‖ψ‖ = 1) : |velocity ψ| ≤ 1 := by
  simpa [hψ] using abs_velocity_le_norm_sq ψ

/-- An eigenvector of `K` with eigenvalue `−1` moves at `−‖ψ‖²`. -/
theorem velocity_of_current_eq_neg {ψ : HU L} (h : current ψ = -ψ) :
    velocity ψ = -‖ψ‖ ^ 2 := by
  rw [velocity, h, inner_neg_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-! ## 4. The phase mode reaches the cone -/

/-- The phase mode `i^j`. -/
def phaseMode (L : ℕ) [NeZero L] : HU L := WithLp.toLp 2 fun j => I ^ j.val

theorem I_pow_val_add_one (h4 : 4 ∣ L) (j : ZMod L) : I ^ (j + 1).val = I * I ^ j.val := by
  have hL : 4 ≤ L := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) h4
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < L),
    pow_eq_pow_mod _ Complex.I_pow_four, Nat.mod_mod_of_dvd _ h4,
    ← pow_eq_pow_mod _ Complex.I_pow_four, pow_succ, mul_comm]

theorem I_pow_val_sub_one (h4 : 4 ∣ L) (j : ZMod L) : I ^ (j - 1).val = -I * I ^ j.val := by
  have h := I_pow_val_add_one h4 (j - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-- **The phase mode moves at `−1`**: `K i^j = −i^j`, for `4 ∣ L`. -/
theorem current_phaseMode (h4 : 4 ∣ L) : current (phaseMode L) = -phaseMode L := by
  ext j
  simp only [current_apply, phaseMode, PiLp.neg_apply,
    I_pow_val_add_one h4, I_pow_val_sub_one h4]
  linear_combination (I ^ j.val) * Complex.I_mul_I

/-- **The phase mode does not fluctuate in transport**: `T° i^j = 0`, for `4 ∣ L`. -/
theorem transport_phaseMode (h4 : 4 ∣ L) : transport (phaseMode L) = 0 := by
  ext j
  simp only [transport_apply, phaseMode, PiLp.zero_apply,
    I_pow_val_add_one h4, I_pow_val_sub_one h4]
  ring

theorem norm_sq_phaseMode : ‖phaseMode L‖ ^ 2 = L := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [phaseMode]

/-- **The cone is reached on the whole axis**: for `4 ∣ L` a unit state moves at `−1`. -/
theorem exists_velocity_eq_neg_one (h4 : 4 ∣ L) :
    ∃ ψ : HU L, ‖ψ‖ = 1 ∧ velocity ψ = -1 := by
  have hpos : 0 < ‖phaseMode L‖ := by
    have : (0 : ℝ) < ‖phaseMode L‖ ^ 2 := by
      rw [norm_sq_phaseMode]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact lt_of_le_of_ne (norm_nonneg _) fun h => by rw [← h] at this; simp at this
  set ψ : HU L := ((‖phaseMode L‖⁻¹ : ℝ) : ℂ) • phaseMode L
  have hψ : ‖ψ‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
      inv_mul_cancel₀ hpos.ne']
  refine ⟨ψ, hψ, ?_⟩
  have hK : current ψ = -ψ := by
    rw [map_smul, current_phaseMode h4, smul_neg]
  rw [velocity_of_current_eq_neg hK, hψ]
  norm_num

/-! ## 5. Transport and current share the unit -/

open PathGraph3DNRS

/-- `‖T°ψ‖² + ‖Kψ‖² = ‖ψ‖²`: the parallelogram law on every link. -/
theorem norm_sq_transport_add_norm_sq_current (ψ : HU L) :
    ‖transport ψ‖ ^ 2 + ‖current ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h : ∀ j, ‖transport ψ j‖ ^ 2 + ‖current ψ j‖ ^ 2 =
      (‖ψ (j + 1)‖ ^ 2 + ‖ψ (j - 1)‖ ^ 2) / 2 := fun j => by
    rw [transport_apply, current_apply, norm_div, norm_mul, norm_div, Complex.norm_I, h2]
    linear_combination (1 / 4 : ℝ) * parallelogram_law_with_norm ℂ (ψ (j + 1)) (ψ (j - 1))
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_add_distrib]
  simp only [h, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [sum_add_one (fun j => ‖ψ j‖ ^ 2), sum_sub_one (fun j => ‖ψ j‖ ^ 2)]
  ring

/-- For a unit state, `Var A = ‖Aψ‖² − ⟨A⟩²`. -/
theorem varianceG_eq (A : HU L →ₗ[ℂ] HU L) {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    varianceG A ψ = ‖A ψ‖ ^ 2 - meanG A ψ ^ 2 := by
  have hre : (inner ℂ (A ψ) ψ).re = meanG A ψ := by
    rw [meanG, ← inner_conj_symm, Complex.conj_re]
  rw [varianceG, centeredG, norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, hψ,
    Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs, RCLike.re_to_complex,
    Complex.re_ofReal_mul, hre]
  ring

/-- **Transport and current share the unit**: `⟨T°⟩² + Var T° + ⟨K⟩² + Var K = 1` for unit
states. -/
theorem statistics_sum {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    meanG transport ψ ^ 2 + varianceG transport ψ + velocity ψ ^ 2 + varianceG current ψ = 1 := by
  have h := norm_sq_transport_add_norm_sq_current ψ
  rw [hψ, one_pow] at h
  rw [varianceG_eq _ hψ, varianceG_eq _ hψ, show meanG current ψ = velocity ψ from rfl]
  linarith

/-- **The cone is a limit**: a unit state whose transport fluctuates moves strictly below one
position per step. -/
theorem abs_velocity_lt_one {ψ : HU L} (hψ : ‖ψ‖ = 1) (hT : 0 < varianceG transport ψ) :
    |velocity ψ| < 1 := by
  have h := statistics_sum hψ
  have hK : 0 ≤ varianceG current ψ := by unfold varianceG; positivity
  have hv : velocity ψ ^ 2 < 1 := by nlinarith [sq_nonneg (meanG transport ψ)]
  rw [← sq_abs] at hv
  nlinarith [abs_nonneg (velocity ψ)]

end TorusUniverse
