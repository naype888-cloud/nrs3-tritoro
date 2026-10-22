/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import QuantumInfo.ClassicalInfo.Entropy

/-!
# The bits of a boundary

Let `X` be a finite set of boundary steps, each open or closed: a configuration is a subset of
`X`, and there are `2^|X|` of them. Everything here depends only on `X`, so it holds for any cut of
any space: the open cube (one face), the three-torus (the plane and the seam), the fibred box.

* **Bound.** Every distribution of the configurations has Shannon entropy `H ≤ |X| log 2`
  (`Hₛ_le_log_d`).
* **Saturation.** `H = |X| log 2` only for the uniform distribution: equality in Jensen for the
  strictly concave `−x log x` puts the same weight on every configuration.
* **No gradient.** Flipping every step, `S ↦ X \ S`, exchanges open and closed at each step, so
  under the uniform distribution every step of `X` is open with probability `1/2`.
* **Fluctuation.** A step open with probability `p` fluctuates `p (1 − p) ≤ 1/4`, and the uniform
  distribution reaches `1/4` on every step.

## Main results

- `BoundaryBits.entropy_le` : `H ≤ |X| log 2`.
- `BoundaryBits.entropy_uniform` : the uniform distribution has `H = |X| log 2`.
- `BoundaryBits.eq_uniform_of_entropy_eq` : `H = log |α|` only for the uniform distribution.
- `BoundaryBits.saturated_iff_uniform` : `H = |X| log 2` iff the distribution is uniform.
- `BoundaryBits.openProb_uniform` : every step of `X` is open with probability `1/2`.
- `BoundaryBits.bitVariance_le`, `BoundaryBits.bitVariance_uniform` : `p (1 − p) ≤ 1/4`,
  reached on every step.
-/

@[expose] public noncomputable section

namespace BoundaryBits

/-! ## 1. The bound and its saturation -/

/-- **Only the uniform distribution reaches `log |α|`.** Equality in Jensen for the strictly
concave `−x log x` puts the same weight on every outcome. -/
theorem eq_uniform_of_entropy_eq {α : Type*} [Fintype α] [Nonempty α] {d : ProbDistribution α}
    (h : Hₛ d = Real.log (Fintype.card α)) : d = ProbDistribution.uniform := by
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  have hn : 0 < n := by rw [hn_def]; exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : α, n⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_inv_cancel₀ hn.ne']
  have hsum : ∑ i, n⁻¹ • (d i : ℝ) = n⁻¹ := by
    rw [← Finset.smul_sum, d.normalized, smul_eq_mul, mul_one]
  have heq : Real.negMulLog (∑ i, n⁻¹ • (d i : ℝ)) = ∑ i, n⁻¹ • Real.negMulLog (d i) := by
    have hH : ∑ i, Real.negMulLog (d i) = Real.log n := h
    rw [hsum, ← Finset.smul_sum, hH, Real.negMulLog, Real.log_inv, smul_eq_mul]
    ring
  have hall := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff_of_pos (t := Finset.univ)
    (fun _ _ => inv_pos.2 hn) hw (fun i _ => Set.mem_Ici.2 (d i).zero_le_coe)).1 heq
  ext x
  have hconst : ∑ i, (d i : ℝ) = ∑ _i : α, (d x : ℝ) :=
    Finset.sum_congr rfl fun i _ => hall (Finset.mem_univ i) (Finset.mem_univ x)
  rw [d.normalized, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def] at hconst
  rw [ProbDistribution.uniform_def, Finset.card_univ, ← hn_def]
  field_simp
  linarith

variable {α : Type*} (X : Finset α)

/-- A configuration of the boundary: the set of its open steps. -/
abbrev Config := ↥X.powerset

instance : Nonempty (Config X) := ⟨⟨∅, Finset.empty_mem_powerset _⟩⟩

lemma log_card_config : Real.log (Fintype.card (Config X)) = X.card * Real.log 2 := by
  rw [Fintype.card_coe, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

variable {X}

/-- **No distribution of the boundary holds more than its bits.** -/
theorem entropy_le (d : ProbDistribution (Config X)) : Hₛ d ≤ X.card * Real.log 2 :=
  (Hₛ_le_log_d d).trans_eq (log_card_config X)

variable (X) in
/-- The uniform distribution reaches the bound. -/
theorem entropy_uniform :
    Hₛ (ProbDistribution.uniform (α := Config X)) = X.card * Real.log 2 := by
  rw [Hₛ_uniform, Finset.card_univ, log_card_config]

/-- **Saturated means perfectly distributed.** -/
theorem saturated_iff_uniform {d : ProbDistribution (Config X)} :
    Hₛ d = X.card * Real.log 2 ↔ d = ProbDistribution.uniform :=
  ⟨fun h => eq_uniform_of_entropy_eq (h.trans (log_card_config X).symm),
    fun h => h ▸ entropy_uniform X⟩

/-! ## 2. No gradient, and the most fluctuation -/

variable [DecidableEq α]

/-- The probability that the step `s` is open. -/
def openProb (d : ProbDistribution (Config X)) (s : α) : ℝ :=
  ∑ S, if s ∈ S.1 then (d S : ℝ) else 0

variable (X) in
/-- Flip every boundary step: the complement of a configuration. -/
def flipAll (S : Config X) : Config X :=
  ⟨X \ S.1, Finset.mem_powerset.2 Finset.sdiff_subset⟩

lemma flipAll_involutive : Function.Involutive (flipAll X) := fun S =>
  Subtype.ext (Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 S.2))

lemma mem_flipAll {s : α} (hs : s ∈ X) (S : Config X) : s ∈ (flipAll X S).1 ↔ s ∉ S.1 := by
  simp [flipAll, hs]

/-- **No gradient.** Under the uniform distribution every step of `X` is open with
probability `1/2`. -/
theorem openProb_uniform {s : α} (hs : s ∈ X) :
    openProb (ProbDistribution.uniform (α := Config X)) s = 1 / 2 := by
  set N : ℝ := (Finset.univ.card (α := Config X) : ℝ) with hN
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Finset.univ_nonempty.card_pos.ne'
  have hopen : openProb (ProbDistribution.uniform (α := Config X)) s =
      ∑ S : Config X, if s ∈ S.1 then 1 / N else 0 := by
    simp only [openProb, ProbDistribution.uniform_def, hN]
  have hclosed : (∑ S : Config X, if s ∈ S.1 then 1 / N else 0) =
      ∑ S : Config X, if s ∉ S.1 then 1 / N else 0 := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm (flipAll X) flipAll_involutive)]
    simp only [Function.Involutive.coe_toPerm, mem_flipAll hs]
  have htotal : (∑ S : Config X, if s ∈ S.1 then 1 / N else 0) +
      (∑ S : Config X, if s ∉ S.1 then 1 / N else 0) = 1 := by
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ S : Config X,
        ((if s ∈ S.1 then 1 / N else 0) + if s ∉ S.1 then 1 / N else 0) = 1 / N := by
      intro S
      by_cases h : s ∈ S.1 <;> simp [h]
    simp only [h1, Finset.sum_const, nsmul_eq_mul, ← hN]
    field_simp
  rw [hopen]
  linarith

/-- A step off the boundary is never open. -/
lemma openProb_eq_zero (d : ProbDistribution (Config X)) {s : α} (hs : s ∉ X) :
    openProb d s = 0 :=
  Finset.sum_eq_zero fun S _ =>
    ite_eq_right_iff.2 fun h => absurd (Finset.mem_powerset.1 S.2 h) hs

/-- A bit open with probability `p` fluctuates at most `1/4`. -/
theorem bitVariance_le (d : ProbDistribution (Config X)) (s : α) :
    openProb d s * (1 - openProb d s) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (openProb d s - 1 / 2)]

/-- **Every boundary step fluctuates the most a bit can.** -/
theorem bitVariance_uniform {s : α} (hs : s ∈ X) :
    openProb (ProbDistribution.uniform (α := Config X)) s *
      (1 - openProb (ProbDistribution.uniform (α := Config X)) s) = 1 / 4 := by
  rw [openProb_uniform hs]
  norm_num

end BoundaryBits
