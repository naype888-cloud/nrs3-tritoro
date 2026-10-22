/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusArea
public import QuantumInfo.ClassicalInfo.Entropy

/-!
# The Bekenstein bound on the three-torus

A configuration of the cut `{x ≤ c}` of the torus is the set of its open boundary steps: one bit
per step, the bits on the boundary. Any probability distribution over the configurations has
Shannon entropy at most the log of their number (`Hₛ_le_log_d`), and that number is the one the
area law counts. So no state of the region holds more than its boundary:

  `H ≤ S = 2 · dy · dz · log 2`,

with no reference to the depth `dx`. With the bit of area `a² = 4 ℓ_P² log 2` of
`bekensteinHawking_iff` this is the Bekenstein bound `H ≤ A / (4 ℓ_P²)`. The bound is sharp: the
uniform distribution, every configuration alike, reaches it.

## Main results

- `TorusBekenstein.entropy_le_cutEntropy` : `H ≤ S` for every distribution of the cut.
- `TorusBekenstein.entropy_le` : `H ≤ 2 · dy · dz · log 2`.
- `TorusBekenstein.entropy_uniform` : the uniform distribution has `H = S`.
- `TorusBekenstein.bekenstein_bound` : with `a² = 4 ℓ_P² log 2`, `H ≤ A / (4 ℓ_P²)`.
- `TorusBekenstein.exists_saturating` : some distribution reaches `A / (4 ℓ_P²)`.
-/

@[expose] public noncomputable section

open TorusArea

namespace TorusBekenstein

variable {dx dy dz : ℕ}

/-- A configuration of the cut: the set of its open boundary steps. -/
abbrev Config (dx dy dz c : ℕ) := ↥(crossSteps dx dy dz c).powerset

instance (c : ℕ) : Nonempty (Config dx dy dz c) := ⟨⟨∅, Finset.empty_mem_powerset _⟩⟩

lemma log_card_config (c : ℕ) :
    Real.log (Fintype.card (Config dx dy dz c)) = cutEntropy dx dy dz c := by
  rw [Fintype.card_coe, cutEntropy]

/-- **No distribution of the cut holds more than its boundary.** -/
theorem entropy_le_cutEntropy {c : ℕ} (d : ProbDistribution (Config dx dy dz c)) :
    Hₛ d ≤ cutEntropy dx dy dz c :=
  (Hₛ_le_log_d d).trans_eq (log_card_config c)

/-- The bound in bits of the boundary: `H ≤ 2 · dy · dz · log 2`, whatever the depth. -/
theorem entropy_le {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx)
    (d : ProbDistribution (Config dx dy dz c)) :
    Hₛ d ≤ (2 * (dy * dz) : ℕ) * Real.log 2 :=
  (entropy_le_cutEntropy d).trans_eq (cutEntropy_eq hc hd)

/-- The uniform distribution reaches the bound. -/
theorem entropy_uniform (c : ℕ) :
    Hₛ (ProbDistribution.uniform (α := Config dx dy dz c)) = cutEntropy dx dy dz c := by
  rw [Hₛ_uniform, Finset.card_univ, log_card_config]

/-- **The Bekenstein bound on the torus.** With the bit of area `a² = 4 ℓ_P² log 2` per
boundary step, every distribution of the cut has `H ≤ A / (4 ℓ_P²)`. -/
theorem bekenstein_bound {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (hy : 0 < dy) (hz : 0 < dz) {c : ℕ}
    (hc : c + 1 < dx) (hd : 3 ≤ dx) (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2)
    (d : ProbDistribution (Config dx dy dz c)) :
    Hₛ d ≤ a ^ 2 * (2 * (dy * dz) : ℕ) / (4 * ℓ ^ 2) :=
  (entropy_le_cutEntropy d).trans_eq ((bekensteinHawking_iff hℓ hy hz hc hd).2 ha)

/-- The Bekenstein bound is sharp: some distribution of the cut reaches `A / (4 ℓ_P²)`. -/
theorem exists_saturating {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (hy : 0 < dy) (hz : 0 < dz) {c : ℕ}
    (hc : c + 1 < dx) (hd : 3 ≤ dx) (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    ∃ d : ProbDistribution (Config dx dy dz c),
      Hₛ d = a ^ 2 * (2 * (dy * dz) : ℕ) / (4 * ℓ ^ 2) :=
  ⟨_, (entropy_uniform c).trans ((bekensteinHawking_iff hℓ hy hz hc hd).2 ha)⟩

end TorusBekenstein
