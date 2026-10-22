/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusBekenstein

/-!
# Saturating a quantum: the region becomes dark

`TorusBekenstein` bounds what a region of the torus holds by its boundary, `H ≤ S`, and the
bound is reached. A distribution with `H = S` has filled the region to capacity: no distribution
of the same cut holds more (`isMax_of_saturated`). It is reached only once: `−x log x` is strictly
concave, so the equality case of Jensen forces every configuration to the same weight. Saturated
means perfectly distributed, every boundary step alike (`saturated_iff_uniform`).

**Nava's postulate (declared).** Compress matter until a quantum is filled to capacity and all of
it becomes dark, dark matter and dark energy: the start of a singularity. It is declared as the
bridge `HSaturationDark`, in the style of `HGaussBonnet` and `HBekensteinHawking`: every region
has a dark share `≤ 1`, and a saturated region has dark share `1`, so its light share is `0`.
Lean does not derive the postulate; it derives what follows from it, and shows it satisfiable.

## Main results

- `TorusSaturation.isMax_of_saturated` : a saturated distribution holds the most the cut allows.
- `TorusSaturation.eq_uniform_of_entropy_eq` : `H = log |α|` only for the uniform distribution.
- `TorusSaturation.saturated_iff_uniform` : `H = S` iff the distribution of the cut is uniform.
- `TorusSaturation.HSaturationDark` : Nava's postulate, declared.
- `TorusSaturation.hSaturationDark_satisfiable` : the bridge is consistent.
- `TorusSaturation.HSaturationDark.darkShare_uniform` : the uniform distribution is dark.
- `TorusSaturation.HSaturationDark.lightShare_eq_zero` : at saturation no light is left.
- `TorusSaturation.HSaturationDark.darkShare_of_area` : reaching `A / (4 ℓ_P²)` is darkness.
- `TorusSaturation.HSaturationDark.eq_uniform_of_saturation` : the dark region of the postulate is
  the perfectly distributed one.
-/

@[expose] public noncomputable section

open TorusArea TorusBekenstein

namespace TorusSaturation

variable {dx dy dz c : ℕ}

/-- **A saturated region is full.** If `H = S`, no distribution of the cut holds more. -/
theorem isMax_of_saturated {d : ProbDistribution (Config dx dy dz c)}
    (h : Hₛ d = cutEntropy dx dy dz c) (d' : ProbDistribution (Config dx dy dz c)) :
    Hₛ d' ≤ Hₛ d :=
  h ▸ entropy_le_cutEntropy d'

/-- **Only the uniform distribution reaches `log |α|`.** Equality in Jensen for the strictly
concave `−x log x` puts the same weight on every outcome. -/
theorem eq_uniform_of_entropy_eq {α : Type*} [Fintype α] [Nonempty α] {d : ProbDistribution α}
    (h : Hₛ d = Real.log (Fintype.card α)) : d = ProbDistribution.uniform :=
  BoundaryBits.eq_uniform_of_entropy_eq h

/-- **Saturated means perfectly distributed.** A distribution of the cut reaches `H = S` iff it
gives every configuration the same weight. -/
theorem saturated_iff_uniform {d : ProbDistribution (Config dx dy dz c)} :
    Hₛ d = cutEntropy dx dy dz c ↔ d = ProbDistribution.uniform :=
  ⟨fun h => eq_uniform_of_entropy_eq (h.trans (log_card_config c).symm),
    fun h => h ▸ entropy_uniform c⟩

/-- **Nava's postulate (declared hypothesis).** Filling a quantum to capacity turns all of it
dark: a distribution of the cut that saturates the Bekenstein bound has dark share `1`. -/
structure HSaturationDark (dx dy dz c : ℕ) where
  darkShare : ProbDistribution (Config dx dy dz c) → ℝ
  darkShare_le_one : ∀ d, darkShare d ≤ 1
  saturation : ∀ d, Hₛ d = cutEntropy dx dy dz c → darkShare d = 1

theorem hSaturationDark_satisfiable : Nonempty (HSaturationDark dx dy dz c) :=
  ⟨⟨fun _ => 1, fun _ => le_rfl, fun _ _ => rfl⟩⟩

namespace HSaturationDark

variable (H : HSaturationDark dx dy dz c)

/-- The light share of a region, the part that is not dark. -/
def lightShare (d : ProbDistribution (Config dx dy dz c)) : ℝ := 1 - H.darkShare d

theorem lightShare_nonneg (d : ProbDistribution (Config dx dy dz c)) : 0 ≤ H.lightShare d :=
  sub_nonneg.2 (H.darkShare_le_one d)

/-- Every configuration alike fills the quantum: the uniform distribution is dark. -/
theorem darkShare_uniform : H.darkShare ProbDistribution.uniform = 1 :=
  H.saturation _ (entropy_uniform c)

/-- **At saturation no light is left.** -/
theorem lightShare_eq_zero {d : ProbDistribution (Config dx dy dz c)}
    (h : Hₛ d = cutEntropy dx dy dz c) : H.lightShare d = 0 := by
  rw [lightShare, H.saturation d h, sub_self]

/-- With the bit of area `a² = 4 ℓ_P² log 2`, a region whose entropy reaches `A / (4 ℓ_P²)` is
dark. -/
theorem darkShare_of_area {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (hy : 0 < dy) (hz : 0 < dz)
    (hc : c + 1 < dx) (hd : 3 ≤ dx) (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2)
    {d : ProbDistribution (Config dx dy dz c)}
    (h : Hₛ d = a ^ 2 * (2 * (dy * dz) : ℕ) / (4 * ℓ ^ 2)) : H.darkShare d = 1 :=
  H.saturation d (h.trans ((bekensteinHawking_iff hℓ hy hz hc hd).2 ha).symm)

/-- The region the postulate makes dark is the perfectly distributed one, and it is dark. -/
theorem eq_uniform_of_saturation {d : ProbDistribution (Config dx dy dz c)}
    (h : Hₛ d = cutEntropy dx dy dz c) : d = ProbDistribution.uniform ∧ H.darkShare d = 1 :=
  ⟨saturated_iff_uniform.1 h, H.saturation d h⟩

end HSaturationDark

end TorusSaturation
