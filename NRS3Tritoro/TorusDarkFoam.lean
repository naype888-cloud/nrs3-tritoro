/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusBoundaryField

/-!
# The dark field is a foam: flat on average, fluctuating at every step

`TorusSaturation` showed that the saturated distribution of the cut is the uniform one, and
`TorusBoundaryField` that each configuration is a field operator `F(S)`. Here is what the uniform
distribution looks like, step by step.

* **No gradient.** Flipping every boundary step, `S ↦ S^c`, is a bijection of the configurations
  that exchanges open and closed at each step. So under the uniform distribution every boundary
  step is open with probability exactly `1/2`: no step is preferred, none pulls more than another.
* **The mean field is flat.** The mean bracket `Σ_S d(S) · [T3c, P_x]|_S` is, entry by entry, the
  probability of the step times the bracket on it. For the uniform distribution it is half the
  full bracket of the cut, on every boundary step alike, and its field is half the field of the
  fully open boundary: `Σ_S d(S) F(S) = ½ F(all open)`.
* **Every step fluctuates the most a bit can.** A step that is open with probability `p` has
  variance `p (1 − p) ≤ 1/4`, and the uniform distribution reaches `1/4` on every step.

Smooth on average, maximally fluctuating at the smallest scale: the dark field of the postulate
behaves as the foam. Every result is stated for any saturated distribution as well.

## Main results

- `TorusDarkFoam.openProb_uniform` : every boundary step is open with probability `1/2`.
- `TorusDarkFoam.meanBracket_apply` : the mean bracket is probability times bracket.
- `TorusDarkFoam.meanBracket_uniform` : the uniform mean bracket is half the full bracket.
- `TorusDarkFoam.meanField_uniform` : `Σ_S d(S) F(S) = ½ F(all open)`.
- `TorusDarkFoam.bitVariance_le`, `TorusDarkFoam.bitVariance_uniform` : `p (1 − p) ≤ 1/4`,
  reached on every step.
- `TorusDarkFoam.openProb_of_saturated`, `TorusDarkFoam.meanBracket_of_saturated`,
  `TorusDarkFoam.bitVariance_of_saturated` : the same for every saturated distribution.
-/

@[expose] public noncomputable section

open TorusArea TorusBekenstein TorusSaturation TorusBoundaryField TorusField
open PathGraph3D (Site3D)

namespace TorusDarkFoam

variable {dx dy dz c : ℕ}

/-- The probability that the step `s` is open (`BoundaryBits.openProb`). -/
abbrev openProb (d : ProbDistribution (Config dx dy dz c))
    (s : Site3D dx dy dz × Site3D dx dy dz) : ℝ :=
  BoundaryBits.openProb d s

/-- **No gradient.** Under the uniform distribution every boundary step is open with
probability `1/2`. -/
theorem openProb_uniform {s : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ crossSteps dx dy dz c) :
    openProb (ProbDistribution.uniform (α := Config dx dy dz c)) s = 1 / 2 :=
  BoundaryBits.openProb_uniform hs

/-- The mean bracket of a distribution of the cut. -/
def meanBracket (d : ProbDistribution (Config dx dy dz c)) :
    Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  ∑ S, ((d S : ℝ) : ℂ) • cutBracket S

/-- **The mean bracket is probability times bracket**, step by step. -/
theorem meanBracket_apply (d : ProbDistribution (Config dx dy dz c)) (p q : Site3D dx dy dz) :
    meanBracket d p q = (openProb d (p, q) : ℂ) * bracketX dx dy dz p q := by
  simp only [meanBracket, openProb, BoundaryBits.openProb, Matrix.sum_apply, Matrix.smul_apply,
    cutBracket,
    smul_eq_mul, mul_ite, mul_zero, Complex.ofReal_sum, apply_ite (fun x : ℝ => (x : ℂ)),
    Complex.ofReal_zero, Finset.sum_mul, ite_mul, zero_mul]

/-- Every boundary step open. -/
def allOpen : Config dx dy dz c := ⟨crossSteps dx dy dz c, Finset.mem_powerset_self _⟩

/-- A step off the boundary is never open. -/
lemma openProb_eq_zero (d : ProbDistribution (Config dx dy dz c))
    {s : Site3D dx dy dz × Site3D dx dy dz} (hs : s ∉ crossSteps dx dy dz c) :
    openProb d s = 0 :=
  BoundaryBits.openProb_eq_zero d hs

/-- **The mean field is flat**: the uniform mean bracket is half the full bracket of the cut. -/
theorem meanBracket_uniform :
    meanBracket (ProbDistribution.uniform (α := Config dx dy dz c)) =
      (1 / 2 : ℂ) • cutBracket (allOpen : Config dx dy dz c) := by
  ext p q
  rw [meanBracket_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (p, q) ∈ crossSteps dx dy dz c
  · rw [openProb_uniform h]
    simp [cutBracket, allOpen, h]
  · rw [openProb_eq_zero _ h]
    simp [cutBracket, allOpen, h]

/-- The mean field operator of the uniform distribution: `Σ_S d(S) F(S) = ½ F(all open)`. -/
theorem meanField_uniform {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : LadderSystem ℂ V d) (e : Site3D dx dy dz ≃ Fin d) :
    ∑ S, (((ProbDistribution.uniform (α := Config dx dy dz c)) S : ℝ) : ℂ) • configField L e S =
      (1 / 2 : ℂ) • configField L e (allOpen : Config dx dy dz c) := by
  simp only [configField, ← map_smul, ← map_sum]
  rw [← meanBracket, meanBracket_uniform]

/-- A bit open with probability `p` fluctuates at most `1/4`. -/
theorem bitVariance_le (d : ProbDistribution (Config dx dy dz c))
    (s : Site3D dx dy dz × Site3D dx dy dz) : openProb d s * (1 - openProb d s) ≤ 1 / 4 :=
  BoundaryBits.bitVariance_le d s

/-- **Every boundary step fluctuates the most a bit can.** -/
theorem bitVariance_uniform {s : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ crossSteps dx dy dz c) :
    openProb (ProbDistribution.uniform (α := Config dx dy dz c)) s *
      (1 - openProb (ProbDistribution.uniform (α := Config dx dy dz c)) s) = 1 / 4 :=
  BoundaryBits.bitVariance_uniform hs

variable {d : ProbDistribution (Config dx dy dz c)}

/-- A saturated distribution has no gradient. -/
theorem openProb_of_saturated (h : Hₛ d = cutEntropy dx dy dz c)
    {s : Site3D dx dy dz × Site3D dx dy dz} (hs : s ∈ crossSteps dx dy dz c) :
    openProb d s = 1 / 2 := by
  rw [saturated_iff_uniform.1 h]
  exact openProb_uniform hs

/-- A saturated distribution has the flat mean bracket. -/
theorem meanBracket_of_saturated (h : Hₛ d = cutEntropy dx dy dz c) :
    meanBracket d = (1 / 2 : ℂ) • cutBracket (allOpen : Config dx dy dz c) := by
  rw [saturated_iff_uniform.1 h]
  exact meanBracket_uniform

/-- A saturated distribution fluctuates the most on every boundary step. -/
theorem bitVariance_of_saturated (h : Hₛ d = cutEntropy dx dy dz c)
    {s : Site3D dx dy dz × Site3D dx dy dz} (hs : s ∈ crossSteps dx dy dz c) :
    openProb d s * (1 - openProb d s) = 1 / 4 := by
  rw [saturated_iff_uniform.1 h]
  exact bitVariance_uniform hs

end TorusDarkFoam
