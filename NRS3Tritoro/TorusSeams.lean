/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusArea
public import NRS3DeSitter.DeSitterHorizon

/-!
# The seams of the three-torus with loop quantum gravity and with de Sitter

**Loop quantum gravity.** Each of the `2 · dy · dz` boundary steps of the cut of the torus
(`TorusArea.crossSteps`) is open or closed: two states, the `2 j + 1 = 2` states of a puncture of
spin `j = 1/2`. The entropy of the cut is then the entropy of `n = 2 · dy · dz` punctures of spin
`1/2` (Rovelli, ch. 10), and the area of the cut is `n · A(1/2)`, `A(1/2) = 4 π √3 γ ℓ_P²` the
lowest level of the area spectrum. The Bekenstein–Hawking law `S = A / (4 ℓ_P²)` holds exactly
when `γ = log 2 / (π √3)`: the Immirzi parameter of the cube, on the torus too, with twice the
punctures.

**de Sitter.** The entropy of the cut fixes the constant of a de Sitter horizon,
`Λ = 3 π / (ℓ² S) = 3 π / (2 ℓ² dy dz log 2)`. The de Sitter scale factor with this `Λ` solves
both Friedmann equations (`NRS3DeSitter`), and with `a² = 4 ℓ² log 2` per step the horizon area
`12 π / Λ` is the area `a² · 2 dy dz` of the two faces of the cut. Closing the axes halves `Λ`
at the same face.

The definitions of the area spectrum and of the puncture entropy are those of `NRS3Rovelli`,
restated because that repository pins a different version of `NavaRobertsonIndependent`.

## Main results

- `TorusSeams.cutEntropy_eq_punctureEntropy` : `S_cut = S_punct(2 dy dz, 1/2)`.
- `TorusSeams.torus_immirzi_iff` : `S = A / (4 ℓ_P²)` iff `γ = log 2 / (π √3)`.
- `TorusSeams.cutCosmologicalConstant_eq` : `Λ = 3 π / (2 ℓ² dy dz log 2)`.
- `TorusSeams.cutCosmologicalConstant_eq_half` : it is half the constant of the cube cut.
- `TorusSeams.horizonArea_cutCosmologicalConstant` : the horizon area is `a² · 2 dy dz`.
- `TorusSeams.cut_firstOrderFriedmann`, `TorusSeams.cut_secondOrderFriedmann` : the de Sitter
  scale factor of the cut solves both Friedmann equations.
-/

@[expose] public noncomputable section

open TorusArea Real

namespace TorusSeams

/-! ## 1. Punctures of spin `1/2` -/

/-- The LQG area spectrum `A(j) = 8 π γ ℓ_P² √(j (j + 1))`. -/
def areaSpectrum (lp γ j : ℝ) : ℝ := 8 * π * γ * lp ^ 2 * √(j * (j + 1))

/-- The lowest level: `A(1/2) = 4 π √3 γ ℓ_P²`. -/
theorem areaSpectrum_half (lp γ : ℝ) : areaSpectrum lp γ (1 / 2) = 4 * π * √3 * γ * lp ^ 2 := by
  have h : √((1 / 2 : ℝ) * (1 / 2 + 1)) = √3 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 / 2 + 1) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [areaSpectrum, h]
  ring

/-- The entropy of `n` punctures of spin `j`: `n log (2 j + 1)`. -/
def punctureEntropy (n : ℕ) (j : ℝ) : ℝ := n * Real.log (2 * j + 1)

variable {dx dy dz : ℕ}

/-- **The boundary steps are punctures of spin `1/2`**: the entropy of the cut is the entropy of
`2 · dy · dz` punctures, two states each. -/
theorem cutEntropy_eq_punctureEntropy {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    cutEntropy dx dy dz c = punctureEntropy (crossSteps dx dy dz c).card (1 / 2) := by
  rw [cutEntropy_eq hc hd, card_crossSteps hc hd, punctureEntropy]
  norm_num

/-- **Bekenstein–Hawking fixes the Immirzi parameter on the torus.** With the boundary steps as
punctures of spin `1/2`, `S = A / (4 ℓ_P²)` holds iff `γ = log 2 / (π √3)`. -/
theorem torus_immirzi_iff {lp γ : ℝ} (hlp : lp ≠ 0) (hy : 0 < dy) (hz : 0 < dz) {c : ℕ}
    (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    cutEntropy dx dy dz c =
        (crossSteps dx dy dz c).card * areaSpectrum lp γ (1 / 2) / (4 * lp ^ 2) ↔
      γ = Real.log 2 / (π * √3) := by
  have hπ : π * √3 ≠ 0 := by positivity
  have hn : ((2 * (dy * dz) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [cutEntropy_eq hc hd, card_crossSteps hc hd, areaSpectrum_half, eq_div_iff hπ]
  constructor
  · intro h
    field_simp at h
    linear_combination -h
  · intro h
    field_simp
    rw [← h]
    ring

/-! ## 2. The de Sitter horizon of the cut -/

open Cosmology.FLRW.FriedmannEquation

/-- The constant of a de Sitter horizon whose entropy is the entropy of the cut. -/
def cutCosmologicalConstant (dx dy dz c : ℕ) (ℓ : ℝ) : ℝ :=
  entropyCosmologicalConstant (cutEntropy dx dy dz c) ℓ

/-- **`Λ = 3 π / (2 ℓ² dy dz log 2)`.** -/
theorem cutCosmologicalConstant_eq {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (ℓ : ℝ) :
    cutCosmologicalConstant dx dy dz c ℓ =
      3 * π / (ℓ ^ 2 * ((2 * (dy * dz) : ℕ) * Real.log 2)) := by
  rw [cutCosmologicalConstant, entropyCosmologicalConstant, cutEntropy_eq hc hd]

/-- **Closing the axes halves `Λ`** at the same face: the torus constant is half the constant
`3 π / (ℓ² dy dz log 2)` of the cut of the cube. -/
theorem cutCosmologicalConstant_eq_half {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (ℓ : ℝ) :
    cutCosmologicalConstant dx dy dz c ℓ =
      3 * π / (ℓ ^ 2 * ((dy * dz : ℕ) * Real.log 2)) / 2 := by
  rw [cutCosmologicalConstant_eq hc hd]
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp
  rcases Nat.eq_zero_or_pos (dy * dz) with h | h
  · simp [h]
  have h1 : (0 : ℝ) < (dy * dz : ℕ) := by exact_mod_cast h
  have h2 := Real.log_pos one_lt_two
  push_cast
  field_simp

theorem cutEntropy_pos {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) :
    0 < cutEntropy dx dy dz c := by
  rw [cutEntropy_eq hc hd]
  have : (0 : ℝ) < (2 * (dy * dz) : ℕ) := by exact_mod_cast (by positivity)
  have := Real.log_pos one_lt_two
  positivity

theorem cutCosmologicalConstant_pos {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy)
    (hz : 0 < dz) {ℓ : ℝ} (hℓ : ℓ ≠ 0) : 0 < cutCosmologicalConstant dx dy dz c ℓ :=
  entropyCosmologicalConstant_pos (cutEntropy_pos hc hd hy hz) hℓ

/-- **The horizon has the area of the two faces.** With `a² = 4 ℓ² log 2` per step, the area
`12 π / Λ` of the de Sitter horizon is `a² · 2 dy dz`. -/
theorem horizonArea_cutCosmologicalConstant {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx)
    (hy : 0 < dy) (hz : 0 < dz) {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    deSitterHorizonArea (cutCosmologicalConstant dx dy dz c ℓ) =
      a ^ 2 * (2 * (dy * dz) : ℕ) := by
  have h1 : (0 : ℝ) < (2 * (dy * dz) : ℕ) := by exact_mod_cast (by positivity)
  have h2 := Real.log_pos one_lt_two
  rw [deSitterHorizonArea_eq (cutCosmologicalConstant_pos hc hd hy hz hℓ),
    cutCosmologicalConstant_eq hc hd, ha]
  field_simp
  norm_num

/-- **The cut fixes a de Sitter solution**: the scale factor with the constant of the cut solves
the first Friedmann equation. -/
theorem cut_firstOrderFriedmann {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy)
    (hz : 0 < dz) {a₀ σ ℓ G cc : ℝ} (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ (cutCosmologicalConstant dx dy dz c ℓ) cc)
      (fun _ => 0) 0 (cutCosmologicalConstant dx dy dz c ℓ) G cc t :=
  entropyCosmologicalConstant_firstOrderFriedmann (cutEntropy_pos hc hd hy hz) hℓ ha₀ hσ t

/-- The same scale factor solves the second Friedmann equation. -/
theorem cut_secondOrderFriedmann {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy)
    (hz : 0 < dz) {a₀ σ ℓ G cc : ℝ} (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ (cutCosmologicalConstant dx dy dz c ℓ) cc)
      (fun _ => 0) (fun _ => 0) (cutCosmologicalConstant dx dy dz c ℓ) G cc t :=
  entropyCosmologicalConstant_secondOrderFriedmann (cutEntropy_pos hc hd hy hz) hℓ ha₀ hσ t

end TorusSeams
