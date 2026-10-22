/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import NRS3Tritoro.Gravity.Unruh

/-!

# The Clausius relation on a local light sheet

On a local light sheet, the Clausius relation `δQ = T δS` with the Unruh temperature and an area
law `δS = η δA` is the equation `R_kk = (2π / η) T_kk`.

## i. Overview

Take a local light sheet through a point, stationary there, with affine parameter `λ` running from
`λ₀ < 0` to `0`. Two quantities flow through it.

- The area. Its expansion is `θ(λ) = - R_kk λ`, the linearization of the Raychaudhuri equation at
  a stationary sheet. The area changes by `δA = ∫_{λ₀}^{0} θ A dλ = R_kk A λ₀² / 2`.
- The heat. The boost Killing field of surface gravity `κ` is `- κ λ k` along the sheet, so the
  heat is `δQ = ∫_{λ₀}^{0} κ (- λ) T_kk A dλ = κ T_kk A λ₀² / 2`.

The Unruh temperature of the boost is `T = κ / (2π)` (`Rindler.unruhTemperature`). The Clausius
relation `δQ = T η δA` therefore holds exactly when `R_kk = (2π / η) T_kk`. With the area law
`η = 1 / (4 ℓ²)` this is `R_kk = 8π ℓ² T_kk`: Einstein's coupling `8π G` in units `ħ = c = 1`.

The area law `δS = η δA`, the linear expansion `θ = - R_kk λ` and the form of the heat enter as
definitions: they are the inputs of Jacobson's argument. Only the integrals and the algebra are
proved here.

## ii. Key results

- `LightSheet.areaChange_eq` : the area changes by `R_kk A λ₀² / 2`.
- `LightSheet.heat_eq` : the heat is `κ T_kk A λ₀² / 2`.
- `LightSheet.clausius_iff` : the Clausius relation holds exactly when `R_kk = (2π / η) T_kk`.
- `LightSheet.eight_pi` : with `η = 1 / (4 ℓ²)`, `R_kk = 8π ℓ² T_kk`.

## iii. Table of contents

- A. The area and the heat of a light sheet
- B. The Clausius relation

## iv. References

- T. Jacobson, *Thermodynamics of spacetime: the Einstein equation of state*,
  Phys. Rev. Lett. 75 (1995) 1260, arXiv:gr-qc/9504004.
- W. G. Unruh, *Notes on black-hole evaporation*, Phys. Rev. D 14 (1976) 870.

-/

@[expose] public section

namespace LightSheet

open intervalIntegral

/-!

## A. The area and the heat of a light sheet

-/

/-- The change of the area of a light sheet stationary at `λ = 0`, from `λ₀` to `0`, with
expansion `θ(λ) = - R_kk λ`: `δA = ∫_{λ₀}^{0} θ A dλ`. -/
noncomputable def areaChange (Rkk A l₀ : ℝ) : ℝ := ∫ l in l₀..0, (- Rkk * l) * A

/-- The heat that crosses a light sheet, from `λ₀` to `0`, for the boost Killing field
`- κ λ k` of surface gravity `κ`: `δQ = ∫_{λ₀}^{0} κ (- λ) T_kk A dλ`. -/
noncomputable def heat (κ Tkk A l₀ : ℝ) : ℝ := ∫ l in l₀..0, κ * (- l) * Tkk * A

variable {Rkk Tkk A κ η l₀ : ℝ}

/-- The area of a light sheet changes by `R_kk A λ₀² / 2`. -/
lemma areaChange_eq (Rkk A l₀ : ℝ) : areaChange Rkk A l₀ = Rkk * A * l₀ ^ 2 / 2 := by
  have h : ∀ l : ℝ, (- Rkk * l) * A = (- Rkk * A) * l := fun l => by ring
  unfold areaChange
  rw [funext h, intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The heat that crosses a light sheet is `κ T_kk A λ₀² / 2`. -/
lemma heat_eq (κ Tkk A l₀ : ℝ) : heat κ Tkk A l₀ = κ * Tkk * A * l₀ ^ 2 / 2 := by
  have h : ∀ l : ℝ, κ * (- l) * Tkk * A = (- (κ * Tkk * A)) * l := fun l => by ring
  unfold heat
  rw [funext h, intervalIntegral.integral_const_mul, integral_id]
  ring

/-!

## B. The Clausius relation

-/

/-- The Clausius relation `δQ = T δS` on a light sheet, with the Unruh temperature of the boost
and the area law `δS = η δA`. -/
def Clausius (η κ Rkk Tkk A l₀ : ℝ) : Prop :=
  heat κ Tkk A l₀ = Rindler.unruhTemperature κ * (η * areaChange Rkk A l₀)

/-- **The Clausius relation is the equation `R_kk = (2π / η) T_kk`**, for a sheet of nonzero area
and extent and a boost of nonzero surface gravity. -/
lemma clausius_iff (hκ : κ ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0) (hη : η ≠ 0) :
    Clausius η κ Rkk Tkk A l₀ ↔ Rkk = 2 * Real.pi / η * Tkk := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hl2 : l₀ ^ 2 ≠ 0 := pow_ne_zero 2 hl
  simp only [Clausius, heat_eq, areaChange_eq, Rindler.unruhTemperature]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp

/-- **Einstein's coupling**: with the area law `η = 1 / (4 ℓ²)`, the Clausius relation is
`R_kk = 8π ℓ² T_kk`. -/
lemma eight_pi {ℓ : ℝ} (hℓ : ℓ ≠ 0) (hκ : κ ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0) :
    Clausius (1 / (4 * ℓ ^ 2)) κ Rkk Tkk A l₀ ↔ Rkk = 8 * Real.pi * ℓ ^ 2 * Tkk := by
  have hη : (1 / (4 * ℓ ^ 2) : ℝ) ≠ 0 := by positivity
  rw [clausius_iff hκ hA hl hη]
  constructor <;> intro h <;> rw [h] <;> field_simp <;> ring

end LightSheet
