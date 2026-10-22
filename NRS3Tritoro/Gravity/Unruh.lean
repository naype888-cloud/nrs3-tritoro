/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!

# The Rindler worldline and the Unruh temperature

A uniformly accelerated observer in the Minkowski plane is periodic in imaginary proper time,
with period `2π / a`, and no smaller period exists.

## i. Overview

In units `ħ = c = k_B = 1`, the worldline of proper acceleration `a ≠ 0` is
`τ ↦ (sinh (a τ) / a, cosh (a τ) / a)` in the coordinates `(t, x)`. It lies on the hyperbola
`x² - t² = 1 / a²`, it is parametrized by proper time, and its acceleration has norm `a`.

Continued to complex `τ`, the worldline is invariant under `τ ↦ τ + 2π i / a`, and it changes
sign under `τ ↦ τ + π i / a`, which exchanges the right and the left wedge of the horizon. The
shortest imaginary period is `2π / a`. A state that is thermal for the observer is periodic in
imaginary time with period `1 / T` (the Kubo–Martin–Schwinger condition), so the period fixes
the temperature `T = a / (2π)`.

The Kubo–Martin–Schwinger condition itself, and the identification of the Minkowski vacuum with
a state that obeys it for the Rindler observer, are not derived here: they enter as the
definition `PeriodicInImaginaryTime`, and the lemmas below are the kinematics that fixes `T`.
This is the Unruh step of Jacobson's derivation of the Einstein equation from the area law.

## ii. Key results

- `Rindler.sq_sub_sq` : the worldline lies on the hyperbola `x² - t² = 1 / a²`.
- `Rindler.velocity_norm` : proper time parametrizes the worldline.
- `Rindler.acceleration_norm` : the proper acceleration is `a`.
- `Rindler.worldlineC_add_two_pi` : the worldline is periodic in imaginary time `2π / a`.
- `Rindler.worldlineC_add_pi` : half a period exchanges the two wedges.
- `Rindler.period_ge` : no imaginary period shorter than `2π / a` exists.
- `Rindler.unruhTemperature_mul_period` : `T · (2π / a) = 1`.

## iii. Table of contents

- A. The worldline in real proper time
- B. The worldline in imaginary proper time
- C. The temperature

## iv. References

- W. G. Unruh, *Notes on black-hole evaporation*, Phys. Rev. D 14 (1976) 870.
- W. Rindler, *Kruskal space and the uniformly accelerated frame*, Am. J. Phys. 34 (1966) 1174.
- T. Jacobson, *Thermodynamics of spacetime: the Einstein equation of state*,
  Phys. Rev. Lett. 75 (1995) 1260, arXiv:gr-qc/9504004.

-/

@[expose] public section

namespace Rindler

open Complex Real

/-!

## A. The worldline in real proper time

-/

/-- The time coordinate of the worldline of proper acceleration `a`. -/
noncomputable def time (a τ : ℝ) : ℝ := Real.sinh (a * τ) / a

/-- The space coordinate of the worldline of proper acceleration `a`. -/
noncomputable def space (a τ : ℝ) : ℝ := Real.cosh (a * τ) / a

variable {a τ : ℝ}

lemma hasDerivAt_time (ha : a ≠ 0) (τ : ℝ) : HasDerivAt (time a) (Real.cosh (a * τ)) τ := by
  have h := (HasDerivAt.sinh ((hasDerivAt_id τ).const_mul a)).div_const a
  show HasDerivAt (fun s => Real.sinh (a * s) / a) _ τ
  convert h using 1
  simp only [id]
  field_simp
  rfl

lemma hasDerivAt_space (ha : a ≠ 0) (τ : ℝ) : HasDerivAt (space a) (Real.sinh (a * τ)) τ := by
  have h := (HasDerivAt.cosh ((hasDerivAt_id τ).const_mul a)).div_const a
  show HasDerivAt (fun s => Real.cosh (a * s) / a) _ τ
  convert h using 1
  simp only [id]
  field_simp
  rfl

/-- **The worldline lies on the hyperbola** `x² - t² = 1 / a²`. -/
lemma sq_sub_sq (τ : ℝ) : space a τ ^ 2 - time a τ ^ 2 = 1 / a ^ 2 := by
  unfold space time
  rw [div_pow, div_pow, ← sub_div, Real.cosh_sq]
  ring

/-- **Proper time parametrizes the worldline**: the velocity `(cosh, sinh)` has norm `1`, that is
`t'² - x'² = 1`. -/
lemma velocity_norm (ha : a ≠ 0) (τ : ℝ) :
    deriv (time a) τ ^ 2 - deriv (space a) τ ^ 2 = 1 := by
  rw [(hasDerivAt_time ha τ).deriv, (hasDerivAt_space ha τ).deriv, Real.cosh_sq]
  ring

lemma hasDerivAt_deriv_time (ha : a ≠ 0) (τ : ℝ) :
    HasDerivAt (deriv (time a)) (a * Real.sinh (a * τ)) τ := by
  have h := HasDerivAt.cosh ((hasDerivAt_id τ).const_mul a)
  have hd : deriv (time a) = fun s => Real.cosh (a * s) :=
    funext fun s => (hasDerivAt_time ha s).deriv
  rw [hd]
  simpa [mul_comm] using h

lemma hasDerivAt_deriv_space (ha : a ≠ 0) (τ : ℝ) :
    HasDerivAt (deriv (space a)) (a * Real.cosh (a * τ)) τ := by
  have h := HasDerivAt.sinh ((hasDerivAt_id τ).const_mul a)
  have hd : deriv (space a) = fun s => Real.sinh (a * s) :=
    funext fun s => (hasDerivAt_space ha s).deriv
  rw [hd]
  simpa [mul_comm] using h

/-- **The proper acceleration is `a`**: `x''² - t''² = a²`. -/
lemma acceleration_norm (ha : a ≠ 0) (τ : ℝ) :
    deriv (deriv (space a)) τ ^ 2 - deriv (deriv (time a)) τ ^ 2 = a ^ 2 := by
  rw [(hasDerivAt_deriv_space ha τ).deriv, (hasDerivAt_deriv_time ha τ).deriv]
  have := Real.cosh_sq (a * τ)
  nlinarith

/-!

## B. The worldline in imaginary proper time

-/

/-- The time coordinate of the worldline continued to complex proper time. -/
noncomputable def timeC (a : ℝ) (τ : ℂ) : ℂ := Complex.sinh (a * τ) / a

/-- The space coordinate of the worldline continued to complex proper time. -/
noncomputable def spaceC (a : ℝ) (τ : ℂ) : ℂ := Complex.cosh (a * τ) / a

/-- The shift of the proper time by `β i` with `a β = n π`. -/
lemma mul_add_mul_I (τ : ℂ) (β : ℝ) :
    (a : ℂ) * (τ + β * I) = a * τ + (a * β : ℝ) * I := by
  push_cast
  ring

/-- **Half a period exchanges the wedges**: `τ ↦ τ + π i / a` changes the sign of `(t, x)`. -/
lemma worldlineC_add_pi (ha : a ≠ 0) (τ : ℂ) :
    timeC a (τ + (π / a : ℝ) * I) = - timeC a τ ∧
      spaceC a (τ + (π / a : ℝ) * I) = - spaceC a τ := by
  have h : (a : ℂ) * (τ + (π / a : ℝ) * I) = a * τ + π * I := by
    rw [mul_add_mul_I]
    congr 2
    field_simp
  refine ⟨?_, ?_⟩
  · rw [timeC, h, Complex.sinh_add_pi_mul_I, timeC, neg_div]
  · rw [spaceC, h, Complex.cosh_add_pi_mul_I, spaceC, neg_div]

/-- **The worldline is periodic in imaginary proper time** with period `2π / a`. -/
lemma worldlineC_add_two_pi (ha : a ≠ 0) (τ : ℂ) :
    timeC a (τ + (2 * π / a : ℝ) * I) = timeC a τ ∧
      spaceC a (τ + (2 * π / a : ℝ) * I) = spaceC a τ := by
  have h : (a : ℂ) * (τ + (2 * π / a : ℝ) * I) = a * τ + π * I + π * I := by
    rw [mul_add_mul_I]
    have : (a * (2 * π / a) : ℝ) = π + π := by field_simp; ring
    rw [this]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [timeC, h, Complex.sinh_add_pi_mul_I, Complex.sinh_add_pi_mul_I, neg_neg, timeC]
  · rw [spaceC, h, Complex.cosh_add_pi_mul_I, Complex.cosh_add_pi_mul_I, neg_neg, spaceC]

/-- A shift of the proper time by `β i` is an imaginary period of the worldline when the
sinh and cosh of `a τ` are unchanged for every `τ`. -/
def PeriodicInImaginaryTime (a β : ℝ) : Prop :=
  ∀ τ : ℂ, timeC a (τ + β * I) = timeC a τ ∧ spaceC a (τ + β * I) = spaceC a τ

/-- The period `2π / a` is an imaginary period of the worldline. -/
lemma periodic_two_pi (ha : a ≠ 0) : PeriodicInImaginaryTime a (2 * π / a) :=
  fun τ => worldlineC_add_two_pi ha τ

/-- **No imaginary period of the worldline is shorter than `2π / a`.** -/
lemma period_ge (ha : 0 < a) {β : ℝ} (hβ : 0 < β) (hper : PeriodicInImaginaryTime a β) :
    2 * π / a ≤ β := by
  obtain ⟨_, h₂⟩ := hper 0
  simp only [spaceC, zero_add, mul_zero, Complex.cosh_zero] at h₂
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hc : Complex.cosh (a * (β * I)) = 1 := by
    field_simp at h₂
    rw [← mul_assoc]
    exact h₂
  have hcos : Real.cos (a * β) = 1 := by
    have h : Complex.cosh (a * (β * I)) = (Real.cos (a * β) : ℂ) := by
      rw [show (a : ℂ) * (β * I) = ((a * β : ℝ) : ℂ) * I by push_cast; ring,
        Complex.cosh_mul_I, Complex.ofReal_cos]
    rw [h] at hc
    exact_mod_cast hc
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
  have hpos : 0 < (n : ℝ) := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith [Real.pi_pos, mul_pos ha hβ]
  have hn1 : (1 : ℝ) ≤ n := by
    have h : (0 : ℤ) < n := by exact_mod_cast hpos
    exact_mod_cast (show (1 : ℤ) ≤ n from h)
  rw [div_le_iff₀ ha]
  nlinarith [Real.pi_pos]

/-!

## C. The temperature

-/

/-- The temperature of an observer of proper acceleration `a`, in units `ħ = c = k_B = 1`:
the inverse of the imaginary period `2π / a`. -/
noncomputable def unruhTemperature (a : ℝ) : ℝ := a / (2 * π)

/-- **The Unruh temperature is the inverse of the shortest imaginary period.** -/
lemma unruhTemperature_mul_period (ha : a ≠ 0) : unruhTemperature a * (2 * π / a) = 1 := by
  unfold unruhTemperature
  field_simp

/-- The Unruh temperature is positive for positive acceleration. -/
lemma unruhTemperature_pos (ha : 0 < a) : 0 < unruhTemperature a := by
  unfold unruhTemperature
  positivity

end Rindler
