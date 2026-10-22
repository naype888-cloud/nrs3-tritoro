/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import NRS3Tritoro.Gravity.Clausius
public import NRS3Tritoro.Gravity.NullForms

/-!

# The Einstein equation from the Clausius relation on every light sheet

If the Clausius relation holds on every local light sheet through every point, the Ricci form and
the stress-energy form obey the Einstein equation with a cosmological constant.

## i. Overview

At a point of `d + 1`-dimensional spacetime, let `Ric` and `T` be symmetric forms on the tangent
space, and let `κ = 2π / η` be the coupling given by the area law `δS = η δA`.

- On every null direction `k` the Clausius relation `δQ = T δS` holds on the light sheet of `k`.
  By `LightSheet.clausius_iff` it is `Ric k k = κ T k k`.
- The form `Ric - κ T` is symmetric and vanishes on the light cone, so by
  `Lorentz.Vector.apply_eq_mul_minkowskiProduct_of_null` it is `f` times the metric:
  `Ric - κ T = f g`.
- The trace of the metric is `d + 1`, so the scalar curvature `R = tr Ric` is
  `κ tr T + (d + 1) f`.
- The contracted Bianchi identity and the conservation of `T` give `∇ f = ½ ∇ R`. Then
  `Λ = R / 2 - f` has zero derivative, it is a constant, and
  `Ric - ½ R g + Λ g = κ T`.
- The constant is `Λ = ½ κ tr T + ½ (d - 1) f`.

The contracted Bianchi identity and the conservation of `T` are not derived here: they enter as
the single hypothesis `fderiv f = ½ fderiv R`, which is their consequence for `Ric - κ T = f g`.
The Clausius relation on every light sheet is the hypothesis of the theorem.

## ii. Key results

- `Lorentz.Vector.trace_minkowski` : the trace of `f g` is `(d + 1) f`.
- `Einstein.exists_eq_mul_of_clausius` : `Ric - κ T = f g`.
- `Einstein.einstein_equation` : the Einstein equation with a constant `Λ`, and its value.

## iii. Table of contents

- A. The trace of a form
- B. The Einstein equation

## iv. References

- T. Jacobson, *Thermodynamics of spacetime: the Einstein equation of state*,
  Phys. Rev. Lett. 75 (1995) 1260, arXiv:gr-qc/9504004.
- A. Einstein, *Kosmologische Betrachtungen zur allgemeinen Relativitätstheorie*,
  Sitzungsber. Preuss. Akad. Wiss. (1917) 142.

-/

@[expose] public section

namespace Lorentz
namespace Vector

open LinearMap (BilinForm)

variable {d : ℕ}

/-!

## A. The trace of a form

-/

/-- The time basis vector. -/
noncomputable abbrev timeBasis : Vector d := basis (Sum.inl 0)

/-- The space basis vector `i`. -/
noncomputable abbrev spaceBasis (i : Fin d) : Vector d := basis (Sum.inr i)

/-- The trace of a bilinear form on Minkowski space, contracted with the inverse metric. -/
noncomputable def trace (S : BilinForm ℝ (Vector d)) : ℝ :=
  S timeBasis timeBasis * ⟪(timeBasis : Vector d), timeBasis⟫ₘ +
    ∑ i : Fin d, S (spaceBasis i) (spaceBasis i) * ⟪(spaceBasis i : Vector d), spaceBasis i⟫ₘ

lemma trace_add (S S' : BilinForm ℝ (Vector d)) : trace (S + S') = trace S + trace S' := by
  simp only [trace, LinearMap.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma trace_smul (c : ℝ) (S : BilinForm ℝ (Vector d)) : trace (c • S) = c * trace S := by
  simp only [trace, LinearMap.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

/-- The trace of a multiple of the metric is `d + 1` times the multiple. -/
lemma trace_minkowski (f : ℝ) :
    trace (f • ContinuousLinearMap.toLinearMap₁₂ (minkowskiProduct (d := d))) = (d + 1) * f := by
  have h₀ : ⟪timeBasis (d := d), timeBasis⟫ₘ ^ 2 = (1 : ℝ) := by
    simp [basis_apply]
  have h₁ : ∀ i : Fin d, ⟪spaceBasis i, spaceBasis i⟫ₘ ^ 2 = (1 : ℝ) := fun i => by
    simp [basis_apply]
  simp only [trace, LinearMap.smul_apply, ContinuousLinearMap.toLinearMap₁₂_apply, smul_eq_mul]
  have e₀ : f * ⟪timeBasis (d := d), timeBasis⟫ₘ * ⟪timeBasis (d := d), timeBasis⟫ₘ = f := by
    rw [mul_assoc, ← sq, h₀, mul_one]
  have e₁ : ∀ i : Fin d, f * ⟪spaceBasis i, spaceBasis i⟫ₘ * ⟪spaceBasis i, spaceBasis i⟫ₘ = f :=
    fun i => by rw [mul_assoc, ← sq, h₁ i, mul_one]
  simp
  ring

end Vector
end Lorentz

namespace Einstein

open Lorentz Vector

open LinearMap (BilinForm)

variable {d : ℕ}

/-!

## B. The Einstein equation

-/

/-- The scalar `f` with `Ric - κ T = f g`: the value of `Ric - κ T` on the time basis vector. -/
noncomputable def fScalar (κ : ℝ) (Ric T : BilinForm ℝ (Vector d)) : ℝ :=
  Ric timeBasis timeBasis - κ * T timeBasis timeBasis

/-- **The Clausius relation on every light sheet makes `Ric - κ T` a multiple of the metric.** -/
lemma exists_eq_mul_of_clausius {Ric T : BilinForm ℝ (Vector d)} (hRic : Ric.IsSymm)
    (hT : T.IsSymm) {η κs A l₀ : ℝ} (hκ : κs ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0) (hη : η ≠ 0)
    (hC : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → LightSheet.Clausius η κs (Ric k k) (T k k) A l₀)
    (p q : Vector d) :
    Ric p q - 2 * Real.pi / η * T p q = fScalar (2 * Real.pi / η) Ric T * ⟪p, q⟫ₘ := by
  have hS : (Ric - (2 * Real.pi / η) • T).IsSymm :=
    ⟨fun p q => by simp [hRic.eq p q, hT.eq p q]⟩
  have hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → (Ric - (2 * Real.pi / η) • T) k k = 0 := by
    intro k hk
    have := (LightSheet.clausius_iff hκ hA hl hη).1 (hC k hk)
    simp [this]
  have h := apply_eq_mul_minkowskiProduct_of_null hS hnull p q
  simpa [fScalar, sub_eq_add_neg] using h

/-- **The Einstein equation.** Let `Ric` and `T` be fields of symmetric forms on a vector space of
points, with the Clausius relation on every light sheet through every point, and with the
contracted Bianchi identity `∇ f = ½ ∇ R` for `Ric - κ T = f g` and `R = tr Ric`. Then there is a
constant `Λ` with `Ric - ½ R g + Λ g = κ T`, and `Λ = ½ κ tr T + ½ (d - 1) f` at every point. -/
theorem einstein_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ric T : E → BilinForm ℝ (Vector d)} (hRic : ∀ x, (Ric x).IsSymm) (hT : ∀ x, (T x).IsSymm)
    {η κs A l₀ : ℝ} (hκ : κs ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0) (hη : η ≠ 0)
    (hC : ∀ x, ∀ k : Vector d, ⟪k, k⟫ₘ = 0 →
      LightSheet.Clausius η κs (Ric x k k) (T x k k) A l₀)
    (hf : Differentiable ℝ fun x => fScalar (2 * Real.pi / η) (Ric x) (T x))
    (hR : Differentiable ℝ fun x => trace (Ric x))
    (hBianchi : ∀ x, fderiv ℝ (fun x => fScalar (2 * Real.pi / η) (Ric x) (T x)) x =
      (1 / 2 : ℝ) • fderiv ℝ (fun x => trace (Ric x)) x) :
    ∃ Λ : ℝ, ∀ x, (∀ p q, Ric x p q - trace (Ric x) / 2 * ⟪p, q⟫ₘ + Λ * ⟪p, q⟫ₘ =
        2 * Real.pi / η * T x p q) ∧
      Λ = (2 * Real.pi / η) * trace (T x) / 2 +
        (d - 1) / 2 * fScalar (2 * Real.pi / η) (Ric x) (T x) := by
  set κ := 2 * Real.pi / η with hκdef
  set f : E → ℝ := fun x => fScalar κ (Ric x) (T x) with hfdef
  have hform : ∀ x p q, Ric x p q = κ * T x p q + f x * ⟪p, q⟫ₘ := fun x p q => by
    have := exists_eq_mul_of_clausius (hRic x) (hT x) hκ hA hl hη (hC x) p q
    simp only [hfdef]
    linarith
  -- The scalar curvature is `κ tr T + (d + 1) f`.
  have htrace : ∀ x, trace (Ric x) = κ * trace (T x) + (d + 1) * f x := fun x => by
    have : Ric x = κ • T x +
        f x • ContinuousLinearMap.toLinearMap₁₂ (minkowskiProduct (d := d)) :=
      LinearMap.ext₂ fun p q => by simp [hform x p q]
    rw [this, trace_add, trace_smul, trace_minkowski]
  -- `Λ = R / 2 - f` has zero derivative.
  set L : E → ℝ := fun x => (1 / 2 : ℝ) * trace (Ric x) - f x with hL
  have hLd : Differentiable ℝ L := (hR.const_mul (1 / 2 : ℝ)).sub hf
  have hL0 : ∀ x, fderiv ℝ L x = 0 := fun x => by
    have h1 : fderiv ℝ L x =
        fderiv ℝ (fun x => (1 / 2 : ℝ) * trace (Ric x)) x - fderiv ℝ f x :=
      fderiv_sub ((hR x).const_mul (1 / 2 : ℝ)) (hf x)
    rw [h1, fderiv_const_mul (hR x), hBianchi x]
    simp
  have hconst : ∀ x y, L x = L y := fun x y => is_const_of_fderiv_eq_zero hLd hL0 x y
  refine ⟨L 0, fun x => ⟨fun p q => ?_, ?_⟩⟩
  · have hx := hconst 0 x
    rw [hx, hL, hform x p q]
    simp only
    ring
  · have hx := hconst 0 x
    have hfx : fScalar κ (Ric x) (T x) = f x := rfl
    rw [hx, hL, hfx]
    simp only
    rw [htrace x]
    ring

end Einstein
