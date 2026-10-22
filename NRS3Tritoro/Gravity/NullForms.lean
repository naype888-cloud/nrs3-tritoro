/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!

# Symmetric forms vanishing on the light cone

A symmetric bilinear form on Minkowski space that vanishes on every null vector is a multiple
of the Minkowski metric.

## i. Overview

Let `S` be a symmetric bilinear form on `Lorentz.Vector d`. If `S k k = 0` for every `k` with
`⟪k, k⟫ₘ = 0`, then `S p q = S e₀ e₀ * ⟪p, q⟫ₘ` for all `p` and `q`, where `e₀` is the time
basis vector. The proof only uses the null vectors `e₀ ± eᵢ` and `5 e₀ + 3 eᵢ ± 4 eⱼ`.

This is the algebraic step in Jacobson's derivation of the Einstein equation from the
thermodynamics of local horizons: once `R_ab k^a k^b = c T_ab k^a k^b` holds for every null `k`,
the form `R_ab - c T_ab` is a multiple `f g_ab` of the metric.

## ii. Key results

- `Lorentz.Vector.apply_eq_mul_minkowskiProduct_of_null` : a symmetric form vanishing on the
  light cone is `S e₀ e₀` times the Minkowski product.
- `Lorentz.Vector.null_iff_exists_eq_mul_minkowskiProduct` : a symmetric form vanishes on the
  light cone exactly when it is a multiple of the Minkowski product.

## iii. Table of contents

- A. Null vectors built from the basis
- B. The components of a form vanishing on the light cone
- C. The form is a multiple of the metric

## iv. References

- T. Jacobson, *Thermodynamics of spacetime: the Einstein equation of state*,
  Phys. Rev. Lett. 75 (1995) 1260, arXiv:gr-qc/9504004.

-/

@[expose] public section

namespace Lorentz
namespace Vector

open LinearMap (BilinForm)

variable {d : ℕ}

/-!

## A. Null vectors built from the basis

-/

/-- `e₀ + eᵢ` is null. -/
lemma minkowskiProduct_basis_inl_add_basis_inr (i : Fin d) :
    ⟪basis (Sum.inl 0) + basis (Sum.inr i), basis (Sum.inl 0) + basis (Sum.inr i)⟫ₘ = 0 := by
  simp [basis_apply]

/-- `e₀ - eᵢ` is null. -/
lemma minkowskiProduct_basis_inl_sub_basis_inr (i : Fin d) :
    ⟪basis (Sum.inl 0) - basis (Sum.inr i), basis (Sum.inl 0) - basis (Sum.inr i)⟫ₘ = 0 := by
  simp [basis_apply]

/-- `5 e₀ + 3 eᵢ + 4 eⱼ` is null for `i ≠ j`. -/
lemma minkowskiProduct_pythagorean_add {i j : Fin d} (hij : i ≠ j) :
    ⟪((5 : ℝ) • basis (Sum.inl 0) + (3 : ℝ) • basis (Sum.inr i)) + (4 : ℝ) • basis (Sum.inr j),
      ((5 : ℝ) • basis (Sum.inl 0) + (3 : ℝ) • basis (Sum.inr i)) + (4 : ℝ) • basis (Sum.inr j)⟫ₘ =
      0 := by
  simp [basis_apply, hij, hij.symm]
  norm_num

/-- `5 e₀ + 3 eᵢ - 4 eⱼ` is null for `i ≠ j`. -/
lemma minkowskiProduct_pythagorean_sub {i j : Fin d} (hij : i ≠ j) :
    ⟪((5 : ℝ) • basis (Sum.inl 0) + (3 : ℝ) • basis (Sum.inr i)) - (4 : ℝ) • basis (Sum.inr j),
      ((5 : ℝ) • basis (Sum.inl 0) + (3 : ℝ) • basis (Sum.inr i)) - (4 : ℝ) • basis (Sum.inr j)⟫ₘ =
      0 := by
  simp [basis_apply, hij, hij.symm]
  norm_num

/-!

## B. The components of a form vanishing on the light cone

-/

variable {S : BilinForm ℝ (Vector d)}

/-- If `u + v` and `u - v` are null, a symmetric form vanishing on the light cone has
`S u v = 0`. -/
lemma apply_eq_zero_of_null_add_sub (hS : S.IsSymm)
    (hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0) {u v : Vector d}
    (hadd : ⟪u + v, u + v⟫ₘ = 0) (hsub : ⟪u - v, u - v⟫ₘ = 0) : S u v = 0 := by
  have h₁ := hnull _ hadd
  have h₂ := hnull _ hsub
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hS.eq v u] at h₁ h₂
  linarith

/-- If `u + v` and `u - v` are null, a form vanishing on the light cone has
`S u u + S v v = 0`. -/
lemma apply_self_add_apply_self_of_null_add_sub
    (hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0) {u v : Vector d}
    (hadd : ⟪u + v, u + v⟫ₘ = 0) (hsub : ⟪u - v, u - v⟫ₘ = 0) : S u u + S v v = 0 := by
  have h₁ := hnull _ hadd
  have h₂ := hnull _ hsub
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h₁ h₂
  linarith

/-- The mixed time–space components of a form vanishing on the light cone are zero. -/
lemma apply_basis_inl_basis_inr_of_null (hS : S.IsSymm)
    (hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0) (i : Fin d) :
    S (basis (Sum.inl 0)) (basis (Sum.inr i)) = 0 :=
  apply_eq_zero_of_null_add_sub hS hnull (minkowskiProduct_basis_inl_add_basis_inr i)
    (minkowskiProduct_basis_inl_sub_basis_inr i)

/-- The space diagonal components of a form vanishing on the light cone are `- S e₀ e₀`. -/
lemma apply_basis_inr_self_of_null (hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0)
    (i : Fin d) :
    S (basis (Sum.inr i)) (basis (Sum.inr i)) = - S (basis (Sum.inl 0)) (basis (Sum.inl 0)) := by
  linarith [apply_self_add_apply_self_of_null_add_sub hnull
    (minkowskiProduct_basis_inl_add_basis_inr i) (minkowskiProduct_basis_inl_sub_basis_inr i)]

/-- The space off-diagonal components of a form vanishing on the light cone are zero. -/
lemma apply_basis_inr_basis_inr_of_null (hS : S.IsSymm)
    (hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0) {i j : Fin d} (hij : i ≠ j) :
    S (basis (Sum.inr i)) (basis (Sum.inr j)) = 0 := by
  have h := apply_eq_zero_of_null_add_sub hS hnull (minkowskiProduct_pythagorean_add hij)
    (minkowskiProduct_pythagorean_sub hij)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    apply_basis_inl_basis_inr_of_null hS hnull j] at h
  linarith

/-!

## C. The form is a multiple of the metric

-/

/-- **A symmetric form vanishing on the light cone is a multiple of the metric**:
`S p q = S e₀ e₀ * ⟪p, q⟫ₘ`. -/
lemma apply_eq_mul_minkowskiProduct_of_null (hS : S.IsSymm)
    (hnull : ∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0) (p q : Vector d) :
    S p q = S (basis (Sum.inl 0)) (basis (Sum.inl 0)) * ⟪p, q⟫ₘ := by
  set f := S (basis (Sum.inl 0)) (basis (Sum.inl 0))
  suffices h : S = f • ContinuousLinearMap.toLinearMap₁₂ minkowskiProduct by
    simp [h]
  refine LinearMap.ext_basis basis basis fun μ ν => ?_
  simp only [LinearMap.smul_apply, ContinuousLinearMap.toLinearMap₁₂_apply, smul_eq_mul]
  rcases μ with μ | i <;> rcases ν with ν | j
  · simp [Fin.fin_one_eq_zero μ, Fin.fin_one_eq_zero ν, f]
  · simp [Fin.fin_one_eq_zero μ, apply_basis_inl_basis_inr_of_null hS hnull j]
  · simp [Fin.fin_one_eq_zero ν, hS.eq, apply_basis_inl_basis_inr_of_null hS hnull i]
  · by_cases hij : i = j
    · subst hij
      simp [apply_basis_inr_self_of_null hnull, f]
    · simp [hij, apply_basis_inr_basis_inr_of_null hS hnull hij]

/-- A symmetric form vanishes on the light cone exactly when it is a multiple of the Minkowski
product. -/
lemma null_iff_exists_eq_mul_minkowskiProduct (hS : S.IsSymm) :
    (∀ k : Vector d, ⟪k, k⟫ₘ = 0 → S k k = 0) ↔ ∃ f : ℝ, ∀ p q, S p q = f * ⟪p, q⟫ₘ := by
  refine ⟨fun h => ⟨_, apply_eq_mul_minkowskiProduct_of_null hS h⟩, ?_⟩
  rintro ⟨f, hf⟩ k hk
  rw [hf, hk, mul_zero]

end Vector
end Lorentz
