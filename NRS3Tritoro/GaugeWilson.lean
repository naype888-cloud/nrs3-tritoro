/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic

/-!
# Gauge links and the Wilson action on a lattice with fixed spacing

The first brick of lattice Yang-Mills: gauge links on a discrete set of sites, the plaquette
holonomy, the gauge transformations, and the Wilson plaquette action for the group `U(n)`.
Nothing is sent to the continuum; the sites are an arbitrary type `ι` with commuting steps
`τ μ : ι ≃ ι` (the lattice `ℤ³ × w` of `LatticeFiberDirac` is one instance).

A link configuration is `U μ p : G`, the transport from `p` to `τ μ p`. The plaquette at `p` in
the plane `(μ, ν)` is the loop `p → τ μ p → τ ν (τ μ p) = τ μ (τ ν p) → τ ν p → p`.

## Main results

- `GaugeWilson.plaquette_gauge` : under `U ↦ g·U·g⁻¹` the plaquette is conjugated at `p`.
- `GaugeWilson.density_gauge` : the Wilson density `n − Re tr P` of a plaquette is gauge
  invariant.
- `GaugeWilson.density_nonneg` : the Wilson density is `≥ 0` for `P ∈ U(n)`.
- `GaugeWilson.density_eq_zero_iff` : it vanishes exactly when the plaquette is trivial.
- `GaugeWilson.action_gauge`, `GaugeWilson.action_nonneg`, `GaugeWilson.action_eq_zero_iff` :
  the same for the action summed over a finite set of plaquettes.

No Hamiltonian, no transfer operator and no gap are claimed here.
-/

@[expose] public noncomputable section

open Matrix Complex

namespace GaugeWilson

/-! ## 1. Links, plaquettes, gauge transformations -/

section Links

variable {ι δ G : Type*} [Group G] (τ : δ → ι ≃ ι)

/-- The plaquette holonomy of the links `U` at the site `p` in the plane `(μ, ν)`. -/
def plaquette (U : δ → ι → G) (μ ν : δ) (p : ι) : G :=
  U μ p * U ν (τ μ p) * (U μ (τ ν p))⁻¹ * (U ν p)⁻¹

/-- A gauge transformation `g` acts on the links: `U μ p ↦ g p · U μ p · g(τ μ p)⁻¹`. -/
def gaugeAct (g : ι → G) (U : δ → ι → G) : δ → ι → G :=
  fun μ p => g p * U μ p * (g (τ μ p))⁻¹

/-- **The plaquette is covariant**: a gauge transformation conjugates it by `g` at the base
point, provided the two steps commute at `p`. -/
theorem plaquette_gauge (g : ι → G) (U : δ → ι → G) (μ ν : δ) (p : ι)
    (h : τ ν (τ μ p) = τ μ (τ ν p)) :
    plaquette τ (gaugeAct τ g U) μ ν p = g p * plaquette τ U μ ν p * (g p)⁻¹ := by
  simp only [plaquette, gaugeAct, h]
  group

end Links

/-! ## 2. The Wilson density of a unitary plaquette -/

section Density

variable {n : ℕ}

/-- The Wilson density of a plaquette `P ∈ U(n)`: `n − Re tr P`. -/
def density (P : unitaryGroup (Fin n) ℂ) : ℝ := n - (Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ)).re

/-- The density is invariant under conjugation. -/
theorem density_conj (g P : unitaryGroup (Fin n) ℂ) : density (g * P * g⁻¹) = density P := by
  have h : Matrix.trace ((g * P * g⁻¹ : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ) := by
    have hinv : ((g⁻¹ : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = star (g : Matrix _ _ ℂ) :=
      rfl
    have hgs : star (g : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      mem_unitaryGroup_iff'.mp g.2
    calc Matrix.trace ((g * P * g⁻¹ : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        = Matrix.trace ((g : Matrix (Fin n) (Fin n) ℂ) * (P : Matrix (Fin n) (Fin n) ℂ)
            * star (g : Matrix (Fin n) (Fin n) ℂ)) := by
          simp [hinv]
      _ = Matrix.trace (star (g : Matrix (Fin n) (Fin n) ℂ) * (g : Matrix (Fin n) (Fin n) ℂ)
            * (P : Matrix (Fin n) (Fin n) ℂ)) := by
          rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ) := by rw [hgs, one_mul]
  simp only [density, h]

/-- Every column of a unitary has norm one. -/
theorem sum_norm_sq_col (P : unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ k, ‖(P : Matrix (Fin n) (Fin n) ℂ) k i‖ ^ 2 = 1 := by
  have h := mem_unitaryGroup_iff'.mp P.2
  have hii := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at hii
  have : ∑ k, star ((P : Matrix (Fin n) (Fin n) ℂ) k i) * (P : Matrix (Fin n) (Fin n) ℂ) k i
      = ((∑ k, ‖(P : Matrix (Fin n) (Fin n) ℂ) k i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [this] at hii
  exact_mod_cast hii

/-- Every diagonal entry of a unitary has modulus at most one. -/
theorem norm_diag_le (P : unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ‖(P : Matrix (Fin n) (Fin n) ℂ) i i‖ ≤ 1 := by
  have hsum := sum_norm_sq_col P i
  have hle : ‖(P : Matrix (Fin n) (Fin n) ℂ) i i‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun k => ‖(P : Matrix (Fin n) (Fin n) ℂ) k i‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg ((P : Matrix (Fin n) (Fin n) ℂ) i i)]

/-- **The Wilson density is nonnegative**: `Re tr P ≤ n` for `P ∈ U(n)`. -/
theorem density_nonneg (P : unitaryGroup (Fin n) ℂ) : 0 ≤ density P := by
  have h : (Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ)).re ≤ n := by
    have : (Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ)).re
        = ∑ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re := by
      simp [Matrix.trace, Complex.re_sum]
    rw [this]
    calc ∑ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ =>
            (Complex.re_le_norm _).trans (norm_diag_le P i)
      _ = n := by simp
  unfold density
  linarith

/-- **The Wilson density vanishes exactly on the trivial plaquette**. -/
theorem density_eq_zero_iff (P : unitaryGroup (Fin n) ℂ) : density P = 0 ↔ P = 1 := by
  have hre : (Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ)).re
      = ∑ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re := by
    simp [Matrix.trace, Complex.re_sum]
  constructor
  · intro h0
    have hsum : ∑ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re = n := by
      unfold density at h0; linarith
    have hle : ∀ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re ≤ 1 := fun i =>
      (Complex.re_le_norm _).trans (norm_diag_le P i)
    have hre1 : ∀ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re = 1 := by
      intro i
      by_contra hne
      have hlt : ((P : Matrix (Fin n) (Fin n) ℂ) i i).re < 1 := lt_of_le_of_ne (hle i) hne
      have : ∑ j, ((P : Matrix (Fin n) (Fin n) ℂ) j j).re < ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hlt⟩
      simp at this
      linarith
    have hdiag : ∀ i, (P : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
      intro i
      have hn := norm_diag_le P i
      have hsq : ((P : Matrix (Fin n) (Fin n) ℂ) i i).re ^ 2
          + ((P : Matrix (Fin n) (Fin n) ℂ) i i).im ^ 2 ≤ 1 := by
        have := Complex.sq_norm ((P : Matrix (Fin n) (Fin n) ℂ) i i)
        rw [Complex.normSq_apply] at this
        nlinarith [norm_nonneg ((P : Matrix (Fin n) (Fin n) ℂ) i i)]
      have him : ((P : Matrix (Fin n) (Fin n) ℂ) i i).im = 0 := by
        rw [hre1 i] at hsq; nlinarith [sq_nonneg ((P : Matrix (Fin n) (Fin n) ℂ) i i).im]
      exact Complex.ext (by simpa using hre1 i) (by simpa using him)
    have hoff : ∀ k i, k ≠ i → (P : Matrix (Fin n) (Fin n) ℂ) k i = 0 := by
      intro k i hki
      have hs := sum_norm_sq_col P i
      have hsplit := Finset.add_sum_erase Finset.univ
        (fun k => ‖(P : Matrix (Fin n) (Fin n) ℂ) k i‖ ^ 2) (Finset.mem_univ i)
      rw [hdiag i] at hsplit
      simp only [norm_one, one_pow] at hsplit
      have hrest : ∑ j ∈ Finset.univ.erase i, ‖(P : Matrix (Fin n) (Fin n) ℂ) j i‖ ^ 2 = 0 := by
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hrest k
        (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
      exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this)
    apply Subtype.ext
    ext k i
    by_cases hki : k = i
    · subst hki; simp [hdiag k]
    · simp [hoff k i hki, Matrix.one_apply_ne hki]
  · rintro rfl
    simp [density]

end Density

/-! ## 3. The Wilson action on a finite set of plaquettes -/

section Action

variable {ι δ : Type*} {n : ℕ} (τ : δ → ι ≃ ι)

/-- The Wilson action of the unitary links `U` on a finite set `R` of plaquettes `(p, μ, ν)`. -/
def action (R : Finset (ι × δ × δ)) (U : δ → ι → unitaryGroup (Fin n) ℂ) : ℝ :=
  ∑ r ∈ R, density (plaquette τ U r.2.1 r.2.2 r.1)

/-- **The Wilson action is gauge invariant** on every finite set of plaquettes whose steps
commute. -/
theorem action_gauge (R : Finset (ι × δ × δ)) (U : δ → ι → unitaryGroup (Fin n) ℂ)
    (g : ι → unitaryGroup (Fin n) ℂ)
    (h : ∀ r ∈ R, τ r.2.2 (τ r.2.1 r.1) = τ r.2.1 (τ r.2.2 r.1)) :
    action τ R (gaugeAct τ g U) = action τ R U := by
  unfold action
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [plaquette_gauge τ g U r.2.1 r.2.2 r.1 (h r hr), density_conj]

/-- **The Wilson action is nonnegative**. -/
theorem action_nonneg (R : Finset (ι × δ × δ)) (U : δ → ι → unitaryGroup (Fin n) ℂ) :
    0 ≤ action τ R U :=
  Finset.sum_nonneg fun _ _ => density_nonneg _

/-- **The Wilson action vanishes exactly when every plaquette is trivial**. -/
theorem action_eq_zero_iff (R : Finset (ι × δ × δ)) (U : δ → ι → unitaryGroup (Fin n) ℂ) :
    action τ R U = 0 ↔ ∀ r ∈ R, plaquette τ U r.2.1 r.2.2 r.1 = 1 := by
  unfold action
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => density_nonneg _]
  exact forall₂_congr fun _ _ => density_eq_zero_iff _

end Action

end GaugeWilson
