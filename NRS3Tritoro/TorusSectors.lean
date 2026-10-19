/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusField

/-!
# The sector of two excitations of the three-torus field

`TorusField` showed that the sector of one excitation is the torus itself. Here the sector of two
excitations over a vacuum `Ω`: a state `Ψ : ι × ι → ℂ` of two positions goes to the field state
`Σ Ψ(p, q) a†_p a†_q Ω`. Second quantization acts on it through the two-body matrix
`D M = M ⊗ 1 + 1 ⊗ M`, so the bracket of the field is again the bracket of the matrices, now on
pairs of positions. With the star structure `IsStar` the form is
`β (Σ Ψ a†a† Ω, Σ Φ a†a† Ω) = Ψ̄ · (Φ + Φᵀ)`: on symmetric states it is `2 Ψ̄ · Φ`, and the
uncertainty field of the field is the one of the two-body matrices on the state `√2 Ψ`.

## Main results

- `TorusSectors.secondQuant_twoExcitation` : `dΓ M (Σ Ψ a†a† Ω) = Σ (D M Ψ) a†a† Ω`.
- `TorusSectors.twoBody_lie` : `D ⁅M, N⁆ = ⁅D M, D N⁆`.
- `TorusSectors.form_twoExcitation` : `β` restricts to `Ψ̄ · (Φ + Φᵀ)`.
- `TorusSectors.uncertainty_twoExcitation` : for symmetric `Ψ`, the uncertainty field of the field
  state is `matUncertainty (√2 Ψ) (D M) (D N)`.
-/

@[expose] public noncomputable section

open TorusField
open scoped Matrix Kronecker

namespace TorusSectors

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-! ## 1. The two-body matrix -/

/-- The two-body matrix `D M = M ⊗ 1 + 1 ⊗ M` on pairs of positions. -/
def twoBody (M : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  M ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ M

omit [Fintype ι] in
lemma twoBody_apply (M : Matrix ι ι ℂ) (x y : ι × ι) :
    twoBody M x y = M x.1 y.1 * (if x.2 = y.2 then 1 else 0) +
      (if x.1 = y.1 then 1 else 0) * M x.2 y.2 := by
  simp [twoBody, Matrix.kroneckerMap_apply, Matrix.one_apply]

omit [Fintype ι] in
lemma twoBody_sub (M N : Matrix ι ι ℂ) : twoBody (M - N) = twoBody M - twoBody N := by
  ext x y
  simp only [twoBody_apply, Matrix.sub_apply]
  ring

lemma twoBody_mulVec (M : Matrix ι ι ℂ) (Ψ : ι × ι → ℂ) (p s : ι) :
    (twoBody M *ᵥ Ψ) (p, s) = ∑ r, M p r * Ψ (r, s) + ∑ q, M s q * Ψ (p, q) := by
  simp only [Matrix.mulVec, dotProduct, twoBody_apply, add_mul, Finset.sum_add_distrib,
    Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun r _ => ?_
    simp [ite_mul, mul_ite]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [ite_mul]

/-- **The two-body matrix respects brackets.** -/
theorem twoBody_lie (M N : Matrix ι ι ℂ) :
    twoBody ⁅M, N⁆ = ⁅twoBody M, twoBody N⁆ := by
  have h1 : (M ⊗ₖ (1 : Matrix ι ι ℂ)) * (N ⊗ₖ (1 : Matrix ι ι ℂ)) = (M * N) ⊗ₖ 1 := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h4 : ((1 : Matrix ι ι ℂ) ⊗ₖ M) * ((1 : Matrix ι ι ℂ) ⊗ₖ N) = (1 : Matrix ι ι ℂ) ⊗ₖ (M * N) := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h2 : (M ⊗ₖ (1 : Matrix ι ι ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ N) = M ⊗ₖ N := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h3 : ((1 : Matrix ι ι ℂ) ⊗ₖ M) * (N ⊗ₖ (1 : Matrix ι ι ℂ)) = N ⊗ₖ M := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h1' : (N ⊗ₖ (1 : Matrix ι ι ℂ)) * (M ⊗ₖ (1 : Matrix ι ι ℂ)) = (N * M) ⊗ₖ 1 := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h4' : ((1 : Matrix ι ι ℂ) ⊗ₖ N) * ((1 : Matrix ι ι ℂ) ⊗ₖ M) = (1 : Matrix ι ι ℂ) ⊗ₖ (N * M) := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h2' : (N ⊗ₖ (1 : Matrix ι ι ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ M) = N ⊗ₖ M := by
    rw [← Matrix.mul_kronecker_mul]; simp
  have h3' : ((1 : Matrix ι ι ℂ) ⊗ₖ N) * (M ⊗ₖ (1 : Matrix ι ι ℂ)) = M ⊗ₖ N := by
    rw [← Matrix.mul_kronecker_mul]; simp
  simp only [Ring.lie_def, twoBody_sub]
  simp only [twoBody, mul_add, add_mul, h1, h2, h3, h4, h1', h2', h3', h4']
  abel

/-! ## 2. Second quantization on two excitations -/

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (L : LadderSystem ℂ V d) (e : ι ≃ Fin d)

lemma a_ac_comm (i j : Fin d) (x : V) :
    L.a i (L.ac j x) = L.ac j (L.a i x) + if i = j then x else 0 := by
  have h := congrArg (fun f : Module.End ℂ V => f x) (L.comm_a_ac i j)
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  split_ifs <;> simp [add_comm]

lemma ac_ac_comm (i j : Fin d) (x : V) : L.ac i (L.ac j x) = L.ac j (L.ac i x) := by
  have h := congrArg (fun f : Module.End ℂ V => f x) (L.comm_ac_ac i j)
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply] at h
  simpa [sub_eq_zero] using h

variable {L}

lemma a_ac_ac_vacuum {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (i j k : Fin d) :
    L.a i (L.ac j (L.ac k Ω)) =
      (if i = j then L.ac k Ω else 0) + (if i = k then L.ac j Ω else 0) := by
  rw [a_ac_comm, a_ac_comm, hΩ]
  split_ifs <;> simp [add_comm]

lemma E_ac_ac_vacuum {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (i j k l : Fin d) :
    L.E i j (L.ac k (L.ac l Ω)) =
      (if j = k then L.ac i (L.ac l Ω) else 0) + (if j = l then L.ac i (L.ac k Ω) else 0) := by
  change (L.ac i * L.a j) _ = _
  rw [Module.End.mul_apply, a_ac_ac_vacuum hΩ]
  split_ifs <;> simp

lemma secondQuant_ac_ac {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ) (r s : ι) :
    secondQuant L e M (L.ac (e r) (L.ac (e s) Ω)) =
      ∑ p, M p r • L.ac (e p) (L.ac (e s) Ω) + ∑ p, M p s • L.ac (e r) (L.ac (e p) Ω) := by
  simp only [secondQuant_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    E_ac_ac_vacuum hΩ, EmbeddingLike.apply_eq_iff_eq, smul_add, smul_ite, smul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [ac_ac_comm]

variable (L)

/-- The sector of two excitations: a state `Ψ` of two positions as `Σ Ψ(p, q) a†_p a†_q Ω`. -/
def twoExcitation (Ω : V) : (ι × ι → ℂ) →ₗ[ℂ] V where
  toFun Ψ := ∑ x, Ψ x • L.ac (e x.1) (L.ac (e x.2) Ω)
  map_add' ψ φ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r ψ := by simp [Finset.smul_sum, smul_smul]

/-- **Second quantization on two excitations is the two-body matrix.** -/
theorem secondQuant_twoExcitation {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ)
    (Ψ : ι × ι → ℂ) :
    secondQuant L e M (twoExcitation L e Ω Ψ) = twoExcitation L e Ω (twoBody M *ᵥ Ψ) := by
  simp only [twoExcitation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    Fintype.sum_prod_type]
  simp only [secondQuant_ac_ac e hΩ, twoBody_mulVec, add_smul, Finset.sum_add_distrib]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul]
  congr 1
  · rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun r _ => by rw [mul_comm]
  · exact Finset.sum_congr rfl fun x _ => (Finset.sum_comm).trans
      (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => by rw [mul_comm])

end Algebraic

/-! ## 3. The star structure on two excitations -/

section Star

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {L : LadderSystem ℂ V d} (e : ι ≃ Fin d)
  {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

/-- A state of two positions is symmetric when it does not see the order of the two. -/
def IsSymm (Ψ : ι × ι → ℂ) : Prop := ∀ p q, Ψ (p, q) = Ψ (q, p)

omit [Fintype ι] [DecidableEq ι] in
lemma IsSymm.swap {Ψ : ι × ι → ℂ} (h : IsSymm Ψ) (x : ι × ι) : Ψ x.swap = Ψ x :=
  (h x.1 x.2).symm

lemma IsSymm.twoBody_mulVec {Ψ : ι × ι → ℂ} (h : IsSymm Ψ) (M : Matrix ι ι ℂ) :
    IsSymm (twoBody M *ᵥ Ψ) := by
  intro p q
  rw [TorusSectors.twoBody_mulVec, TorusSectors.twoBody_mulVec, add_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun r _ => by rw [h]

variable {Ω : V} (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1)
include hL hΩ hn

lemma form_ac_ac (p q r s : Fin d) :
    β (L.ac p (L.ac q Ω)) (L.ac r (L.ac s Ω)) =
      (if p = r then (if q = s then 1 else 0) else 0) +
        (if p = s then (if q = r then 1 else 0) else 0) := by
  rw [hL, a_ac_ac_vacuum hΩ]
  split_ifs <;> subst_vars <;> simp_all [form_ac_vacuum hL hΩ hn, eq_comm]

/-- **The star structure on two excitations:** `β` restricts to `Ψ̄ · (Φ + Φᵀ)`. -/
theorem form_twoExcitation (Ψ Φ : ι × ι → ℂ) :
    β (twoExcitation L e Ω Ψ) (twoExcitation L e Ω Φ) =
      star Ψ ⬝ᵥ (Φ + fun x => Φ x.swap) := by
  simp only [twoExcitation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.map_smulₛₗ₂,
    LinearMap.sum_apply, map_smul, form_ac_ac hL hΩ hn, Fintype.sum_prod_type, dotProduct,
    EmbeddingLike.apply_eq_iff_eq, smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib,
    Pi.add_apply, Pi.star_apply, Complex.star_def, Prod.swap_prod_mk]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp [mul_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp [mul_comm]

/-- On symmetric states the form is twice the dot product. -/
theorem form_twoExcitation_symm {Φ : ι × ι → ℂ} (hΦ : IsSymm Φ) (Ψ : ι × ι → ℂ) :
    β (twoExcitation L e Ω Ψ) (twoExcitation L e Ω Φ) = 2 * (star Ψ ⬝ᵥ Φ) := by
  have h : (Φ + fun x => Φ x.swap) = (2 : ℂ) • Φ := by
    funext x
    simp [hΦ.swap x]
    ring
  rw [form_twoExcitation e hL hΩ hn, h, dotProduct_smul, smul_eq_mul]

lemma form_mul {Ψ : ι × ι → ℂ} (hΨ : IsSymm Ψ) (M N : Matrix ι ι ℂ) :
    β (twoExcitation L e Ω Ψ)
        ((secondQuant L e M * secondQuant L e N) (twoExcitation L e Ω Ψ)) =
      2 * (star Ψ ⬝ᵥ ((twoBody M * twoBody N) *ᵥ Ψ)) := by
  rw [Module.End.mul_apply, secondQuant_twoExcitation L e hΩ, secondQuant_twoExcitation L e hΩ,
    form_twoExcitation_symm e hL hΩ hn ((hΨ.twoBody_mulVec N).twoBody_mulVec M),
    Matrix.mulVec_mulVec]

lemma form_one {Ψ : ι × ι → ℂ} (hΨ : IsSymm Ψ) (M : Matrix ι ι ℂ) :
    β (twoExcitation L e Ω Ψ) (secondQuant L e M (twoExcitation L e Ω Ψ)) =
      2 * (star Ψ ⬝ᵥ (twoBody M *ᵥ Ψ)) := by
  rw [secondQuant_twoExcitation L e hΩ,
    form_twoExcitation_symm e hL hΩ hn (hΨ.twoBody_mulVec M)]

lemma form_lie {Ψ : ι × ι → ℂ} (hΨ : IsSymm Ψ) (M N : Matrix ι ι ℂ) :
    β (twoExcitation L e Ω Ψ)
        (⁅secondQuant L e M, secondQuant L e N⁆ (twoExcitation L e Ω Ψ)) =
      2 * (star Ψ ⬝ᵥ (⁅twoBody M, twoBody N⁆ *ᵥ Ψ)) := by
  rw [← secondQuant_lie, form_one e hL hΩ hn hΨ, twoBody_lie]

omit [DecidableEq ι] hL hΩ hn in
lemma scale_form (X : Matrix (ι × ι) (ι × ι) ℂ) (Ψ : ι × ι → ℂ) :
    star ((Real.sqrt 2 : ℂ) • Ψ) ⬝ᵥ (X *ᵥ ((Real.sqrt 2 : ℂ) • Ψ)) = 2 * (star Ψ ⬝ᵥ (X *ᵥ Ψ)) := by
  have hc : (starRingEnd ℂ) (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc]
  rw [Complex.star_def, mul_comm (Real.sqrt 2 : ℂ), hc]

/-- **The uncertainty field of two excitations is the one of the two-body matrices.** -/
theorem uncertainty_twoExcitation {Ψ : ι × ι → ℂ} (hΨ : IsSymm Ψ) (M N : Matrix ι ι ℂ) :
    uncertainty β (twoExcitation L e Ω Ψ) (secondQuant L e M) (secondQuant L e N) =
      matUncertainty ((Real.sqrt 2 : ℂ) • Ψ) (twoBody M) (twoBody N) := by
  rw [uncertainty, matUncertainty, form_mul e hL hΩ hn hΨ, form_mul e hL hΩ hn hΨ,
    form_one e hL hΩ hn hΨ, form_one e hL hΩ hn hΨ, form_lie e hL hΩ hn hΨ]
  simp only [scale_form]

end Star

end TorusSectors
