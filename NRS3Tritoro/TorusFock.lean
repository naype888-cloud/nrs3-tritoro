/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSectors

/-!
# The sector of `n` excitations of the three-torus field

`TorusField` showed that the sector of one excitation is the torus, and `TorusSectors` that the
sector of two is the pairs of positions with the two-body matrix. Here the sector of `n`
excitations over a vacuum `Ω`: a state `Ψ : (Fin n → ι) → ℂ` of `n` positions goes to the field
state `Σ Ψ(x) a†_{x₀} ⋯ a†_{x_{n-1}} Ω`. Second quantization acts on it through the `n`-body matrix
`D_n M`, which applies `M` to one position at a time, so the bracket of the field is the bracket of
matrices on `n` positions. With the star structure `IsStar` the form on a symmetric `Φ` is
`β (Σ Ψ a†…a† Ω, Σ Φ a†…a† Ω) = n! Ψ̄ · Φ`, and the uncertainty field of the field is the one of
the `n`-body matrices on the state `√(n!) Ψ`.

## Main results

- `TorusFock.secondQuant_nExcitation` : `dΓ M (Σ Ψ a†…a† Ω) = Σ (D_n M Ψ) a†…a† Ω`.
- `TorusFock.nBody_lie` : `D_n ⁅M, N⁆ = ⁅D_n M, D_n N⁆`.
- `TorusFock.form_nExcitation_symm` : for symmetric `Φ`, `β` restricts to `n! Ψ̄ · Φ`.
- `TorusFock.uncertainty_nExcitation` : for symmetric `Ψ`, the uncertainty field of the field
  state is `matUncertainty (√(n!) Ψ) (D_n M) (D_n N)`.
-/

@[expose] public noncomputable section

open TorusField TorusSectors
open scoped Matrix

namespace TorusFock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-! ## 1. Words of creation operators -/

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (L : LadderSystem ℂ V d) (e : ι ≃ Fin d)
  (Ω : V)

/-- The word `a†_{x₀} ⋯ a†_{x_{n-1}} Ω`. -/
def word : (n : ℕ) → (Fin n → ι) → V
  | 0, _ => Ω
  | n + 1, x => L.ac (e (x 0)) (word n (Fin.tail x))

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma word_zero (x : Fin 0 → ι) : word L e Ω 0 x = Ω := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma word_succ (n : ℕ) (x : Fin (n + 1) → ι) :
    word L e Ω (n + 1) x = L.ac (e (x 0)) (word L e Ω n (Fin.tail x)) := rfl

lemma E_ac_comm (i j r : Fin d) (v : V) :
    L.E i j (L.ac r v) = L.ac r (L.E i j v) + if j = r then L.ac i v else 0 := by
  change (L.ac i * L.a j) _ = (L.ac r) ((L.ac i * L.a j) v) + _
  rw [Module.End.mul_apply, a_ac_comm, map_add, ac_ac_comm, Module.End.mul_apply]
  split_ifs <;> simp

omit [DecidableEq ι] in
/-- Second quantization commutes with a creation operator up to the matrix acting on it. -/
lemma secondQuant_ac_comm (M : Matrix ι ι ℂ) (r : ι) (v : V) :
    secondQuant L e M (L.ac (e r) v) =
      L.ac (e r) (secondQuant L e M v) + ∑ p, M p r • L.ac (e p) v := by
  classical
  simp only [secondQuant_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply, E_ac_comm,
    EmbeddingLike.apply_eq_iff_eq, smul_add, smul_ite, smul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_sum, map_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma secondQuant_vacuum_aux {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (i j : Fin d) : L.E i j Ω = 0 := by
  change (L.ac i * L.a j) Ω = 0
  rw [Module.End.mul_apply, hΩ, map_zero]

omit [DecidableEq ι] in
lemma secondQuant_vacuum {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ) :
    secondQuant L e M Ω = 0 := by
  simp [secondQuant_eq_sum, secondQuant_vacuum_aux L hΩ]

omit [DecidableEq ι] in
/-- **Second quantization on a word moves one creation operator at a time.** -/
theorem secondQuant_word {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ) (n : ℕ) :
    ∀ x : Fin n → ι, secondQuant L e M (word L e Ω n x) =
      ∑ k, ∑ p, M p (x k) • word L e Ω n (Function.update x k p) := by
  induction n with
  | zero => intro x; simp [secondQuant_vacuum L e hΩ]
  | succ n ih =>
    intro x
    rw [word_succ, secondQuant_ac_comm, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    refine Eq.trans (add_comm (_ : V) _) ?_
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp [word_succ, Fin.tail_update_zero]
    · simp only [map_sum, map_smul]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
      rw [word_succ, Function.update_of_ne (Fin.succ_ne_zero k).symm, Fin.tail_update_succ]
      rfl

/-- The sector of `n` excitations: a state `Ψ` of `n` positions as `Σ Ψ(x) a†_{x₀} ⋯ Ω`. -/
def nExcitation (n : ℕ) : ((Fin n → ι) → ℂ) →ₗ[ℂ] V where
  toFun Ψ := ∑ x, Ψ x • word L e Ω n x
  map_add' ψ φ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r ψ := by simp [Finset.smul_sum, smul_smul]

/-- The matrix `M` applied to the `k`-th position of `n`, the others fixed. -/
def moveAt (n : ℕ) (k : Fin n) (M : Matrix ι ι ℂ) : Module.End ℂ ((Fin n → ι) → ℂ) where
  toFun Ψ := fun y => ∑ r, M (y k) r * Ψ (Function.update y k r)
  map_add' ψ φ := by
    ext y
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext y
    simp [Finset.mul_sum, mul_left_comm]

/-- The `n`-body operator of a matrix: `M` applied to one position at a time. -/
def nBody (n : ℕ) (M : Matrix ι ι ℂ) : Module.End ℂ ((Fin n → ι) → ℂ) := ∑ k, moveAt n k M

omit [DecidableEq ι] in
lemma nBody_apply (n : ℕ) (M : Matrix ι ι ℂ) (Ψ : (Fin n → ι) → ℂ) (y : Fin n → ι) :
    nBody n M Ψ y = ∑ k, ∑ r, M (y k) r * Ψ (Function.update y k r) := by
  simp [nBody, moveAt, LinearMap.sum_apply, Finset.sum_apply]

omit [DecidableEq ι] in
/-- **Second quantization on `n` excitations is the `n`-body operator.** -/
theorem secondQuant_nExcitation {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ) (n : ℕ)
    (Ψ : (Fin n → ι) → ℂ) :
    secondQuant L e M (nExcitation L e Ω n Ψ) = nExcitation L e Ω n (nBody n M Ψ) := by
  simp only [nExcitation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    secondQuant_word L e hΩ, nBody_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hinv : Function.Involutive
      (fun z : (Fin n → ι) × ι => (Function.update z.1 k z.2, z.1 k)) := by
    intro z
    simp
  let σ : Equiv.Perm ((Fin n → ι) × ι) :=
    { toFun := fun z => (Function.update z.1 k z.2, z.1 k)
      invFun := fun z => (Function.update z.1 k z.2, z.1 k)
      left_inv := hinv
      right_inv := hinv }
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine (Equiv.sum_comp σ
    (fun z : (Fin n → ι) × ι => (Ψ z.1 * M z.2 (z.1 k)) •
      word L e Ω n (Function.update z.1 k z.2))).symm.trans ?_
  refine Finset.sum_congr rfl fun z _ => ?_
  show (Ψ (Function.update z.1 k z.2) * M (z.1 k) (Function.update z.1 k z.2 k)) •
    word L e Ω n (Function.update (Function.update z.1 k z.2) k (z.1 k)) = _
  simp [mul_comm]

end Algebraic

/-! ## 2. The `n`-body operators respect brackets -/

section NBody

variable (n : ℕ)

omit [DecidableEq ι] in
lemma moveAt_mul (k : Fin n) (M N : Matrix ι ι ℂ) :
    moveAt n k (M * N) = moveAt n k M * moveAt n k N := by
  refine LinearMap.ext fun Ψ => funext fun y => ?_
  simp only [moveAt, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Function.update_self, Function.update_idem, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

omit [DecidableEq ι] in
lemma moveAt_comm {j k : Fin n} (hjk : j ≠ k) (M N : Matrix ι ι ℂ) :
    moveAt n j M * moveAt n k N = moveAt n k N * moveAt n j M := by
  refine LinearMap.ext fun Ψ => funext fun y => ?_
  simp only [moveAt, Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum,
    Function.update_of_ne hjk, Function.update_of_ne hjk.symm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [Function.update_comm hjk]
  ring

omit [DecidableEq ι] in
lemma moveAt_sub (k : Fin n) (M N : Matrix ι ι ℂ) :
    moveAt n k (M - N) = moveAt n k M - moveAt n k N := by
  refine LinearMap.ext fun Ψ => funext fun y => ?_
  simp [moveAt, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
/-- **The `n`-body operators respect brackets.** -/
theorem nBody_lie (M N : Matrix ι ι ℂ) :
    nBody n ⁅M, N⁆ = ⁅nBody n M, nBody n N⁆ := by
  have key : ∀ k : Fin n, ∑ l, (moveAt n k M * moveAt n l N - moveAt n l N * moveAt n k M) =
      moveAt n k M * moveAt n k N - moveAt n k N * moveAt n k M := by
    intro k
    rw [Finset.sum_eq_single k]
    · intro l _ hl
      rw [moveAt_comm n hl.symm, sub_self]
    · simp
  rw [Ring.lie_def, Ring.lie_def, nBody, nBody, nBody, Finset.sum_mul_sum, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm (f := fun l k => moveAt n l N * moveAt n k M)]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib, key, ← moveAt_mul, ← moveAt_mul, ← moveAt_sub]

end NBody

/-- The matrix of an `n`-body operator on the states of `n` positions. -/
def nBodyMat (n : ℕ) (M : Matrix ι ι ℂ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  LinearMap.toMatrix' (nBody n M)

lemma nBodyMat_mulVec (n : ℕ) (M : Matrix ι ι ℂ) (Ψ : (Fin n → ι) → ℂ) :
    nBodyMat n M *ᵥ Ψ = nBody n M Ψ := by
  rw [nBodyMat, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- The matrices of the `n`-body operators respect brackets. -/
theorem nBodyMat_lie (n : ℕ) (M N : Matrix ι ι ℂ) :
    nBodyMat n ⁅M, N⁆ = ⁅nBodyMat n M, nBodyMat n N⁆ := by
  unfold nBodyMat
  rw [nBody_lie, Ring.lie_def, Ring.lie_def, map_sub, LinearMap.toMatrix'_mul,
    LinearMap.toMatrix'_mul]

/-! ## 3. Lowering a creation operator on a word -/

section Lower

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {L : LadderSystem ℂ V d} (e : ι ≃ Fin d)
  {Ω : V} (hΩ : ∀ i, L.a i Ω = 0)
include hΩ

omit [Fintype ι] in
/-- **An annihilation operator removes one creation operator of the word at a time.** -/
theorem a_word (j : ι) (m : ℕ) : ∀ y : Fin (m + 1) → ι,
    L.a (e j) (word L e Ω (m + 1) y) =
      ∑ k, if y k = j then word L e Ω m (fun i => y (k.succAbove i)) else 0 := by
  induction m with
  | zero =>
    intro y
    rw [word_succ, word_zero, a_ac_vacuum hΩ]
    simp [eq_comm]
  | succ m ih =>
    intro y
    rw [word_succ, a_ac_comm, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    refine Eq.trans (add_comm (_ : V) _) (congrArg₂ (· + ·) ?_ ?_)
    · have h0 : (fun i => y ((0 : Fin (m + 2)).succAbove i)) = Fin.tail y := by
        funext i
        simp [Fin.tail]
      rw [h0]
      by_cases h : y 0 = j
      · simp [h]
      · have : e j ≠ e (y 0) := fun h' => h (e.injective h').symm
        simp [h, this]
    · rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : y k.succ = j
      · have hc : (fun i => y (k.succ.succAbove i)) =
            Fin.cons (y 0) (fun i' => y ((k.succAbove i').succ)) := by
          funext i
          refine Fin.cases ?_ ?_ i <;> simp [Fin.succ_succAbove_succ]
        simp only [h, ite_true, hc, word_succ, Fin.cons_zero, Fin.tail_cons]
        simp only [show Fin.tail y k = j from h, ite_true]
        rfl
      · simp [Fin.tail, h]

end Lower

/-! ## 4. Symmetric states and the form -/

section Star

/-- A state of `n` positions is symmetric when it does not see the order of the positions. -/
def IsSymmN (n : ℕ) (Ψ : (Fin n → ι) → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ι), Ψ (x ∘ σ) = Ψ x

omit [DecidableEq ι] in
lemma IsSymmN.nBody {n : ℕ} {Ψ : (Fin n → ι) → ℂ} (h : IsSymmN n Ψ) (M : Matrix ι ι ℂ) :
    IsSymmN n (TorusFock.nBody n M Ψ) := by
  intro σ x
  rw [nBody_apply, nBody_apply]
  refine Eq.trans ?_ (Equiv.sum_comp σ (fun k => ∑ r, M (x k) r * Ψ (Function.update x k r)))
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => ?_
  have : Function.update (x ∘ σ) k r = Function.update x (σ k) r ∘ σ := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · have : σ i ≠ σ k := fun h' => hi (σ.injective h')
      simp [Function.update_of_ne hi, Function.update_of_ne this]
  rw [this, h σ]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma IsSymmN.cons {n : ℕ} {Φ : (Fin (n + 1) → ι) → ℂ} (h : IsSymmN (n + 1) Φ) (a : ι) :
    IsSymmN n (fun w => Φ (Fin.cons a w)) := by
  intro σ w
  let σ' : Equiv.Perm (Fin (n + 1)) :=
    (finSuccEquiv n).trans ((Equiv.optionCongr σ).trans (finSuccEquiv n).symm)
  have : (Fin.cons a w : Fin (n + 1) → ι) ∘ σ' = Fin.cons a (w ∘ σ) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [σ']
    · simp [σ']
  show Φ (Fin.cons a (w ∘ σ)) = Φ (Fin.cons a w)
  rw [← this]
  exact h σ' _

omit [Fintype ι] [DecidableEq ι] in
lemma insertNth_eq_cons_comp {m : ℕ} (k : Fin (m + 1)) (j : ι) (w : Fin m → ι) :
    Fin.insertNth k j w = Fin.cons j w ∘ k.cycleRange := by
  funext i
  refine Fin.succAboveCases k ?_ ?_ i
  · simp [Fin.cycleRange_self]
  · intro i'
    simp [Fin.cycleRange_succAbove]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {L : LadderSystem ℂ V d} (e : ι ≃ Fin d)
  {Ω : V} (hΩ : ∀ i, L.a i Ω = 0)
include hΩ

/-- **Lowering a symmetric `(m + 1)`-excitation state with `a_j` gives `m + 1` times the
`m`-excitation state `Φ(j, ·)`.** -/
theorem a_nExcitation {m : ℕ} {Φ : (Fin (m + 1) → ι) → ℂ} (hΦ : IsSymmN (m + 1) Φ) (j : ι) :
    L.a (e j) (nExcitation L e Ω (m + 1) Φ) =
      ((m + 1 : ℕ) : ℂ) • nExcitation L e Ω m (fun w => Φ (Fin.cons j w)) := by
  simp only [nExcitation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, a_word e hΩ,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin (m + 1), ∑ y : Fin (m + 1) → ι,
      Φ y • (if y k = j then word L e Ω m (fun i => y (k.succAbove i)) else 0) =
      ∑ w : Fin m → ι, Φ (Fin.cons j w) • word L e Ω m w := by
    intro k
    refine (Equiv.sum_comp (Fin.insertNthEquiv (fun _ => ι) k)
      (fun y : Fin (m + 1) → ι =>
        Φ y • (if y k = j then word L e Ω m (fun i => y (k.succAbove i)) else 0))).symm.trans ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun w _ => ?_
      have h1 : Φ (Fin.insertNth k j w) = Φ (Fin.cons j w) := by
        rw [insertNth_eq_cons_comp]
        exact hΦ k.cycleRange _
      simp [Fin.insertNthEquiv, h1]
    · intro a _ ha
      simp [Fin.insertNthEquiv, ha]
    · simp
  simp only [hk, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]

variable {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hL : IsStar L β) (hn : β Ω Ω = 1)
include hL hn

/-- **The form against a symmetric state: `β (word x, Σ Φ word) = n! Φ(x)`.** -/
theorem form_word_nExcitation (n : ℕ) : ∀ (Φ : (Fin n → ι) → ℂ), IsSymmN n Φ →
    ∀ x : Fin n → ι, β (word L e Ω n x) (nExcitation L e Ω n Φ) = (n.factorial : ℂ) * Φ x := by
  induction n with
  | zero =>
    intro Φ _ x
    have hx : ∀ x' : Fin 0 → ι, x' = x := fun x' => Subsingleton.elim _ _
    simp [nExcitation, hn, hx]
  | succ n ih =>
    intro Φ hΦ x
    rw [word_succ, hL, a_nExcitation e hΩ hΦ, map_smul, ih _ (hΦ.cons (x 0)) (Fin.tail x),
      Fin.cons_self_tail, Nat.factorial_succ]
    simp only [smul_eq_mul]
    push_cast
    ring

/-- **The form on `n` excitations: `β (Σ Ψ word, Σ Φ word) = n! Ψ̄ · Φ` for symmetric `Φ`.** -/
theorem form_nExcitation_symm {n : ℕ} {Φ : (Fin n → ι) → ℂ} (hΦ : IsSymmN n Φ)
    (Ψ : (Fin n → ι) → ℂ) :
    β (nExcitation L e Ω n Ψ) (nExcitation L e Ω n Φ) = (n.factorial : ℂ) * (star Ψ ⬝ᵥ Φ) := by
  have h : nExcitation L e Ω n Ψ = ∑ x, Ψ x • word L e Ω n x := rfl
  rw [h]
  simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply,
    form_word_nExcitation e hΩ hL hn n Φ hΦ, dotProduct, Pi.star_apply, smul_eq_mul,
    Finset.mul_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma form_mul {n : ℕ} {Ψ : (Fin n → ι) → ℂ} (hΨ : IsSymmN n Ψ) (M N : Matrix ι ι ℂ) :
    β (nExcitation L e Ω n Ψ) ((secondQuant L e M * secondQuant L e N) (nExcitation L e Ω n Ψ)) =
      (n.factorial : ℂ) * (star Ψ ⬝ᵥ ((nBodyMat n M * nBodyMat n N) *ᵥ Ψ)) := by
  rw [Module.End.mul_apply, secondQuant_nExcitation L e hΩ, secondQuant_nExcitation L e hΩ,
    form_nExcitation_symm e hΩ hL hn ((hΨ.nBody N).nBody M), ← Matrix.mulVec_mulVec,
    nBodyMat_mulVec, nBodyMat_mulVec]

lemma form_one {n : ℕ} {Ψ : (Fin n → ι) → ℂ} (hΨ : IsSymmN n Ψ) (M : Matrix ι ι ℂ) :
    β (nExcitation L e Ω n Ψ) (secondQuant L e M (nExcitation L e Ω n Ψ)) =
      (n.factorial : ℂ) * (star Ψ ⬝ᵥ (nBodyMat n M *ᵥ Ψ)) := by
  rw [secondQuant_nExcitation L e hΩ, form_nExcitation_symm e hΩ hL hn (hΨ.nBody M),
    nBodyMat_mulVec]

lemma form_lie {n : ℕ} {Ψ : (Fin n → ι) → ℂ} (hΨ : IsSymmN n Ψ) (M N : Matrix ι ι ℂ) :
    β (nExcitation L e Ω n Ψ)
        (⁅secondQuant L e M, secondQuant L e N⁆ (nExcitation L e Ω n Ψ)) =
      (n.factorial : ℂ) * (star Ψ ⬝ᵥ (⁅nBodyMat n M, nBodyMat n N⁆ *ᵥ Ψ)) := by
  rw [← secondQuant_lie, form_one e hΩ hL hn hΨ, nBodyMat_lie]

omit hΩ hL hn in
lemma scale_form {X : Type*} [Fintype X] [DecidableEq X] (a : ℝ) (ha : 0 ≤ a)
    (A : Matrix X X ℂ) (Ψ : X → ℂ) :
    star ((Real.sqrt a : ℂ) • Ψ) ⬝ᵥ (A *ᵥ ((Real.sqrt a : ℂ) • Ψ)) = (a : ℂ) * (star Ψ ⬝ᵥ (A *ᵥ Ψ)) := by
  have hc : (starRingEnd ℂ) (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = a := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, Complex.star_def, mul_comm (Real.sqrt a : ℂ), hc]

/-- **The uncertainty field of `n` excitations is the one of the `n`-body matrices**, on the
state `√(n!) Ψ`. -/
theorem uncertainty_nExcitation {n : ℕ} {Ψ : (Fin n → ι) → ℂ} (hΨ : IsSymmN n Ψ)
    (M N : Matrix ι ι ℂ) :
    uncertainty β (nExcitation L e Ω n Ψ) (secondQuant L e M) (secondQuant L e N) =
      matUncertainty ((Real.sqrt (n.factorial : ℝ) : ℂ) • Ψ) (nBodyMat n M) (nBodyMat n N) := by
  have hf : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  rw [uncertainty, matUncertainty, form_mul e hΩ hL hn hΨ, form_mul e hΩ hL hn hΨ,
    form_one e hΩ hL hn hΨ, form_one e hΩ hL hn hΨ, form_lie e hΩ hL hn hΨ]
  simp only [scale_form _ hf]
  push_cast
  rfl

end Star

end TorusFock
