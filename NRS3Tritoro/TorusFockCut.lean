/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusFock
public import NRS3Tritoro.TorusSectorCut

/-!
# The cut of the three-torus on `n` excitations

On the sector of `n` excitations the bracket of the field is the `n`-body matrix of the bracket,
`⁅dΓ T3c, dΓ P_x⁆ = dΓ [T3c, P_x]`, acting as `D_n [T3c, P_x]` (`TorusFock`). Its entries move one
excitation at a time. A boundary step of the `n`-body cut is a boundary step of the torus taken by
one of the `n` excitations while the other `n - 1` sit at any of the `dx · dy · dz` positions each:
`n · (2 · dy · dz) · (dx · dy · dz) ^ (n - 1)` steps. For `n = 2` this is `TorusSectorCut`.

## Main results

- `TorusFockCut.form_bracket_n` : on a symmetric state of `n` excitations the bracket of the field
  reads `n! Ψ̄ · D_n [T3c, P_x] Ψ`.
- `TorusFockCut.nBodyMat_apply_step` : the entry of `D_n M` on a step of one excitation is the
  entry of `M`.
- `TorusFockCut.bracketNSteps_eq` : the `n`-body steps across `{x ≤ c}` on which the bracket is
  nonzero are exactly one boundary step with `n - 1` spectators.
- `TorusFockCut.card_bracketNSteps` : there are `n · (2 · dy · dz) · (dx · dy · dz) ^ (n - 1)`.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone TorusArea TorusField TorusSectors TorusFock
  TorusSectorCut
open scoped Matrix
open PathGraph3D (Site3D)

namespace TorusFockCut

variable {dx dy dz : ℕ}

/-! ## 1. The field bracket on `n` excitations -/

section Field

variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {L : LadderSystem ℂ V d}
  {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Ω : V} (e : Site3D dx dy dz ≃ Fin d)

/-- **The bracket of the field on `n` excitations reads the `n`-body bracket of the torus.** -/
theorem form_bracket_n (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1) {n : ℕ}
    {Ψ : (Fin n → Site3D dx dy dz) → ℂ} (hΨ : IsSymmN n Ψ) :
    β (nExcitation L e Ω n Ψ)
        (⁅secondQuant L e (T3c dx dy dz), secondQuant L e (posX dx dy dz)⁆
          (nExcitation L e Ω n Ψ)) =
      (n.factorial : ℂ) * (star Ψ ⬝ᵥ (nBodyMat n (bracketX dx dy dz) *ᵥ Ψ)) := by
  rw [form_lie e hΩ hL hn hΨ, ← nBodyMat_lie]
  rfl

end Field

/-! ## 2. The entries of the `n`-body matrix -/

section Entries

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- **The entry of the `n`-body matrix**: `M` on one position, the other ones fixed. -/
theorem nBodyMat_apply (M : Matrix ι ι ℂ) (x y : Fin n → ι) :
    nBodyMat n M x y = ∑ k, if (∀ i, i ≠ k → x i = y i) then M (x k) (y k) else 0 := by
  rw [nBodyMat, LinearMap.toMatrix'_apply, nBody_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : ∀ i, i ≠ k → x i = y i
  · rw [show (if (∀ i, i ≠ k → x i = y i) then M (x k) (y k) else 0) = M (x k) (y k) by simp only [eq_true_intro h, ite_true],
      Finset.sum_eq_single (y k)]
    · have : Function.update x k (y k) = y := by
        funext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [Function.update_of_ne hi, h i hi]
      simp [this]
    · intro r _ hr
      have : Function.update x k r ≠ y := fun h' => hr (by simpa using congrFun h' k)
      simp [this]
    · simp
  · rw [show (if (∀ i, i ≠ k → x i = y i) then M (x k) (y k) else 0) = 0 by simp only [eq_false_intro h, ite_false]]
    refine Finset.sum_eq_zero fun r _ => ?_
    have : Function.update x k r ≠ y := by
      intro h'
      apply h
      intro i hi
      simpa [Function.update_of_ne hi] using congrFun h' i
    simp [this]

/-- On a step of one excitation, the entry of the `n`-body matrix is the entry of `M`. -/
theorem nBodyMat_apply_step (M : Matrix ι ι ℂ) {x y : Fin n → ι} {k : Fin n}
    (hk : ∀ i, i ≠ k → x i = y i) (hne : x k ≠ y k) : nBodyMat n M x y = M (x k) (y k) := by
  rw [nBodyMat_apply, Finset.sum_eq_single k]
  · simp only [eq_true_intro hk, ite_true]
  · intro l _ hl
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (h k hl.symm) hne
  · simp

end Entries

/-! ## 3. The steps of the `n`-body cut -/

section Steps

variable (n : ℕ)

open Classical in
/-- The `n`-body steps across the region `{x ≤ c}` on which the bracket is nonzero: one excitation
crosses, the other ones stay. -/
def bracketNSteps (dx dy dz c : ℕ) :
    Finset ((Fin n → Site3D dx dy dz) × (Fin n → Site3D dx dy dz)) :=
  Finset.univ.filter fun xy =>
    nBodyMat n (bracketX dx dy dz) xy.1 xy.2 ≠ 0 ∧
      ∃ k, (xy.1 k).1.val ≤ c ∧ c < (xy.2 k).1.val ∧ ∀ i, i ≠ k → xy.1 i = xy.2 i

open Classical in
/-- One boundary step taken by one of the `n` excitations, the other ones fixed. -/
def nSteps (dx dy dz c : ℕ) : Finset ((Fin n → Site3D dx dy dz) × (Fin n → Site3D dx dy dz)) :=
  Finset.univ.filter fun xy =>
    ∃ k, (xy.1 k, xy.2 k) ∈ crossSteps dx dy dz c ∧ ∀ i, i ≠ k → xy.1 i = xy.2 i

/-- **The `n`-body steps of the cut are one boundary step with `n - 1` spectators.** -/
theorem bracketNSteps_eq (hd : 3 ≤ dx) (c : ℕ) :
    bracketNSteps n dx dy dz c = nSteps n dx dy dz c := by
  classical
  ext ⟨x, y⟩
  simp only [bracketNSteps, nSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, k, hp, hq, hk⟩
    have hxy : x k ≠ y k := fun h => by
      have : (x k).1.val = (y k).1.val := congrArg (fun p : Site3D dx dy dz => p.1.val) h
      omega
    rw [nBodyMat_apply_step _ hk hxy] at hne
    refine ⟨k, ?_, hk⟩
    rw [← bracketCrossSteps_eq hd]
    simp only [bracketCrossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hp, hq, hne⟩
  · rintro ⟨k, hm, hk⟩
    have hne := cross_ne hm
    have hmem := hm
    rw [← bracketCrossSteps_eq hd] at hmem
    have hb := (Finset.mem_filter.mp hmem).2
    exact ⟨by rw [nBodyMat_apply_step _ hk hne]; exact hb.2.2, k, hb.1, hb.2.1, hk⟩

open Classical in
/-- The steps of the `k`-th excitation. -/
def kSteps (dx dy dz c : ℕ) (k : Fin n) :
    Finset ((Fin n → Site3D dx dy dz) × (Fin n → Site3D dx dy dz)) :=
  Finset.univ.filter fun xy =>
    (xy.1 k, xy.2 k) ∈ crossSteps dx dy dz c ∧ ∀ i, i ≠ k → xy.1 i = xy.2 i

lemma card_kSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (k : Fin n) :
    (kSteps n dx dy dz c k).card = (2 * (dy * dz)) * (dx * dy * dz) ^ (n - 1) := by
  classical
  have hcard : Fintype.card {i : Fin n // i ≠ k} = n - 1 := by
    rw [Fintype.card_subtype_compl (fun i => i = k), Fintype.card_subtype_eq, Fintype.card_fin]
  have : (kSteps n dx dy dz c k).card =
      (crossSteps dx dy dz c ×ˢ (Finset.univ : Finset ({i : Fin n // i ≠ k} → Site3D dx dy dz))).card := by
    refine Finset.card_bij (fun xy _ => ((xy.1 k, xy.2 k), fun j => xy.1 j.1)) ?_ ?_ ?_
    · intro xy hxy
      simp only [kSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      exact Finset.mem_product.mpr ⟨hxy.1, Finset.mem_univ _⟩
    · intro xy hxy xy' hxy' h
      simp only [kSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hxy hxy'
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · by_cases hi : i = k
        · subst hi; exact h1
        · exact congrFun h3 ⟨i, hi⟩
      · by_cases hi : i = k
        · subst hi; exact h2
        · rw [← hxy.2 i hi, ← hxy'.2 i hi]
          exact congrFun h3 ⟨i, hi⟩
    · intro z hz
      obtain ⟨⟨a, b⟩, f⟩ := z
      have hz' := (Finset.mem_product.mp hz).1
      refine ⟨(fun i => if h : i = k then a else f ⟨i, h⟩,
        fun i => if h : i = k then b else f ⟨i, h⟩), ?_, ?_⟩
      · simp only [kSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by simpa using hz', fun i hi => by simp [hi]⟩
      · refine Prod.ext (by simp) (funext fun j => ?_)
        simp [j.2]
  rw [this, Finset.card_product, card_crossSteps hc hd, Finset.card_univ, Fintype.card_fun,
    hcard]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring_nf

/-- **The field bracket on `n` excitations reads `n · (2 · dy · dz) · (dx · dy · dz) ^ (n - 1)`
steps.** -/
theorem card_bracketNSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (bracketNSteps n dx dy dz c).card = n * ((2 * (dy * dz)) * (dx * dy * dz) ^ (n - 1)) := by
  classical
  have h : nSteps n dx dy dz c = Finset.univ.biUnion (kSteps n dx dy dz c) := by
    ext xy
    simp [nSteps, kSteps]
  rw [bracketNSteps_eq n hd, h, Finset.card_biUnion]
  · simp [card_kSteps n hc hd]
  · intro k _ l _ hkl
    rw [Function.onFun, Finset.disjoint_left]
    intro xy hk hl
    simp only [kSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hk hl
    exact cross_ne hl.1 (hk.2 l (Ne.symm hkl))

end Steps

end TorusFockCut
