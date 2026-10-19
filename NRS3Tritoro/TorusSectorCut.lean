/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSectors
public import NRS3Tritoro.TorusPatterns

/-!
# The cut of the three-torus on two excitations

On the sector of two excitations the bracket of the field is the two-body matrix of the bracket,
`⁅dΓ T3c, dΓ P_x⁆ = dΓ [T3c, P_x]`, acting as `D [T3c, P_x]` (`TorusSectors`). Its entries move one
excitation at a time, the other one stays where it is. A boundary step of the two-body cut is a
boundary step of the torus (the plane and the seam) taken by one of the two excitations, while the
other one sits at any of the `dx · dy · dz` positions. So the field bracket on two excitations
reads `2 · dx · dy · dz` times the `2 · dy · dz` steps that it reads on one.

## Main results

- `TorusSectorCut.form_bracket_two` : on a symmetric state of two excitations, the bracket of the
  field reads `2 Ψ̄ · D [T3c, P_x] Ψ`.
- `TorusSectorCut.bracketTwoSteps_eq` : the two-body steps across `{x ≤ c}` on which the bracket is
  nonzero are exactly one boundary step taken by one excitation, the other one fixed.
- `TorusSectorCut.card_bracketTwoSteps` : there are `2 · (dx · dy · dz) · (2 · dy · dz)` of them.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone TorusArea TorusField TorusSectors
open scoped Matrix
open PathGraph3D (Site3D)

namespace TorusSectorCut

variable {dx dy dz : ℕ}

/-! ## 1. The field bracket on two excitations -/

section Field

variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {L : LadderSystem ℂ V d}
  {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Ω : V} (e : Site3D dx dy dz ≃ Fin d)

/-- **The bracket of the field on two excitations reads the two-body bracket of the torus.** -/
theorem form_bracket_two (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1)
    {Ψ : Site3D dx dy dz × Site3D dx dy dz → ℂ} (hΨ : IsSymm Ψ) :
    β (twoExcitation L e Ω Ψ)
        (⁅secondQuant L e (T3c dx dy dz), secondQuant L e (posX dx dy dz)⁆
          (twoExcitation L e Ω Ψ)) =
      2 * (star Ψ ⬝ᵥ (twoBody (bracketX dx dy dz) *ᵥ Ψ)) := by
  rw [form_lie e hL hΩ hn hΨ, ← twoBody_lie]
  rfl

end Field

/-! ## 2. The steps of the two-body cut -/

open Classical in
/-- The two-body steps across the region `{x ≤ c}` on which the bracket is nonzero: one
excitation crosses, the other one stays. -/
def bracketTwoSteps (dx dy dz c : ℕ) :
    Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
  Finset.univ.filter fun xy =>
    twoBody (bracketX dx dy dz) xy.1 xy.2 ≠ 0 ∧
      ((xy.1.1.1.val ≤ c ∧ c < xy.2.1.1.val ∧ xy.1.2 = xy.2.2) ∨
        (xy.1.2.1.val ≤ c ∧ c < xy.2.2.1.val ∧ xy.1.1 = xy.2.1))

open Classical in
/-- One boundary step, taken by the first excitation or by the second, the other one fixed. -/
def twoSteps (dx dy dz c : ℕ) :
    Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
  ((crossSteps dx dy dz c ×ˢ (Finset.univ : Finset (Site3D dx dy dz))).image
      fun t => ((t.1.1, t.2), (t.1.2, t.2))) ∪
    ((crossSteps dx dy dz c ×ˢ (Finset.univ : Finset (Site3D dx dy dz))).image
      fun t => ((t.2, t.1.1), (t.2, t.1.2)))

lemma cross_ne {c : ℕ} {s : Site3D dx dy dz × Site3D dx dy dz} (hs : s ∈ crossSteps dx dy dz c) :
    s.1 ≠ s.2 := by
  intro h
  have h1 := (Finset.mem_filter.mp hs).2
  have : s.1.1.val = s.2.1.val := congrArg (fun p : Site3D dx dy dz => p.1.val) h
  omega

lemma twoBody_first (M : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ)
    {s : Site3D dx dy dz × Site3D dx dy dz} (hs : s.1 ≠ s.2) (r : Site3D dx dy dz) :
    twoBody M (s.1, r) (s.2, r) = M s.1 s.2 := by
  simp [twoBody_apply, hs]

lemma twoBody_second (M : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ)
    {s : Site3D dx dy dz × Site3D dx dy dz} (hs : s.1 ≠ s.2) (r : Site3D dx dy dz) :
    twoBody M (r, s.1) (r, s.2) = M s.1 s.2 := by
  simp [twoBody_apply, hs]

/-- **The two-body steps of the cut are one boundary step with a spectator.** -/
theorem bracketTwoSteps_eq (hd : 3 ≤ dx) (c : ℕ) :
    bracketTwoSteps dx dy dz c = twoSteps dx dy dz c := by
  classical
  ext ⟨⟨p, r⟩, ⟨q, r'⟩⟩
  simp only [bracketTwoSteps, twoSteps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hne, h1 | h2⟩
    · obtain ⟨hp, hq, hr⟩ := h1
      subst hr
      have hpq : p ≠ q := by
        intro h; subst h; omega
      rw [twoBody_first _ (s := (p, q)) hpq] at hne
      have hs : (p, q) ∈ bracketCrossSteps dx dy dz c := by
        simp only [bracketCrossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp, hq, hne⟩
      rw [bracketCrossSteps_eq hd] at hs
      exact Or.inl ⟨((p, q), r), Finset.mem_product.mpr ⟨hs, Finset.mem_univ _⟩, rfl⟩
    · obtain ⟨hp, hq, hr⟩ := h2
      subst hr
      have hpq : r ≠ r' := by
        intro h; subst h; omega
      rw [twoBody_second _ (s := (r, r')) hpq] at hne
      have hs : (r, r') ∈ bracketCrossSteps dx dy dz c := by
        simp only [bracketCrossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp, hq, hne⟩
      rw [bracketCrossSteps_eq hd] at hs
      exact Or.inr ⟨((r, r'), p), Finset.mem_product.mpr ⟨hs, Finset.mem_univ _⟩, rfl⟩
  · rintro (⟨⟨t, w⟩, hm, heq⟩ | ⟨⟨t, w⟩, hm, heq⟩)
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
      subst h1 h2 h3 h4
      have hs := (Finset.mem_product.mp hm).1
      have hne := cross_ne hs
      have hmem := hs
      rw [← bracketCrossSteps_eq hd] at hmem
      have hb := (Finset.mem_filter.mp hmem).2
      exact ⟨by rw [twoBody_first _ hne]; exact hb.2.2, Or.inl ⟨hb.1, hb.2.1, rfl⟩⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
      subst h1 h2 h3 h4
      have hs := (Finset.mem_product.mp hm).1
      have hne := cross_ne hs
      have hmem := hs
      rw [← bracketCrossSteps_eq hd] at hmem
      have hb := (Finset.mem_filter.mp hmem).2
      exact ⟨by rw [twoBody_second _ hne]; exact hb.2.2, Or.inr ⟨hb.1, hb.2.1, rfl⟩⟩

/-- **The field bracket on two excitations reads `2 · (dx · dy · dz) · (2 · dy · dz)` steps.** -/
theorem card_bracketTwoSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (bracketTwoSteps dx dy dz c).card = 2 * ((dx * dy * dz) * (2 * (dy * dz))) := by
  classical
  rw [bracketTwoSteps_eq hd, twoSteps, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective, Finset.card_product, card_crossSteps hc hd]
  · simp [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc]
    ring
  · intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact Prod.ext (Prod.ext (by assumption) (by assumption)) (by assumption)
  · intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact Prod.ext (Prod.ext (by assumption) (by assumption)) (by assumption)
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, h⟩ := Finset.mem_image.mp hx'
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact cross_ne (Finset.mem_product.mp ha).1 (h1.symm.trans h3)

end TorusSectorCut
