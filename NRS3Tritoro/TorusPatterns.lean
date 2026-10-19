/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusField
public import NRS3Tritoro.TorusTime

/-!
# The patterns of the cut of the three-torus

A boundary step of the region `{x ≤ c}` (`TorusArea.crossSteps`, the plane and the seam) is open
for a state `ψ` when its two ends carry coherence, `ψ̄_p ψ_q ≠ 0`, and closed otherwise. The
bracket `[T3c, P_x]` reads only that coherence: the contribution of a step to `⟨ψ, [T3c, P_x] ψ⟩`
is `B (z − z̄)`, with `z = ψ̄_p ψ_q` and `B` the bracket on the step, which is antisymmetric.

Every set of boundary steps is the set of open steps of some unit state: the vector that is `1`
on the ends of the set opens exactly those steps. With at least three positions the plane and the
seam of one fibre never share both ends, so no step opens by accident. Hence the patterns the
bracket can read are all the subsets, `2 ^ (2 · dy · dz)`, and the entropy of the cut is the log
of their number, with no definition of "open or closed" put in by hand. At the level of the field
the same patterns are opened by unit one-excitation states.

## Main results

- `TorusPatterns.bracketX_swap` : the bracket on a step run backwards is minus the bracket.
- `TorusPatterns.bracketX_stepTerm` : a step contributes `B (z − z̄)`, the coherence only.
- `TorusPatterns.cutPatterns_eq` : every set of boundary steps is the open set of a unit state.
- `TorusPatterns.card_cutPatterns` : there are `2 ^ (2 · dy · dz)` patterns.
- `TorusPatterns.cutEntropy_eq_cutPatterns` : `S = log #patterns`.
- `TorusPatterns.exists_field_pattern` : every pattern is opened by a unit one-excitation field
  state, on which the bracket of the field reads the bracket of the torus.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone TorusArea TorusField
open scoped Matrix
open PathGraph3D (Site3D)

namespace TorusPatterns

variable {dx dy dz : ℕ}

/-! ## 1. The bracket reads the coherence of a step -/


lemma liftAlong_symm {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (e : ι ≃ α × β) {A : Matrix α α ℂ}
    (hA : ∀ i j, A j i = A i j) (p q : ι) : liftAlong e A q p = liftAlong e A p q := by
  simp only [liftAlong, Matrix.of_apply, hA]
  by_cases h : (e p).2 = (e q).2
  · simp [h]
  · simp [h, Ne.symm h]

/-- The transport of the torus is symmetric. -/
lemma T3c_symm (p q : Site3D dx dy dz) : T3c dx dy dz q p = T3c dx dy dz p q := by
  simp only [T3c, Matrix.add_apply]
  rw [liftAlong_symm _ (TorusTime.ring_comm dx) p q, liftAlong_symm _ (TorusTime.ring_comm dy) p q,
    liftAlong_symm _ (TorusTime.ring_comm dz) p q]

/-- **Run backwards, a step has minus the bracket.** -/
theorem bracketX_swap (p q : Site3D dx dy dz) :
    bracketX dx dy dz q p = -bracketX dx dy dz p q := by
  rw [bracketX_apply, bracketX_apply, T3c_symm]
  ring

/-- **The bracket reads only the coherence of a step.** The contribution of a step to
`⟨ψ, [T3c, P_x] ψ⟩` is `B (z − z̄)`, with `z = ψ̄_p ψ_q` the coherence between its two ends. -/
theorem bracketX_stepTerm (p q : Site3D dx dy dz) (ψ : H3D dx dy dz) :
    star (ψ p) * bracketX dx dy dz p q * ψ q + star (ψ q) * bracketX dx dy dz q p * ψ p =
      bracketX dx dy dz p q * (star (ψ p) * ψ q - star (star (ψ p) * ψ q)) := by
  rw [bracketX_swap, star_mul, star_star]
  ring

/-! ## 2. Open and closed steps -/

/-- A boundary step goes from `(c, y, z)` to `(c + 1, y, z)` (the plane) or from `(0, y, z)` to
`(dx − 1, y, z)` (the seam). -/
lemma mem_crossSteps_iff (hd : 3 ≤ dx) {c : ℕ} {s : Site3D dx dy dz × Site3D dx dy dz} :
    s ∈ crossSteps dx dy dz c ↔
      s.1.1.val ≤ c ∧ c < s.2.1.val ∧
        ((s.1.1.val = c ∧ s.2.1.val = c + 1) ∨ (s.1.1.val = 0 ∧ s.2.1.val + 1 = dx)) ∧
        s.1.2 = s.2.2 := by
  simp only [crossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hq, h⟩
    exact ⟨hp, hq, (T3c_ne_zero_iff hd hp hq).mp h⟩
  · rintro ⟨hp, hq, h⟩
    exact ⟨hp, hq, (T3c_ne_zero_iff hd hp hq).mpr h⟩

/-- A boundary step is fixed by the positions of its ends along `x` and by its fibre. -/
lemma crossSteps_ext {s t : Site3D dx dy dz × Site3D dx dy dz} (h1 : s.1.1 = t.1.1)
    (h2 : s.2.1 = t.2.1) (hs : s.1.2 = s.2.2) (ht : t.1.2 = t.2.2) (h3 : s.1.2 = t.1.2) :
    s = t := by
  obtain ⟨⟨a, w⟩, ⟨b, w'⟩⟩ := s
  obtain ⟨⟨a', v⟩, ⟨b', v'⟩⟩ := t
  simp only at h1 h2 hs ht h3
  subst h1 h2 hs ht h3
  rfl

open Classical in
/-- The open steps of `ψ`: the boundary steps whose two ends carry coherence, `ψ̄_p ψ_q ≠ 0`.
On the others the bracket reads zero. -/
def openSteps (dx dy dz c : ℕ) (ψ : H3D dx dy dz) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  (crossSteps dx dy dz c).filter fun s => star (ψ s.1) * ψ s.2 ≠ 0

lemma openSteps_subset (c : ℕ) (ψ : H3D dx dy dz) :
    openSteps dx dy dz c ψ ⊆ crossSteps dx dy dz c :=
  Finset.filter_subset _ _

/-- Rescaling a state does not open or close a step. -/
lemma openSteps_smul (c : ℕ) {r : ℂ} (hr : r ≠ 0) (ψ : H3D dx dy dz) :
    openSteps dx dy dz c (r • ψ) = openSteps dx dy dz c ψ := by
  ext s
  have : star r * r ≠ 0 := mul_ne_zero (star_ne_zero.mpr hr) hr
  simp only [openSteps, Finset.mem_filter, PiLp.smul_apply, smul_eq_mul, star_mul]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun h0 => h' (by rw [show star (ψ s.1) * star r * (r * ψ s.2) =
      (star r * r) * (star (ψ s.1) * ψ s.2) by ring, h0, mul_zero])⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, by rw [show star (ψ s.1) * star r * (r * ψ s.2) =
      (star r * r) * (star (ψ s.1) * ψ s.2) by ring]; exact mul_ne_zero this h'⟩

open Classical in
/-- The vector that is `1` on the ends of the steps of `S` and `0` elsewhere. -/
def supportVec (S : Finset (Site3D dx dy dz × Site3D dx dy dz)) : H3D dx dy dz :=
  WithLp.toLp 2 fun p => if ∃ t ∈ S, t.1 = p ∨ t.2 = p then 1 else 0

/-- **`supportVec S` opens exactly the steps of `S`.** With three positions or more, the plane
and the seam of a fibre do not share both ends, so no other step opens. -/
theorem openSteps_supportVec (hd : 3 ≤ dx) {c : ℕ}
    {S : Finset (Site3D dx dy dz × Site3D dx dy dz)} (hS : S ⊆ crossSteps dx dy dz c) :
    openSteps dx dy dz c (supportVec S) = S := by
  classical
  ext s
  rw [openSteps, Finset.mem_filter]
  simp only [supportVec]
  constructor
  · rintro ⟨hs, h⟩
    by_contra hns
    apply h
    by_cases h1 : ∃ t ∈ S, t.1 = s.1 ∨ t.2 = s.1
    · by_cases h2 : ∃ u ∈ S, u.1 = s.2 ∨ u.2 = s.2
      · exfalso
        obtain ⟨t, ht, ht'⟩ := h1
        obtain ⟨u, hu, hu'⟩ := h2
        have hs' := (mem_crossSteps_iff hd).mp hs
        have ht1 := (mem_crossSteps_iff hd).mp (hS ht)
        have hu1 := (mem_crossSteps_iff hd).mp (hS hu)
        have e1 : (t.1.1.val = s.1.1.val ∨ t.2.1.val = s.1.1.val) ∧ (t.1.2 = s.1.2) := by
          rcases ht' with h | h
          · exact ⟨Or.inl (by rw [h]), by rw [h]⟩
          · exact ⟨Or.inr (by rw [h]), ht1.2.2.2.trans (by rw [h])⟩
        have e2 : (u.1.1.val = s.2.1.val ∨ u.2.1.val = s.2.1.val) ∧ (u.1.2 = s.2.2) := by
          rcases hu' with h | h
          · exact ⟨Or.inl (by rw [h]), by rw [h]⟩
          · exact ⟨Or.inr (by rw [h]), hu1.2.2.2.trans (by rw [h])⟩
        have hn : (t.1.1.val = s.1.1.val ∧ t.2.1.val = s.2.1.val) ∨
            (u.1.1.val = s.1.1.val ∧ u.2.1.val = s.2.1.val) := by omega
        rcases hn with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact hns (crossSteps_ext (Fin.ext ha.symm) (Fin.ext hb.symm) hs'.2.2.2 ht1.2.2.2
            e1.2.symm ▸ ht)
        · exact hns (crossSteps_ext (Fin.ext ha.symm) (Fin.ext hb.symm) hs'.2.2.2 hu1.2.2.2
            (hs'.2.2.2.trans e2.2.symm) ▸ hu)
      · simp [h2]
    · simp [h1]
  · intro hs
    refine ⟨hS hs, ?_⟩
    have e1 : ∃ t ∈ S, t.1 = s.1 ∨ t.2 = s.1 := ⟨s, hs, Or.inl rfl⟩
    have e2 : ∃ t ∈ S, t.1 = s.2 ∨ t.2 = s.2 := ⟨s, hs, Or.inr rfl⟩
    simp [e1, e2]

open Classical in
/-- The patterns of open steps that unit states realize across the region `{x ≤ c}`. -/
def cutPatterns (dx dy dz c : ℕ) : Finset (Finset (Site3D dx dy dz × Site3D dx dy dz)) :=
  (crossSteps dx dy dz c).powerset.filter fun S =>
    ∃ ψ : H3D dx dy dz, ‖ψ‖ = 1 ∧ openSteps dx dy dz c ψ = S

/-- **Every set of boundary steps is the open set of some unit state.** -/
theorem cutPatterns_eq {c : ℕ} (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) :
    cutPatterns dx dy dz c = (crossSteps dx dy dz c).powerset := by
  classical
  ext S
  simp only [cutPatterns, Finset.mem_filter, Finset.mem_powerset, and_iff_left_iff_imp]
  intro hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · let p₀ : Site3D dx dy dz := (⟨0, by omega⟩, ⟨0, hy⟩, ⟨0, hz⟩)
    refine ⟨EuclideanSpace.single p₀ 1, by simp, ?_⟩
    ext s
    simp only [openSteps, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_not]
    intro hs
    have hs' := (mem_crossSteps_iff hd).mp hs
    have hne : s.1 ≠ s.2 := fun h => by
      have h' : s.1.1.val = s.2.1.val := congrArg (fun p : Site3D dx dy dz => p.1.val) h
      omega
    by_cases h1 : s.1 = p₀
    · have : s.2 ≠ p₀ := fun h => hne (h1.trans h.symm)
      simp [PiLp.single_apply, this]
    · simp [PiLp.single_apply, h1]
  · let φ := supportVec S
    have hφ : φ ≠ 0 := fun h => by
      have h1 : ∃ u ∈ S, u.1 = t.1 ∨ u.2 = t.1 := ⟨t, ht, Or.inl rfl⟩
      have h2 : φ t.1 = 1 := by
        change (if ∃ u ∈ S, u.1 = t.1 ∨ u.2 = t.1 then (1 : ℂ) else 0) = 1
        simp only [eq_true_intro h1, ite_true]
      rw [h] at h2
      simp at h2
    have hn : (‖φ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hφ)
    refine ⟨(‖φ‖ : ℂ)⁻¹ • φ, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ)]
    · rw [openSteps_smul c (inv_ne_zero hn)]
      exact openSteps_supportVec hd hS

/-- **There are `2 ^ (2 · dy · dz)` patterns: two per boundary step, open or closed.** -/
theorem card_cutPatterns {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) :
    (cutPatterns dx dy dz c).card = 2 ^ (2 * (dy * dz)) := by
  rw [cutPatterns_eq hd hy hz, Finset.card_powerset, card_crossSteps hc hd]

/-- **The entropy of the cut counts the patterns the bracket reads.** No definition of
"open or closed" enters: `S = log #patterns = 2 · dy · dz · log 2`. -/
theorem cutEntropy_eq_cutPatterns {c : ℕ} (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) :
    cutEntropy dx dy dz c = Real.log (cutPatterns dx dy dz c).card := by
  rw [cutEntropy, cutPatterns_eq hd hy hz]

/-! ## 3. The patterns at the level of the field -/

section Field

variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {L : LadderSystem ℂ V d}
  {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Ω : V} (e : Site3D dx dy dz ≃ Fin d)

/-- **The patterns of the cut are the same at the level of the field.** Every set `S` of
boundary steps is opened by a unit state `ψ` of the torus whose field state `Σ ψ_p a†_p Ω` is a
unit for `β`, and on it the bracket of the field reads the bracket of the torus. -/
theorem exists_field_pattern (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1)
    {c : ℕ} (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz)
    {S : Finset (Site3D dx dy dz × Site3D dx dy dz)} (hS : S ⊆ crossSteps dx dy dz c) :
    ∃ ψ : H3D dx dy dz, openSteps dx dy dz c ψ = S ∧
      β (oneExcitation L e Ω ψ) (oneExcitation L e Ω ψ) = 1 ∧
      β (oneExcitation L e Ω ψ)
          (⁅secondQuant L e (T3c dx dy dz), secondQuant L e (posX dx dy dz)⁆
            (oneExcitation L e Ω ψ)) =
        star ⇑ψ ⬝ᵥ (bracketX dx dy dz *ᵥ ⇑ψ) := by
  have hS' : S ∈ cutPatterns dx dy dz c := by
    rw [cutPatterns_eq hd hy hz]
    exact Finset.mem_powerset.mpr hS
  classical
  obtain ⟨ψ, hψ, hψS⟩ := (Finset.mem_filter.mp hS').2
  refine ⟨ψ, hψS, ?_, ?_⟩
  · rw [form_oneExcitation e hL hΩ hn, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hψ]
    simp
  · rw [form_bracket_torus e hL hΩ hn]

end Field

end TorusPatterns
