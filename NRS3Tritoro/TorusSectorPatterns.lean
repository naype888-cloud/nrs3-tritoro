/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSectorCut

/-!
# The patterns of the cut on two excitations

A two-body step of the cut (`TorusSectorCut.twoSteps`) is open for a symmetric state `Ψ` of two
excitations when its two ends carry coherence, `Ψ̄(s.1) Ψ(s.2) ≠ 0`. On one excitation every set of
boundary steps is the open set of some unit state (`TorusPatterns.cutPatterns_eq`). On two it is not:

- a symmetric state opens a step together with its image under the exchange of the two
  excitations, so every pattern is invariant under the exchange;
- a pattern is closed: if both ends of a step lie in the ends of the pattern, or in their
  exchanged images, the step belongs to the pattern. This characterizes the patterns exactly;
- hence there are at most `2 ^ (N · 2 · dy · dz)` patterns, `N = dx · dy · dz`, and strictly fewer.

## Main results

- `TorusSectorPatterns.mem_patterns_iff` : the patterns are the closed sets of two-body steps.
- `TorusSectorPatterns.swap_mem_of_mem_patterns` : every pattern is invariant under the exchange.
- `TorusSectorPatterns.card_patterns_le` : at most `2 ^ (N · (2 · dy · dz))` patterns.
- `TorusSectorPatterns.card_patterns_lt` : strictly fewer: not every invariant set is a pattern.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone TorusArea TorusField TorusSectors TorusSectorCut
open scoped Matrix
open PathGraph3D (Site3D)

namespace TorusSectorPatterns

variable {dx dy dz : ℕ}

/-! ## 1. The exchange of the two excitations on steps -/

/-- The exchange of the two excitations, on a two-body step. -/
def swapStep (s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :
    (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz) :=
  (s.1.swap, s.2.swap)

lemma swapStep_swapStep
    (s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :
    swapStep (swapStep s) = s := by
  simp [swapStep]

open Classical in
/-- The steps taken by the first excitation, the second one fixed. -/
def firstSteps (dx dy dz c : ℕ) :
    Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
  (crossSteps dx dy dz c ×ˢ (Finset.univ : Finset (Site3D dx dy dz))).image
    fun t => ((t.1.1, t.2), (t.1.2, t.2))

open Classical in
/-- The steps taken by the second excitation, the first one fixed. -/
def secondSteps (dx dy dz c : ℕ) :
    Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
  (crossSteps dx dy dz c ×ˢ (Finset.univ : Finset (Site3D dx dy dz))).image
    fun t => ((t.2, t.1.1), (t.2, t.1.2))

lemma twoSteps_eq (c : ℕ) :
    twoSteps dx dy dz c = firstSteps dx dy dz c ∪ secondSteps dx dy dz c := rfl

lemma swapStep_mem_secondSteps {c : ℕ}
    {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)}
    (hs : s ∈ firstSteps dx dy dz c) : swapStep s ∈ secondSteps dx dy dz c := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

lemma swapStep_mem_firstSteps {c : ℕ}
    {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)}
    (hs : s ∈ secondSteps dx dy dz c) : swapStep s ∈ firstSteps dx dy dz c := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨t, ht, rfl⟩

lemma swapStep_mem_twoSteps {c : ℕ}
    {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)}
    (hs : s ∈ twoSteps dx dy dz c) : swapStep s ∈ twoSteps dx dy dz c := by
  rw [twoSteps_eq, Finset.mem_union] at hs ⊢
  exact hs.imp swapStep_mem_secondSteps swapStep_mem_firstSteps |>.symm

lemma disjoint_firstSteps_secondSteps (c : ℕ) :
    Disjoint (firstSteps dx dy dz c) (secondSteps dx dy dz c) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, h⟩ := Finset.mem_image.mp hx'
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact cross_ne (Finset.mem_product.mp ha).1 (h1.symm.trans h3)

lemma card_firstSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (firstSteps dx dy dz c).card = (dx * dy * dz) * (2 * (dy * dz)) := by
  classical
  rw [firstSteps, Finset.card_image_of_injective, Finset.card_product, card_crossSteps hc hd]
  · simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  · intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact Prod.ext (Prod.ext h1 h3) h2

/-! ## 2. Open steps and patterns -/

open Classical in
/-- The open steps of a state of two excitations: the two-body steps whose ends both carry
amplitude. -/
def openSteps (dx dy dz c : ℕ) (Ψ : Site3D dx dy dz × Site3D dx dy dz → ℂ) :
    Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
  (twoSteps dx dy dz c).filter fun s => star (Ψ s.1) * Ψ s.2 ≠ 0

lemma mem_openSteps {c : ℕ} {Ψ : Site3D dx dy dz × Site3D dx dy dz → ℂ}
    {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)} :
    s ∈ openSteps dx dy dz c Ψ ↔ s ∈ twoSteps dx dy dz c ∧ Ψ s.1 ≠ 0 ∧ Ψ s.2 ≠ 0 := by
  classical
  simp [openSteps, Finset.mem_filter, mul_eq_zero, not_or]

/-- **A symmetric state opens a step together with its exchanged image.** -/
theorem swapStep_mem_openSteps {c : ℕ} {Ψ : Site3D dx dy dz × Site3D dx dy dz → ℂ}
    (hΨ : IsSymm Ψ) {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)}
    (hs : s ∈ openSteps dx dy dz c Ψ) : swapStep s ∈ openSteps dx dy dz c Ψ := by
  rw [mem_openSteps] at hs ⊢
  obtain ⟨h1, h2, h3⟩ := hs
  exact ⟨swapStep_mem_twoSteps h1, by simpa [swapStep, hΨ.swap] using h2,
    by simpa [swapStep, hΨ.swap] using h3⟩

open Classical in
/-- The patterns of the cut on two excitations: the sets of two-body steps opened by a symmetric
state that is a unit for the form of the field (`2 Ψ̄ · Ψ = 1`). -/
def patterns (dx dy dz c : ℕ) :
    Finset (Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz))) :=
  (twoSteps dx dy dz c).powerset.filter fun S =>
    ∃ Ψ : Site3D dx dy dz × Site3D dx dy dz → ℂ,
      IsSymm Ψ ∧ 2 * (star Ψ ⬝ᵥ Ψ) = 1 ∧ openSteps dx dy dz c Ψ = S

/-- **Every pattern is invariant under the exchange of the two excitations.** -/
theorem swap_mem_of_mem_patterns {c : ℕ} {S : Finset _} (hS : S ∈ patterns dx dy dz c)
    {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)} (hs : s ∈ S) :
    swapStep s ∈ S := by
  classical
  obtain ⟨Ψ, hΨ, -, rfl⟩ := (Finset.mem_filter.mp hS).2
  exact swapStep_mem_openSteps hΨ hs

/-! ## 3. The patterns are the closed sets -/

lemma twoSteps_ne {c : ℕ}
    {s : (Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)}
    (hs : s ∈ twoSteps dx dy dz c) : s.1 ≠ s.2 := by
  classical
  rw [twoSteps_eq, Finset.mem_union] at hs
  rcases hs with hs | hs
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    intro h
    exact cross_ne (Finset.mem_product.mp ht).1 (congrArg (fun p => p.1) h)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    intro h
    exact cross_ne (Finset.mem_product.mp ht).1 (congrArg (fun p => p.2) h)

section Closed

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A symmetric unit state with a prescribed support: `2 Ψ̄ · Ψ = 1` and `Ψ x ≠ 0 ↔ x ∈ U`. -/
lemma exists_unit_support (U : Finset (X × X)) (hne : U.Nonempty)
    (hU : ∀ x ∈ U, x.swap ∈ U) :
    ∃ Ψ : X × X → ℂ, IsSymm Ψ ∧ 2 * (star Ψ ⬝ᵥ Ψ) = 1 ∧ ∀ x, Ψ x ≠ 0 ↔ x ∈ U := by
  classical
  set r : ℝ := (Real.sqrt (2 * U.card))⁻¹ with hr
  have hcard : (0 : ℝ) < 2 * U.card := by
    have := hne.card_pos
    positivity
  have hr0 : r ≠ 0 := inv_ne_zero (Real.sqrt_ne_zero'.mpr hcard)
  refine ⟨fun x => if x ∈ U then (r : ℂ) else 0, ?_, ?_, ?_⟩
  · intro p q
    have : (q, p) ∈ U ↔ (p, q) ∈ U :=
      ⟨fun h => by simpa using hU _ h, fun h => by simpa using hU _ h⟩
    simp only [this]
  · have h1 : ∀ x : X × X, star (if x ∈ U then (r : ℂ) else 0) * (if x ∈ U then (r : ℂ) else 0)
        = if x ∈ U then ((r * r : ℝ) : ℂ) else 0 := by
      intro x
      split_ifs <;> simp
    simp only [dotProduct, Pi.star_apply, h1, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    have : r * r = (2 * (U.card : ℝ))⁻¹ := by
      rw [hr, ← mul_inv, Real.mul_self_sqrt hcard.le]
    rw [this]
    have h2 : (2 * (U.card : ℝ)) ≠ 0 := hcard.ne'
    push_cast
    have h3 : (U.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_pos.ne'
    field_simp
  · intro x
    by_cases hx : x ∈ U
    · simp [hx, hr0]
    · simp [hx]

end Closed

/-- The ends of a set of steps, and their exchanged images. -/
def ends {dx dy dz : ℕ}
    (S : Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz))) :
    Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  S.biUnion fun t => {t.1, t.2, t.1.swap, t.2.swap}

lemma mem_ends {S : Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz))}
    {x : Site3D dx dy dz × Site3D dx dy dz} :
    x ∈ ends S ↔ ∃ t ∈ S, x = t.1 ∨ x = t.2 ∨ x = t.1.swap ∨ x = t.2.swap := by
  classical
  simp [ends, Finset.mem_biUnion]

lemma swap_mem_ends {S : Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz))}
    {x : Site3D dx dy dz × Site3D dx dy dz} (hx : x ∈ ends S) : x.swap ∈ ends S := by
  obtain ⟨t, ht, h⟩ := mem_ends.mp hx
  refine mem_ends.mpr ⟨t, ht, ?_⟩
  rcases h with rfl | rfl | rfl | rfl <;> simp

/-- **The patterns on two excitations are the closed sets of two-body steps:** a set of steps is
opened by a symmetric unit state exactly when every step whose two ends lie among the ends of the
set, or their exchanged images, is already in the set. -/
theorem mem_patterns_iff {c : ℕ} (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) {S : Finset _} :
    S ∈ patterns dx dy dz c ↔ S ⊆ twoSteps dx dy dz c ∧
      ∀ s ∈ twoSteps dx dy dz c, s.1 ∈ ends S → s.2 ∈ ends S → s ∈ S := by
  classical
  constructor
  · intro hS
    have hmem := (Finset.mem_filter.mp hS)
    obtain ⟨Ψ, hΨ, -, rfl⟩ := hmem.2
    refine ⟨Finset.mem_powerset.mp hmem.1, fun s hs h1 h2 => ?_⟩
    have key : ∀ x ∈ ends (openSteps dx dy dz c Ψ), Ψ x ≠ 0 := by
      intro x hx
      obtain ⟨t, ht, h⟩ := mem_ends.mp hx
      obtain ⟨-, h1, h2⟩ := mem_openSteps.mp ht
      rcases h with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · rwa [hΨ.swap]
      · rwa [hΨ.swap]
    exact mem_openSteps.mpr ⟨hs, key _ h1, key _ h2⟩
  · rintro ⟨hsub, hcl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, ?_⟩
    rcases S.eq_empty_or_nonempty with rfl | hne
    · let p₀ : Site3D dx dy dz := (⟨0, by omega⟩, ⟨0, hy⟩, ⟨0, hz⟩)
      obtain ⟨Ψ, hΨ, hn, hsupp⟩ := exists_unit_support {(p₀, p₀)} ⟨_, Finset.mem_singleton_self _⟩
        (fun x hx => by simp_all)
      refine ⟨Ψ, hΨ, hn, ?_⟩
      ext s
      simp only [Finset.notMem_empty, iff_false, mem_openSteps, not_and, not_not]
      intro hs h1
      have h1' := (hsupp _).mp h1
      by_contra h2
      have h2' := (hsupp _).mp h2
      simp only [Finset.mem_singleton] at h1' h2'
      exact absurd (h1'.trans h2'.symm) (twoSteps_ne hs)
    · obtain ⟨Ψ, hΨ, hn, hsupp⟩ := exists_unit_support (ends S)
        (by obtain ⟨t, ht⟩ := hne; exact ⟨t.1, mem_ends.mpr ⟨t, ht, Or.inl rfl⟩⟩)
        (fun x hx => swap_mem_ends hx)
      refine ⟨Ψ, hΨ, hn, ?_⟩
      ext s
      rw [mem_openSteps]
      constructor
      · rintro ⟨hs, h1, h2⟩
        exact hcl s hs ((hsupp _).mp h1) ((hsupp _).mp h2)
      · intro hs
        obtain ⟨t1, t2⟩ := s
        exact ⟨hsub hs, (hsupp _).mpr (mem_ends.mpr ⟨_, hs, Or.inl rfl⟩),
          (hsupp _).mpr (mem_ends.mpr ⟨_, hs, Or.inr (Or.inl rfl)⟩)⟩

/-! ## 4. At most `2 ^ (N · 2 · dy · dz)` patterns, and strictly fewer -/

section Count

variable {c : ℕ}

open Classical in
/-- The part of a set of steps taken by the first excitation. -/
def firstPart (c : ℕ)
    (S : Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz))) :
    Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
  S.filter fun s => s ∈ firstSteps dx dy dz c

/-- A pattern is its first part together with the exchanged image of its first part. -/
lemma eq_firstPart_union {S : Finset _} (hS : S ∈ patterns dx dy dz c) :
    ∀ s, s ∈ S ↔ s ∈ firstPart c S ∨ ∃ t ∈ firstPart c S, swapStep t = s := by
  classical
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  intro s
  constructor
  · intro hs
    have hs' := hsub hs
    rw [twoSteps_eq, Finset.mem_union] at hs'
    rcases hs' with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs, h⟩)
    · refine Or.inr ⟨swapStep s, Finset.mem_filter.mpr ⟨swap_mem_of_mem_patterns hS hs,
        swapStep_mem_firstSteps h⟩, swapStep_swapStep s⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact (Finset.mem_filter.mp h).1
    · exact swap_mem_of_mem_patterns hS (Finset.mem_filter.mp ht).1

/-- **At most `2 ^ (N · 2 · dy · dz)` patterns**, `N = dx · dy · dz`: a pattern is fixed by its
part taken by the first excitation. -/
theorem card_patterns_le (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (patterns dx dy dz c).card ≤ 2 ^ ((dx * dy * dz) * (2 * (dy * dz))) := by
  classical
  have hinj : Set.InjOn (firstPart (dx := dx) (dy := dy) (dz := dz) c) (patterns dx dy dz c : Set _) := by
    intro S hS S' hS' h
    ext s
    rw [eq_firstPart_union hS, eq_firstPart_union hS', h]
  calc (patterns dx dy dz c).card ≤ (firstSteps dx dy dz c).powerset.card := by
        refine Finset.card_le_card_of_injOn (firstPart (dx := dx) (dy := dy) (dz := dz) c) (fun S hS => ?_) hinj
        exact Finset.mem_powerset.mpr (fun s hs => (Finset.mem_filter.mp hs).2)
    _ = _ := by rw [Finset.card_powerset, card_firstSteps hc hd]

/-- **Not every exchange-invariant set of steps is a pattern.** Two boundary steps `t ≠ t'`:
the first excitation takes `t` with the second one at either end of `t'`. A symmetric state that
opens both is nonzero at the four corners, so it also opens the step of the second excitation
along `t'`, which the set does not contain. -/
theorem card_patterns_lt (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) :
    (patterns dx dy dz c).card < 2 ^ ((dx * dy * dz) * (2 * (dy * dz))) := by
  classical
  have h2 : 1 < (crossSteps dx dy dz c).card := by
    rw [card_crossSteps hc hd]
    have : 0 < dy * dz := Nat.mul_pos hy hz
    omega
  obtain ⟨t, ht, t', ht', hne⟩ := Finset.one_lt_card.mp h2
  let T : Finset ((Site3D dx dy dz × Site3D dx dy dz) × (Site3D dx dy dz × Site3D dx dy dz)) :=
    {((t.1, t'.1), (t.2, t'.1)), ((t.1, t'.2), (t.2, t'.2))}
  have hT : T ∈ (firstSteps dx dy dz c).powerset := by
    refine Finset.mem_powerset.mpr fun s hs => ?_
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact Finset.mem_image.mpr ⟨(t, t'.1), Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(t, t'.2), Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, rfl⟩
  have hnot : T ∉ (patterns dx dy dz c).image (firstPart (dx := dx) (dy := dy) (dz := dz) c) := by
    intro hmem
    obtain ⟨S, hS, hST⟩ := Finset.mem_image.mp hmem
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hTS : ∀ x ∈ T, x ∈ S := fun x hx => by
      rw [← hST] at hx
      exact (Finset.mem_filter.mp hx).1
    have e1 : ((t.1, t'.1), (t.2, t'.1)) ∈ S := hTS _ (by simp [T])
    have e2 : ((t.1, t'.2), (t.2, t'.2)) ∈ S := hTS _ (by simp [T])
    have hs : ((t.1, t'.1), (t.1, t'.2)) ∈ twoSteps dx dy dz c := by
      rw [twoSteps_eq, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨(t', t.1),
        Finset.mem_product.mpr ⟨ht', Finset.mem_univ _⟩, rfl⟩)
    have hin := (mem_patterns_iff hd hy hz).mp hS
    have hmemS := hin.2 _ hs (mem_ends.mpr ⟨_, e1, Or.inl rfl⟩)
      (mem_ends.mpr ⟨_, e2, Or.inl rfl⟩)
    have hsw := swap_mem_of_mem_patterns hS hmemS
    have hfirst : swapStep ((t.1, t'.1), (t.1, t'.2)) ∈ firstSteps dx dy dz c :=
      swapStep_mem_firstSteps (Finset.mem_image.mpr ⟨(t', t.1),
        Finset.mem_product.mpr ⟨ht', Finset.mem_univ _⟩, rfl⟩)
    have hinT : swapStep ((t.1, t'.1), (t.1, t'.2)) ∈ T := by
      rw [← hST]
      exact Finset.mem_filter.mpr ⟨hsw, hfirst⟩
    simp only [T, swapStep, Finset.mem_insert, Finset.mem_singleton, Prod.swap_prod_mk,
      Prod.mk.injEq] at hinT
    rcases hinT with ⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩
    · exact hne (Prod.ext h1.symm h3.symm)
    · exact cross_ne ht (h2.trans h3)
  have hinj : Set.InjOn (firstPart (dx := dx) (dy := dy) (dz := dz) c) (patterns dx dy dz c : Set _) := by
    intro S hS S' hS' h
    ext s
    rw [eq_firstPart_union hS, eq_firstPart_union hS', h]
  calc (patterns dx dy dz c).card
      = ((patterns dx dy dz c).image (firstPart (dx := dx) (dy := dy) (dz := dz) c)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ < (firstSteps dx dy dz c).powerset.card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
        · intro U hU
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
          exact Finset.mem_powerset.mpr (fun s hs => (Finset.mem_filter.mp hs).2)
        · intro h
          exact hnot (h ▸ hT)
    _ = _ := by rw [Finset.card_powerset, card_firstSteps hc hd]

end Count

end TorusSectorPatterns
