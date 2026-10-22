/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusWhiteBall

/-!
# The ball of yarn: layers of quanta, and only the outer face is seen

`TorusWhiteBall` declares that a quantum below capacity keeps light on its edge and a full one is
dark. A star that does not reach its collapse mass wraps itself in layers and layers of quanta,
stacked on the threads along which the field moves its excitations. Here are the layers.

* **The face hides the interior.** Take an outer face `X` and the steps `Y` of the layers behind
  it, disjoint from `X`. Every configuration of the face is compatible with exactly `2^|Y|`
  configurations of the whole ball, the same number for every face. What is seen from outside
  says nothing about the layers inside: they stay intact.
* **Spread over the quanta, none full: everything keeps its light.** For a family of layers,
  each a white ball, every layer keeps light on its edge exactly when no layer is filled to
  capacity. One full layer is one dark quantum: the collapse.
* **On `T³`.** The walls `x = c | c + 1` at different positions are disjoint, so the walls of a
  set of positions `C` are `|C| · dy · dz` steps, and a wall in front of them hides
  `2^(|C| · dy · dz)` interiors behind each of its faces.

The light of a layer is an excitation of the field being measured; on the vacuum there is
nothing to measure (`TorusFock.secondQuant_vacuum`), and an open step of a face is the field
moving an excitation across it (`TorusBoundaryField.configField_eq_sum`).

## Main results

- `TorusLayers.card_interiors` : every face of `X` hides `2^|Y|` configurations of the layers.
- `TorusLayers.lightShare_pos_iff` : every layer keeps light iff no layer is full.
- `TorusLayers.lightShare_eq_zero_of_full` : a full layer is dark.
- `TorusLayers.exists_dark_iff` : some layer is dark iff some layer is full.
- `TorusLayers.disjoint_planeSteps` : the walls of `T³` at different positions are disjoint.
- `TorusLayers.card_layerSteps` : the walls of `C` have `|C| · dy · dz` steps.
- `TorusLayers.card_interiors_torus` : a wall of `T³` hides `2^(|C| · dy · dz)` interiors.
-/

@[expose] public noncomputable section

open BoundaryBits TorusWhiteBall
open PathGraph3D (Site3D)

namespace TorusLayers

/-! ## 1. The face hides the interior -/

section Face

variable {α : Type*} [DecidableEq α] {X Y : Finset α}

/-- **Every face hides the same interior.** For a face `S ⊆ X` and layers `Y` disjoint from `X`,
the configurations of the whole ball `X ∪ Y` that show the face `S` are `2^|Y|`. -/
theorem card_interiors (hXY : Disjoint X Y) {S : Finset α} (hS : S ⊆ X) :
    ((X ∪ Y).powerset.filter fun T => T ∩ X = S).card = 2 ^ Y.card := by
  rw [← Finset.card_powerset Y]
  refine Finset.card_nbij' (fun T => T ∩ Y) (fun U => S ∪ U) ?_ ?_ ?_ ?_
  · intro T _
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact Finset.inter_subset_right
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_powerset] at hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset_union hS hU, ?_⟩
    ext a
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨ha | ha, hx⟩
      · exact ha
      · exact absurd hx (Finset.disjoint_right.1 hXY (hU ha))
    · intro ha
      exact ⟨Or.inl ha, hS ha⟩
  · intro T hT
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hT, rfl⟩ := hT
    ext a
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    · intro ha
      rcases Finset.mem_union.1 (hT ha) with hx | hy
      · exact Or.inl ⟨ha, hx⟩
      · exact Or.inr ⟨ha, hy⟩
  · intro U hU
    rw [Finset.mem_coe, Finset.mem_powerset] at hU
    ext a
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨ha | ha, hy⟩
      · exact absurd (hS ha) (Finset.disjoint_right.1 hXY hy)
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hU ha⟩

end Face

/-! ## 2. Spread over the quanta, none full -/

section Layers

variable {ι α : Type*} {X : ι → Finset α} (W : ∀ i, HWhiteBall (X i))
  (d : ∀ i, ProbDistribution (Config (X i)))

/-- **Spread over the quanta without filling any: every layer keeps its light.** -/
theorem lightShare_pos_iff :
    (∀ i, 0 < (W i).lightShare (d i)) ↔ ∀ i, d i ≠ ProbDistribution.uniform :=
  forall_congr' fun i => (W i).lightShare_pos_iff

/-- **A full layer is dark**: the quantum collapses. -/
theorem lightShare_eq_zero_of_full {i : ι} (h : d i = ProbDistribution.uniform) :
    (W i).lightShare (d i) = 0 := by
  rw [HWhiteBall.lightShare, (W i).darkShare_eq_one_iff.2 h, sub_self]

/-- Some layer is dark exactly when some layer is full. -/
theorem exists_dark_iff :
    (∃ i, (W i).lightShare (d i) = 0) ↔ ∃ i, d i = ProbDistribution.uniform := by
  refine exists_congr fun i => ⟨fun h => ?_, lightShare_eq_zero_of_full W d⟩
  by_contra hne
  exact ((W i).lightShare_pos_iff.2 hne).ne' h

end Layers

/-! ## 3. The layers of `T³` -/

section Torus

variable {dx dy dz : ℕ}

/-- **The walls of `T³` at different positions are disjoint.** -/
theorem disjoint_planeSteps {c c' : ℕ} (hc : c + 1 < dx) (hc' : c' + 1 < dx) (h : c ≠ c') :
    Disjoint (TorusArea.planeSteps dx dy dz c hc) (TorusArea.planeSteps dx dy dz c' hc') := by
  rw [Finset.disjoint_left]
  intro pq h1 h2
  simp only [TorusArea.planeSteps, Finset.mem_image, Finset.mem_univ, true_and] at h1 h2
  obtain ⟨yz, rfl⟩ := h1
  obtain ⟨yz', h'⟩ := h2
  exact h (by simpa using (congrArg (fun pq => pq.1.1.val) h').symm)

/-- The layers behind a face: the walls at the positions `C`. -/
def layerSteps (dx dy dz : ℕ) (C : Finset (Fin (dx - 1))) :
    Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  C.biUnion fun i => TorusArea.planeSteps dx dy dz i.val (by omega)

/-- **The layers of `C` have `|C| · dy · dz` steps.** -/
theorem card_layerSteps (C : Finset (Fin (dx - 1))) :
    (layerSteps dx dy dz C).card = C.card * (dy * dz) := by
  rw [layerSteps, Finset.card_biUnion]
  · simp [TorusArea.card_planeSteps]
  · intro i _ j _ hij
    exact disjoint_planeSteps _ _ (fun h => hij (Fin.ext h))

/-- **A wall of `T³` hides `2^(|C| · dy · dz)` interiors behind each of its faces.** -/
theorem card_interiors_torus (c : Fin (dx - 1)) {C : Finset (Fin (dx - 1))} (hc : c ∉ C)
    {S : Finset (Site3D dx dy dz × Site3D dx dy dz)}
    (hS : S ⊆ TorusArea.planeSteps dx dy dz c.val (by omega)) :
    ((TorusArea.planeSteps dx dy dz c.val (by omega) ∪ layerSteps dx dy dz C).powerset.filter
      fun T => T ∩ TorusArea.planeSteps dx dy dz c.val (by omega) = S).card =
      2 ^ (C.card * (dy * dz)) := by
  rw [card_interiors _ hS, card_layerSteps]
  rw [layerSteps, Finset.disjoint_biUnion_right]
  intro i hi
  exact disjoint_planeSteps _ _ (fun h => hc (by rw [Fin.ext h]; exact hi))

end Torus

end TorusLayers
