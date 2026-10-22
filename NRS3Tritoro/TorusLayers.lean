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
dark. The picture is bubble wrap: the hopping is the plastic that joins the bubbles, each quantum
is a bubble, transparent, and its boundary is the thin film that makes it. Behind a transparent
bubble there is only black, what has not happened; the bubble itself turns black only when it is
filled. Crumple the sheet without popping it and only light is left. A star that does not reach
its collapse mass wraps itself in layers and layers of quanta, stacked on the threads along which
the field moves its excitations. Here are the layers.

* **The face hides the interior.** Take an outer face `X` and the steps `Y` of the layers behind
  it, disjoint from `X`. Every configuration of the face is compatible with exactly `2^|Y|`
  configurations of the whole ball, the same number for every face. What is seen from outside
  says nothing about the layers inside: they stay intact.
* **Pop the whole sheet and the face is popped.** Each face weighs what the layers behind it
  weigh together (`face`). A full ball, uniform over `X ∪ Y`, shows a full face, uniform over
  `X`, so its face is dark; a face that still shines hides a ball that is not full.
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
- `TorusLayers.face_uniform` : a full ball shows a full face.
- `TorusLayers.face_dark_of_full`, `TorusLayers.not_full_of_face_shines` : the face of a full ball
  is dark, and a face that shines hides a ball that is not full.
- `TorusLayers.disjoint_planeSteps` : the walls of `T³` at different positions are disjoint.
- `TorusLayers.card_layerSteps` : the walls of `C` have `|C| · dy · dz` steps.
- `TorusLayers.card_interiors_torus` : a wall of `T³` hides `2^(|C| · dy · dz)` interiors.
- `TorusLayers.face_dark_torus` : on `T³`, a full ball shows a dark wall.
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

variable (X Y) in
/-- What the face `X` shows of a configuration of the whole ball. -/
def restrict (T : Config (X ∪ Y)) : Config X :=
  ⟨T.1 ∩ X, Finset.mem_powerset.2 Finset.inter_subset_right⟩

variable (X Y) in
/-- **The face of the ball**: each face weighs what the layers behind it weigh together. -/
def face (d : ProbDistribution (Config (X ∪ Y))) : ProbDistribution (Config X) :=
  .mk' (fun S => ∑ T, if restrict X Y T = S then (d T : ℝ) else 0)
    (fun _ => Finset.sum_nonneg fun T _ => by split_ifs <;> simp [Prob.zero_le_coe])
    (by
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ProbDistribution.normalized])

/-- **A full ball shows a full face.** Every face hides the same `2^|Y|` interiors, so the
uniform distribution of the ball gives the uniform distribution of the face. -/
theorem face_uniform (hXY : Disjoint X Y) :
    face X Y ProbDistribution.uniform = ProbDistribution.uniform := by
  refine ProbDistribution.ext fun S => Prob.ext ?_
  have h : ∀ T : Config (X ∪ Y), restrict X Y T = S ↔ T.1 ∩ X = S.1 := fun _ => Subtype.ext_iff
  change (∑ T, if restrict X Y T = S then ((ProbDistribution.uniform T : Prob) : ℝ) else 0) = _
  simp only [ProbDistribution.uniform_def, h]
  rw [Finset.sum_coe_sort (X ∪ Y).powerset
      (fun T => if T ∩ X = S.1 then 1 / ((Finset.univ : Finset (Config (X ∪ Y))).card : ℝ)
        else 0),
    ← Finset.sum_filter, Finset.sum_const, card_interiors hXY (Finset.mem_powerset.1 S.2)]
  simp only [Finset.card_univ, Fintype.card_coe, Finset.card_powerset,
    Finset.card_union_of_disjoint hXY, nsmul_eq_mul, pow_add]
  field_simp
  push_cast
  ring

/-- **Pop the whole sheet and the face is popped**: a full ball shows a dark face. -/
theorem face_dark_of_full (hXY : Disjoint X Y) (W : HWhiteBall X)
    {d : ProbDistribution (Config (X ∪ Y))} (h : d = ProbDistribution.uniform) :
    W.lightShare (face X Y d) = 0 := by
  rw [HWhiteBall.lightShare, W.darkShare_eq_one_iff.2 (h ▸ face_uniform hXY), sub_self]

/-- **A face that shines hides a ball that is not full.** -/
theorem not_full_of_face_shines (hXY : Disjoint X Y) (W : HWhiteBall X)
    {d : ProbDistribution (Config (X ∪ Y))} (h : 0 < W.lightShare (face X Y d)) :
    d ≠ ProbDistribution.uniform :=
  fun hd => h.ne' (face_dark_of_full hXY W hd)

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

/-- A wall of `T³` is disjoint from the layers at the other positions. -/
theorem disjoint_layerSteps (c : Fin (dx - 1)) {C : Finset (Fin (dx - 1))} (hc : c ∉ C) :
    Disjoint (TorusArea.planeSteps dx dy dz c.val (by omega)) (layerSteps dx dy dz C) := by
  rw [layerSteps, Finset.disjoint_biUnion_right]
  intro i hi
  exact disjoint_planeSteps _ _ (fun h => hc (by rw [Fin.ext h]; exact hi))

/-- **A wall of `T³` hides `2^(|C| · dy · dz)` interiors behind each of its faces.** -/
theorem card_interiors_torus (c : Fin (dx - 1)) {C : Finset (Fin (dx - 1))} (hc : c ∉ C)
    {S : Finset (Site3D dx dy dz × Site3D dx dy dz)}
    (hS : S ⊆ TorusArea.planeSteps dx dy dz c.val (by omega)) :
    ((TorusArea.planeSteps dx dy dz c.val (by omega) ∪ layerSteps dx dy dz C).powerset.filter
      fun T => T ∩ TorusArea.planeSteps dx dy dz c.val (by omega) = S).card =
      2 ^ (C.card * (dy * dz)) := by
  rw [card_interiors (disjoint_layerSteps c hc) hS, card_layerSteps]

/-- **On `T³`, a full ball shows a dark wall.** -/
theorem face_dark_torus (c : Fin (dx - 1)) {C : Finset (Fin (dx - 1))} (hc : c ∉ C)
    (W : HWhiteBall (TorusArea.planeSteps dx dy dz c.val (by omega))) :
    W.lightShare (face _ (layerSteps dx dy dz C) ProbDistribution.uniform) = 0 :=
  face_dark_of_full (disjoint_layerSteps c hc) W rfl

end Torus

end TorusLayers
