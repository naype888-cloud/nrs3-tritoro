/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D37f_LightCone

/-!
# The area law of the three-torus

Close each axis of the cube `dx × dy × dz` with the link `{0, d − 1}` (`D16e`): the transport of
an axis is `(A_d + S)/2`, every step of the ring, the open links and the seam, with the same
weight `1/2`. The total transport `T3c` moves one step along one axis, so a step is local as on
the cube.

A plane `x = c | c + 1` does not separate the torus: the ring comes back through the seam. The
region `{x ≤ c}` is bounded by two cuts, the plane and the seam, and each carries `dy · dz`
crossing steps. The boundary has `2 · dy · dz` steps, open or closed, so the entropy of the cut
is `S = 2 · dy · dz · log 2`: twice the open cube, still an area, independent of the depth `dx`
and of where the plane sits. The Bekenstein–Hawking law holds exactly when each step has area
`a² = 4 ℓ_P² log 2`, the same bit of area as on the open cube.

## Main results

- `TorusArea.card_planeSteps`, `TorusArea.card_seamSteps` : each of the two cuts has `dy · dz`
  steps.
- `TorusArea.card_crossSteps` : the boundary has `2 · dy · dz` steps.
- `TorusArea.cutEntropy_eq` : `S = 2 · dy · dz · log 2`.
- `TorusArea.cutEntropy_eq_of_depth` : it does not depend on the depth nor on the plane.
- `TorusArea.bekensteinHawking_iff` : with area `a²` per step, `S = a² A / (4 ℓ_P²)` iff
  `a² = 4 ℓ_P² log 2`.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone
open PathGraph3D (Site3D)

namespace TorusArea

variable {dx dy dz : ℕ}

/-! ## 1. The closed transport -/

/-- The seam of the ring of `d` positions: the link between the first and the last. -/
def Seam (d : ℕ) (i j : Fin d) : Prop :=
  (i.val = 0 ∧ j.val + 1 = d) ∨ (j.val = 0 ∧ i.val + 1 = d)

instance (d : ℕ) (i j : Fin d) : Decidable (Seam d i j) := by unfold Seam; infer_instance

/-- The closed transport `(A_d + S)/2` of the ring, with `A_d = ρ_d T_d`. -/
def ring (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (rho d / 2 : ℝ) * Td d i j + if Seam d i j then 1 / 2 else 0

/-- Total transport of the three-torus: one step along one axis, every axis closed. -/
def T3c (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (ring dx) + liftAlong (eY dx dy dz) (ring dy) +
    liftAlong (eZ dx dy dz) (ring dz)

/-- For three positions or more the seam is not a minimal step. -/
lemma not_seam_of_minStep {d : ℕ} (hd : 3 ≤ d) {i j : Fin d} (h : MinStep i j) :
    ¬ Seam d i j := by
  unfold MinStep at h
  unfold Seam
  omega

lemma ring_ne_zero_iff {d : ℕ} (hd : 3 ≤ d) {i j : Fin d} :
    ring d i j ≠ 0 ↔ MinStep i j ∨ Seam d i j := by
  have hr : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos d (by omega)).ne'
  by_cases hm : MinStep i j
  · have := not_seam_of_minStep hd hm
    simp [ring, Td, Ad, hm, this, hr]
  · by_cases hs : Seam d i j <;> simp [ring, Td, Ad, hm, hs]

/-- Off the `x` axis the torus transport is the ring transport on equal `y, z`. -/
lemma T3c_apply_of_ne {p q : Site3D dx dy dz} (h : p.1 ≠ q.1) :
    T3c dx dy dz p q = ring dx p.1 q.1 * if p.2 = q.2 then 1 else 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only at h
  simp [T3c, liftAlong, eX, eY, eZ, h]

/-- **A step crosses the region `{x ≤ c}` iff it is the plane step or the seam step.** -/
theorem T3c_ne_zero_iff (hd : 3 ≤ dx) {c : ℕ} {p q : Site3D dx dy dz} (hp : p.1.val ≤ c)
    (hq : c < q.1.val) :
    T3c dx dy dz p q ≠ 0 ↔
      ((p.1.val = c ∧ q.1.val = c + 1) ∨ (p.1.val = 0 ∧ q.1.val + 1 = dx)) ∧ p.2 = q.2 := by
  have hne : p.1 ≠ q.1 := fun h => by rw [h] at hp; omega
  rw [T3c_apply_of_ne hne]
  by_cases h2 : p.2 = q.2
  · simp only [h2, ite_true, mul_one, ring_ne_zero_iff hd, and_true]
    unfold MinStep Seam
    omega
  · simp [h2]

/-! ## 2. The two cuts of the region `{x ≤ c}` -/

open Classical in
/-- The steps of the torus transport that leave the region `{x ≤ c}`. -/
def crossSteps (dx dy dz c : ℕ) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.filter fun pq => pq.1.1.val ≤ c ∧ c < pq.2.1.val ∧ T3c dx dy dz pq.1 pq.2 ≠ 0

/-- The steps across the plane `x = c | c + 1`. -/
def planeSteps (dx dy dz c : ℕ) (hc : c + 1 < dx) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.image fun yz : Fin dy × Fin dz => ((⟨c, by omega⟩, yz), (⟨c + 1, hc⟩, yz))

/-- The steps across the seam, from the last position back to the first. -/
def seamSteps (dx dy dz : ℕ) (hd : 3 ≤ dx) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.image fun yz : Fin dy × Fin dz =>
    ((⟨0, by omega⟩, yz), (⟨dx - 1, by omega⟩, yz))

theorem card_planeSteps {c : ℕ} (hc : c + 1 < dx) : (planeSteps dx dy dz c hc).card = dy * dz := by
  rw [planeSteps, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  intro a b h
  simpa using congrArg (fun pq => pq.1.2) h

theorem card_seamSteps (hd : 3 ≤ dx) : (seamSteps dx dy dz hd).card = dy * dz := by
  rw [seamSteps, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  intro a b h
  simpa using congrArg (fun pq => pq.1.2) h

/-- **The boundary of `{x ≤ c}` is the plane and the seam.** -/
theorem crossSteps_eq {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    crossSteps dx dy dz c = planeSteps dx dy dz c hc ∪ seamSteps dx dy dz hd := by
  ext ⟨p, q⟩
  simp only [crossSteps, planeSteps, seamSteps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hp, hq, h⟩
    obtain ⟨h1, h2⟩ := (T3c_ne_zero_iff hd hp hq).mp h
    rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · exact Or.inl ⟨p.2, by ext <;> simp [h1, h1', h2]⟩
    · exact Or.inr ⟨p.2, by ext <;> simp [h1, h2]; omega⟩
  · rintro (⟨yz, h⟩ | ⟨yz, h⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨le_rfl, by simp, (T3c_ne_zero_iff (c := c) hd le_rfl (by simp)).mpr (by simp)⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      have h0 : (0 : ℕ) ≤ c := Nat.zero_le c
      have hq : c < dx - 1 := by omega
      exact ⟨h0, hq, (T3c_ne_zero_iff (c := c) hd h0 hq).mpr
        ⟨Or.inr ⟨rfl, by simp; omega⟩, rfl⟩⟩

theorem disjoint_planeSteps_seamSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    Disjoint (planeSteps dx dy dz c hc) (seamSteps dx dy dz hd) := by
  rw [Finset.disjoint_left]
  intro pq h1 h2
  obtain ⟨yz, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨yz', -, h⟩ := Finset.mem_image.mp h2
  have := congrArg (fun pq => pq.1.1.val) h
  simp only at this
  have h' := congrArg (fun pq => pq.2.1.val) h
  simp only at h'
  omega

/-- **The boundary of `{x ≤ c}` has `2 · dy · dz` steps**: the plane and the seam, `dy · dz`
each. -/
theorem card_crossSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (crossSteps dx dy dz c).card = 2 * (dy * dz) := by
  rw [crossSteps_eq hc hd, Finset.card_union_of_disjoint (disjoint_planeSteps_seamSteps hc hd),
    card_planeSteps, card_seamSteps]
  ring

/-! ## 3. The entropy of the cut is an area -/

/-- Each boundary step is open or closed: the entropy of the cut is the log of the number of
sets of open steps. -/
def cutEntropy (dx dy dz c : ℕ) : ℝ := Real.log (crossSteps dx dy dz c).powerset.card

/-- **The area law of the torus: `S = 2 · dy · dz · log 2`.** -/
theorem cutEntropy_eq {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    cutEntropy dx dy dz c = (2 * (dy * dz) : ℕ) * Real.log 2 := by
  rw [cutEntropy, Finset.card_powerset, card_crossSteps hc hd, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]

/-- **The entropy does not see the depth.** Any depth, any plane: the same entropy. -/
theorem cutEntropy_eq_of_depth {dx' c c' : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx)
    (hc' : c' + 1 < dx') (hd' : 3 ≤ dx') :
    cutEntropy dx dy dz c = cutEntropy dx' dy dz c' := by
  rw [cutEntropy_eq hc hd, cutEntropy_eq hc' hd']

/-- **Bekenstein–Hawking fixes the area of a step.** With area `a²` per boundary step, the
law `S = A / (4 ℓ_P²)` holds iff `a² = 4 ℓ_P² log 2`: the same bit of area as on the open cube. -/
theorem bekensteinHawking_iff {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (hy : 0 < dy) (hz : 0 < dz) {c : ℕ}
    (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    cutEntropy dx dy dz c = a ^ 2 * (2 * (dy * dz) : ℕ) / (4 * ℓ ^ 2) ↔
      a ^ 2 = 4 * ℓ ^ 2 * Real.log 2 := by
  have hA : ((2 * (dy * dz) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [cutEntropy_eq hc hd, eq_div_iff (by positivity)]
  constructor
  · intro h
    apply mul_right_cancel₀ hA
    linarith
  · intro h
    rw [h]
    ring

end TorusArea
