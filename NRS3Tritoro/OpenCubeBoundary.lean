/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.BoundaryBits
public import NRS3Tritoro.TorusArea

/-!
# The open cube: one wall of bits, the same foam

On the open cube `dx × dy × dz` the transport `T3` has no seam: the axes end. A step leaves the
region `{x ≤ c}` only across the plane `x = c | c + 1`, so the boundary is one wall of `dy · dz`
steps, the plane steps of the torus (`TorusArea.planeSteps`). The torus adds the seam: its
boundary is the open one and the seam, twice the bits.

The open cube's area law is `NRS3DefectCurvature.AreaLaw`; it is restated here on the same
`planeSteps` because the two repositories pin different versions of `NavaRobertsonIndependent`.
With the boundary in hand, `BoundaryBits` gives the rest at once: the Bekenstein bound
`H ≤ dy · dz · log 2`, saturation only for the uniform distribution, and the foam of the full
state, every step open half of the time and fluctuating `1/4`.

## Main results

- `OpenCubeBoundary.T3_ne_zero_iff` : a step of the open cube leaves `{x ≤ c}` only across the
  plane.
- `OpenCubeBoundary.openCrossSteps_eq` : the boundary is the plane, `card_openCrossSteps` :
  `dy · dz` steps.
- `OpenCubeBoundary.crossSteps_eq_union` : the torus boundary is the open one and the seam.
- `OpenCubeBoundary.entropy_le`, `OpenCubeBoundary.bekenstein_bound` : `H ≤ dy · dz · log 2`,
  `H ≤ A / (4 ℓ_P²)`.
- `OpenCubeBoundary.saturated_iff_uniform` : full means perfectly mixed.
- `OpenCubeBoundary.openProb_uniform`, `OpenCubeBoundary.bitVariance_uniform` : the foam, no
  gradient and the most fluctuation.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone TorusArea
open PathGraph3D (Site3D)

namespace OpenCubeBoundary

variable {dx dy dz : ℕ}

/-- Off the `x` axis the open transport is the path transport on equal `y, z`. -/
lemma T3_apply_of_ne {p q : Site3D dx dy dz} (h : p.1 ≠ q.1) :
    T3 dx dy dz p q = Td dx p.1 q.1 * if p.2 = q.2 then 1 else 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  simp only at h
  simp [T3, liftAlong, eX, eY, eZ, h]

lemma Td_ne_zero_iff {d : ℕ} (hd : 2 ≤ d) {i j : Fin d} : Td d i j ≠ 0 ↔ MinStep i j := by
  have hr : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos d hd).ne'
  by_cases hm : MinStep i j <;> simp [Td, Ad, hm, hr]

/-- **A step of the open cube leaves `{x ≤ c}` only across the plane.** -/
theorem T3_ne_zero_iff (hd : 2 ≤ dx) {c : ℕ} {p q : Site3D dx dy dz} (hp : p.1.val ≤ c)
    (hq : c < q.1.val) :
    T3 dx dy dz p q ≠ 0 ↔ (p.1.val = c ∧ q.1.val = c + 1) ∧ p.2 = q.2 := by
  have hne : p.1 ≠ q.1 := fun h => by rw [h] at hp; omega
  rw [T3_apply_of_ne hne]
  by_cases h2 : p.2 = q.2
  · simp only [h2, ite_true, mul_one, Td_ne_zero_iff hd, and_true]
    unfold MinStep
    omega
  · simp [h2]

open Classical in
/-- The steps of the open transport that leave the region `{x ≤ c}`. -/
def openCrossSteps (dx dy dz c : ℕ) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.filter fun pq => pq.1.1.val ≤ c ∧ c < pq.2.1.val ∧ T3 dx dy dz pq.1 pq.2 ≠ 0

/-- **The boundary of the open region is the plane.** -/
theorem openCrossSteps_eq {c : ℕ} (hc : c + 1 < dx) :
    openCrossSteps dx dy dz c = planeSteps dx dy dz c hc := by
  ext ⟨p, q⟩
  simp only [openCrossSteps, planeSteps, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨hp, hq, h⟩
    obtain ⟨⟨h1, h1'⟩, h2⟩ := (T3_ne_zero_iff (by omega) hp hq).mp h
    exact ⟨p.2, by ext <;> simp [h1, h1', h2]⟩
  · rintro ⟨yz, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨le_rfl, by simp, (T3_ne_zero_iff (c := c) (by omega) le_rfl (by simp)).mpr (by simp)⟩

/-- The open boundary has `dy · dz` steps: one wall. -/
theorem card_openCrossSteps {c : ℕ} (hc : c + 1 < dx) :
    (openCrossSteps dx dy dz c).card = dy * dz := by
  rw [openCrossSteps_eq hc, card_planeSteps]

/-- **The torus boundary is the open boundary and the seam.** -/
theorem crossSteps_eq_union {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    crossSteps dx dy dz c = openCrossSteps dx dy dz c ∪ seamSteps dx dy dz hd := by
  rw [crossSteps_eq hc hd, openCrossSteps_eq hc]

/-- A configuration of the open boundary. -/
abbrev Config (dx dy dz c : ℕ) := BoundaryBits.Config (openCrossSteps dx dy dz c)

variable {c : ℕ}

/-- **The Bekenstein bound on the open cube**: `H ≤ dy · dz · log 2`. -/
theorem entropy_le (hc : c + 1 < dx) (d : ProbDistribution (Config dx dy dz c)) :
    Hₛ d ≤ ((dy * dz : ℕ) : ℝ) * Real.log 2 := by
  have h := BoundaryBits.entropy_le d
  rwa [card_openCrossSteps hc] at h

/-- With the bit of area `a² = 4 ℓ_P² log 2` per step, `H ≤ A / (4 ℓ_P²)`. -/
theorem bekenstein_bound {a ℓ : ℝ} (hℓ : ℓ ≠ 0) (hc : c + 1 < dx)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) (d : ProbDistribution (Config dx dy dz c)) :
    Hₛ d ≤ a ^ 2 * (dy * dz : ℕ) / (4 * ℓ ^ 2) := by
  refine (entropy_le hc d).trans_eq ?_
  rw [ha]
  field_simp

/-- **Full means perfectly mixed**, on the open cube too. -/
theorem saturated_iff_uniform (hc : c + 1 < dx) {d : ProbDistribution (Config dx dy dz c)} :
    Hₛ d = ((dy * dz : ℕ) : ℝ) * Real.log 2 ↔ d = ProbDistribution.uniform := by
  rw [← card_openCrossSteps hc]
  exact BoundaryBits.saturated_iff_uniform

/-- **The foam of the open cube: no gradient.** -/
theorem openProb_uniform {s : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ openCrossSteps dx dy dz c) :
    BoundaryBits.openProb (ProbDistribution.uniform (α := Config dx dy dz c)) s = 1 / 2 :=
  BoundaryBits.openProb_uniform hs

/-- **The foam of the open cube: every step fluctuates the most a bit can.** -/
theorem bitVariance_uniform {s : Site3D dx dy dz × Site3D dx dy dz}
    (hs : s ∈ openCrossSteps dx dy dz c) :
    BoundaryBits.openProb (ProbDistribution.uniform (α := Config dx dy dz c)) s *
      (1 - BoundaryBits.openProb (ProbDistribution.uniform (α := Config dx dy dz c)) s) =
        1 / 4 :=
  BoundaryBits.bitVariance_uniform hs

end OpenCubeBoundary
