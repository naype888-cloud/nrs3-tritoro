/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.Gyroscope
public import NRS3Tritoro.ClausiusInput

/-!
# The bits of the fibred box: one wall across an open axis, two across the fiber

The box of `nrs3-hopf` has `x`, `y`, `z` open and the fiber `w` closed with three positions; its
transport is `H = T_x + T_y + T_z + T°` (`Gyroscope.boxTransport`). Cut it in two ways.

* **Across the open axis `x`**, the region `{x ≤ c}`: a step leaves it only across the plane, so
  the boundary is one wall of `dy · dz · 3` steps, as on the open cube.
* **Across the fiber**, the region `{w ≤ c}` (`c = 0, 1`): the fiber is a ring, every two of its
  three positions are joined, and the region is left through two links, so the boundary has
  `2 · dx · dy · dz` steps, two walls, as on `T³`.

With the boundary in hand, `BoundaryBits` gives the Bekenstein bound, saturation only for the
uniform distribution and the foam, and `ClausiusInput` gives the same entropy per unit area
`η = log 2 / a²` as on the open cube and on `T³`.

## Main results

- `FiberBoundary.xSteps_eq`, `FiberBoundary.card_xSteps` : the cut across `x` is one wall,
  `dy · dz · 3` steps.
- `FiberBoundary.wSteps_eq`, `FiberBoundary.card_wSteps` : the cut across the fiber is two walls,
  `2 · dx · dy · dz` steps.
- `FiberBoundary.entropy_le_x`, `FiberBoundary.entropy_le_w` : the Bekenstein bounds.
- `FiberBoundary.saturated_iff_uniform_w`, `FiberBoundary.openProb_uniform_w`,
  `FiberBoundary.bitVariance_uniform_w` : full means perfectly mixed, and the foam.
- `FiberBoundary.eta_x`, `FiberBoundary.eta_w` : `η = 1 / (4 ℓ_P²)` on both cuts.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS FourAxes BoxTwoRelations Gyroscope

namespace FiberBoundary

variable {dx dy dz : ℕ}

/-! ## 1. The transport off one axis -/

lemma boxTransport_apply_of_ne_x {p q : Site4D dx dy dz 3} (h : p.1 ≠ q.1) :
    boxTransport dx dy dz p q = Td dx p.1 q.1 * if p.2 = q.2 then 1 else 0 := by
  obtain ⟨i, j, k, l⟩ := p
  obtain ⟨i', j', k', l'⟩ := q
  simp only at h
  simp [boxTransport, lam, liftAlong, FourAxes.eX, FourAxes.eY, FourAxes.eZ, FourAxes.eW, h]

lemma boxTransport_apply_of_ne_w {p q : Site4D dx dy dz 3} (h : p.2.2.2 ≠ q.2.2.2) :
    boxTransport dx dy dz p q =
      ClosedThree.Tc p.2.2.2 q.2.2.2 *
        if (p.1, p.2.1, p.2.2.1) = (q.1, q.2.1, q.2.2.1) then 1 else 0 := by
  obtain ⟨i, j, k, l⟩ := p
  obtain ⟨i', j', k', l'⟩ := q
  simp only at h
  simp [boxTransport, lam, liftAlong, FourAxes.eX, FourAxes.eY, FourAxes.eZ, FourAxes.eW, h]

/-! ## 2. The two cuts -/

open Classical in
/-- The steps of the box that leave the region `{x ≤ c}`. -/
def xSteps (dx dy dz c : ℕ) : Finset (Site4D dx dy dz 3 × Site4D dx dy dz 3) :=
  Finset.univ.filter fun pq =>
    pq.1.1.val ≤ c ∧ c < pq.2.1.val ∧ boxTransport dx dy dz pq.1 pq.2 ≠ 0

open Classical in
/-- The steps of the box that leave the region `{w ≤ c}` of the fiber. -/
def wSteps (dx dy dz c : ℕ) : Finset (Site4D dx dy dz 3 × Site4D dx dy dz 3) :=
  Finset.univ.filter fun pq =>
    pq.1.2.2.2.val ≤ c ∧ c < pq.2.2.2.2.val ∧ boxTransport dx dy dz pq.1 pq.2 ≠ 0

/-- **The cut across `x` is the plane.** -/
theorem xSteps_eq {c : ℕ} (hc : c + 1 < dx) :
    xSteps dx dy dz c = Finset.univ.image fun r : Fin dy × Fin dz × Fin 3 =>
      (((⟨c, by omega⟩ : Fin dx), r), ((⟨c + 1, hc⟩ : Fin dx), r)) := by
  have hr : (rho dx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos dx (by omega)).ne'
  ext ⟨p, q⟩
  simp only [xSteps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hp, hq, h⟩
    have hne : p.1 ≠ q.1 := fun h' => by rw [h'] at hp; omega
    rw [boxTransport_apply_of_ne_x hne] at h
    by_cases h2 : p.2 = q.2
    · simp only [h2, ite_true, mul_one, Td, Ad] at h
      split_ifs at h with hm
      · unfold MinStep at hm
        refine ⟨p.2, ?_⟩
        ext <;> simp [h2] <;> omega
      · simp at h
    · simp [h2] at h
  · rintro ⟨r, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨le_rfl, by simp, ?_⟩
    rw [boxTransport_apply_of_ne_x (by simp [Fin.ext_iff])]
    simp [Td, Ad, MinStep, hr]

theorem card_xSteps {c : ℕ} (hc : c + 1 < dx) : (xSteps dx dy dz c).card = dy * dz * 3 := by
  rw [xSteps_eq hc, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, mul_assoc]
  intro a b h
  simpa using congrArg (fun pq => pq.1.2) h

/-- The pairs of positions of the fiber that leave `{w ≤ c}`. -/
def fiberPairs (c : ℕ) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter fun ab => ab.1.val ≤ c ∧ c < ab.2.val

theorem card_fiberPairs {c : ℕ} (hc : c + 1 < 3) : (fiberPairs c).card = 2 := by
  have : c < 2 := by omega
  interval_cases c <;> decide

/-- **The cut across the fiber has two walls**: every step from `{w ≤ c}` to its complement,
on equal `x`, `y`, `z`. -/
theorem wSteps_eq (c : ℕ) :
    wSteps dx dy dz c =
      (Finset.univ ×ˢ fiberPairs c).image fun ra : (Fin dx × Fin dy × Fin dz) × (Fin 3 × Fin 3) =>
        ((ra.1.1, ra.1.2.1, ra.1.2.2, ra.2.1), (ra.1.1, ra.1.2.1, ra.1.2.2, ra.2.2)) := by
  ext ⟨⟨i, j, k, l⟩, ⟨i', j', k', l'⟩⟩
  simp only [wSteps, fiberPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, h⟩
    have hne : l ≠ l' := fun h' => by rw [h'] at hp; omega
    rw [boxTransport_apply_of_ne_w hne] at h
    by_cases h2 : (i, j, k) = (i', j', k')
    · obtain ⟨rfl, rfl, rfl⟩ : i = i' ∧ j = j' ∧ k = k' := by simpa using h2
      exact ⟨i, j, k, l, l', ⟨hp, hq⟩, by simp⟩
    · simp [h2] at h
  · rintro ⟨a, b, e, u, v, ⟨hu, hv⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
    refine ⟨hu, hv, ?_⟩
    have hne : u ≠ v := fun h' => by rw [h'] at hu; omega
    rw [boxTransport_apply_of_ne_w hne]
    simp [ClosedThree.Tc, hne]

theorem card_wSteps {c : ℕ} (hc : c + 1 < 3) : (wSteps dx dy dz c).card = 2 * (dx * dy * dz) := by
  rw [wSteps_eq, Finset.card_image_of_injective, Finset.card_product, card_fiberPairs hc,
    Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin]
  · ring
  · rintro ⟨⟨a, b, e⟩, u, v⟩ ⟨⟨a', b', e'⟩, u', v'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl, rfl⟩, -, -, -, rfl⟩ := h
    rfl

/-! ## 3. Bekenstein, saturation and the foam -/

variable {c : ℕ}

/-- The Bekenstein bound across `x`: `H ≤ dy · dz · 3 · log 2`. -/
theorem entropy_le_x (hc : c + 1 < dx)
    (d : ProbDistribution (BoundaryBits.Config (xSteps dx dy dz c))) :
    Hₛ d ≤ ((dy * dz * 3 : ℕ) : ℝ) * Real.log 2 := by
  have h := BoundaryBits.entropy_le d
  rwa [card_xSteps hc] at h

/-- The Bekenstein bound across the fiber: `H ≤ 2 · dx · dy · dz · log 2`. -/
theorem entropy_le_w (hc : c + 1 < 3)
    (d : ProbDistribution (BoundaryBits.Config (wSteps dx dy dz c))) :
    Hₛ d ≤ ((2 * (dx * dy * dz) : ℕ) : ℝ) * Real.log 2 := by
  have h := BoundaryBits.entropy_le d
  rwa [card_wSteps hc] at h

/-- Full means perfectly mixed, across the fiber. -/
theorem saturated_iff_uniform_w (hc : c + 1 < 3)
    {d : ProbDistribution (BoundaryBits.Config (wSteps dx dy dz c))} :
    Hₛ d = ((2 * (dx * dy * dz) : ℕ) : ℝ) * Real.log 2 ↔ d = ProbDistribution.uniform := by
  rw [← card_wSteps hc]
  exact BoundaryBits.saturated_iff_uniform

/-- The foam across the fiber: every boundary step is open half of the time. -/
theorem openProb_uniform_w {s : Site4D dx dy dz 3 × Site4D dx dy dz 3}
    (hs : s ∈ wSteps dx dy dz c) :
    BoundaryBits.openProb
      (ProbDistribution.uniform (α := BoundaryBits.Config (wSteps dx dy dz c))) s = 1 / 2 :=
  BoundaryBits.openProb_uniform hs

/-- The foam across the fiber: every boundary step fluctuates the most a bit can. -/
theorem bitVariance_uniform_w {s : Site4D dx dy dz 3 × Site4D dx dy dz 3}
    (hs : s ∈ wSteps dx dy dz c) :
    BoundaryBits.openProb
        (ProbDistribution.uniform (α := BoundaryBits.Config (wSteps dx dy dz c))) s *
      (1 - BoundaryBits.openProb
        (ProbDistribution.uniform (α := BoundaryBits.Config (wSteps dx dy dz c))) s) = 1 / 4 :=
  BoundaryBits.bitVariance_uniform hs

/-! ## 4. The entropy per unit area -/

variable {a ℓ : ℝ}

/-- Across `x`, `η = 1 / (4 ℓ_P²)`. -/
theorem eta_x (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    ClausiusInput.entropyPerArea (xSteps dx dy dz c) a = 1 / (4 * ℓ ^ 2) := by
  refine ClausiusInput.entropyPerArea_eta ?_ hℓ ha
  rw [← Finset.card_pos, card_xSteps hc]
  positivity

/-- Across the fiber, `η = 1 / (4 ℓ_P²)`: the same as on `R³` and `T³`. -/
theorem eta_w (hx : 0 < dx) (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < 3) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    ClausiusInput.entropyPerArea (wSteps dx dy dz c) a = 1 / (4 * ℓ ^ 2) := by
  refine ClausiusInput.entropyPerArea_eta ?_ hℓ ha
  rw [← Finset.card_pos, card_wSteps hc]
  positivity

end FiberBoundary
