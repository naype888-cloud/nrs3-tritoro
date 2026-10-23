/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.SiteEvents
public import NRS3Hopf.Gyroscope

/-!
# Site events on the three topologies: `R³`, `T³` and the fibred box

`SiteEvents` proves continuity, conservation and Robertson for the site events of any lattice;
the topology only decides which sites are linked. Here are the three lattices of the program.

* **`R³`, the open cube** `Fin dx × Fin dy × Fin dz` with `T = T_x + T_y + T_z`, each `T_d` the
  open chain lifted to its axis. A link only joins sites that differ along one axis
  (`openCube_linkFlow_eq_zero`); the rate of a site is the sum of its link flows.
* **`T³`** `ZMod a × ZMod b × ZMod c` with `T = T_x + T_y + T_z`, each a hop around a closed axis.
  Every site has the same six links, two per axis:
  `rate_p = Σ_axes (F_axis(p − e_axis) − F_axis(p))`.
* **The fibred box** `Fin dx × Fin dy × Fin dz × Fin 3` with `T = T_x + T_y + T_z + T°`
  (`Gyroscope.boxTransport`): three open axes and the closed fiber of three.

On each of them the rates of all sites add up to `0` and every site obeys
`rate_p² ≤ 4 Var T · p_p (1 − p_p)`.

## Main results

- `SiteEventsTopologies.liftAlong_isHermitian` : a lifted Hermitian matrix is Hermitian.
- `SiteEventsTopologies.rate_openCube`, `SiteEventsTopologies.openCube_linkFlow_eq_zero`,
  `SiteEventsTopologies.sum_rate_openCube`, `SiteEventsTopologies.rate_openCube_sq_le` : `R³`.
- `SiteEventsTopologies.rate_torus`, `SiteEventsTopologies.sum_rate_torus`,
  `SiteEventsTopologies.rate_torus_sq_le` : `T³`.
- `SiteEventsTopologies.rate_box`, `SiteEventsTopologies.sum_rate_box`,
  `SiteEventsTopologies.rate_box_sq_le` : the fibred box.
-/

@[expose] public noncomputable section

open Complex Matrix QuantumEvents SiteEvents TransportPosition PathGraph3DNRS

namespace SiteEventsTopologies

/-! ## 1. Lifted matrices -/

section Lift

variable {ι α β : Type*} [DecidableEq β]

/-- A Hermitian matrix lifted to an axis is Hermitian. -/
theorem liftAlong_isHermitian (e : ι ≃ α × β) {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (liftAlong e A).IsHermitian := by
  ext p q
  simp only [conjTranspose_apply, liftAlong, of_apply, star_mul', ← hA.apply (e p).1 (e q).1]
  by_cases h : (e p).2 = (e q).2
  · simp [h]
  · simp [h, Ne.symm h]

/-- A lifted matrix only links sites that agree off its axis. -/
theorem liftAlong_apply_of_ne (e : ι ≃ α × β) (A : Matrix α α ℂ) {p q : ι}
    (h : (e p).2 ≠ (e q).2) : liftAlong e A p q = 0 := by
  simp [liftAlong, h]

end Lift

/-! ## 2. `R³`: the open cube -/

section OpenCube

variable (dx dy dz : ℕ)

/-- The transport of the open cube, `T_x + T_y + T_z`. -/
def openTransport : Matrix (PathGraph3D.Site3D dx dy dz) (PathGraph3D.Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (Td dx) + liftAlong (eY dx dy dz) (Td dy) +
    liftAlong (eZ dx dy dz) (Td dz)

theorem openTransport_isHermitian : (openTransport dx dy dz).IsHermitian :=
  ((liftAlong_isHermitian _ (Td_isHermitian dx)).add
    (liftAlong_isHermitian _ (Td_isHermitian dy))).add (liftAlong_isHermitian _ (Td_isHermitian dz))

variable {dx dy dz}

/-- **The rate of a site of the open cube is the sum of its link flows.** -/
theorem rate_openCube (p : PathGraph3D.Site3D dx dy dz) (ψ : H3D dx dy dz) :
    rate (toEuclideanLin (openTransport dx dy dz)) (siteEvent p) ψ =
      ∑ q, linkFlow (openTransport dx dy dz) ψ p q :=
  rate_matrix (openTransport_isHermitian dx dy dz) p ψ

/-- **Links of the open cube run along one axis**: two sites that differ along two axes are not
linked. -/
theorem openCube_linkFlow_eq_zero (ψ : H3D dx dy dz) {p q : PathGraph3D.Site3D dx dy dz}
    (hx : (eX dx dy dz p).2 ≠ (eX dx dy dz q).2) (hy : (eY dx dy dz p).2 ≠ (eY dx dy dz q).2)
    (hz : (eZ dx dy dz p).2 ≠ (eZ dx dy dz q).2) : linkFlow (openTransport dx dy dz) ψ p q = 0 :=
  linkFlow_eq_zero ψ (by
    simp only [openTransport, Matrix.add_apply, liftAlong_apply_of_ne _ _ hx,
      liftAlong_apply_of_ne _ _ hy, liftAlong_apply_of_ne _ _ hz, add_zero])

theorem sum_rate_openCube (ψ : H3D dx dy dz) :
    ∑ p, rate (toEuclideanLin (openTransport dx dy dz)) (siteEvent p) ψ = 0 :=
  sum_rate_site (isSymmetric_toEuclideanLin_iff.mpr (openTransport_isHermitian dx dy dz)) ψ

theorem rate_openCube_sq_le (p : PathGraph3D.Site3D dx dy dz) {ψ : H3D dx dy dz}
    (hψ : ‖ψ‖ = 1) :
    rate (toEuclideanLin (openTransport dx dy dz)) (siteEvent p) ψ ^ 2 ≤
      4 * variance (toEuclideanLin (openTransport dx dy dz)) ψ * (‖ψ p‖ ^ 2 * (1 - ‖ψ p‖ ^ 2)) :=
  rate_site_sq_le (isSymmetric_toEuclideanLin_iff.mpr (openTransport_isHermitian dx dy dz)) p hψ

end OpenCube

/-! ## 3. `T³` -/

section Torus

variable {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]

/-- The sites of `T³`. -/
abbrev TSite (a b c : ℕ) := ZMod a × ZMod b × ZMod c

/-- One step along `x`, `y`, `z` of `T³`. -/
def σx : TSite a b c ≃ TSite a b c where
  toFun p := (p.1 + 1, p.2)
  invFun p := (p.1 - 1, p.2)
  left_inv p := by simp
  right_inv p := by simp

def σy : TSite a b c ≃ TSite a b c where
  toFun p := (p.1, p.2.1 + 1, p.2.2)
  invFun p := (p.1, p.2.1 - 1, p.2.2)
  left_inv p := by simp
  right_inv p := by simp

def σz : TSite a b c ≃ TSite a b c where
  toFun p := (p.1, p.2.1, p.2.2 + 1)
  invFun p := (p.1, p.2.1, p.2.2 - 1)
  left_inv p := by simp
  right_inv p := by simp

/-- The transport of `T³`, a hop around each closed axis. -/
def torusTransport : EuclideanSpace ℂ (TSite a b c) →ₗ[ℂ] EuclideanSpace ℂ (TSite a b c) :=
  SiteHop.hop σx 1 + SiteHop.hop σy 1 + SiteHop.hop σz 1

theorem torusTransport_isSymmetric :
    (torusTransport : EuclideanSpace ℂ (TSite a b c) →ₗ[ℂ] _).IsSymmetric :=
  ((SiteHop.hop_isSymmetric _ fun _ => rfl).add (SiteHop.hop_isSymmetric _ fun _ => rfl)).add
    (SiteHop.hop_isSymmetric _ fun _ => rfl)

/-- **Every site of `T³` has six links**: `rate_p = Σ_axes (F(p − e) − F(p))`. -/
theorem rate_torus (p : TSite a b c) (ψ : EuclideanSpace ℂ (TSite a b c)) :
    rate torusTransport (siteEvent p) ψ =
      (hopFlow σx ψ (σx.symm p) - hopFlow σx ψ p) + (hopFlow σy ψ (σy.symm p) - hopFlow σy ψ p) +
        (hopFlow σz ψ (σz.symm p) - hopFlow σz ψ p) := by
  rw [torusTransport, rate_add, rate_add, rate_hop, rate_hop, rate_hop]

theorem sum_rate_torus (ψ : EuclideanSpace ℂ (TSite a b c)) :
    ∑ p, rate torusTransport (siteEvent p) ψ = 0 :=
  sum_rate_site torusTransport_isSymmetric ψ

theorem rate_torus_sq_le (p : TSite a b c) {ψ : EuclideanSpace ℂ (TSite a b c)} (hψ : ‖ψ‖ = 1) :
    rate torusTransport (siteEvent p) ψ ^ 2 ≤
      4 * variance torusTransport ψ * (‖ψ p‖ ^ 2 * (1 - ‖ψ p‖ ^ 2)) :=
  rate_site_sq_le torusTransport_isSymmetric p hψ

end Torus

/-! ## 4. The fibred box -/

section Box

variable (dx dy dz : ℕ)

theorem boxTransport_isHermitian : (Gyroscope.boxTransport dx dy dz).IsHermitian := by
  rw [Gyroscope.boxTransport]
  exact (((liftAlong_isHermitian _ (Td_isHermitian dx)).add
    (liftAlong_isHermitian _ (Td_isHermitian dy))).add
    (liftAlong_isHermitian _ (Td_isHermitian dz))).add
    (liftAlong_isHermitian _ ClosedThree.Tc_isHermitian)

variable {dx dy dz}

/-- **The rate of a site of the fibred box is the sum of its link flows.** -/
theorem rate_box (p : FourAxes.Site4D dx dy dz 3)
    (ψ : EuclideanSpace ℂ (FourAxes.Site4D dx dy dz 3)) :
    rate (toEuclideanLin (Gyroscope.boxTransport dx dy dz)) (siteEvent p) ψ =
      ∑ q, linkFlow (Gyroscope.boxTransport dx dy dz) ψ p q :=
  rate_matrix (boxTransport_isHermitian dx dy dz) p ψ

theorem sum_rate_box (ψ : EuclideanSpace ℂ (FourAxes.Site4D dx dy dz 3)) :
    ∑ p, rate (toEuclideanLin (Gyroscope.boxTransport dx dy dz)) (siteEvent p) ψ = 0 :=
  sum_rate_site (isSymmetric_toEuclideanLin_iff.mpr (boxTransport_isHermitian dx dy dz)) ψ

theorem rate_box_sq_le (p : FourAxes.Site4D dx dy dz 3)
    {ψ : EuclideanSpace ℂ (FourAxes.Site4D dx dy dz 3)} (hψ : ‖ψ‖ = 1) :
    rate (toEuclideanLin (Gyroscope.boxTransport dx dy dz)) (siteEvent p) ψ ^ 2 ≤
      4 * variance (toEuclideanLin (Gyroscope.boxTransport dx dy dz)) ψ *
        (‖ψ p‖ ^ 2 * (1 - ‖ψ p‖ ^ 2)) :=
  rate_site_sq_le (isSymmetric_toEuclideanLin_iff.mpr (boxTransport_isHermitian dx dy dz)) p hψ

end Box

end SiteEventsTopologies
