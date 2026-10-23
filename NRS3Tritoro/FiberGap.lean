/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.FiberDirac
public import NRS3Tritoro.DiracSpeed
public import NRS3Tritoro.SiteEventsTopologies

/-!
# The mass gap `1/2` on the fibred box

On the fibred box (`x`, `y`, `z` open, the fiber `w` a ring of three) `FiberDirac` gives
`D² = T_x² + T_y² + T_z² + T°²`. The ring of three has `T°² = (1 + T°)/2` (eigenvalues `1` and
`−1/2`), so `‖T° χ‖² ≥ ‖χ‖²/4` for every state (`DiracSpeed.norm_sq_ge_of_sq_eq`), and every
eigenvalue of `D` has `|E| ≥ 1/2`: the fiber gives a mass gap whether the other axes are open
(the box) or closed (`TorusFiberGap`).

The speed limit `1/φ` does not carry over: on an open axis the current and the transport do not
satisfy `K² + T² = 1`, so `DiracSpeed.abs_velocity_le` needs the closed axes of `T³ × w`.

## Main results

- `FiberDirac.Tc_sq` : `T°² = (1 + T°)/2` on the ring of three.
- `FiberDirac.norm_sq_fiber_ge` : `‖T° χ‖² ≥ ‖χ‖²/4` on the box.
- `FiberDirac.abs_energy_ge` : every eigenvalue of `D` on the box has `|E| ≥ 1/2`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS FourAxes OpenDirac

namespace FiberDirac

variable {dx dy dz : ℕ}

/-- **The ring of three**: `T°² = (1 + T°)/2`. -/
theorem Tc_sq : ClosedThree.Tc * ClosedThree.Tc = ((1 / 2 : ℝ) : ℂ) • (1 + ClosedThree.Tc) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ClosedThree.Tc, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- The fiber transport on the box. -/
abbrev fiberOp (dx dy dz : ℕ) :=
  toEuclideanLin (liftAlong (eW dx dy dz 3) ClosedThree.Tc)

theorem lift_isSymmetric {d : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (e : Site4D dx dy dz 3 ≃ Fin d × β) {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    (toEuclideanLin (liftAlong e A)).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (SiteEventsTopologies.liftAlong_isHermitian e hA)

theorem fiberOp_sq (χ : EuclideanSpace ℂ (Site4D dx dy dz 3)) :
    fiberOp dx dy dz (fiberOp dx dy dz χ) = ((1 / 2 : ℝ) : ℂ) • (χ + fiberOp dx dy dz χ) := by
  have h : liftAlong (eW dx dy dz 3) ClosedThree.Tc * liftAlong (eW dx dy dz 3) ClosedThree.Tc =
      ((1 / 2 : ℝ) : ℂ) • (1 + liftAlong (eW dx dy dz 3) ClosedThree.Tc) := by
    rw [← BoxTwoRelations.liftAlong_mul, Tc_sq, BoxTwoRelations.liftAlong_smul,
      BoxTwoRelations.liftAlong_add, liftAlong_one]
  have h2 := congrArg (fun M => toEuclideanLin M χ) h
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_smul,
    map_add, Matrix.toLpLin_one, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply] at h2
  exact h2

/-- **The fiber is never smaller than `1/2` on the box.** -/
theorem norm_sq_fiber_ge (χ : EuclideanSpace ℂ (Site4D dx dy dz 3)) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖fiberOp dx dy dz χ‖ ^ 2 :=
  DiracSpeed.norm_sq_ge_of_sq_eq (lift_isSymmetric _ ClosedThree.Tc_isHermitian) fiberOp_sq χ

theorem tel_mul (M N : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ)
    (χ : EuclideanSpace ℂ (Site4D dx dy dz 3)) :
    toEuclideanLin (M * N) χ = toEuclideanLin M (toEuclideanLin N χ) := by
  simp [Matrix.toEuclideanLin]

theorem re_inner_sq {S : EuclideanSpace ℂ (Site4D dx dy dz 3) →ₗ[ℂ] _} (hS : S.IsSymmetric)
    (χ : EuclideanSpace ℂ (Site4D dx dy dz 3)) : (inner ℂ χ (S (S χ))).re = ‖S χ‖ ^ 2 := by
  rw [← hS]
  simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (S χ)

/-- **The mass gap of the fibred box**: every eigenvalue of `D` has `|E| ≥ 1/2`. -/
theorem abs_energy_ge {E : ℝ} {χ : EuclideanSpace ℂ (Site4D dx dy dz 3)} (hχ : χ ≠ 0)
    (hE : toEuclideanLin (dirac dx dy dz) χ = (E : ℂ) • χ) : 1 / 2 ≤ |E| := by
  have h2 : toEuclideanLin (dirac dx dy dz * dirac dx dy dz) χ = ((E ^ 2 : ℝ) : ℂ) • χ := by
    rw [tel_mul, hE, map_smul, hE, smul_smul]; push_cast; ring_nf
  rw [dirac_sq] at h2
  have hX := lift_isSymmetric (eX dx dy dz 3) (Td_isHermitian dx)
  have hY := lift_isSymmetric (eY dx dy dz 3) (Td_isHermitian dy)
  have hZ := lift_isSymmetric (eZ dx dy dz 3) (Td_isHermitian dz)
  have hW := lift_isSymmetric (eW dx dy dz 3) ClosedThree.Tc_isHermitian
  have h3 := congrArg (fun η => (inner ℂ χ η).re) h2
  simp only [map_add, LinearMap.add_apply, tel_mul, inner_add_right, Complex.add_re,
    inner_smul_right, Complex.re_ofReal_mul] at h3
  rw [re_inner_sq hX, re_inner_sq hY, re_inner_sq hZ, re_inner_sq hW] at h3
  have hN : (inner ℂ χ χ).re = ‖χ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) χ
  rw [hN] at h3
  have hW4 := norm_sq_fiber_ge (dx := dx) (dy := dy) (dz := dz) χ
  have hn : 0 < ‖χ‖ ^ 2 := by positivity
  have hE2 : (1 / 2 : ℝ) ^ 2 ≤ E ^ 2 := by
    refine le_of_mul_le_mul_right ?_ hn
    nlinarith only [h3, hW4, sq_nonneg ‖toEuclideanLin (liftAlong (eX dx dy dz 3) (Td dx)) χ‖,
      sq_nonneg ‖toEuclideanLin (liftAlong (eY dx dy dz 3) (Td dy)) χ‖,
      sq_nonneg ‖toEuclideanLin (liftAlong (eZ dx dy dz 3) (Td dz)) χ‖]
  rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact sq_le_sq.1 hE2

end FiberDirac
