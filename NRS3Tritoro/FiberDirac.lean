/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.OpenDirac
public import NRS3Hopf.BoxCommute
public import NRS3Hopf.ClosedThree

/-!
# Dirac on the fibred box: the fiber is the mass

The fiber `w` of the box is a ring of three positions, an odd ring: going once around it changes
the staggered sign an odd number of times, so the sign cannot alternate on it and the fiber
cannot take part in the Kogut–Susskind signs as a fourth spatial axis. It enters instead as a
mass. With the open axes `x`, `y`, `z` as on the open cube (`OpenDirac`) and the transport `T°` of
the fiber in the place of the mass,

  `D = T_x + σ_x T_y + σ_x σ_y T_z + σ_x σ_y σ_z T°`,

the four terms anticommute and

  `D² = T_x² + T_y² + T_z² + T°²`.

This is Kaluza and Klein's reading of a closed fifth dimension: motion around the closed fiber is
seen in `x`, `y`, `z` as mass. On the fiber `T°` has the uniform mode, eigenvalue `1`, and the two
rotating modes, eigenvalue `−1/2`, so a state in a fiber mode has `T°² = 1` or `1/4`: the fiber
gives the masses `1` and `1/2`. The rotating modes are those of the conserved rotation of the
fiber (`RotationFiber`), its spin.

## Main results

- `FiberDirac.dirac_sq_fiber_of_relations` : the square in any ring, the fiber in the place of
  the mass.
- `FiberDirac.dirac_sq` : `D² = T_x² + T_y² + T_z² + T°²` on the box.
- `FiberDirac.Tc_uniform`, `FiberDirac.Tc_rotating` : `T°` is `1` on the uniform mode and `−1/2`
  on the rotating modes.
- `FiberDirac.fiberMass_sq` : on a product with a fiber mode of eigenvalue `λ`, `T°² = λ²`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS FourAxes BoxCommute OpenDirac

namespace FiberDirac

/-! ## 1. The algebra, in any ring -/

section Algebra

variable {R : Type*} [Ring R] {X Y Z W Sx Sy Sz : R}

/-- **The fiber in the place of the mass.** With the relations of `dirac_sq_of_relations` and a
`W` that commutes with the transports and the signs of `x`, `y`, `z`,
`(X + Sx Y + Sx Sy Z + Sx Sy Sz W)² = X² + Y² + Z² + W²`. -/
theorem dirac_sq_fiber_of_relations (hYX : Y * X = X * Y) (hZX : Z * X = X * Z)
    (hZY : Z * Y = Y * Z) (hSySx : Sy * Sx = Sx * Sy) (hSzSx : Sz * Sx = Sx * Sz)
    (hSzSy : Sz * Sy = Sy * Sz) (hx : Sx * Sx = 1) (hy : Sy * Sy = 1) (hz : Sz * Sz = 1)
    (hXSx : X * Sx = -(Sx * X)) (hYSy : Y * Sy = -(Sy * Y)) (hZSz : Z * Sz = -(Sz * Z))
    (hYSx : Y * Sx = Sx * Y) (hZSx : Z * Sx = Sx * Z) (hXSy : X * Sy = Sy * X)
    (hZSy : Z * Sy = Sy * Z) (hXSz : X * Sz = Sz * X) (hYSz : Y * Sz = Sz * Y)
    (hWX : W * X = X * W) (hWY : W * Y = Y * W) (hWZ : W * Z = Z * W)
    (hWSx : W * Sx = Sx * W) (hWSy : W * Sy = Sy * W) (hWSz : W * Sz = Sz * W) :
    (X + Sx * Y + Sx * Sy * Z + Sx * Sy * Sz * W) * (X + Sx * Y + Sx * Sy * Z + Sx * Sy * Sz * W) =
      X * X + Y * Y + Z * Z + W * W := by
  -- every relation also with a tail: signs to the left, then `X, Y, Z`, and `W` last
  have t : ∀ {a b c d : R}, a * b = c * d → ∀ w, a * (b * w) = c * (d * w) := fun h w => by
    rw [← mul_assoc, h, mul_assoc]
  have tn : ∀ {a b c d : R}, a * b = -(c * d) → ∀ w, a * (b * w) = -(c * (d * w)) :=
    fun h w => by rw [← mul_assoc, h, neg_mul, mul_assoc]
  have t1 : ∀ {a : R}, a * a = 1 → ∀ w, a * (a * w) = w := fun h w => by
    rw [← mul_assoc, h, one_mul]
  simp only [add_mul, mul_add, mul_assoc, mul_neg, hYX, hZX, hZY, hWX, hWY, hWZ, t hSySx, t hSzSx,
    t hSzSy, t1 hx, t1 hy, t1 hz, tn hXSx, tn hYSy, tn hZSz, t hYSx, t hZSx, t hXSy, t hZSy, t hXSz,
    t hYSz, t hWSx, t hWSy, t hWSz]
  abel

end Algebra

/-! ## 2. The box -/

variable {dx dy dz : ℕ}

/-- The Dirac operator of the box, the fiber in the place of the mass:
`D = T_x + σ_x T_y + σ_x σ_y T_z + σ_x σ_y σ_z T°`. -/
def dirac (dx dy dz : ℕ) : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ :=
  liftAlong (eX dx dy dz 3) (Td dx) +
    liftAlong (eX dx dy dz 3) (stagger dx) * liftAlong (eY dx dy dz 3) (Td dy) +
    liftAlong (eX dx dy dz 3) (stagger dx) * liftAlong (eY dx dy dz 3) (stagger dy) *
      liftAlong (eZ dx dy dz 3) (Td dz) +
    liftAlong (eX dx dy dz 3) (stagger dx) * liftAlong (eY dx dy dz 3) (stagger dy) *
      liftAlong (eZ dx dy dz 3) (stagger dz) * liftAlong (eW dx dy dz 3) ClosedThree.Tc

/-- **The fiber is the mass**: `D² = T_x² + T_y² + T_z² + T°²` on the box. -/
theorem dirac_sq :
    dirac dx dy dz * dirac dx dy dz =
      liftAlong (eX dx dy dz 3) (Td dx) * liftAlong (eX dx dy dz 3) (Td dx) +
        liftAlong (eY dx dy dz 3) (Td dy) * liftAlong (eY dx dy dz 3) (Td dy) +
        liftAlong (eZ dx dy dz 3) (Td dz) * liftAlong (eZ dx dy dz 3) (Td dz) +
        liftAlong (eW dx dy dz 3) ClosedThree.Tc * liftAlong (eW dx dy dz 3) ClosedThree.Tc := by
  exact dirac_sq_fiber_of_relations
    (liftAlong_xy_comm (Td dx) (Td dy)).symm (liftAlong_xz_comm (Td dx) (Td dz)).symm
    (liftAlong_yz_comm (Td dy) (Td dz)).symm (liftAlong_xy_comm (stagger dx) (stagger dy)).symm
    (liftAlong_xz_comm (stagger dx) (stagger dz)).symm
    (liftAlong_yz_comm (stagger dy) (stagger dz)).symm
    (liftAlong_stagger_mul_self (eX dx dy dz 3)) (liftAlong_stagger_mul_self (eY dx dy dz 3))
    (liftAlong_stagger_mul_self (eZ dx dy dz 3)) (liftAlong_Td_mul_stagger (eX dx dy dz 3))
    (liftAlong_Td_mul_stagger (eY dx dy dz 3)) (liftAlong_Td_mul_stagger (eZ dx dy dz 3))
    (liftAlong_xy_comm (stagger dx) (Td dy)).symm (liftAlong_xz_comm (stagger dx) (Td dz)).symm
    (liftAlong_xy_comm (Td dx) (stagger dy)) (liftAlong_yz_comm (stagger dy) (Td dz)).symm
    (liftAlong_xz_comm (Td dx) (stagger dz)) (liftAlong_yz_comm (Td dy) (stagger dz))
    (liftAlong_xw_comm (Td dx) ClosedThree.Tc).symm (liftAlong_yw_comm (Td dy) ClosedThree.Tc).symm
    (liftAlong_zw_comm (Td dz) ClosedThree.Tc).symm
    (liftAlong_xw_comm (stagger dx) ClosedThree.Tc).symm
    (liftAlong_yw_comm (stagger dy) ClosedThree.Tc).symm
    (liftAlong_zw_comm (stagger dz) ClosedThree.Tc).symm

/-! ## 3. The masses of the fiber -/

/-- The uniform mode of the fiber. -/
def uniform : Hd 3 := WithLp.toLp 2 fun _ => 1

/-- A rotating mode of the fiber. -/
def rotating : Hd 3 := WithLp.toLp 2 ![1, -1, 0]

/-- `T°` is `1` on the uniform mode. -/
theorem Tc_uniform : ClosedThree.TcOp uniform = uniform := by
  obtain ⟨h0, h1, h2⟩ := ClosedThree.TcOp_apply uniform
  ext i
  fin_cases i
  · refine h0.trans ?_; simp [uniform]
  · refine h1.trans ?_; simp [uniform]
  · refine h2.trans ?_; simp [uniform]

/-- `T°` is `−1/2` on the rotating mode. -/
theorem Tc_rotating : ClosedThree.TcOp rotating = (-1 / 2 : ℂ) • rotating := by
  obtain ⟨h0, h1, h2⟩ := ClosedThree.TcOp_apply rotating
  ext i
  fin_cases i
  · refine h0.trans ?_; simp [rotating]
  · refine h1.trans ?_; simp [rotating]; norm_num
  · refine h2.trans ?_; simp [rotating]

/-- **The fiber gives the mass.** On a product with a fiber mode of eigenvalue `λ`, `T°² = λ²`:
`1` on the uniform mode, `1/4` on the rotating ones. -/
theorem fiberMass_sq {v : Hd 3} {lam : ℂ} (hv : ClosedThree.TcOp v = lam • v)
    (φ : EuclideanSpace ℂ (Fin dx × Fin dy × Fin dz)) :
    Matrix.toEuclideanLin (liftAlong (eW dx dy dz 3) ClosedThree.Tc *
        liftAlong (eW dx dy dz 3) ClosedThree.Tc) (prodAlong (eW dx dy dz 3) v φ) =
      (lam ^ 2) • prodAlong (eW dx dy dz 3) v φ := by
  have hv' : Matrix.toEuclideanLin ClosedThree.Tc v = lam • v := hv
  rw [← BoxTwoRelations.liftAlong_mul, toEuclideanLin_liftAlong, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply, hv', map_smul, hv', smul_smul, prodAlong_smul, sq]

end FiberDirac
