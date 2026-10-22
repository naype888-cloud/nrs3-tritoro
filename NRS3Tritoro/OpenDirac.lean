/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxTwoRelations

/-!
# Dirac's square root on the open cube

On the open cube `dx × dy × dz` take the transports `T_x, T_y, T_z` of the three open axes and the
staggered sign `σ = (−1)^j` of each axis. A step of an open axis joins `j` to `j ± 1`, so it
always changes the sign: `σ T = −T σ` on every open axis, whatever its size. The
Kogut–Susskind operators

  `A_x = T_x`, `A_y = σ_x T_y`, `A_z = σ_x σ_y T_z`, `ε = σ_x σ_y σ_z`

anticommute pairwise, `A_y² = T_y²`, `A_z² = T_z²`, `ε² = 1`, and the massive Dirac operator
`D_m = A_x + A_y + A_z + m ε` squares to

  `D_m² = T_x² + T_y² + T_z² + m²`.

On the three-torus the same holds only for even sizes, where the seam keeps the sign alternating
(`TorusDirac3.dirac3_sq`); the open cube needs no parity.

The algebra is done once, in any ring: four pairwise anticommuting elements square to the sum of
their squares (`sq_add_of_anticomm`), and the relations of the lifted operators give the
anticommutations (`dirac_sq_of_relations`).

## Main results

- `OpenDirac.sq_add_of_anticomm` : `(a + b + c + e)² = a² + b² + c² + e²` for pairwise
  anticommuting `a, b, c, e`.
- `OpenDirac.dirac_sq_of_relations` : the Kogut–Susskind square from the commutation relations.
- `OpenDirac.stagger_mul_Td` : `σ T_d = −T_d σ` on every open axis.
- `OpenDirac.dirac_sq` : `D_m² = T_x² + T_y² + T_z² + m²` on the open cube, every size.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS LightCone
open PathGraph3D (Site3D)

namespace OpenDirac

/-! ## 1. The algebra, in any ring -/

section Algebra

variable {R : Type*} [Ring R]

/-- **Four pairwise anticommuting elements square to the sum of their squares.** -/
theorem sq_add_of_anticomm {a b c e : R} (hab : b * a = -(a * b)) (hac : c * a = -(a * c))
    (hae : e * a = -(a * e)) (hbc : c * b = -(b * c)) (hbe : e * b = -(b * e))
    (hce : e * c = -(c * e)) :
    (a + b + c + e) * (a + b + c + e) = a * a + b * b + c * c + e * e := by
  simp only [add_mul, mul_add, hab, hac, hae, hbc, hbe, hce]
  abel

variable [Algebra ℂ R] {X Y Z Sx Sy Sz : R}

/-- **The Kogut–Susskind square.** If the transports of different axes commute, the signs commute
among themselves and with the transports of the other axes, square to `1`, and anticommute with
the transport of their own axis, then
`(X + Sx Y + Sx Sy Z + m Sx Sy Sz)² = X² + Y² + Z² + m²`. -/
theorem dirac_sq_of_relations (hYX : Y * X = X * Y) (hZX : Z * X = X * Z) (hZY : Z * Y = Y * Z)
    (hSySx : Sy * Sx = Sx * Sy) (hSzSx : Sz * Sx = Sx * Sz) (hSzSy : Sz * Sy = Sy * Sz)
    (hx : Sx * Sx = 1) (hy : Sy * Sy = 1) (hz : Sz * Sz = 1)
    (hXSx : X * Sx = -(Sx * X)) (hYSy : Y * Sy = -(Sy * Y)) (hZSz : Z * Sz = -(Sz * Z))
    (hYSx : Y * Sx = Sx * Y) (hZSx : Z * Sx = Sx * Z) (hXSy : X * Sy = Sy * X)
    (hZSy : Z * Sy = Sy * Z) (hXSz : X * Sz = Sz * X) (hYSz : Y * Sz = Sz * Y) (m : ℂ) :
    (X + Sx * Y + Sx * Sy * Z + m • (Sx * Sy * Sz)) *
        (X + Sx * Y + Sx * Sy * Z + m • (Sx * Sy * Sz)) =
      X * X + Y * Y + Z * Z + (m ^ 2) • (1 : R) := by
  -- every relation also with a tail, so that `simp` sorts right-associated products:
  -- signs to the left in the order `Sx, Sy, Sz`, transports in the order `X, Y, Z`
  have t : ∀ {a b c d : R}, a * b = c * d → ∀ w, a * (b * w) = c * (d * w) := fun h w => by
    rw [← mul_assoc, h, mul_assoc]
  have tn : ∀ {a b c d : R}, a * b = -(c * d) → ∀ w, a * (b * w) = -(c * (d * w)) :=
    fun h w => by rw [← mul_assoc, h, neg_mul, mul_assoc]
  have t1 : ∀ {a : R}, a * a = 1 → ∀ w, a * (a * w) = w := fun h w => by
    rw [← mul_assoc, h, one_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc,
    mul_neg, smul_neg, mul_one, hYX, hZX, hZY, hx, hy, hz, hZSz, hXSz, hYSz, t hSySx, t hSzSx,
    t hSzSy, t1 hx, t1 hy, tn hXSx, tn hYSy, t hYSx, t hZSx, t hXSy, t hZSy]
  rw [sq]
  abel

end Algebra

/-! ## 2. The open cube -/

section Cube

variable {dx dy dz : ℕ}

/-- The staggered sign `(−1)^j` of an axis. -/
def stagger (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := diagonal fun j => (-1) ^ j.val

theorem stagger_mul_self (d : ℕ) : stagger d * stagger d = 1 := by
  rw [stagger, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  rw [← mul_pow]
  norm_num

/-- **A step of an open axis always changes the sign**: `σ T_d = −T_d σ`, every size. -/
theorem stagger_mul_Td (d : ℕ) : stagger d * Td d = -(Td d * stagger d) := by
  ext i j
  rw [Matrix.neg_apply, stagger, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Td, Ad]
  split_ifs with h
  · unfold MinStep at h
    rcases h with h | h
    · rw [← h, pow_succ]; ring
    · rw [← h, pow_succ]; ring
  · simp

section Lift

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq α]
  [DecidableEq β] (e : ι ≃ α × β)

omit [Fintype ι] [Fintype α] [Fintype β] in
theorem liftAlong_one : liftAlong e (1 : Matrix α α ℂ) = 1 := by
  ext p q
  simp only [liftAlong, Matrix.of_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp [h]
  · have hne : e p ≠ e q := e.injective.ne h
    by_cases h1 : (e p).1 = (e q).1
    · have h2 : (e p).2 ≠ (e q).2 := fun h2 => hne (Prod.ext h1 h2)
      simp [h, h1, h2]
    · simp [h, h1]

omit [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq α] in
theorem liftAlong_neg (A : Matrix α α ℂ) : liftAlong e (-A) = -liftAlong e A := by
  ext p q
  simp only [liftAlong, Matrix.of_apply, Matrix.neg_apply]
  split_ifs <;> simp

variable {d : ℕ} (e' : ι ≃ Fin d × β)

omit [DecidableEq ι] in
/-- On every open axis, lifted to any product, `T σ = −σ T`. -/
theorem liftAlong_Td_mul_stagger :
    liftAlong e' (Td d) * liftAlong e' (stagger d) =
      -(liftAlong e' (stagger d) * liftAlong e' (Td d)) := by
  have h : Td d * stagger d = -(stagger d * Td d) := by rw [stagger_mul_Td, neg_neg]
  rw [← BoxTwoRelations.liftAlong_mul, ← BoxTwoRelations.liftAlong_mul, ← liftAlong_neg, h]

/-- On every axis, lifted to any product, `σ² = 1`. -/
theorem liftAlong_stagger_mul_self :
    liftAlong e' (stagger d) * liftAlong e' (stagger d) = 1 := by
  rw [← BoxTwoRelations.liftAlong_mul, stagger_mul_self, liftAlong_one]

end Lift

/-- The Kogut–Susskind Dirac operator of the open cube,
`D_m = T_x + σ_x T_y + σ_x σ_y T_z + m σ_x σ_y σ_z`. -/
def dirac (dx dy dz : ℕ) (m : ℂ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (Td dx) +
    liftAlong (eX dx dy dz) (stagger dx) * liftAlong (eY dx dy dz) (Td dy) +
    liftAlong (eX dx dy dz) (stagger dx) * liftAlong (eY dx dy dz) (stagger dy) *
      liftAlong (eZ dx dy dz) (Td dz) +
    m • (liftAlong (eX dx dy dz) (stagger dx) * liftAlong (eY dx dy dz) (stagger dy) *
      liftAlong (eZ dx dy dz) (stagger dz))

/-- **Dirac's square root on the open cube, every size**: `D_m² = T_x² + T_y² + T_z² + m²`. -/
theorem dirac_sq (m : ℂ) :
    dirac dx dy dz m * dirac dx dy dz m =
      liftAlong (eX dx dy dz) (Td dx) * liftAlong (eX dx dy dz) (Td dx) +
        liftAlong (eY dx dy dz) (Td dy) * liftAlong (eY dx dy dz) (Td dy) +
        liftAlong (eZ dx dy dz) (Td dz) * liftAlong (eZ dx dy dz) (Td dz) + (m ^ 2) • 1 := by
  have hx := liftAlong_stagger_mul_self (eX dx dy dz)
  have hy := liftAlong_stagger_mul_self (eY dx dy dz)
  have hz := liftAlong_stagger_mul_self (eZ dx dy dz)
  have hXSx := liftAlong_Td_mul_stagger (eX dx dy dz)
  have hYSy := liftAlong_Td_mul_stagger (eY dx dy dz)
  have hZSz := liftAlong_Td_mul_stagger (eZ dx dy dz)
  have hYX := (liftAlong_xy_comm dx dy dz (Td dx) (Td dy)).symm
  have hZX := (liftAlong_xz_comm dx dy dz (Td dx) (Td dz)).symm
  have hZY := (liftAlong_yz_comm dx dy dz (Td dy) (Td dz)).symm
  have hSySx := (liftAlong_xy_comm dx dy dz (stagger dx) (stagger dy)).symm
  have hSzSx := (liftAlong_xz_comm dx dy dz (stagger dx) (stagger dz)).symm
  have hSzSy := (liftAlong_yz_comm dx dy dz (stagger dy) (stagger dz)).symm
  have hYSx := (liftAlong_xy_comm dx dy dz (stagger dx) (Td dy)).symm
  have hZSx := (liftAlong_xz_comm dx dy dz (stagger dx) (Td dz)).symm
  have hXSy := liftAlong_xy_comm dx dy dz (Td dx) (stagger dy)
  have hZSy := (liftAlong_yz_comm dx dy dz (stagger dy) (Td dz)).symm
  have hXSz := liftAlong_xz_comm dx dy dz (Td dx) (stagger dz)
  have hYSz := liftAlong_yz_comm dx dy dz (Td dy) (stagger dz)
  exact dirac_sq_of_relations hYX hZX hZY hSySx hSzSx hSzSy hx hy hz hXSx hYSy hZSz hYSx hZSx
    hXSy hZSy hXSz hYSz m

end Cube

end OpenDirac
