/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.SiteHop
public import Mathlib.Data.ZMod.Basic

/-!
# Dirac on the three-torus with the fiber

Put the fiber `w`, the closed ring `ZMod 3`, over the three-torus `ZMod a × ZMod b × ZMod c`
(even sizes). The fiber cannot carry an alternating sign, so it enters in the place of the mass
(`FiberDirac`, `FiberDiracAxis`):

  `D = T_x + B`,  `B = A_y + A_z + M_w`,  `A_y = (−1)^x T_y`, `A_z = (−1)^(x+y) T_z`,
  `M_w = (−1)^(x+y+z) T°_w`.

Every term is a hop of `SiteHop`, so the relations come from the hop lemmas: `T_x` and the
current `K_x` anticommute with `B`, and `A_y + A_z` anticommutes with `M_w`. With them
`TorusFiberGap` proves the mass gap `1/2` and the speed limit `1/φ`.

## Main results

- `TorusFiberDirac.dirac` : `D` on `T³ × w`.
- `TorusFiberDirac.Tx_rest`, `TorusFiberDirac.Kx_rest` : `T_x` and `K_x` anticommute with the rest
  `B` of `D`.
- `TorusFiberDirac.AyAz_Mw` : `A_y + A_z` anticommutes with the fiber term.
-/

@[expose] public noncomputable section

open Complex SiteHop

namespace TorusFiberDirac

/-! ## 1. The three-torus with the fiber -/

variable {a b c : ℕ}

/-- The sites `(x, y, z, w)` of `T³ × w`. -/
abbrev Site (a b c : ℕ) := ZMod a × ZMod b × ZMod c × ZMod 3

/-- The states of `T³ × w`. -/
abbrev HT (a b c : ℕ) := EuclideanSpace ℂ (Site a b c)

/-- One step along `x`. -/
def τx : Site a b c ≃ Site a b c where
  toFun p := (p.1 + 1, p.2)
  invFun p := (p.1 - 1, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- One step along `y`. -/
def τy : Site a b c ≃ Site a b c where
  toFun p := (p.1, p.2.1 + 1, p.2.2)
  invFun p := (p.1, p.2.1 - 1, p.2.2)
  left_inv p := by simp
  right_inv p := by simp

/-- One step along `z`. -/
def τz : Site a b c ≃ Site a b c where
  toFun p := (p.1, p.2.1, p.2.2.1 + 1, p.2.2.2)
  invFun p := (p.1, p.2.1, p.2.2.1 - 1, p.2.2.2)
  left_inv p := by simp
  right_inv p := by simp

/-- One step around the fiber. -/
def τw : Site a b c ≃ Site a b c where
  toFun p := (p.1, p.2.1, p.2.2.1, p.2.2.2 + 1)
  invFun p := (p.1, p.2.1, p.2.2.1, p.2.2.2 - 1)
  left_inv p := by simp
  right_inv p := by simp

section Steps

variable (x : ZMod a) (y : ZMod b) (z : ZMod c) (w : ZMod 3)

theorem τx_apply : τx (x, y, z, w) = (x + 1, y, z, w) := rfl
theorem τx_symm_apply : τx.symm (x, y, z, w) = (x - 1, y, z, w) := rfl
theorem τy_apply : τy (x, y, z, w) = (x, y + 1, z, w) := rfl
theorem τy_symm_apply : τy.symm (x, y, z, w) = (x, y - 1, z, w) := rfl
theorem τz_apply : τz (x, y, z, w) = (x, y, z + 1, w) := rfl
theorem τz_symm_apply : τz.symm (x, y, z, w) = (x, y, z - 1, w) := rfl
theorem τw_apply : τw (x, y, z, w) = (x, y, z, w + 1) := rfl
theorem τw_symm_apply : τw.symm (x, y, z, w) = (x, y, z, w - 1) := rfl

end Steps

/-- The staggered signs `(−1)^x`, `(−1)^(x+y)`, `(−1)^(x+y+z)`. -/
def sx (p : Site a b c) : ℝ := (-1) ^ p.1.val
def sxy (p : Site a b c) : ℝ := (-1) ^ p.1.val * (-1) ^ p.2.1.val
def sxyz (p : Site a b c) : ℝ := (-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val

theorem neg_one_pow_add_one {n : ℕ} [NeZero n] (h : 2 ∣ n) (j : ZMod n) :
    (-1 : ℝ) ^ (j + 1).val = -(-1) ^ j.val := by
  have hn : 2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) h
  have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < n),
    pow_eq_pow_mod _ h1, Nat.mod_mod_of_dvd _ h, ← pow_eq_pow_mod _ h1, pow_succ]
  ring

theorem neg_one_pow_sub_one {n : ℕ} [NeZero n] (h : 2 ∣ n) (j : ZMod n) :
    (-1 : ℝ) ^ (j - 1).val = -(-1) ^ j.val := by
  have h' := neg_one_pow_add_one h (j - 1)
  rw [sub_add_cancel] at h'
  rw [h', neg_neg]

/-- The transports, the current along `x` and the Dirac operator of `T³ × w`. -/
def Tx : HT a b c →ₗ[ℂ] HT a b c := hop τx 1
def Tw : HT a b c →ₗ[ℂ] HT a b c := hop τw 1
def Kx : HT a b c →ₗ[ℂ] HT a b c := cur τx
def Ay : HT a b c →ₗ[ℂ] HT a b c := hop τy sx
def Az : HT a b c →ₗ[ℂ] HT a b c := hop τz sxy
def Mw : HT a b c →ₗ[ℂ] HT a b c := hop τw sxyz

/-- Everything but the transport along `x`. -/
def rest : HT a b c →ₗ[ℂ] HT a b c := Ay + Az + Mw

/-- **The Dirac operator of `T³ × w`**, the fiber in the place of the mass. -/
def dirac : HT a b c →ₗ[ℂ] HT a b c := Tx + rest

/-! ## 2. The relations -/

section Signs

theorem sx_τx [NeZero a] (ha : 2 ∣ a) (p : Site a b c) : sx (τx p) = -sx p :=
  neg_one_pow_add_one ha p.1
theorem sx_τx_symm [NeZero a] (ha : 2 ∣ a) (p : Site a b c) : sx (τx.symm p) = -sx p :=
  neg_one_pow_sub_one ha p.1
theorem sxy_τx [NeZero a] (ha : 2 ∣ a) (p : Site a b c) : sxy (τx p) = -sxy p := by
  show (-1 : ℝ) ^ (p.1 + 1).val * (-1) ^ p.2.1.val = -((-1) ^ p.1.val * (-1) ^ p.2.1.val)
  rw [neg_one_pow_add_one ha]; ring
theorem sxy_τx_symm [NeZero a] (ha : 2 ∣ a) (p : Site a b c) : sxy (τx.symm p) = -sxy p := by
  show (-1 : ℝ) ^ (p.1 - 1).val * (-1) ^ p.2.1.val = -((-1) ^ p.1.val * (-1) ^ p.2.1.val)
  rw [neg_one_pow_sub_one ha]; ring
theorem sxyz_τx [NeZero a] (ha : 2 ∣ a) (p : Site a b c) : sxyz (τx p) = -sxyz p := by
  show (-1 : ℝ) ^ (p.1 + 1).val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val =
      -((-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val)
  rw [neg_one_pow_add_one ha]; ring
theorem sxyz_τx_symm [NeZero a] (ha : 2 ∣ a) (p : Site a b c) : sxyz (τx.symm p) = -sxyz p := by
  show (-1 : ℝ) ^ (p.1 - 1).val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val =
      -((-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val)
  rw [neg_one_pow_sub_one ha]; ring
theorem sxyz_τy [NeZero b] (hb : 2 ∣ b) (p : Site a b c) : sxyz (τy p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1.val * (-1) ^ (p.2.1 + 1).val * (-1) ^ p.2.2.1.val =
      -((-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val)
  rw [neg_one_pow_add_one hb]; ring
theorem sxyz_τy_symm [NeZero b] (hb : 2 ∣ b) (p : Site a b c) : sxyz (τy.symm p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1.val * (-1) ^ (p.2.1 - 1).val * (-1) ^ p.2.2.1.val =
      -((-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val)
  rw [neg_one_pow_sub_one hb]; ring
theorem sxyz_τz [NeZero c] (hc : 2 ∣ c) (p : Site a b c) : sxyz (τz p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ (p.2.2.1 + 1).val =
      -((-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val)
  rw [neg_one_pow_add_one hc]; ring
theorem sxyz_τz_symm [NeZero c] (hc : 2 ∣ c) (p : Site a b c) : sxyz (τz.symm p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ (p.2.2.1 - 1).val =
      -((-1) ^ p.1.val * (-1) ^ p.2.1.val * (-1) ^ p.2.2.1.val)
  rw [neg_one_pow_sub_one hc]; ring

/-- `T_x` anticommutes with the rest of `D`. -/
theorem Tx_rest [NeZero a] (ha : 2 ∣ a) (χ : HT a b c) : Tx (rest χ) = -rest (Tx χ) := by
  simp only [rest, LinearMap.add_apply, map_add, neg_add, Tx, Ay, Az, Mw]
  rw [hop_hop_anticomm (τ := τx) (σ := τy)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (sx_τx ha) (sx_τx_symm ha),
    hop_hop_anticomm (τ := τx) (σ := τz) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (sxy_τx ha) (sxy_τx_symm ha),
    hop_hop_anticomm (τ := τx) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (sxyz_τx ha) (sxyz_τx_symm ha)]

/-- `K_x` anticommutes with the rest of `D`. -/
theorem Kx_rest [NeZero a] (ha : 2 ∣ a) (χ : HT a b c) : Kx (rest χ) = -rest (Kx χ) := by
  simp only [rest, LinearMap.add_apply, map_add, neg_add, Kx, Ay, Az, Mw]
  rw [cur_hop_anticomm (τ := τx) (σ := τy)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (sx_τx ha) (sx_τx_symm ha),
    cur_hop_anticomm (τ := τx) (σ := τz) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (sxy_τx ha) (sxy_τx_symm ha),
    cur_hop_anticomm (τ := τx) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (sxyz_τx ha) (sxyz_τx_symm ha)]

/-- `A_y + A_z` anticommutes with the fiber term. -/
theorem AyAz_Mw [NeZero b] [NeZero c] (hb : 2 ∣ b) (hc : 2 ∣ c) (χ : HT a b c) :
    (Ay + Az : HT a b c →ₗ[ℂ] HT a b c) (Mw χ) =
      -Mw ((Ay + Az : HT a b c →ₗ[ℂ] HT a b c) χ) := by
  simp only [LinearMap.add_apply, map_add, neg_add, Ay, Az, Mw]
  rw [hop_hop_anticomm (τ := τy) (σ := τw)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (sxyz_τy hb) (sxyz_τy_symm hb),
    hop_hop_anticomm (τ := τz) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (sxyz_τz hc) (sxyz_τz_symm hc)]

end Signs

variable [NeZero a] [NeZero b] [NeZero c]

theorem Tx_isSymmetric : (Tx : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
  hop_isSymmetric _ fun _ => rfl
theorem Tw_isSymmetric : (Tw : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
  hop_isSymmetric _ fun _ => rfl
theorem Kx_isSymmetric : (Kx : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := cur_isSymmetric _
theorem Mw_isSymmetric : (Mw : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
  hop_isSymmetric _ fun _ => rfl
theorem rest_isSymmetric : (rest : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
  ((hop_isSymmetric _ fun _ => rfl).add (hop_isSymmetric _ fun _ => rfl)).add Mw_isSymmetric

end TorusFiberDirac
