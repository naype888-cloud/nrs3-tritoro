/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.SiteHopL2
public import NRS3Tritoro.DiracSpeed
public import Mathlib.Data.ZMod.Basic

/-!
# Dirac on the infinite lattice `ℤ³` with the fiber: mass gap `1/2`, speed `1/φ`

The same Dirac operator as `TorusFiberDirac`, now on the infinite discrete lattice:
the sites are `ℤ × ℤ × ℤ × ZMod 3`, the states are `ℓ²` of the sites, and nothing is sent to
the continuum. The three axes are open and infinite (bilateral), the fiber `w` is the closed
ring of three:
  `D = T_x + B`,  `B = A_y + A_z + M_w`,  `A_y = (−1)^x T_y`, `A_z = (−1)^(x+y) T_z`,
  `M_w = (−1)^(x+y+z) T°_w`.
The shift along an infinite axis is unitary on `ℓ²`, so `K_x² + T_x² = 1` holds at every site
(`SiteHopL2`) and `DiracSpeed` applies as on the torus. A lattice spacing `a > 0` turns the
dimensionless bound into a physical one; `a` is kept, never sent to zero.

## Main results

- `LatticeFiberDirac.norm_sq_rest_ge` : `‖Bχ‖² ≥ ‖χ‖²/4` for every state of `ℓ²(ℤ³ × w)`.
- `LatticeFiberDirac.abs_energy_ge` : `|E| ≥ 1/2` for every eigenvalue of `D`.
- `LatticeFiberDirac.abs_velocity_le_inv_goldenRatio` : `|⟨K_x⟩| ≤ 1/φ` for every unit
  eigenvector of `D`.
- `LatticeFiberDirac.abs_physical_velocity_le` : with spacing `a > 0`, `|a ⟨K_x⟩| ≤ a/φ`.
-/

@[expose] public noncomputable section

open Complex SiteHopL2

namespace LatticeFiberDirac

/-! ## 1. The lattice with the fiber -/

/-- The sites `(x, y, z, w)` of `ℤ³ × w`. -/
abbrev Site := ℤ × ℤ × ℤ × ZMod 3

/-- The states of `ℤ³ × w`. -/
abbrev H := L2 Site

/-- One step along `x`. -/
def τx : Site ≃ Site where
  toFun p := (p.1 + 1, p.2)
  invFun p := (p.1 - 1, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- One step along `y`. -/
def τy : Site ≃ Site where
  toFun p := (p.1, p.2.1 + 1, p.2.2)
  invFun p := (p.1, p.2.1 - 1, p.2.2)
  left_inv p := by simp
  right_inv p := by simp

/-- One step along `z`. -/
def τz : Site ≃ Site where
  toFun p := (p.1, p.2.1, p.2.2.1 + 1, p.2.2.2)
  invFun p := (p.1, p.2.1, p.2.2.1 - 1, p.2.2.2)
  left_inv p := by simp
  right_inv p := by simp

/-- One step around the fiber. -/
def τw : Site ≃ Site where
  toFun p := (p.1, p.2.1, p.2.2.1, p.2.2.2 + 1)
  invFun p := (p.1, p.2.1, p.2.2.1, p.2.2.2 - 1)
  left_inv p := by simp
  right_inv p := by simp

/-- The staggered signs `(−1)^x`, `(−1)^(x+y)`, `(−1)^(x+y+z)`. -/
def sx (p : Site) : ℝ := (-1) ^ p.1
def sxy (p : Site) : ℝ := (-1) ^ p.1 * (-1) ^ p.2.1
def sxyz (p : Site) : ℝ := (-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1

theorem neg_one_zpow_add_one (n : ℤ) : (-1 : ℝ) ^ (n + 1) = -(-1) ^ n := by
  rw [zpow_add_one₀ (by norm_num)]; ring

theorem neg_one_zpow_sub_one (n : ℤ) : (-1 : ℝ) ^ (n - 1) = -(-1) ^ n := by
  rw [zpow_sub_one₀ (by norm_num), inv_neg, inv_one]; ring

theorem abs_neg_one_zpow (n : ℤ) : |(-1 : ℝ) ^ n| = 1 := by
  rw [abs_zpow, abs_neg, abs_one, one_zpow]

theorem neg_one_zpow_mul_self (n : ℤ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_zpow]; norm_num

theorem abs_sx (p : Site) : |sx p| ≤ 1 := (abs_neg_one_zpow _).le

theorem abs_sxy (p : Site) : |sxy p| ≤ 1 := by
  simp only [sxy, abs_mul, abs_neg_one_zpow, mul_one, le_refl]

theorem abs_sxyz (p : Site) : |sxyz p| ≤ 1 := by
  simp only [sxyz, abs_mul, abs_neg_one_zpow, mul_one, le_refl]

theorem sxyz_mul_self (p : Site) : sxyz p * sxyz p = 1 := by
  simp only [sxyz]
  linear_combination ((-1 : ℝ) ^ p.2.1 * (-1) ^ p.2.1) * ((-1 : ℝ) ^ p.2.2.1 * (-1) ^ p.2.2.1) *
      neg_one_zpow_mul_self p.1 +
    ((-1 : ℝ) ^ p.2.2.1 * (-1) ^ p.2.2.1) * neg_one_zpow_mul_self p.2.1 +
    neg_one_zpow_mul_self p.2.2.1

/-- The transports, the current along `x` and the Dirac operator of `ℤ³ × w`. -/
def Tx : H →ₗ[ℂ] H := hop τx (c := 1) abs_one_le
def Tw : H →ₗ[ℂ] H := hop τw (c := 1) abs_one_le
def Kx : H →ₗ[ℂ] H := cur τx
def Ay : H →ₗ[ℂ] H := hop τy abs_sx
def Az : H →ₗ[ℂ] H := hop τz abs_sxy
def Mw : H →ₗ[ℂ] H := hop τw abs_sxyz

/-- Everything but the transport along `x`. -/
def rest : H →ₗ[ℂ] H := Ay + Az + Mw

/-- **The Dirac operator of `ℤ³ × w`**, the fiber in the place of the mass. -/
def dirac : H →ₗ[ℂ] H := Tx + rest

/-! ## 2. The relations -/

theorem sx_τx (p : Site) : sx (τx p) = -sx p := neg_one_zpow_add_one p.1
theorem sx_τx_symm (p : Site) : sx (τx.symm p) = -sx p := neg_one_zpow_sub_one p.1

theorem sxy_τx (p : Site) : sxy (τx p) = -sxy p := by
  show (-1 : ℝ) ^ (p.1 + 1) * (-1) ^ p.2.1 = -((-1) ^ p.1 * (-1) ^ p.2.1)
  rw [neg_one_zpow_add_one]; ring

theorem sxy_τx_symm (p : Site) : sxy (τx.symm p) = -sxy p := by
  show (-1 : ℝ) ^ (p.1 - 1) * (-1) ^ p.2.1 = -((-1) ^ p.1 * (-1) ^ p.2.1)
  rw [neg_one_zpow_sub_one]; ring

theorem sxyz_τx (p : Site) : sxyz (τx p) = -sxyz p := by
  show (-1 : ℝ) ^ (p.1 + 1) * (-1) ^ p.2.1 * (-1) ^ p.2.2.1 =
      -((-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1)
  rw [neg_one_zpow_add_one]; ring

theorem sxyz_τx_symm (p : Site) : sxyz (τx.symm p) = -sxyz p := by
  show (-1 : ℝ) ^ (p.1 - 1) * (-1) ^ p.2.1 * (-1) ^ p.2.2.1 =
      -((-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1)
  rw [neg_one_zpow_sub_one]; ring

theorem sxyz_τy (p : Site) : sxyz (τy p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1 * (-1) ^ (p.2.1 + 1) * (-1) ^ p.2.2.1 =
      -((-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1)
  rw [neg_one_zpow_add_one]; ring

theorem sxyz_τy_symm (p : Site) : sxyz (τy.symm p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1 * (-1) ^ (p.2.1 - 1) * (-1) ^ p.2.2.1 =
      -((-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1)
  rw [neg_one_zpow_sub_one]; ring

theorem sxyz_τz (p : Site) : sxyz (τz p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ (p.2.2.1 + 1) =
      -((-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1)
  rw [neg_one_zpow_add_one]; ring

theorem sxyz_τz_symm (p : Site) : sxyz (τz.symm p) = -sxyz p := by
  show (-1 : ℝ) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ (p.2.2.1 - 1) =
      -((-1) ^ p.1 * (-1) ^ p.2.1 * (-1) ^ p.2.2.1)
  rw [neg_one_zpow_sub_one]; ring

/-- `T_x` anticommutes with the rest of `D`. -/
theorem Tx_rest (χ : H) : Tx (rest χ) = -rest (Tx χ) := by
  simp only [rest, LinearMap.add_apply, map_add, neg_add, Tx, Ay, Az, Mw]
  rw [hop_hop_anticomm (τ := τx) (σ := τy) _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) sx_τx sx_τx_symm,
    hop_hop_anticomm (τ := τx) (σ := τz) _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) sxy_τx sxy_τx_symm,
    hop_hop_anticomm (τ := τx) (σ := τw) _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) sxyz_τx sxyz_τx_symm]

/-- `K_x` anticommutes with the rest of `D`. -/
theorem Kx_rest (χ : H) : Kx (rest χ) = -rest (Kx χ) := by
  simp only [rest, LinearMap.add_apply, map_add, neg_add, Kx, Ay, Az, Mw]
  rw [cur_hop_anticomm (τ := τx) (σ := τy) _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) sx_τx sx_τx_symm,
    cur_hop_anticomm (τ := τx) (σ := τz) _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) sxy_τx sxy_τx_symm,
    cur_hop_anticomm (τ := τx) (σ := τw) _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) sxyz_τx sxyz_τx_symm]

/-- `A_y + A_z` anticommutes with the fiber term. -/
theorem AyAz_Mw (χ : H) : (Ay + Az) (Mw χ) = -Mw ((Ay + Az) χ) := by
  simp only [LinearMap.add_apply, map_add, neg_add, Ay, Az, Mw]
  rw [hop_hop_anticomm (τ := τy) (σ := τw) _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) sxyz_τy sxyz_τy_symm,
    hop_hop_anticomm (τ := τz) (σ := τw) _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) sxyz_τz sxyz_τz_symm]

theorem Tx_isSymmetric : Tx.IsSymmetric := hop_isSymmetric _ _ fun _ => rfl
theorem Tw_isSymmetric : Tw.IsSymmetric := hop_isSymmetric _ _ fun _ => rfl
theorem Kx_isSymmetric : Kx.IsSymmetric := cur_isSymmetric _
theorem Mw_isSymmetric : Mw.IsSymmetric := hop_isSymmetric _ _ fun _ => rfl

theorem AyAz_isSymmetric : (Ay + Az).IsSymmetric :=
  (hop_isSymmetric _ _ fun _ => rfl).add (hop_isSymmetric _ _ fun _ => rfl)

theorem rest_isSymmetric : rest.IsSymmetric := AyAz_isSymmetric.add Mw_isSymmetric

/-! ## 3. The fiber gap -/

/-- On the ring of three, `T°_w² = (1 + T°_w)/2`. -/
theorem Tw_sq (χ : H) : Tw (Tw χ) = ((1 / 2 : ℝ) : ℂ) • (χ + Tw χ) := by
  refine lp.ext <| funext fun ⟨x, y, z, w⟩ => ?_
  have e1 : (w + 1 + 1 : ZMod 3) = w - 1 := by
    rw [add_assoc, sub_eq_add_neg]; congr 1
  have e2 : (w - 1 - 1 : ZMod 3) = w + 1 := by
    rw [sub_sub, sub_eq_add_neg]; congr 1
  have a1 : τw (τw (x, y, z, w)) = τw.symm (x, y, z, w) :=
    show (x, y, z, w + 1 + 1) = (x, y, z, w - 1) by rw [e1]
  have a2 : τw.symm (τw.symm (x, y, z, w)) = τw (x, y, z, w) :=
    show (x, y, z, w - 1 - 1) = (x, y, z, w + 1) by rw [e2]
  simp only [Tw, hop_apply, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Pi.one_apply, Complex.ofReal_one, one_mul, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, a1, a2]
  push_cast
  ring

/-- The sign does not change the square of the fiber term: `M_w² = T°_w²`. -/
theorem Mw_sq (χ : H) : Mw (Mw χ) = Tw (Tw χ) := by
  refine lp.ext <| funext fun p => ?_
  have hs : ∀ q : Site, sxyz (τw q) = sxyz q := fun _ => rfl
  have hs' : ∀ q : Site, sxyz (τw.symm q) = sxyz q := fun _ => rfl
  have h1 : ((sxyz p : ℝ) : ℂ) * (sxyz p : ℂ) = 1 := by exact_mod_cast sxyz_mul_self p
  simp only [Mw, Tw, hop_apply, hs, hs', Pi.one_apply, Complex.ofReal_one, one_mul]
  linear_combination ((χ (τw (τw p)) + χ (τw.symm (τw p)) +
    (χ (τw (τw.symm p)) + χ (τw.symm (τw.symm p)))) / 4) * h1

theorem norm_sq_eq_re_inner {X : H →ₗ[ℂ] H} (hX : X.IsSymmetric) (χ : H) :
    ‖X χ‖ ^ 2 = (inner ℂ χ (X (X χ))).re := by
  rw [← hX]
  have := inner_self_eq_norm_sq (𝕜 := ℂ) (X χ)
  simpa only [RCLike.re_to_complex] using this.symm

/-- **The fiber gap**: `‖T°_w χ‖² ≥ ‖χ‖²/4` for every state. -/
theorem norm_sq_fiber_ge (χ : H) : (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖Tw χ‖ ^ 2 :=
  DiracSpeed.norm_sq_ge_of_sq_eq Tw_isSymmetric Tw_sq χ

/-- **The rest of `D` is never smaller than the mass `1/2`**: `‖Bχ‖² ≥ ‖χ‖²/4`. -/
theorem norm_sq_rest_ge (χ : H) : (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖rest χ‖ ^ 2 := by
  have h := DiracSpeed.norm_sq_add_of_anticomm AyAz_isSymmetric Mw_isSymmetric AyAz_Mw χ
  have hM : ‖Mw χ‖ ^ 2 = ‖Tw χ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner Mw_isSymmetric, norm_sq_eq_re_inner Tw_isSymmetric, Mw_sq]
  have hr : rest χ = (Ay + Az) χ + Mw χ := rfl
  rw [hr, h, hM]
  nlinarith only [norm_sq_fiber_ge χ, sq_nonneg ‖(Ay + Az) χ‖]

/-! ## 4. Mass gap and speed limit -/

/-- **The mass gap of `ℤ³ × w`**: every eigenvalue of `D` has `|E| ≥ 1/2`. -/
theorem abs_energy_ge {E : ℝ} {χ : H} (hχ : χ ≠ 0) (hE : dirac χ = (E : ℂ) • χ) :
    1 / 2 ≤ |E| := by
  have h := DiracSpeed.abs_energy_ge Tx_isSymmetric rest_isSymmetric Tx_rest
    (m := 1 / 2) norm_sq_rest_ge hχ hE
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h

/-- **Spin `1/2`, speed `1/φ`, on the infinite lattice `ℤ³ × w`**: every unit eigenvector of
`D` moves along `x` at most at `1/φ`. -/
theorem abs_velocity_le_inv_goldenRatio {E : ℝ} {ψ : H} (hψ : ‖ψ‖ = 1)
    (hE : dirac ψ = (E : ℂ) • ψ) : |(inner ℂ ψ (Kx ψ)).re| ≤ Real.goldenRatio⁻¹ := by
  rw [← DiracSpeed.speedLimit_half (m := 1 / 2) (by norm_num)]
  exact DiracSpeed.abs_velocity_le Tx_isSymmetric rest_isSymmetric Kx_isSymmetric
    (hop_cur τx) Kx_rest Tx_rest (cur_sq_add_hop_sq τx) (by norm_num) norm_sq_rest_ge hψ hE

/-- **With the lattice spacing `a > 0`**, kept as the resolution and never sent to zero: the
physical velocity `a ⟨K_x⟩` is at most `a/φ`. -/
theorem abs_physical_velocity_le {a E : ℝ} (ha : 0 < a) {ψ : H} (hψ : ‖ψ‖ = 1)
    (hE : dirac ψ = (E : ℂ) • ψ) :
    |a * (inner ℂ ψ (Kx ψ)).re| ≤ a * Real.goldenRatio⁻¹ := by
  rw [abs_mul, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left (abs_velocity_le_inv_goldenRatio hψ hE) ha.le

end LatticeFiberDirac
