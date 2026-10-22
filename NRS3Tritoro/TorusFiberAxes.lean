/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusFiberGap

/-!
# The speed limit `1/φ` on the three axes of `T³ × w`

`TorusFiberGap` bounds the velocity along `x`. Along `y` and `z` the transport carries the
staggered sign, `A_y = (−1)^x T_y`, `A_z = (−1)^(x+y) T_z`, and so does the velocity:
`V_y = (−1)^x K_y`, `V_z = (−1)^(x+y) K_z` (the current `i[D, Y]`, `i[D, Z]` of the Dirac
operator). Split `D` along each axis,

  `D = A_y + (T_x + A_z + M_w)`,  `D = A_z + (T_x + A_y + M_w)`.

In each split the velocity commutes with its transport, `V² + A² = 1`, and both anticommute with
the rest, which still contains the fiber term and is never smaller than the mass `1/2`. So
`DiracSpeed` applies on every axis: every unit eigenvector of `D` moves at most at `1/φ` along
`x`, along `y` and along `z`.

## Main results

- `TorusFiberDirac.abs_velocity_y_le_inv_goldenRatio` : `|⟨V_y⟩| ≤ 1/φ`.
- `TorusFiberDirac.abs_velocity_z_le_inv_goldenRatio` : `|⟨V_z⟩| ≤ 1/φ`.
- `TorusFiberDirac.abs_velocity_le_inv_goldenRatio_axes` : the three axes at once.
-/

@[expose] public noncomputable section

open Complex SiteHop

namespace TorusFiberDirac

variable {a b c : ℕ}

/-! ## 1. Velocities and the signs they need -/

/-- The velocity along `y`, `(−1)^x K_y`. -/
def Vy : HT a b c →ₗ[ℂ] HT a b c := curw τy sx

/-- The velocity along `z`, `(−1)^(x+y) K_z`. -/
def Vz : HT a b c →ₗ[ℂ] HT a b c := curw τz sxy

theorem sxy_τy [NeZero b] (hb : 2 ∣ b) (p : Site a b c) : sxy (τy p) = -sxy p := by
  show (-1 : ℝ) ^ p.1.val * (-1) ^ (p.2.1 + 1).val = -((-1) ^ p.1.val * (-1) ^ p.2.1.val)
  rw [neg_one_pow_add_one hb]; ring

theorem sxy_τy_symm [NeZero b] (hb : 2 ∣ b) (p : Site a b c) : sxy (τy.symm p) = -sxy p := by
  show (-1 : ℝ) ^ p.1.val * (-1) ^ (p.2.1 - 1).val = -((-1) ^ p.1.val * (-1) ^ p.2.1.val)
  rw [neg_one_pow_sub_one hb]; ring

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow]; norm_num

theorem sx_mul_self (p : Site a b c) : sx p * sx p = 1 := neg_one_pow_mul_self _

theorem sxy_mul_self (p : Site a b c) : sxy p * sxy p = 1 := by
  simp only [sxy]
  linear_combination ((-1 : ℝ) ^ p.2.1.val * (-1) ^ p.2.1.val) *
    neg_one_pow_mul_self p.1.val + neg_one_pow_mul_self p.2.1.val

/-- Anticommutation read the other way round. -/
theorem anticomm_symm {f g : HT a b c →ₗ[ℂ] HT a b c} (h : ∀ χ, f (g χ) = -g (f χ)) (χ) :
    g (f χ) = -f (g χ) := by
  rw [h, neg_neg]

/-- An operator that anticommutes with three operators anticommutes with their sum. -/
theorem anticomm_add₃ {f g₁ g₂ g₃ : HT a b c →ₗ[ℂ] HT a b c} (h₁ : ∀ χ, f (g₁ χ) = -g₁ (f χ))
    (h₂ : ∀ χ, f (g₂ χ) = -g₂ (f χ)) (h₃ : ∀ χ, f (g₃ χ) = -g₃ (f χ)) (χ) :
    f ((g₁ + g₂ + g₃) χ) = -(g₁ + g₂ + g₃) (f χ) := by
  simp only [LinearMap.add_apply, map_add, h₁, h₂, h₃]
  abel

/-- An operator that anticommutes with two operators anticommutes with their sum. -/
theorem anticomm_add₂ {f g₁ g₂ : HT a b c →ₗ[ℂ] HT a b c} (h₁ : ∀ χ, g₁ (f χ) = -f (g₁ χ))
    (h₂ : ∀ χ, g₂ (f χ) = -f (g₂ χ)) (χ) : (g₁ + g₂) (f χ) = -f ((g₁ + g₂) χ) := by
  simp only [LinearMap.add_apply, map_add, h₁, h₂]
  abel

/-! ## 2. The axis `y` -/

section AxisY

variable [NeZero a] [NeZero b] [NeZero c] (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c)

/-- The rest of `D` along `y`. -/
def restY : HT a b c →ₗ[ℂ] HT a b c := Tx + Az + Mw

omit [NeZero a] [NeZero b] [NeZero c] in
theorem dirac_eq_y (χ : HT a b c) : dirac χ = Ay χ + restY χ := by
  simp only [dirac, rest, restY, LinearMap.add_apply]; abel

include ha hb hc in
/-- **`|⟨V_y⟩| ≤ 1/φ`** for every unit eigenvector of `D`. -/
theorem abs_velocity_y_le_inv_goldenRatio {E : ℝ} {ψ : HT a b c} (hψ : ‖ψ‖ = 1)
    (hE : dirac ψ = (E : ℂ) • ψ) : |(inner ℂ ψ (Vy ψ)).re| ≤ Real.goldenRatio⁻¹ := by
  have hAy : (Ay : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := hop_isSymmetric _ fun _ => rfl
  have hAz : (Az : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := hop_isSymmetric _ fun _ => rfl
  have hB : (restY : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
    (Tx_isSymmetric.add hAz).add Mw_isSymmetric
  have hV : (Vy : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := curw_isSymmetric _ fun _ => rfl
  have hAV : ∀ χ : HT a b c, Ay (Vy χ) = Vy (Ay χ) :=
    hop_curw τy (fun _ => rfl) (fun _ => rfl)
  have hVB : ∀ χ : HT a b c, Vy (restY χ) = -restY (Vy χ) :=
    anticomm_add₃ (f := Vy) (g₁ := Tx) (g₂ := Az) (g₃ := Mw)
      (anticomm_symm (hop_curw_anticomm (τ := τx) (σ := τy) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sx_τx ha) (sx_τx_symm ha)))
      (curw_hop_anticomm (τ := τy) (σ := τz) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sxy_τy hb) (sxy_τy_symm hb))
      (curw_hop_anticomm (τ := τy) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sxyz_τy hb) (sxyz_τy_symm hb))
  have hAB : ∀ χ : HT a b c, Ay (restY χ) = -restY (Ay χ) :=
    anticomm_add₃ (f := Ay) (g₁ := Tx) (g₂ := Az) (g₃ := Mw)
      (anticomm_symm (hop_hop_anticomm (τ := τx) (σ := τy) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sx_τx ha) (sx_τx_symm ha)))
      (hop_hop_anticomm (τ := τy) (σ := τz) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sxy_τy hb) (sxy_τy_symm hb))
      (hop_hop_anticomm (τ := τy) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sxyz_τy hb) (sxyz_τy_symm hb))
  have hVV : ∀ χ : HT a b c, Vy (Vy χ) + Ay (Ay χ) = χ :=
    curw_sq_add_hop_sq τy (fun _ => rfl) (fun _ => rfl) sx_mul_self
  -- the rest is never smaller than the mass
  have hTA : (Tx + Az : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := Tx_isSymmetric.add hAz
  have hMw : ∀ χ : HT a b c, (Tx + Az : HT a b c →ₗ[ℂ] HT a b c) (Mw χ) =
      -Mw ((Tx + Az : HT a b c →ₗ[ℂ] HT a b c) χ) :=
    anticomm_add₂ (f := Mw) (g₁ := Tx) (g₂ := Az)
      (hop_hop_anticomm (τ := τx) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sxyz_τx ha) (sxyz_τx_symm ha))
      (hop_hop_anticomm (τ := τz) (σ := τw) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (sxyz_τz hc) (sxyz_τz_symm hc))
  have hBm : ∀ χ : HT a b c, (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖restY χ‖ ^ 2 := fun χ => by
    have h := DiracSpeed.norm_sq_add_of_anticomm hTA Mw_isSymmetric hMw χ
    have hr : restY χ = (Tx + Az : HT a b c →ₗ[ℂ] HT a b c) χ + Mw χ := rfl
    rw [hr, h, norm_sq_Mw]
    nlinarith only [norm_sq_fiber_ge χ, sq_nonneg ‖(Tx + Az : HT a b c →ₗ[ℂ] HT a b c) χ‖]
  rw [← DiracSpeed.speedLimit_half (m := 1 / 2) (by norm_num)]
  exact DiracSpeed.abs_velocity_le hAy hB hV hAV hVB hAB hVV (by norm_num) hBm hψ
    (by rw [← dirac_eq_y]; exact hE)

end AxisY

/-! ## 3. The axis `z` -/

section AxisZ

variable [NeZero a] [NeZero b] [NeZero c] (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c)

/-- The rest of `D` along `z`. -/
def restZ : HT a b c →ₗ[ℂ] HT a b c := Tx + Ay + Mw

omit [NeZero a] [NeZero b] [NeZero c] in
theorem dirac_eq_z (χ : HT a b c) : dirac χ = Az χ + restZ χ := by
  simp only [dirac, rest, restZ, LinearMap.add_apply]; abel

include ha hb hc in
/-- **`|⟨V_z⟩| ≤ 1/φ`** for every unit eigenvector of `D`. -/
theorem abs_velocity_z_le_inv_goldenRatio {E : ℝ} {ψ : HT a b c} (hψ : ‖ψ‖ = 1)
    (hE : dirac ψ = (E : ℂ) • ψ) : |(inner ℂ ψ (Vz ψ)).re| ≤ Real.goldenRatio⁻¹ := by
  have hAy : (Ay : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := hop_isSymmetric _ fun _ => rfl
  have hAz : (Az : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := hop_isSymmetric _ fun _ => rfl
  have hB : (restZ : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
    (Tx_isSymmetric.add hAy).add Mw_isSymmetric
  have hV : (Vz : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := curw_isSymmetric _ fun _ => rfl
  have hAV : ∀ χ : HT a b c, Az (Vz χ) = Vz (Az χ) :=
    hop_curw τz (fun _ => rfl) (fun _ => rfl)
  have hVB : ∀ χ : HT a b c, Vz (restZ χ) = -restZ (Vz χ) :=
    anticomm_add₃ (f := Vz) (g₁ := Tx) (g₂ := Ay) (g₃ := Mw)
      (anticomm_symm (hop_curw_anticomm (τ := τx) (σ := τz)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxy_τx ha) (sxy_τx_symm ha)))
      (anticomm_symm (hop_curw_anticomm (τ := τy) (σ := τz)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxy_τy hb) (sxy_τy_symm hb)))
      (curw_hop_anticomm (τ := τz) (σ := τw)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxyz_τz hc) (sxyz_τz_symm hc))
  have hAB : ∀ χ : HT a b c, Az (restZ χ) = -restZ (Az χ) :=
    anticomm_add₃ (f := Az) (g₁ := Tx) (g₂ := Ay) (g₃ := Mw)
      (anticomm_symm (hop_hop_anticomm (τ := τx) (σ := τz)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxy_τx ha) (sxy_τx_symm ha)))
      (anticomm_symm (hop_hop_anticomm (τ := τy) (σ := τz)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxy_τy hb) (sxy_τy_symm hb)))
      (hop_hop_anticomm (τ := τz) (σ := τw)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxyz_τz hc) (sxyz_τz_symm hc))
  have hVV : ∀ χ : HT a b c, Vz (Vz χ) + Az (Az χ) = χ :=
    curw_sq_add_hop_sq τz (fun _ => rfl) (fun _ => rfl) sxy_mul_self
  -- the rest is never smaller than the mass
  have hTA : (Tx + Ay : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric := Tx_isSymmetric.add hAy
  have hMw : ∀ χ : HT a b c, (Tx + Ay : HT a b c →ₗ[ℂ] HT a b c) (Mw χ) =
      -Mw ((Tx + Ay : HT a b c →ₗ[ℂ] HT a b c) χ) :=
    anticomm_add₂ (f := Mw) (g₁ := Tx) (g₂ := Ay)
      (hop_hop_anticomm (τ := τx) (σ := τw)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxyz_τx ha) (sxyz_τx_symm ha))
      (hop_hop_anticomm (τ := τy) (σ := τw)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (sxyz_τy hb) (sxyz_τy_symm hb))
  have hBm : ∀ χ : HT a b c, (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖restZ χ‖ ^ 2 := fun χ => by
    have h := DiracSpeed.norm_sq_add_of_anticomm hTA Mw_isSymmetric hMw χ
    have hr : restZ χ = (Tx + Ay : HT a b c →ₗ[ℂ] HT a b c) χ + Mw χ := rfl
    rw [hr, h, norm_sq_Mw]
    nlinarith only [norm_sq_fiber_ge χ, sq_nonneg ‖(Tx + Ay : HT a b c →ₗ[ℂ] HT a b c) χ‖]
  rw [← DiracSpeed.speedLimit_half (m := 1 / 2) (by norm_num)]
  exact DiracSpeed.abs_velocity_le hAz hB hV hAV hVB hAB hVV (by norm_num) hBm hψ
    (by rw [← dirac_eq_z]; exact hE)

end AxisZ

/-- **The speed limit on the three axes of `T³ × w`**: every unit eigenvector of `D` moves at
most at `1/φ` along `x`, along `y` and along `z`. -/
theorem abs_velocity_le_inv_goldenRatio_axes [NeZero a] [NeZero b] [NeZero c] (ha : 2 ∣ a)
    (hb : 2 ∣ b) (hc : 2 ∣ c) {E : ℝ} {ψ : HT a b c} (hψ : ‖ψ‖ = 1)
    (hE : dirac ψ = (E : ℂ) • ψ) :
    |(inner ℂ ψ (Kx ψ)).re| ≤ Real.goldenRatio⁻¹ ∧
      |(inner ℂ ψ (Vy ψ)).re| ≤ Real.goldenRatio⁻¹ ∧
      |(inner ℂ ψ (Vz ψ)).re| ≤ Real.goldenRatio⁻¹ :=
  ⟨abs_velocity_le_inv_goldenRatio ha hb hc hψ hE,
    abs_velocity_y_le_inv_goldenRatio ha hb hc hψ hE,
    abs_velocity_z_le_inv_goldenRatio ha hb hc hψ hE⟩

end TorusFiberDirac
