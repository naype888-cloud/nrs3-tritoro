/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusFiberDirac
public import NRS3Tritoro.DiracSpeed
public import NRS3Tritoro.FiberDiracAxis

/-!
# The mass gap `1/2` and the speed limit `1/φ` on `T³ × w`

The fiber transport has the eigenvalues `1` and `−1/2`, so `T°_w² = (1 + T°_w)/2` and
`‖T°_w χ‖² ≥ ‖χ‖²/4` for every state of `T³ × w`. The rest `B = A_y + A_z + M_w` of `D` splits
into two anticommuting parts, `‖Bχ‖² = ‖(A_y + A_z)χ‖² + ‖M_w χ‖² ≥ ‖T°_w χ‖²`, so `B` is never
smaller than the mass `1/2`, and `DiracSpeed` applies:

* **mass gap**: every eigenvalue of `D` has `|E| ≥ 1/2`; in the rotating mode of the fiber the
  eight doublers of `T³` reach it, `E = −1/2` (and `+1/2`).
* **speed limit**: a unit eigenvector of `D` and of `T_x²` moves along `x` at most at
  `√(5/4) − 1/2 = 1/φ`. `T_x²` commutes with `D`, so every eigenspace of `D` has a basis of such
  states.

Both hold for every state, not only for products with a fiber mode.

## Main results

- `TorusFiberDirac.norm_sq_fiber_ge` : `‖T°_w χ‖² ≥ ‖χ‖²/4`.
- `TorusFiberDirac.norm_sq_rest_ge` : `‖Bχ‖² ≥ ‖χ‖²/4`.
- `TorusFiberDirac.abs_energy_ge` : `|E| ≥ 1/2` for every eigenvalue of `D`.
- `TorusFiberDirac.dirac_Tx_sq` : `T_x²` commutes with `D`.
- `TorusFiberDirac.abs_velocity_le_inv_goldenRatio` : `|⟨K_x⟩| ≤ 1/φ`.
- `TorusFiberDirac.dirac_tensor` : `D (ψ ⊗ v) = (D_λ ψ) ⊗ v`, `D_λ` of `TorusDirac3`.
- `TorusFiberDirac.dirac_doublers` : the doublers in the rotating mode have energy `−1/2`.
-/

@[expose] public noncomputable section

open Complex SiteHop

namespace TorusFiberDirac

variable {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]

/-! ## 1. The fiber gap -/

omit [NeZero a] [NeZero b] [NeZero c] in
/-- On the ring of three, `T°_w² = (1 + T°_w)/2`. -/
theorem Tw_sq (χ : HT a b c) : Tw (Tw χ) = ((1 / 2 : ℝ) : ℂ) • (χ + Tw χ) := by
  ext ⟨x, y, z, w⟩
  have e1 : (w + 1 + 1 : ZMod 3) = w - 1 := by
    rw [add_assoc, sub_eq_add_neg]; congr 1
  have e2 : (w - 1 - 1 : ZMod 3) = w + 1 := by
    rw [sub_sub, sub_eq_add_neg]; congr 1
  simp only [Tw, hop_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Pi.one_apply,
    Complex.ofReal_one, one_mul, τw_apply, τw_symm_apply, add_sub_cancel_right, sub_add_cancel,
    e1, e2]
  push_cast
  ring

omit [NeZero a] [NeZero b] [NeZero c] in
theorem sxyz_mul_self (p : Site a b c) : sxyz p * sxyz p = 1 := by
  have h : ∀ n : ℕ, ((-1 : ℝ) ^ n) ^ 2 = 1 := fun n => by rw [sq, ← mul_pow]; norm_num
  simp only [sxyz]
  linear_combination ((-1 : ℝ) ^ p.2.1.val) ^ 2 * ((-1 : ℝ) ^ p.2.2.1.val) ^ 2 * h p.1.val +
    ((-1 : ℝ) ^ p.2.2.1.val) ^ 2 * h p.2.1.val + h p.2.2.1.val

omit [NeZero a] [NeZero b] [NeZero c] in
/-- The sign does not change the square of the fiber term: `M_w² = T°_w²`. -/
theorem Mw_sq (χ : HT a b c) : Mw (Mw χ) = Tw (Tw χ) := by
  ext p
  have hs : ∀ q : Site a b c, sxyz (τw q) = sxyz q := fun _ => rfl
  have hs' : ∀ q : Site a b c, sxyz (τw.symm q) = sxyz q := fun _ => rfl
  have h1 : ((sxyz p : ℝ) : ℂ) * (sxyz p : ℂ) = 1 := by exact_mod_cast sxyz_mul_self p
  simp only [Mw, Tw, hop_apply, hs, hs', Pi.one_apply, Complex.ofReal_one, one_mul]
  linear_combination ((χ (τw (τw p)) + χ (τw.symm (τw p)) +
    (χ (τw (τw.symm p)) + χ (τw.symm (τw.symm p)))) / 4) * h1

theorem norm_sq_eq_re_inner {X : HT a b c →ₗ[ℂ] HT a b c} (hX : X.IsSymmetric) (χ : HT a b c) :
    ‖X χ‖ ^ 2 = (inner ℂ χ (X (X χ))).re := by
  rw [← hX]
  have := inner_self_eq_norm_sq (𝕜 := ℂ) (X χ)
  simpa only [RCLike.re_to_complex] using this.symm

/-- **The fiber gap**: `‖T°_w χ‖² ≥ ‖χ‖²/4` for every state. -/
theorem norm_sq_fiber_ge (χ : HT a b c) : (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖Tw χ‖ ^ 2 := by
  have hN : (inner ℂ χ χ).re = ‖χ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) χ
  set t := (inner ℂ χ (Tw χ)).re
  have hT2 : ‖Tw χ‖ ^ 2 = 1 / 2 * (‖χ‖ ^ 2 + t) := by
    rw [norm_sq_eq_re_inner Tw_isSymmetric, Tw_sq, inner_smul_right, Complex.re_ofReal_mul,
      inner_add_right, Complex.add_re, hN]
  have hpos := sq_nonneg ‖Tw χ + ((1 / 2 : ℝ) : ℂ) • χ‖
  rw [norm_add_sq (𝕜 := ℂ), norm_smul, Complex.norm_real, inner_smul_right,
    RCLike.re_to_complex, Complex.re_ofReal_mul, Tw_isSymmetric] at hpos
  norm_num at hpos
  nlinarith only [hpos, hT2]

/-- The fiber term keeps the norm of the fiber transport. -/
theorem norm_sq_Mw (χ : HT a b c) : ‖Mw χ‖ ^ 2 = ‖Tw χ‖ ^ 2 := by
  rw [norm_sq_eq_re_inner Mw_isSymmetric, norm_sq_eq_re_inner Tw_isSymmetric, Mw_sq]

/-- **The rest of `D` is never smaller than the mass `1/2`**: `‖Bχ‖² ≥ ‖χ‖²/4`. -/
theorem norm_sq_rest_ge (hb : 2 ∣ b) (hc : 2 ∣ c) (χ : HT a b c) :
    (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖rest χ‖ ^ 2 := by
  have hs : (Ay + Az : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
    (hop_isSymmetric _ fun _ => rfl).add (hop_isSymmetric _ fun _ => rfl)
  have h := DiracSpeed.norm_sq_add_of_anticomm hs Mw_isSymmetric (AyAz_Mw hb hc) χ
  have hr : rest χ = (Ay + Az : HT a b c →ₗ[ℂ] HT a b c) χ + Mw χ := rfl
  rw [hr, h, norm_sq_Mw]
  nlinarith only [norm_sq_fiber_ge χ, sq_nonneg ‖(Ay + Az : HT a b c →ₗ[ℂ] HT a b c) χ‖]

/-! ## 2. Mass gap and speed limit -/

/-- **The mass gap of `T³ × w`**: every eigenvalue of `D` has `|E| ≥ 1/2`. -/
theorem abs_energy_ge (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c) {E : ℝ} {χ : HT a b c}
    (hχ : χ ≠ 0) (hE : dirac χ = (E : ℂ) • χ) : 1 / 2 ≤ |E| := by
  have h := DiracSpeed.abs_energy_ge Tx_isSymmetric rest_isSymmetric (Tx_rest ha)
    (m := 1 / 2) (norm_sq_rest_ge hb hc) hχ hE
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h

omit [NeZero b] [NeZero c] in
/-- `T_x²` commutes with `D`. -/
theorem dirac_Tx_sq (ha : 2 ∣ a) (χ : HT a b c) : dirac (Tx (Tx χ)) = Tx (Tx (dirac χ)) := by
  have h : ∀ η : HT a b c, rest (Tx η) = -Tx (rest η) := fun η => by rw [Tx_rest ha, neg_neg]
  simp only [dirac, LinearMap.add_apply, map_add, h, map_neg, neg_neg]

/-- **Spin `1/2`, speed `1/φ`, on `T³ × w`**: a unit eigenvector of `D` and of `T_x²` moves
along `x` at most at `1/φ`. -/
theorem abs_velocity_le_inv_goldenRatio (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c) {E t : ℝ}
    {ψ : HT a b c} (hψ : ‖ψ‖ = 1) (hE : dirac ψ = (E : ℂ) • ψ) (hT : Tx (Tx ψ) = (t : ℂ) • ψ) :
    |(inner ℂ ψ (Kx ψ)).re| ≤ Real.goldenRatio⁻¹ := by
  rw [← TorusUniverse.speedLimit_half (m := 1 / 2) (by norm_num)]
  exact DiracSpeed.abs_velocity_le Tx_isSymmetric rest_isSymmetric Kx_isSymmetric
    (hop_cur τx) (Kx_rest ha) (Tx_rest ha) (cur_sq_add_hop_sq τx) (by norm_num)
    (norm_sq_rest_ge hb hc) hψ hE hT

/-! ## 3. Products with a fiber mode, and the doublers -/

/-- The product `ψ ⊗ v` of a state of `T³` and a state of the fiber. -/
def tensor (ψ : TorusDirac3.H3 a b c) (v : TorusUniverse.HU 3) : HT a b c :=
  WithLp.toLp 2 fun p => ψ (p.1, p.2.1, p.2.2.1) * v p.2.2.2

omit [NeZero a] [NeZero b] [NeZero c] in
theorem tensor_smul (s : ℂ) (ψ : TorusDirac3.H3 a b c) (v : TorusUniverse.HU 3) :
    tensor (s • ψ) v = s • tensor ψ v := by
  ext p; simp only [tensor, PiLp.smul_apply, smul_eq_mul]; ring

omit [NeZero a] [NeZero b] [NeZero c] in
/-- **A fiber mode is a mass on `T³`**: `D (ψ ⊗ v) = (D_λ ψ) ⊗ v` if `T°_w v = λ v`. -/
theorem dirac_tensor {lam : ℝ} {v : TorusUniverse.HU 3}
    (hv : TorusUniverse.transport v = (lam : ℂ) • v) (ψ : TorusDirac3.H3 a b c) :
    dirac (tensor ψ v) = tensor (TorusDirac3.dirac3 lam ψ) v := by
  ext ⟨x, y, z, w⟩
  have hk : (v (w + 1) + v (w - 1)) / 2 = lam * v w := by
    simpa [TorusUniverse.transport_apply] using congrArg (fun χ : TorusUniverse.HU 3 => χ w) hv
  simp only [dirac, rest, Tx, Ay, Az, Mw, LinearMap.add_apply, PiLp.add_apply, hop_apply,
    τx_apply, τx_symm_apply, τy_apply, τy_symm_apply, τz_apply, τz_symm_apply, τw_apply,
    τw_symm_apply, tensor, TorusDirac3.dirac3, LinearMap.smul_apply, PiLp.smul_apply,
    smul_eq_mul, TorusDirac3.Tx_apply, TorusDirac3.Ay_apply, TorusDirac3.Az_apply,
    TorusDirac3.eps_apply, TorusDirac3.sg, sx, sxy, sxyz, Pi.one_apply]
  push_cast
  linear_combination ((-1) ^ x.val * (-1) ^ y.val * (-1) ^ z.val * ψ (x, y, z)) * hk

/-- **The doublers reach the gap**: in the rotating mode of the fiber, a pair of opposite
doublers of `T³` has energy `−1/2` (and `e − e'` has `+1/2`). -/
theorem dirac_doublers (ha : 4 ∣ a) (hb : 4 ∣ b) (hc : 4 ∣ c) {u v w : ℂ}
    (hu : u = I ∨ u = -I) (hv : v = I ∨ v = -I) (hw : w = I ∨ w = -I) :
    dirac (tensor (TorusDirac3.wave3 u v w + TorusDirac3.wave3 (-u) (-v) (-w) :
        TorusDirac3.H3 a b c) FiberDiracAxis.rotating) =
      ((-1 / 2 : ℝ) : ℂ) • tensor (TorusDirac3.wave3 u v w + TorusDirac3.wave3 (-u) (-v) (-w))
        FiberDiracAxis.rotating := by
  rw [dirac_tensor FiberDiracAxis.transport_rotating,
    TorusDirac3.dirac3_pair_add ha hb hc hu hv hw, tensor_smul]

end TorusFiberDirac
