/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusFiberDirac
public import NRS3Tritoro.TorusDirac3
public import NRS3Tritoro.FiberDiracAxis

/-!
# The doublers of `T³` reach the mass gap of `T³ × w`

On a product `ψ ⊗ v` with a fiber mode `T°_w v = λ v` the Dirac operator of `T³ × w` is the
massive Dirac operator of `T³` (`TorusDirac3`) with mass `λ`. In the rotating mode, `λ = −1/2`,
a pair of opposite doublers has energy `−1/2`: the gap `1/2` of `TorusFiberGap` is reached.

## Main results

- `TorusFiberDirac.dirac_tensor` : `D (ψ ⊗ v) = (D_λ ψ) ⊗ v`.
- `TorusFiberDirac.dirac_doublers` : the doublers in the rotating mode have energy `−1/2`.
-/

@[expose] public noncomputable section

open Complex SiteHop

namespace TorusFiberDirac

variable {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]

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
