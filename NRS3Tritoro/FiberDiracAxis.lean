/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusDiracBound
public import NRS3Hopf.ClosedThree

/-!
# The fiber feeds the mass of the axis: spin `1/2`, speed `1/φ`

Put the fiber `w`, the closed ring of three positions, over the axis of the universe `ZMod L`
(`L` even). The fiber is the axis `ZMod 3` with the same transport, every link alike; it is the
`T°` of `ClosedThree` (`transport_three_eq_TcOp`). Three is odd, so the staggered sign cannot
alternate on it, and the fiber enters as the mass, as in `FiberDirac`:

  `(Dχ)_{j,k} = (T°_axis χ)_{j,k} + (−1)^j (T°_fiber χ)_{j,k}`,  `D² = T°_axis² + T°_fiber²`.

On a product `ψ ⊗ v` with `T°_fiber v = λ v` the operator is the massive Dirac operator of the
axis, `D (ψ ⊗ v) = (D_λ ψ) ⊗ v`. The fiber has the uniform mode, `λ = 1`, and the rotating
modes of its conserved rotation, `λ = −1/2`. So a stationary state in a rotating mode of the fiber
is a Dirac state of mass `1/2` on the axis, and `TorusUniverse.abs_velocity_le_inv_goldenRatio`
bounds its speed by `1/φ`; in the uniform mode the mass is `1` and the speed at most `√2 − 1`.

## Main results

- `FiberDiracAxis.transport_three_eq_TcOp` : the fiber is the ring `T°` of `ClosedThree`.
- `FiberDiracAxis.dirac_sq` : `D² = T°_axis² + T°_fiber²`.
- `FiberDiracAxis.dirac_tensor` : `D (ψ ⊗ v) = (D_λ ψ) ⊗ v` for a fiber mode `v`.
- `FiberDiracAxis.transport_uniform`, `FiberDiracAxis.transport_rotating` : `λ = 1` and
  `λ = −1/2`.
- `FiberDiracAxis.abs_velocity_le_inv_goldenRatio_of_rotating` : rotating mode, speed `≤ 1/φ`.
- `FiberDiracAxis.abs_velocity_le_sqrt_two_sub_one_of_uniform` : uniform mode, speed `≤ √2 − 1`.
-/

@[expose] public noncomputable section

open Complex TorusUniverse

namespace FiberDiracAxis

variable {L : ℕ}

/-! ## 1. The fiber -/

/-- The fiber is the closed transport of `ClosedThree`. -/
theorem transport_three_eq_TcOp (v : HU 3) : transport v = ClosedThree.TcOp v := by
  obtain ⟨h0, h1, h2⟩ := ClosedThree.TcOp_apply v
  ext k
  fin_cases k
  · exact (transport_apply v 0).trans (Eq.trans (by rfl) h0.symm)
  · exact (transport_apply v 1).trans ((congrArg (· / 2) (add_comm _ _)).trans h1.symm)
  · exact (transport_apply v 2).trans (Eq.trans (by rfl) h2.symm)

/-- The uniform mode of the fiber. -/
def uniform : HU 3 := WithLp.toLp 2 fun _ => 1

/-- A rotating mode of the fiber. -/
def rotating : HU 3 := WithLp.toLp 2 ![1, -1, 0]

/-- The uniform mode has mass `1`. -/
theorem transport_uniform : transport uniform = ((1 : ℝ) : ℂ) • uniform := by
  ext k
  simp [transport_apply, uniform]

/-- The rotating mode has mass `−1/2`. -/
theorem transport_rotating : transport rotating = ((-1 / 2 : ℝ) : ℂ) • rotating := by
  ext k
  fin_cases k
  · show ((-1 : ℂ) + 0) / 2 = ((-1 / 2 : ℝ) : ℂ) * 1
    push_cast; ring
  · show ((0 : ℂ) + 1) / 2 = ((-1 / 2 : ℝ) : ℂ) * (-1)
    push_cast; ring
  · show ((1 : ℂ) + -1) / 2 = ((-1 / 2 : ℝ) : ℂ) * 0
    push_cast; ring

/-! ## 2. The axis with the fiber -/

/-- The states on the axis with the fiber. -/
abbrev HF (L : ℕ) := EuclideanSpace ℂ (ZMod L × ZMod 3)

/-- The Dirac operator of the axis with the fiber in the place of the mass,
`(Dχ)_{j,k} = (χ_{j+1,k} + χ_{j−1,k})/2 + (−1)^j (χ_{j,k+1} + χ_{j,k−1})/2`. -/
def dirac : HF L →ₗ[ℂ] HF L where
  toFun χ := WithLp.toLp 2 fun p =>
    (χ (p.1 + 1, p.2) + χ (p.1 - 1, p.2)) / 2 +
      (-1) ^ p.1.val * ((χ (p.1, p.2 + 1) + χ (p.1, p.2 - 1)) / 2)
  map_add' χ η := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' s χ := by
    ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The transport of the axis. -/
def axisT : HF L →ₗ[ℂ] HF L where
  toFun χ := WithLp.toLp 2 fun p => (χ (p.1 + 1, p.2) + χ (p.1 - 1, p.2)) / 2
  map_add' χ η := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' s χ := by
    ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The transport of the fiber. -/
def fiberT : HF L →ₗ[ℂ] HF L where
  toFun χ := WithLp.toLp 2 fun p => (χ (p.1, p.2 + 1) + χ (p.1, p.2 - 1)) / 2
  map_add' χ η := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' s χ := by
    ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem dirac_apply (χ : HF L) (j : ZMod L) (k : ZMod 3) :
    dirac χ (j, k) = (χ (j + 1, k) + χ (j - 1, k)) / 2 +
      (-1) ^ j.val * ((χ (j, k + 1) + χ (j, k - 1)) / 2) := rfl

theorem axisT_apply (χ : HF L) (j : ZMod L) (k : ZMod 3) :
    axisT χ (j, k) = (χ (j + 1, k) + χ (j - 1, k)) / 2 := rfl

theorem fiberT_apply (χ : HF L) (j : ZMod L) (k : ZMod 3) :
    fiberT χ (j, k) = (χ (j, k + 1) + χ (j, k - 1)) / 2 := rfl

/-- **The fiber is the mass**: `D² = T°_axis² + T°_fiber²`. -/
theorem dirac_sq [NeZero L] (h2 : 2 ∣ L) (χ : HF L) :
    dirac (dirac χ) = axisT (axisT χ) + fiberT (fiberT χ) := by
  ext ⟨j, k⟩
  have hs : ((-1 : ℂ) ^ j.val) ^ 2 = 1 := by rw [sq, ← mul_pow]; norm_num
  simp only [dirac_apply, axisT_apply, fiberT_apply, PiLp.add_apply, add_sub_cancel_right,
    sub_add_cancel, neg_one_pow_val_add_one h2, neg_one_pow_val_sub_one h2]
  linear_combination ((χ (j, k + 1 + 1) + χ (j, k) + (χ (j, k) + χ (j, k - 1 - 1))) / 4) * hs

/-! ## 3. Fiber modes give the mass of the axis -/

/-- The product `ψ ⊗ v`. -/
def tensor (ψ : HU L) (v : HU 3) : HF L := WithLp.toLp 2 fun p => ψ p.1 * v p.2

theorem tensor_apply (ψ : HU L) (v : HU 3) (j : ZMod L) (k : ZMod 3) :
    tensor ψ v (j, k) = ψ j * v k := rfl

/-- **A fiber mode is a mass on the axis**: if `T°_fiber v = λ v`, then
`D (ψ ⊗ v) = (D_λ ψ) ⊗ v`. -/
theorem dirac_tensor {lam : ℝ} {v : HU 3} (hv : transport v = (lam : ℂ) • v) (ψ : HU L) :
    dirac (tensor ψ v) = tensor (TorusUniverse.dirac lam ψ) v := by
  ext ⟨j, k⟩
  have hk : (v (k + 1) + v (k - 1)) / 2 = lam * v k := by
    have := congrArg (fun χ : HU 3 => χ k) hv
    simpa [transport_apply] using this
  simp only [dirac_apply, tensor_apply, TorusUniverse.dirac, LinearMap.add_apply,
    LinearMap.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, transport_apply,
    stagger_apply]
  linear_combination (-1) ^ j.val * ψ j * hk

/-- A stationary product with a fiber mode is a stationary Dirac state of the axis. -/
theorem dirac_eigen_of_tensor {lam E : ℝ} {v : HU 3} (hv : transport v = (lam : ℂ) • v)
    {k : ZMod 3} (hk : v k ≠ 0) {ψ : HU L}
    (hE : dirac (tensor ψ v) = (E : ℂ) • tensor ψ v) :
    TorusUniverse.dirac lam ψ = (E : ℂ) • ψ := by
  rw [dirac_tensor hv] at hE
  ext j
  have := congrArg (fun χ : HF L => χ (j, k)) hE
  simp only [tensor_apply, PiLp.smul_apply, smul_eq_mul] at this
  rw [PiLp.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ hk (by rw [this, mul_assoc])

/-- **Spin `1/2`, speed `1/φ`**: a unit stationary state `ψ ⊗ v` with `v` the rotating mode of
the fiber moves on the axis at most at `1/φ`. -/
theorem abs_velocity_le_inv_goldenRatio_of_rotating [NeZero L] (h2 : 2 ∣ L) {E : ℝ} {ψ : HU L}
    (hψ : ‖ψ‖ = 1) (hE : dirac (tensor ψ rotating) = (E : ℂ) • tensor ψ rotating) :
    |velocity ψ| ≤ Real.goldenRatio⁻¹ := by
  have h0 : rotating 0 ≠ 0 := by simp [rotating]
  refine abs_velocity_le_inv_goldenRatio h2 (m := -1 / 2) (E := E) (by norm_num [abs_div]) hψ ?_
  exact dirac_eigen_of_tensor transport_rotating h0 hE

/-- Uniform mode of the fiber: mass `1`, speed at most `√2 − 1`. -/
theorem abs_velocity_le_sqrt_two_sub_one_of_uniform [NeZero L] (h2 : 2 ∣ L) {E : ℝ}
    {ψ : HU L} (hψ : ‖ψ‖ = 1) (hE : dirac (tensor ψ uniform) = (E : ℂ) • tensor ψ uniform) :
    |velocity ψ| ≤ Real.sqrt 2 - 1 := by
  have h0 : uniform 0 ≠ 0 := by simp [uniform]
  refine abs_velocity_le_sqrt_two_sub_one h2 (m := 1) (E := E) (by norm_num) hψ ?_
  exact dirac_eigen_of_tensor transport_uniform h0 hE

end FiberDiracAxis
