/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.OpenDirac
public import NavaRobertsonIndependent.Mathematics.D38_GroupVelocity

/-!
# The velocity of a Dirac state on the open axis

On `H_d` take the open axis `(T_d, P_d)` and the massive Dirac operator `D_m = T_d + m σ`, with
`σ = (−1)^j` the staggered sign (`OpenDirac.dirac` along one axis). The velocity of a state is
`((d − 1)/2) ⟨i[T_d, P_d]⟩` in units of the local `c`, one position per step between adjacent
positions (`GroupVelocity.velocity`). The sign `σ` is diagonal, like `P_d`, so it commutes with the
position and the mass term does not move anything:

  `i[D_m, P_d] = i[T_d, P_d]`.

The tension read by a Dirac state is the tension of the transport alone: the mass lowers no
ceiling, it only fixes which states are stationary. For a stationary state the Heisenberg
equation reads `⟨i[D_m, P_d]⟩ = 0`: the mean position does not drift. This is the mean of the
current, not the absence of transport: `[T_d, P_d] ≠ 0` for every state, and the transport keeps
its fluctuations.

## Main results

- `OpenDiracVelocity.stagger_mul_Pd` : `σ P_d = P_d σ`.
- `OpenDiracVelocity.observableTension_diracOp` : `i[D_m, P_d] = i[T_d, P_d]`.
- `OpenDiracVelocity.tension_eq_zero_of_eigenvector` : an eigenvector of `D_m` has mean current
  `0`.
- `OpenDiracVelocity.velocity_eq_zero_of_eigenvector` : and zero mean drift of `⟨P_d⟩`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition SpectralExtremal NearMaxTension GroupVelocity

namespace OpenDiracVelocity

variable {d : ℕ}

/-- `P_d` is diagonal. -/
theorem Pd_eq_diagonal (d : ℕ) : Pd d = diagonal fun j => (posCoord d j : ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Pd]
  · simp [Pd, h]

/-- **The staggered sign commutes with the position**: both are diagonal. -/
theorem stagger_mul_Pd (d : ℕ) : OpenDirac.stagger d * Pd d = Pd d * OpenDirac.stagger d := by
  rw [Pd_eq_diagonal, OpenDirac.stagger, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  ring

/-- The staggered sign as an operator of `H_d`. -/
def staggerOp (d : ℕ) : Hd d →ₗ[ℂ] Hd d := Matrix.toEuclideanLin (OpenDirac.stagger d)

/-- The Dirac operator of the open axis, `D_m = T_d + m σ`. -/
def diracOp (d : ℕ) (m : ℝ) : Hd d →ₗ[ℂ] Hd d := TdOp d + (m : ℂ) • staggerOp d

theorem staggerOp_isSymmetric (d : ℕ) : (staggerOp d).IsSymmetric := by
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr ?_
  rw [OpenDirac.stagger, Matrix.isHermitian_diagonal_iff]
  intro j
  simp [IsSelfAdjoint, star_pow]

theorem diracOp_isSymmetric (d : ℕ) (m : ℝ) : (diracOp d m).IsSymmetric := by
  intro x y
  simp only [diracOp, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [TdOp_isSymmetric d x y, staggerOp_isSymmetric d x y]

/-- `σ` commutes with `P_d` as operators. -/
theorem staggerOp_comp_PdOp (d : ℕ) :
    (staggerOp d).comp (PdOp d) = (PdOp d).comp (staggerOp d) := by
  ext x : 1
  simp only [staggerOp, PdOp, Matrix.toEuclideanLin, LinearMap.comp_apply, Matrix.toLpLin_apply,
    Matrix.mulVec_mulVec, stagger_mul_Pd]

/-- **The mass does not move the position**: `i[D_m, P_d] = i[T_d, P_d]`. -/
theorem observableTension_diracOp (d : ℕ) (m : ℝ) :
    observableTension (diracOp d m) (PdOp d) = observableTension (TdOp d) (PdOp d) := by
  have h := staggerOp_comp_PdOp d
  simp only [observableTension, opCommutator, diracOp, LinearMap.add_comp, LinearMap.comp_add,
    LinearMap.smul_comp, LinearMap.comp_smul, h]
  ext x : 1
  simp

/-- **Heisenberg stationarity**: for a symmetric `H` and `P`, an eigenvector of `H` with a real
eigenvalue has `⟨ψ, i[H, P] ψ⟩ = 0`. -/
theorem inner_observableTension_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A P : H →ₗ[ℂ] H} (hA : A.IsSymmetric) {E : ℝ} {ψ : H} (hψ : A ψ = (E : ℂ) • ψ) :
    inner ℂ ψ (observableTension A P ψ) = 0 := by
  have h1 : inner ℂ ψ (A (P ψ)) = (E : ℂ) * inner ℂ ψ (P ψ) := by
    rw [← hA ψ (P ψ), hψ, inner_smul_left, Complex.conj_ofReal]
  have h2 : inner ℂ ψ (P (A ψ)) = (E : ℂ) * inner ℂ ψ (P ψ) := by
    rw [hψ, map_smul, inner_smul_right]
  simp only [observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, inner_smul_right, inner_sub_right, h1, h2]
  ring

/-- **A stationary Dirac state has mean current `0`.** -/
theorem tension_eq_zero_of_eigenvector (m : ℝ) {E : ℝ} {ψ : Hd d}
    (hψ : diracOp d m ψ = (E : ℂ) • ψ) : tension d ψ = 0 := by
  have h := inner_observableTension_eq_zero (P := PdOp d) (diracOp_isSymmetric d m) hψ
  rw [observableTension_diracOp] at h
  unfold tension KdOp
  rw [h]
  simp

/-- **The mean position of a stationary Dirac state does not drift**: `velocity d ψ = 0`, the mean
of the current; the transport itself is not null. -/
theorem velocity_eq_zero_of_eigenvector (m : ℝ) {E : ℝ} {ψ : Hd d}
    (hψ : diracOp d m ψ = (E : ℂ) • ψ) : velocity d ψ = 0 := by
  unfold velocity
  rw [tension_eq_zero_of_eigenvector m hψ, mul_zero]

end OpenDiracVelocity
