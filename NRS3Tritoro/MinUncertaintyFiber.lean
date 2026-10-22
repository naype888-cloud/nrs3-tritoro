/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.DiracSpeed
public import NRS3Tritoro.FiberDiracAxis
public import NavaRobertsonCertificados.D23g_MinUncertaintyUpperBound

/-!
# The `1/φ` of minimum uncertainty and the `1/φ` of the fiber are one number for one reason

Two results of the program end at `1/φ`:

* **minimum uncertainty at `d = 4`** (`D23f`, `D23g`): the states of `H₄` that saturate
  Robertson–Schrödinger carry tension at most `1/ρ₄`, and `ψ♭` reaches it; `ρ₄ = 2 cos(π/5)` is
  the spectral radius of the open chain of four positions.
* **the fiber** (`DiracSpeed`, `TorusFiberGap`, `TorusFiberAxes`): the rotating modes of the ring
  of three give the mass `m = 1/2`, and a Dirac state of mass `m` moves at most at
  `√(1 + m²) − m`.

They are equal for an exact reason, not by coincidence of decimals: `√(1 + m²) − m = ρ⁻¹` holds
if and only if `ρ − ρ⁻¹ = 2m` (`DiracSpeed.speedLimit_eq_inv_iff`), and `ρ₄ − ρ₄⁻¹ = 1 = 2 · 1/2`
because `ρ₄ = φ` solves `ρ² = ρ + 1`. In rapidity form, the fiber mass is `sinh θ` with
`θ = log ρ₄`, and both limits are `e^{−θ}`.

So the largest tension that minimum uncertainty allows on `H₄` **is** the Dirac speed limit at the
mass of the fiber (`isGreatest_minUncertaintyTension`).

## Main results

- `MinUncertaintyFiber.fiberMass` : the rotating mode of the fiber has `T° = −1/2`.
- `MinUncertaintyFiber.rho_four_sub_inv` : `ρ₄ − ρ₄⁻¹ = 2 · |−1/2|`.
- `MinUncertaintyFiber.speedLimit_fiber_eq_inv_rho` : `√(1 + m²) − |m| = ρ₄⁻¹` at the fiber mass.
- `MinUncertaintyFiber.speedLimit_fiber_eq_exp` : it is `e^{−log ρ₄}`, with `sinh (log ρ₄) = 1/2`.
- `MinUncertaintyFiber.isGreatest_minUncertaintyTension` : the maximal tension of the
  minimum-uncertainty states of `H₄` is the speed limit at the fiber mass.
-/

@[expose] public noncomputable section

open Complex TransportPosition NRSInequality SpectralExtremal EigenvectorSaturation

namespace MinUncertaintyFiber

/-- The mass of the rotating modes of the fiber: `T° = −1/2` on them. -/
def fiberMass : ℝ := -1 / 2

theorem transport_rotating :
    TorusUniverse.transport FiberDiracAxis.rotating =
      ((fiberMass : ℝ) : ℂ) • FiberDiracAxis.rotating :=
  FiberDiracAxis.transport_rotating

theorem abs_fiberMass : |fiberMass| = 1 / 2 := by norm_num [fiberMass, abs_div]

/-- `ρ₄ = φ`. -/
theorem rho_four_eq : rho 4 = Real.goldenRatio := by
  rw [MinUncertaintyFour.rho_four]

/-- **`ρ₄ − ρ₄⁻¹ = 2 |m|`** for the mass of the fiber. -/
theorem rho_four_sub_inv : rho 4 - (rho 4)⁻¹ = 2 * |fiberMass| := by
  rw [rho_four_eq, Real.inv_goldenRatio, abs_fiberMass]
  linarith [Real.goldenRatio_add_goldenConj]

/-- The speed limit at the mass of the fiber is `ρ₄⁻¹`. -/
theorem speedLimit_fiber_eq_inv_rho :
    Real.sqrt (1 + fiberMass ^ 2) - |fiberMass| = (rho 4)⁻¹ := by
  have h := (DiracSpeed.speedLimit_eq_inv_iff (abs_nonneg fiberMass)
    MinUncertaintyFour.rho_four_pos).2 rho_four_sub_inv
  rwa [sq_abs, abs_abs] at h

/-- **Rapidity form**: the fiber mass is `sinh (log ρ₄)` and the limit is `e^{−log ρ₄}`. -/
theorem speedLimit_fiber_eq_exp :
    Real.sinh (Real.log (rho 4)) = |fiberMass| ∧
      Real.sqrt (1 + fiberMass ^ 2) - |fiberMass| = Real.exp (-Real.log (rho 4)) := by
  have hs : Real.sinh (Real.log (rho 4)) = |fiberMass| := by
    rw [rho_four_eq, DiracSpeed.sinh_log_goldenRatio, abs_fiberMass]
  refine ⟨hs, ?_⟩
  have hθ : 0 ≤ Real.log (rho 4) := by
    rw [rho_four_eq]; exact Real.log_nonneg Real.one_lt_goldenRatio.le
  have h := DiracSpeed.speedLimit_sinh hθ
  rwa [hs, abs_abs, sq_abs] at h

/-- **One number for one reason**: the maximal tension of the minimum-uncertainty states of `H₄`
is the Dirac speed limit at the mass of the fiber. -/
theorem isGreatest_minUncertaintyTension :
    IsGreatest {t | ∃ ψ : Hd 4, ‖ψ‖ = 1 ∧ gramDefectAt (TdOp 4) (PdOp 4) ψ = 0 ∧
        NearMaxTension.tension 4 ψ = t}
      (Real.sqrt (1 + fiberMass ^ 2) - |fiberMass|) := by
  rw [speedLimit_fiber_eq_inv_rho]
  refine ⟨⟨MinUncertaintyFour.psiSat, MinUncertaintyFour.norm_psiSat,
    MinUncertaintyFour.saturated_psiSat, by rw [MinUncertaintyFour.tension_psiSat_rho, one_div]⟩,
    ?_⟩
  rintro t ⟨ψ, hψ, hsat, rfl⟩
  have h := MinUncertaintyBoundFour.tension_le_of_saturated ψ hψ hsat
  rw [← MinUncertaintyFour.tension_psiSat, MinUncertaintyFour.tension_psiSat_rho, one_div] at h
  exact h

end MinUncertaintyFiber
