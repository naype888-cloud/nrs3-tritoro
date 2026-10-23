/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.DiracQubitAxis
public import NRS3Tritoro.DiracQubitParam
public import NRS3Tritoro.MinUncertaintyFiber

/-!
# The map from minimum uncertainty on `H₄` to Dirac states of the fiber mass

`MinUncertaintyFiber` shows that the largest tension of the minimum-uncertainty states of `H₄`
is the Dirac speed limit at the mass of the fiber. This file maps the states themselves.

`ψ♭` is not a Dirac state of `H₄` (on the open chain `T₄` and `K₄` do not commute, and
`T₄² + K₄² ≠ 1`), so the map does not keep the state; it keeps what is measured. Every
minimum-uncertainty state `ψ` of `H₄` goes to the Dirac qubit of the fiber mass
(`DiracQubit`, `m = −1/2`, the two-wave block of the axis of the universe) at the momentum whose
upper eigenstate moves exactly at the tension of `ψ`:

  `Φ ψ = speedState (speedParam |t| m) m`,  `t = ⟨K₄⟩_ψ`,  velocity of `Φ ψ` = `t`.

* the tension of a minimum-uncertainty state lies in `[−1/φ, 1/φ]`: `D23g` gives the top, the
  mirror `ψ ↦ ψ̄` (complex conjugation; `T₄`, `P₄` are real) gives the bottom;
* `Φ ψ` is a unit eigenvector of the qubit, at a momentum with `c² + s² = 1`, and its velocity is
  the tension of `ψ`;
* `Φ ψ♭` is the fastest Dirac state, at `c² = |m| r = 1/(2φ)`, and it is the only one that
  reaches `1/φ`.

## Main results

- `MinUncertaintyDiracMap.tension_mirror`, `MinUncertaintyDiracMap.gramDefect_mirror` : the
  mirror keeps saturation and reverses the tension.
- `MinUncertaintyDiracMap.abs_tension_le` : `|⟨K₄⟩| ≤ 1/φ` on minimum-uncertainty states.
- `MinUncertaintyDiracMap.toDirac_spec` : `Φ ψ` is a unit Dirac eigenstate with velocity `⟨K₄⟩_ψ`.
- `MinUncertaintyDiracMap.toDirac_psiSat` : `Φ ψ♭` sits at `c² = |m| r` and moves at `1/φ`.
- `MinUncertaintyDiracMap.eq_psiSat_param_of_velocity` : no other Dirac state of the family
  reaches `1/φ`.
- `MinUncertaintyDiracMap.toDirac_on_axis` : when the momentum of `Φ ψ` is a lattice momentum `u`
  of the axis, `ι (Φ ψ) ⊗ v_rot` is an exact unit eigenstate of the Dirac operator of the axis
  with the fiber, moving along the axis at the tension of `ψ`.

The qubit takes every momentum; a finite axis only the roots of unity. The momentum of `Φ ψ♭`,
`cos² k = 1/(2φ)`, is not proved here to be off the lattice.
-/

@[expose] public noncomputable section

open Complex TransportPosition NRSInequality SpectralExtremal EigenvectorSaturation

namespace MinUncertaintyDiracMap

/-! ## 1. The mirror `ψ ↦ ψ̄` -/

/-- Complex conjugation of the coordinates. -/
def mirror (ψ : Hd 4) : Hd 4 := WithLp.toLp 2 fun i => (starRingEnd ℂ) (ψ i)

theorem mirror_apply (ψ : Hd 4) (i : Fin 4) : mirror ψ i = (starRingEnd ℂ) (ψ i) := rfl

theorem inner_mirror (x y : Hd 4) :
    inner ℂ (mirror x) (mirror y) = (starRingEnd ℂ) (inner ℂ x y) := by
  simp only [PiLp.inner_apply, mirror_apply, RCLike.inner_apply', map_sum, map_mul,
    Complex.conj_conj]

theorem norm_mirror (x : Hd 4) : ‖mirror x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, mirror_apply, Complex.norm_conj]

theorem mirror_sub (x y : Hd 4) : mirror (x - y) = mirror x - mirror y := by
  ext i; simp [mirror_apply]

theorem mirror_smul (r : ℝ) (x : Hd 4) : mirror ((r : ℂ) • x) = (r : ℂ) • mirror x := by
  ext i; simp [mirror_apply]

theorem TdOp_mirror (u : Hd 4) : TdOp 4 (mirror u) = mirror (TdOp 4 u) := by
  rw [MinUncertaintyFour.TdOp_four_apply, MinUncertaintyFour.TdOp_four_apply]
  ext i; fin_cases i <;> simp [mirror_apply]

theorem PdOp_mirror (u : Hd 4) : PdOp 4 (mirror u) = mirror (PdOp 4 u) := by
  rw [MinUncertaintyFour.PdOp_four_apply, MinUncertaintyFour.PdOp_four_apply]
  ext i; fin_cases i <;> simp [mirror_apply, map_ofNat]

section Real

variable {A : Hd 4 →ₗ[ℂ] Hd 4} (hA : ∀ u, A (mirror u) = mirror (A u))
include hA

theorem mean_mirror (ψ : Hd 4) : mean A (mirror ψ) = mean A ψ := by
  rw [mean, mean, hA, inner_mirror, Complex.conj_re]

theorem centered_mirror (ψ : Hd 4) : centered A (mirror ψ) = mirror (centered A ψ) := by
  rw [centered, centered, hA, mean_mirror hA, mirror_sub, mirror_smul]

theorem variance_mirror (ψ : Hd 4) : variance A (mirror ψ) = variance A ψ := by
  rw [variance, variance, centered_mirror hA, norm_mirror]

end Real

/-- **The mirror keeps minimum uncertainty.** -/
theorem gramDefect_mirror (ψ : Hd 4) :
    gramDefectAt (TdOp 4) (PdOp 4) (mirror ψ) = gramDefectAt (TdOp 4) (PdOp 4) ψ := by
  rw [gramDefectAt, gramDefectAt, variance_mirror TdOp_mirror, variance_mirror PdOp_mirror,
    centered_mirror TdOp_mirror, centered_mirror PdOp_mirror, inner_mirror, Complex.norm_conj]

/-- **The mirror reverses the tension.** -/
theorem tension_mirror (ψ : Hd 4) :
    NearMaxTension.tension 4 (mirror ψ) = -NearMaxTension.tension 4 ψ := by
  rw [NearMaxTension.tension, NearMaxTension.tension, re_inner_KdOp, re_inner_KdOp, TdOp_mirror,
    PdOp_mirror, inner_mirror, Complex.conj_im]
  ring

/-! ## 2. The tension band of minimum uncertainty -/

/-- The fiber mass and its speed limit. -/
abbrev m : ℝ := MinUncertaintyFiber.fiberMass

/-- `r = √(1 + m²) − |m| = 1/φ`. -/
abbrev r : ℝ := Real.sqrt (1 + m ^ 2) - |m|

theorem r_eq : r = (√5 - 1) / 2 := by
  rw [r, MinUncertaintyFiber.speedLimit_fiber_eq_inv_rho, ← one_div,
    ← MinUncertaintyFour.tension_psiSat_rho, MinUncertaintyFour.tension_psiSat]

theorem m_ne_zero : m ≠ 0 := by norm_num [m, MinUncertaintyFiber.fiberMass]

/-- **`|⟨K₄⟩| ≤ 1/φ`** for every minimum-uncertainty state of `H₄`. -/
theorem abs_tension_le {ψ : Hd 4} (hψ : ‖ψ‖ = 1) (hsat : gramDefectAt (TdOp 4) (PdOp 4) ψ = 0) :
    |NearMaxTension.tension 4 ψ| ≤ r := by
  rw [r_eq, abs_le]
  refine ⟨?_, MinUncertaintyBoundFour.tension_le_of_saturated ψ hψ hsat⟩
  have h := MinUncertaintyBoundFour.tension_le_of_saturated (mirror ψ)
    (by rw [norm_mirror, hψ]) (by rw [gramDefect_mirror, hsat])
  rw [tension_mirror] at h
  linarith

/-! ## 3. The map -/

/-- The momentum parameter `c² = a` of the image of `ψ`. -/
def param (ψ : Hd 4) : ℝ := DiracQubit.speedParam |NearMaxTension.tension 4 ψ| m

/-- The sine of the momentum: its sign carries the direction of the tension. -/
def sinMom (ψ : Hd 4) : ℝ :=
  if 0 ≤ NearMaxTension.tension 4 ψ then -Real.sqrt (1 - param ψ) else Real.sqrt (1 - param ψ)

/-- **The map** `Φ ψ`: the upper Dirac eigenstate of the fiber mass at momentum `param ψ`. -/
def toDirac (ψ : Hd 4) : DiracQubit.Q := DiracQubit.speedState (param ψ) m

theorem velocity_neg (s : ℝ) (χ : DiracQubit.Q) :
    DiracQubit.velocity (-s) χ = -DiracQubit.velocity s χ := by
  rw [DiracQubit.velocity_eq, DiracQubit.velocity_eq]; ring

/-- **`Φ ψ` is a unit Dirac eigenstate whose velocity is the tension of `ψ`.** -/
theorem toDirac_spec {ψ : Hd 4} (hψ : ‖ψ‖ = 1) (hsat : gramDefectAt (TdOp 4) (PdOp 4) ψ = 0) :
    ‖toDirac ψ‖ = 1 ∧
      DiracQubit.dirac (Real.sqrt (param ψ)) m (toDirac ψ) =
        ((DiracQubit.energy (param ψ) m : ℝ) : ℂ) • toDirac ψ ∧
      Real.sqrt (param ψ) ^ 2 + sinMom ψ ^ 2 = 1 ∧
      DiracQubit.velocity (sinMom ψ) (toDirac ψ) = NearMaxTension.tension 4 ψ := by
  have ht := abs_tension_le hψ hsat
  have ht0 := abs_nonneg (NearMaxTension.tension 4 ψ)
  have ha : 0 ≤ param ψ := DiracQubit.speedParam_nonneg ht0 ht
  have ha1 : param ψ ≤ 1 := DiracQubit.speedParam_le_one
  have hv : DiracQubit.velocity (-Real.sqrt (1 - param ψ)) (DiracQubit.speedState (param ψ) m) =
      |NearMaxTension.tension 4 ψ| := DiracQubit.velocity_speedState_param ht0 ht m_ne_zero
  have h1' : 0 ≤ 1 - param ψ := by linarith
  refine ⟨DiracQubit.norm_speedState ha m_ne_zero, DiracQubit.dirac_speedState ha, ?_, ?_⟩
  · have h1 : sinMom ψ ^ 2 = 1 - param ψ := by
      unfold sinMom
      split_ifs
      · rw [neg_sq, Real.sq_sqrt h1']
      · rw [Real.sq_sqrt h1']
    rw [h1, Real.sq_sqrt ha]; ring
  · unfold sinMom toDirac
    split_ifs with h
    · rw [hv, abs_of_nonneg h]
    · rw [← neg_neg (Real.sqrt (1 - param ψ)), velocity_neg, hv, abs_of_neg (not_le.1 h),
        neg_neg]

/-- **`Φ ψ♭` is the fastest Dirac state**: it sits at `c² = |m| r = 1/(2φ)` and moves at `1/φ`. -/
theorem toDirac_psiSat :
    param MinUncertaintyFour.psiSat = |m| * r ∧
      DiracQubit.velocity (sinMom MinUncertaintyFour.psiSat) (toDirac MinUncertaintyFour.psiSat)
        = r := by
  have ht : NearMaxTension.tension 4 MinUncertaintyFour.psiSat = r := by
    rw [r_eq, MinUncertaintyFour.tension_psiSat]
  refine ⟨?_, ?_⟩
  · rw [param, ht, abs_of_nonneg (DiracSpeed.speedLimit_nonneg m)]
    exact DiracQubit.speedParam_speedLimit m
  · rw [(toDirac_spec MinUncertaintyFour.norm_psiSat MinUncertaintyFour.saturated_psiSat).2.2.2, ht]

/-- **And it is the only one**: a state of the family that moves at `1/φ` sits at the momentum of
`Φ ψ♭`. -/
theorem eq_psiSat_param_of_velocity {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (h : DiracQubit.velocity (-Real.sqrt (1 - a)) (DiracQubit.speedState a m) = r) :
    a = param MinUncertaintyFour.psiSat := by
  rw [toDirac_psiSat.1]
  exact DiracQubit.eq_of_velocity_eq_speedLimit ha ha1 m_ne_zero h

/-- **On the axis of the universe with the fiber**: if the momentum of `Φ ψ` is a lattice
momentum `u` of the axis (`u^L = 1`, `|u| = 1`, `L` even), then `ι (Φ ψ) ⊗ v_rot` is an exact
eigenstate of the Dirac operator of the axis with the fiber, and `ι (Φ ψ)` is a unit state of the
axis moving at the tension of `ψ`. -/
theorem toDirac_on_axis {ψ : Hd 4} (hψ : ‖ψ‖ = 1)
    (hsat : gramDefectAt (TdOp 4) (PdOp 4) ψ = 0) {L : ℕ} [NeZero L] {u : ℂ} (hL : u ^ L = 1)
    (hn : ‖u‖ = 1) (h2 : 2 ∣ L) (hre : u.re = Real.sqrt (param ψ)) (him : u.im = sinMom ψ) :
    ‖DiracQubitAxis.embed L u (toDirac ψ)‖ = 1 ∧
      FiberDiracAxis.dirac
          (FiberDiracAxis.tensor (DiracQubitAxis.embed L u (toDirac ψ)) FiberDiracAxis.rotating) =
        ((DiracQubit.energy (param ψ) m : ℝ) : ℂ) •
          FiberDiracAxis.tensor (DiracQubitAxis.embed L u (toDirac ψ)) FiberDiracAxis.rotating ∧
      TorusUniverse.velocity (DiracQubitAxis.embed L u (toDirac ψ)) =
        NearMaxTension.tension 4 ψ := by
  obtain ⟨hnorm, hE, -, hv⟩ := toDirac_spec hψ hsat
  refine ⟨by rw [DiracQubitAxis.norm_embed hn h2, hnorm], ?_, ?_⟩
  · exact DiracQubitAxis.fiberDirac_tensor_embed hL hn h2 (by rw [hre]; exact hE)
  · rw [DiracQubitAxis.velocity_embed hL hn h2, him, hv]

end MinUncertaintyDiracMap
