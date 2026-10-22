/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSpectrum

/-!
# Dipole on S², modes on T³

The real spherical harmonics of degree `ℓ = 1` are the three coordinate functions on `ℝ³`.
They are in bijection with the three axes of `T³`. A pure-axis mode puts one ring wave number
`m` on the chosen axis and wave number `0` on the other two.

The pair `(T, P)` of that mode is the quadrature of the same angle that diagonalizes the ring:

  `T = cos (2π m / d)`,  `P = sin (2π m / d)`.

`T` is the eigenvalue of `ring d` (`TorusSpectrum.ring_mulVec_wave`). `P` is the sine of that
same angle. This file does not claim that `P` is an eigenvalue of `PdOp`.

Multipoles `ℓ ≥ 2` are not identified here.
-/

@[expose] public noncomputable section

open TorusSpectrum

namespace TorusDipole

/-- The three real harmonics of degree `ℓ = 1`, named by axis: `x ~ Y_{1,1}`, `y ~ Y_{1,-1}`,
`z ~ Y_{1,0}`. -/
inductive Harmonic1
  | x | y | z
  deriving DecidableEq, Repr

/-- The axis of `T³` that carries this dipole harmonic. -/
def axis : Harmonic1 → Fin 3
  | .x => 0
  | .y => 1
  | .z => 2

theorem axis_bijective : Function.Bijective axis := by
  refine ⟨?_, ?_⟩
  · intro a b h
    cases a <;> cases b <;> simp [axis] at h <;> rfl
  · intro i
    match i with
    | ⟨0, _⟩ => exact ⟨.x, rfl⟩
    | ⟨1, _⟩ => exact ⟨.y, rfl⟩
    | ⟨2, _⟩ => exact ⟨.z, rfl⟩
    | ⟨n + 3, h⟩ => omega

/-- Cartesian dipole coefficient of a vector in `ℝ³`. -/
def coeff (v : Fin 3 → ℝ) (h : Harmonic1) : ℝ :=
  v (axis h)

theorem coeff_basis (i j : Harmonic1) :
    coeff (Pi.single (axis i) 1) j = if i = j then (1 : ℝ) else 0 := by
  cases i <;> cases j <;> simp [coeff, axis, Pi.single]

/-- Angle of the ring wave `m` on a ring of `d` positions. -/
def phase (d m : ℕ) : ℝ :=
  2 * Real.pi * m / d

/-- Transport quadrature `T = cos (2π m / d)`. -/
def transportEigen (d m : ℕ) : ℝ :=
  Real.cos (phase d m)

/-- Momentum quadrature `P = sin (2π m / d)`. -/
def momentumEigen (d m : ℕ) : ℝ :=
  Real.sin (phase d m)

theorem transportEigen_eq_lam (d m : ℕ) :
    (transportEigen d m : ℂ) = lam d m := by
  simp [transportEigen, phase, lam]

/-- The mode quadratures sit on the unit circle: `T² + P² = 1`. -/
theorem transport_sq_add_momentum_sq (d m : ℕ) :
    transportEigen d m ^ 2 + momentumEigen d m ^ 2 = 1 := by
  simp [transportEigen, momentumEigen, Real.cos_sq_add_sin_sq]

lemma lam_zero (d : ℕ) : lam d 0 = 1 := by
  simp [lam]

/-- Pure-axis mode: wave number `m` on the dipole axis, `0` on the other two. -/
def axisMode {d : ℕ} [NeZero d] (h : Harmonic1) (m : Fin d) : Fin d × Fin d × Fin d :=
  match h with
  | .x => (m, 0, 0)
  | .y => (0, m, 0)
  | .z => (0, 0, m)

/-- The torus eigenvalue of a pure-axis mode is `cos (2π m / d) + 2`. The two quiet axes
each contribute `cos 0 = 1`. -/
theorem lam3_axisMode {d : ℕ} [NeZero d] (h : Harmonic1) (m : Fin d) :
    lam3 (axisMode h m) = lam d m.val + 2 := by
  cases h <;> simp [axisMode, lam3, lam_zero] <;> ring

/-- `T3c` sends the pure-axis wave to `(T + 2)` times itself. -/
theorem T3c_axisMode {d : ℕ} [NeZero d] (hd : 3 ≤ d) (h : Harmonic1) (m : Fin d) :
    (TorusArea.T3c d d d).mulVec (wave3 (axisMode h m)) =
      lam3 (axisMode h m) • wave3 (axisMode h m) :=
  T3c_mulVec_wave3 hd hd hd (axisMode h m)

end TorusDipole
