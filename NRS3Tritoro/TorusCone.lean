/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.Torus
public import NRS3UncertaintyCone.TimeDilation

/-!
# The uncertainty cone on the torus

Every axis of the torus `T^k`, closed with three positions, carries the pair `(T°, P₃)`, and the
fluctuation vectors of that pair form an uncertainty four-vector `v`
(`UncertaintyCone.coneVector`). For every state and every axis, `v` lies in the closed future
cone: nothing is spacelike. The interval `η(v, v)` is the Robertson–Schrödinger defect of the
axis, so the proper time `τ = √η(v, v)` is the distance of the state from the edge of the cone.

On `T³`, with no open axis, every axis in its band is strictly timelike, entangled across the
axes or not: the quantum that cannot be resolved is a positive proper time on `x`, `y` and `z`.

## Main results

- `TorusCone.axisVector_mem_futureCone` : every axis of every state lies in the closed future
  cone.
- `TorusCone.interval_axisVector` : the interval of an axis is its Robertson–Schrödinger defect.
- `TorusCone.timelike_of_band` : in the band, `η(v, v) > 0` on that axis.
- `TorusCone.properTime_pos_of_band` : the same for the proper time.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS CauchyGram UncertaintyCone

namespace TorusCone

variable {k : ℕ}

/-- The uncertainty four-vector of axis `i` of the torus. -/
def axisVector (Φ : Torus.HT k) (i : Fin k) : Fin 4 → ℝ :=
  coneVector (centeredG (Torus.torusPairs k (0, i)) Φ) (centeredG (Torus.torusPairs k (1, i)) Φ)

/-- **Nothing is spacelike.** For every state and every axis of the torus, the four-vector lies
in the closed future cone. -/
theorem axisVector_mem_futureCone (Φ : Torus.HT k) (i : Fin k) :
    0 ≤ axisVector Φ i 0 ∧ 0 ≤ interval (axisVector Φ i) :=
  mem_futureCone (H := Torus.HT k) _ _

/-- The interval of an axis is its Robertson–Schrödinger defect. -/
theorem interval_axisVector (Φ : Torus.HT k) (i : Fin k) :
    interval (axisVector Φ i) =
      gramDefectC (centeredG (Torus.torusPairs k (0, i)) Φ)
        (centeredG (Torus.torusPairs k (1, i)) Φ) :=
  interval_eq_gramDefectC _ _

/-- **Strictly timelike in the band, for every state.** An axis of the torus with tension above
`1` lies strictly inside the cone, whatever the entanglement with the other axes. -/
theorem timelike_of_band {Φ : Torus.HT k} (hΦ : ‖Φ‖ = 1) (i : Fin k)
    (hb : 1 < |tensionG (Torus.torusPairs k (0, i)) (Torus.torusPairs k (1, i)) Φ|) :
    0 < interval (axisVector Φ i) := by
  rw [interval_axisVector]
  exact Torus.gramDefect_pos i hΦ hb

/-- **The unresolvable quantum is a positive proper time on every axis in its band.** -/
theorem properTime_pos_of_band {Φ : Torus.HT k} (hΦ : ‖Φ‖ = 1) (i : Fin k)
    (hb : 1 < |tensionG (Torus.torusPairs k (0, i)) (Torus.torusPairs k (1, i)) Φ|) :
    0 < properTime (axisVector Φ i) :=
  Real.sqrt_pos.2 (timelike_of_band hΦ i hb)

end TorusCone
