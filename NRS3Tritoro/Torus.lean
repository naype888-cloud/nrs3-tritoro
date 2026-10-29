/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxExcess
public import NRS3Hopf.ClosedAxisEntangled

/-!
# The closed torus: every axis closed

Close every axis of the box with the link `{0, 2}` (`D16e`): `k` closed axes with three positions
each, the space `ℂ^(Fin k → Fin 3)`. With `k = 3` it is the three-torus `T³ = x × y × z`, finite
and without boundary; with `k = 4` it is `T⁴ = x × y × z × w`, the box of `NRS3Hopf` with every
axis closed. Each axis carries the pair `(T°, P₃)` of `ClosedThree`.

* **RS^N³ on every axis.** The defect of a closed axis in its band is positive for every state of
  the torus, entangled with the other axes or not (`ClosedAxisEntangled`): each axis is a
  `ℂ³ ⊗ ℂ^β` with `β` the other `k − 1` axes.
* **det|RS^N³| at the maximal current state.** Each closed axis contributes `F = 5/4`
  (`BoxExcess.closedFactor_eq`), so `det Σ = (5/4)^k |det Ω|`: `125/64` on `T³`, `625/256` on
  `T⁴`. Robertson 1934 is strict for every `k ≥ 1`.

The ladder at three positions per axis, at the maximal current state:

| space | open axes | closed axes | `det Σ / |det Ω|` |
|---|---|---|---|
| cube `x × y × z` | 3 | 0 | `1` (`CubeInBox.cube_three_saturates`) |
| box `x × y × z × w` | 3 | 1 | `5/4` |
| `T³` | 0 | 3 | `125/64` |
| `T⁴` | 0 | 4 | `625/256` |

The open cube with three positions saturates; each closing adds the factor `5/4`, never removes
one: closing an axis adds one link, one more quantum (`D16c`, `D16e`).

## Main results

- `Torus.robertson_det_torus` : Robertson 1934 on the torus, every state.
- `Torus.gramDefect_pos` : on every axis of the torus, tension above `1` forces a positive
  defect, for every unit state.
- `Torus.det_covMatrix_maxState` : `det Σ = (5/4)^k |det Ω|` at the maximal current state.
- `Torus.three_torus`, `Torus.four_torus` : the ratios `125/64` and `625/256`.
- `Torus.robertson_det_maxState_strict` : strict for every `k ≥ 1`.
- `Torus.box_three` : the box with `x`, `y`, `z` open and `w` closed has ratio `5/4`.
- `Torus.ladder` : `1`, `5/4`, `125/64`, `625/256` in one statement.
-/

@[expose] public noncomputable section

open Matrix RobertsonDeterminant StackedFibers BoxExcess CubeInBox FourAxes TransportPosition
open PathGraph3DNRS RobertsonDeterminantProduct NRSInequality EigenvectorSaturation ClosedThree
open DimensionalQuantum VolumetricQuantum Gnomon RobertsonDeterminant3D CubeSpectrum CauchyGram

namespace Torus

/-- The space of the torus with `k` closed axes of three positions. -/
abbrev HT (k : ℕ) := EuclideanSpace ℂ (Fin k → Fin 3)

/-- The `2k` observables of the torus: `T°` and `P₃` on each axis. -/
abbrev torusPairs (k : ℕ) : Fin 2 × Fin k → HT k →ₗ[ℂ] HT k := ops closedPair

/-- Every axis at the maximal current state of the closed axis. -/
def maxState (k : ℕ) : HT k := prodK fun _ => ClosedThree.maxState

variable {k : ℕ}

/-- **Robertson 1934 on the torus**, for every state. -/
theorem robertson_det_torus (Φ : HT k) :
    |(imMatrix (torusPairs k) Φ).det| ≤ (covMatrix (torusPairs k) Φ).det :=
  robertson_det _ Φ

/-- **RS^N³ on every axis of the torus.** If the tension of axis `i` exceeds `1`, its defect is
positive, for every unit state, entangled with the other axes or not. -/
theorem gramDefect_pos (i : Fin k) {Φ : HT k} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (torusPairs k (0, i)) (torusPairs k (1, i)) Φ|) :
    0 < gramDefectC (centeredG (torusPairs k (0, i)) Φ) (centeredG (torusPairs k (1, i)) Φ) :=
  ClosedAxisEntangled.gramDefect_pos_of_band (split i) hΦ hb

/-- **det|RS^N³| on the torus**: at the maximal current state, `det Σ = (5/4)^k |det Ω|`. -/
theorem det_covMatrix_maxState (k : ℕ) :
    (covMatrix (torusPairs k) (maxState k)).det =
      (5 / 4) ^ k * |(imMatrix (torusPairs k) (maxState k)).det| := by
  rw [← closedFactor_eq]
  exact closed_stack k

theorem abs_det_imMatrix_maxState_pos (k : ℕ) :
    0 < |(imMatrix (torusPairs k) (maxState k)).det| := by
  rw [maxState, abs_det_imMatrix_prodK closedPair_isHermitian
    (fun _ => ClosedThree.norm_maxState)]
  refine Finset.prod_pos fun _ _ => ?_
  rw [abs_det_imMatrix_closed]
  exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 imPart_maxState_ne_zero).symm

/-- **The three-torus**: `det Σ₆ = (125/64) |det Ω₆|`. -/
theorem three_torus :
    (covMatrix (torusPairs 3) (maxState 3)).det =
      125 / 64 * |(imMatrix (torusPairs 3) (maxState 3)).det| := by
  rw [det_covMatrix_maxState]
  norm_num

/-- **The four-torus**: `det Σ₈ = (625/256) |det Ω₈|`. -/
theorem four_torus :
    (covMatrix (torusPairs 4) (maxState 4)).det =
      625 / 256 * |(imMatrix (torusPairs 4) (maxState 4)).det| := by
  rw [det_covMatrix_maxState]
  norm_num

/-- **Strict on every torus**: with at least one closed axis, Robertson 1934 is strict at the
maximal current state. -/
theorem robertson_det_maxState_strict (hk : 1 ≤ k) :
    |(imMatrix (torusPairs k) (maxState k)).det| < (covMatrix (torusPairs k) (maxState k)).det := by
  rw [det_covMatrix_maxState]
  have h := abs_det_imMatrix_maxState_pos k
  have hF : (1 : ℝ) < (5 / 4) ^ k := one_lt_pow₀ (by norm_num) (by omega)
  nlinarith

/-- **The box with one closed axis**: `x`, `y`, `z` open with three positions at their maximal
current state and `w` closed at its own, `det Σ₈ = (5/4) |det Ω₈|`. -/
theorem box_three :
    (covMatrix (boxPairs 3 3 3 3 closedPair)
        (prod4 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)
          ClosedThree.maxState)).det =
      5 / 4 * |(imMatrix (boxPairs 3 3 3 3 closedPair)
        (prod4 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)
          ClosedThree.maxState)).det| := by
  rw [det_covMatrix_box_maxCurrent (by norm_num) (by norm_num) (by norm_num), boxExcess_three]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  congr 1
  nlinarith

/-- **The ladder of closings** at three positions per axis: the open cube saturates, and each
closed axis multiplies the ratio by `5/4`. -/
theorem ladder :
    (covMatrix (pairs 3 3 3) (maxCurrentCubeState 3 3 3)).det =
        |(imMatrix (pairs 3 3 3) (maxCurrentCubeState 3 3 3)).det| ∧
      (covMatrix (boxPairs 3 3 3 3 closedPair)
          (prod4 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)
            ClosedThree.maxState)).det =
        5 / 4 * |(imMatrix (boxPairs 3 3 3 3 closedPair)
          (prod4 (maxCurrentState 3) (maxCurrentState 3) (maxCurrentState 3)
            ClosedThree.maxState)).det| ∧
      (covMatrix (torusPairs 3) (maxState 3)).det =
        125 / 64 * |(imMatrix (torusPairs 3) (maxState 3)).det| ∧
      (covMatrix (torusPairs 4) (maxState 4)).det =
        625 / 256 * |(imMatrix (torusPairs 4) (maxState 4)).det| :=
  ⟨cube_three_saturates.1, box_three, three_torus, four_torus⟩

end Torus
