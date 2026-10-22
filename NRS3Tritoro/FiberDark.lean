/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedAxisEntangled
public import NRS3Hopf.BoxExcess
public import NRS3Dark.DarkShare

/-!
# What is resolved and what is dark, on the fibred box

The box of `nrs3-hopf`: `x`, `y`, `z` open with any number of positions, and the closed fiber `w`
with three positions. On the fiber the product of the uncertainties of `(T°, P₃)` splits into what
the pair resolves and what it cannot (`DarkShare`): `lightShare + darkShare = 1`, for every state.

* **In the band the fiber keeps a dark share, for every state.** If the tension of the fiber
  exceeds `1`, its defect is positive whatever its entanglement with `x`, `y`, `z`
  (`ClosedAxisEntangled.gramDefect_box_pos`), so its dark share is positive.
* **At the `c` of the fiber**, with any unit state on `x`, `y`, `z`, the fiber resolves `4/5` and
  keeps `1/5` dark: the value of every axis of `T³` (`TorusDark`). The open axes of the box are
  those of `R³` (`DarkShare`).

## Main results

- `FiberDark.lightShare_add_darkShare` : the two shares of the fiber add up to one.
- `FiberDark.darkShare_pos_of_band` : in the band the fiber keeps a dark share, every state.
- `FiberDark.lightShare_fiberMaxState` : at the `c` of the fiber it resolves `4/5`.
- `FiberDark.darkShare_fiberMaxState` : at the `c` of the fiber it keeps `1/5` dark.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS CauchyGram DarkShare CubeInBox FourAxes ClosedThree
open NRSInequality EigenvectorSaturation

namespace FiberDark

variable {dx dy dz : ℕ}

/-- The fluctuation vector of the fiber pair `a` (`T°` for `0`, `P₃` for `1`). -/
abbrev fib (a : Fin 2) (Φ : H4D dx dy dz 3) : H4D dx dy dz 3 :=
  centeredG (boxPairs dx dy dz 3 closedPair (a, 3)) Φ

/-- **The two shares of the fiber add up to one**, for every state. -/
theorem lightShare_add_darkShare (Φ : H4D dx dy dz 3) (h : ‖fib 0 Φ‖ * ‖fib 1 Φ‖ ≠ 0) :
    lightShare (fib 0 Φ) (fib 1 Φ) + darkShare (fib 0 Φ) (fib 1 Φ) = 1 :=
  DarkShare.lightShare_add_darkShare _ _ h

/-- **In the band the fiber keeps a dark share**, for every state, entangled with `x`, `y`, `z`
or not. -/
theorem darkShare_pos_of_band {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|) :
    0 < darkShare (fib 0 Φ) (fib 1 Φ) := by
  have hd := ClosedAxisEntangled.gramDefect_box_pos hΦ hb
  set x := fib 0 Φ
  set y := fib 1 Φ
  have hle : gramDefectC x y ≤ (‖x‖ * ‖y‖) ^ 2 := by
    rw [gramDefectC, varianceC, varianceC, mul_pow]
    nlinarith [sq_nonneg ‖inner ℂ x y‖]
  exact div_pos hd (by linarith)

/-! ## At the `c` of the fiber -/

section MaxState

variable {φ : EuclideanSpace ℂ (Fin dx × Fin dy × Fin dz)} (hφ : ‖φ‖ = 1)
include hφ

/-- The box state with the fiber at its `c` and any state `φ` on `x`, `y`, `z`. -/
def fiberMaxState (φ : EuclideanSpace ℂ (Fin dx × Fin dy × Fin dz)) : H4D dx dy dz 3 :=
  prodAlong (eW dx dy dz 3) ClosedThree.maxState φ

lemma fib_fiberMaxState (a : Fin 2) :
    fib a (fiberMaxState φ) =
      prodAlong (eW dx dy dz 3) (centeredG (Matrix.toEuclideanLin (closedPair a))
        ClosedThree.maxState) φ :=
  centeredG_lift (eW dx dy dz 3) hφ _ _

/-- **At the `c` of the fiber, the fiber resolves `4/5`.** -/
theorem lightShare_fiberMaxState :
    lightShare (fib 0 (fiberMaxState φ)) (fib 1 (fiberMaxState φ)) = 4 / 5 := by
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hc := BoxExcess.covariance_maxState
  have hi := BoxExcess.imPart_maxState
  rw [covariance] at hc
  rw [imPart] at hi
  have e0 : centeredG (Matrix.toEuclideanLin (closedPair 0)) ClosedThree.maxState =
      centered ClosedThree.TcOp ClosedThree.maxState := rfl
  have e1 : centeredG (Matrix.toEuclideanLin (closedPair 1)) ClosedThree.maxState =
      centered (PdOp 3) ClosedThree.maxState := rfl
  have hT : ‖centered ClosedThree.TcOp ClosedThree.maxState‖ ^ 2 = 9 / 16 :=
    BoxExcess.variance_TcOp_maxState
  have hP : ‖centered (PdOp 3) ClosedThree.maxState‖ ^ 2 = 5 / 6 :=
    BoxExcess.variance_PdOp_maxState
  rw [fib_fiberMaxState hφ, fib_fiberMaxState hφ, lightShare, inner_prodAlong,
    inner_self_of_norm_one hφ, mul_one, mul_pow, norm_sq_prodAlong _ _ _ hφ,
    norm_sq_prodAlong _ _ _ hφ, e0, e1, hT, hP, Complex.sq_norm, Complex.normSq_apply, hc, hi]
  have h38 : (0 : ℝ) * 0 + -(√6 / 4) * -(√6 / 4) = 3 / 8 := by nlinarith [h6]
  rw [h38]
  norm_num

/-- **At the `c` of the fiber, the fiber keeps `1/5` dark.** -/
theorem darkShare_fiberMaxState :
    darkShare (fib 0 (fiberMaxState φ)) (fib 1 (fiberMaxState φ)) = 1 / 5 := by
  have hT : ‖fib 0 (fiberMaxState φ)‖ ^ 2 = 9 / 16 := by
    rw [fib_fiberMaxState hφ, norm_sq_prodAlong _ _ _ hφ]
    exact BoxExcess.variance_TcOp_maxState
  have hP : ‖fib 1 (fiberMaxState φ)‖ ^ 2 = 5 / 6 := by
    rw [fib_fiberMaxState hφ, norm_sq_prodAlong _ _ _ hφ]
    exact BoxExcess.variance_PdOp_maxState
  have hne : ‖fib 0 (fiberMaxState φ)‖ * ‖fib 1 (fiberMaxState φ)‖ ≠ 0 := by
    intro h0
    have := congrArg (· ^ 2) h0
    simp only [mul_pow, hT, hP] at this
    norm_num at this
  have h := lightShare_add_darkShare (fiberMaxState φ) hne
  rw [lightShare_fiberMaxState hφ] at h
  linarith

end MaxState

end FiberDark
