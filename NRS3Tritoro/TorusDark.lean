/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.Torus
public import NRS3Dark.DarkShare

/-!
# What is resolved and what is dark, on the torus

On every axis of the torus the product of the uncertainties of `(T°, P₃)` splits into what the
pair resolves and what it cannot resolve (`DarkShare`):

  `lightShare + darkShare = 1`.

On `T³` every axis is closed. In its band the dark share of an axis is positive for every state,
entangled across the axes or not. At the maximal current state, the `c` of the closed axis, each
axis resolves `4/5` and keeps `1/5` dark. On the open cube with three positions the dark share at
`c` is `0` (`DarkShare.darkShare_maxCurrentState_eq_zero_iff`): closing the axis is what leaves a
dark share on every axis of `T³`.

## Main results

- `TorusDark.lightShare_add_darkShare` : the two shares of every axis add up to one.
- `TorusDark.darkShare_pos_of_band` : in the band the dark share is positive, every state.
- `TorusDark.lightShare_maxState` : at `c`, every axis resolves `4/5`.
- `TorusDark.darkShare_maxState` : at `c`, every axis keeps `1/5` dark.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS CauchyGram DarkShare StackedFibers CubeInBox FourAxes
open NRSInequality EigenvectorSaturation

namespace TorusDark

variable {k : ℕ}

/-- **The two shares of every axis add up to one**, for every state. -/
theorem lightShare_add_darkShare (Φ : Torus.HT k) (i : Fin k)
    (h : ‖centeredG (Torus.torusPairs k (0, i)) Φ‖ *
      ‖centeredG (Torus.torusPairs k (1, i)) Φ‖ ≠ 0) :
    lightShare (centeredG (Torus.torusPairs k (0, i)) Φ)
        (centeredG (Torus.torusPairs k (1, i)) Φ) +
      darkShare (centeredG (Torus.torusPairs k (0, i)) Φ)
        (centeredG (Torus.torusPairs k (1, i)) Φ) = 1 :=
  DarkShare.lightShare_add_darkShare _ _ h

/-- **In the band every axis keeps a dark share**, for every state, entangled or not. -/
theorem darkShare_pos_of_band {Φ : Torus.HT k} (hΦ : ‖Φ‖ = 1) (i : Fin k)
    (hb : 1 < |tensionG (Torus.torusPairs k (0, i)) (Torus.torusPairs k (1, i)) Φ|) :
    0 < darkShare (centeredG (Torus.torusPairs k (0, i)) Φ)
      (centeredG (Torus.torusPairs k (1, i)) Φ) := by
  have hd := Torus.gramDefect_pos i hΦ hb
  set x := centeredG (Torus.torusPairs k (0, i)) Φ
  set y := centeredG (Torus.torusPairs k (1, i)) Φ
  have hle : gramDefectC x y ≤ (‖x‖ * ‖y‖) ^ 2 := by
    rw [gramDefectC, varianceC, varianceC, mul_pow]
    nlinarith [sq_nonneg ‖inner ℂ x y‖]
  exact div_pos hd (by linarith)

/-! ## At the maximal current state -/

section MaxState

variable (i : Fin k)

theorem inner_maxState (a b : Fin 2) :
    inner ℂ (centeredG (Torus.torusPairs k (a, i)) (Torus.maxState k))
        (centeredG (Torus.torusPairs k (b, i)) (Torus.maxState k)) =
      inner ℂ (centeredG (wPair closedPair a) ClosedThree.maxState)
        (centeredG (wPair closedPair b) ClosedThree.maxState) := by
  rw [Torus.maxState, inner_centered_ops closedPair_isHermitian
    (fun _ => ClosedThree.norm_maxState), ite_eq_left rfl]

theorem normSq_maxState (a : Fin 2) :
    ‖centeredG (Torus.torusPairs k (a, i)) (Torus.maxState k)‖ ^ 2 =
      ‖centeredG (wPair closedPair a) ClosedThree.maxState‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, inner_maxState]

theorem normSq_T : ‖centeredG (Torus.torusPairs k (0, i)) (Torus.maxState k)‖ ^ 2 = 9 / 16 := by
  rw [normSq_maxState]
  exact BoxExcess.variance_TcOp_maxState

theorem normSq_P : ‖centeredG (Torus.torusPairs k (1, i)) (Torus.maxState k)‖ ^ 2 = 5 / 6 := by
  rw [normSq_maxState]
  exact BoxExcess.variance_PdOp_maxState

theorem normSq_inner :
    ‖inner ℂ (centeredG (Torus.torusPairs k (0, i)) (Torus.maxState k))
      (centeredG (Torus.torusPairs k (1, i)) (Torus.maxState k))‖ ^ 2 = 3 / 8 := by
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hc := BoxExcess.covariance_maxState
  have hi := BoxExcess.imPart_maxState
  rw [covariance] at hc
  rw [imPart] at hi
  have e0 : centeredG (wPair closedPair 0) ClosedThree.maxState =
      centered ClosedThree.TcOp ClosedThree.maxState := rfl
  have e1 : centeredG (wPair closedPair 1) ClosedThree.maxState =
      centered (PdOp 3) ClosedThree.maxState := rfl
  rw [inner_maxState, Complex.sq_norm, Complex.normSq_apply, e0, e1, hc, hi]
  nlinarith [h6]

/-- **At `c` every axis of the torus resolves `4/5`.** -/
theorem lightShare_maxState :
    lightShare (centeredG (Torus.torusPairs k (0, i)) (Torus.maxState k))
      (centeredG (Torus.torusPairs k (1, i)) (Torus.maxState k)) = 4 / 5 := by
  rw [lightShare, mul_pow, normSq_T, normSq_P, normSq_inner]
  norm_num

/-- **At `c` every axis of the torus keeps `1/5` dark.** -/
theorem darkShare_maxState :
    darkShare (centeredG (Torus.torusPairs k (0, i)) (Torus.maxState k))
      (centeredG (Torus.torusPairs k (1, i)) (Torus.maxState k)) = 1 / 5 := by
  have h := lightShare_add_darkShare (Torus.maxState k) i (by
    intro h0
    have := congrArg (· ^ 2) h0
    simp only [mul_pow, normSq_T, normSq_P] at this
    norm_num at this)
  rw [lightShare_maxState] at h
  linarith

end MaxState

end TorusDark
