/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusLayers

/-!
# Stacking light until the face is full: the inverted quantum

`TorusLayers` crumples the bubble wrap without popping it, and only light is left. This file keeps
stacking. The face has a fixed capacity `S = |X| log 2`, its area, while the layers behind it grow
with every layer (`TorusLayers.card_layerSteps`). Stack enough layers of light and the face is
full: it turns dark. It is the inverted quantum. The black background has nothing in it; the
collapsed quantum has everything in it, spread so evenly that every step of its face is open with
probability exactly `1/2` (`BoundaryBits.openProb_uniform`) and nothing stands out. It is a full
quantum, not a point: no state fixes position absolutely
(`PlatformBlindness.variance_T_pos_of_P_eigenvector`).

**Each layer of light feeds the face (declared).** `HStack X ε`: the face after `n` layers is a
distribution `faceOf n` of the boundary `X`, and every new layer adds at least `ε > 0` to what the
face holds, until the face is full. From it, after `n` layers the face holds at least
`min S (n ε)`, and after `⌈S / ε⌉` layers it is full, dark under `HWhiteBall`, with no gradient.

All of it on the three topologies: `R³` (`S = dy dz log 2`), `T³` (`S = 2 dy dz log 2`) and the
fibred box (`S = 3 dy dz log 2` across `x`, `S = 2 dx dy dz log 2` across `w`).

## Main results

- `TorusStack.HStack` : each layer of light feeds the face, declared.
- `TorusStack.HStack.min_le_entropy` : after `n` layers the face holds at least `min S (n ε)`.
- `TorusStack.HStack.full_of_le` : once `S ≤ n ε` the face is full, uniform.
- `TorusStack.HStack.dark_of_le`, `TorusStack.HStack.dark_ceil` : then it is dark, and
  `⌈S / ε⌉` layers are enough.
- `TorusStack.HStack.no_gradient` : the collapsed face has every step open with probability `1/2`.
- `TorusStack.oneLayer` : the bridge is satisfiable.
- `TorusStack.dark_openCube`, `dark_torus`, `dark_fiberX`, `dark_fiberW` : the three topologies.
-/

@[expose] public noncomputable section

open BoundaryBits TorusWhiteBall

namespace TorusStack

variable {α : Type*} {X : Finset α}

/-! ## 1. Each layer feeds the face -/

/-- **Each layer of light feeds the face (declared hypothesis).** The face after `n` layers is
`faceOf n`, and a new layer adds at least `ε` to what it holds, until it is full. -/
structure HStack (X : Finset α) (ε : ℝ) where
  faceOf : ℕ → ProbDistribution (Config X)
  ε_pos : 0 < ε
  feed : ∀ n, min (capacity X) (Hₛ (faceOf n) + ε) ≤ Hₛ (faceOf (n + 1))

namespace HStack

variable {ε : ℝ} (St : HStack X ε)

/-- **After `n` layers the face holds at least `min S (n ε)`.** -/
theorem min_le_entropy (n : ℕ) : min (capacity X) (n * ε) ≤ Hₛ (St.faceOf n) := by
  induction n with
  | zero => simpa using le_trans (min_le_right _ _) (Hₛ_nonneg (St.faceOf 0))
  | succ n ih =>
    refine le_trans ?_ (St.feed n)
    rcases le_total (capacity X) (n * ε) with h | h
    · rw [min_eq_left h] at ih
      rw [min_eq_left (by linarith [St.ε_pos] : capacity X ≤ Hₛ (St.faceOf n) + ε)]
      exact min_le_left _ _
    · rw [min_eq_right h] at ih
      push_cast
      exact min_le_min le_rfl (by linarith)

/-- **Once `S ≤ n ε` the face is full**: it is the uniform distribution. -/
theorem full_of_le {n : ℕ} (h : capacity X ≤ n * ε) :
    St.faceOf n = ProbDistribution.uniform := by
  rw [← saturated_iff_uniform]
  refine le_antisymm (entropy_le _) ?_
  simpa [min_eq_left h] using St.min_le_entropy n

/-- **Stacked light collapses**: once `S ≤ n ε` the face is dark. -/
theorem dark_of_le (W : HWhiteBall X) {n : ℕ} (h : capacity X ≤ n * ε) :
    W.lightShare (St.faceOf n) = 0 := by
  rw [HWhiteBall.lightShare, W.darkShare_eq_one_iff.2 (St.full_of_le h), sub_self]

/-- **`⌈S / ε⌉` layers are enough to fill the face.** -/
theorem dark_ceil (W : HWhiteBall X) {n : ℕ} (hn : ⌈capacity X / ε⌉₊ ≤ n) :
    W.lightShare (St.faceOf n) = 0 := by
  have h : capacity X / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  exact St.dark_of_le W ((div_le_iff₀ St.ε_pos).1 h)

/-- **The inverted quantum has no gradient**: every step of the collapsed face is open with
probability `1/2`, and nothing stands out. -/
theorem no_gradient [DecidableEq α] {n : ℕ} (h : capacity X ≤ n * ε) {s : α} (hs : s ∈ X) :
    openProb (St.faceOf n) s = 1 / 2 := by
  rw [St.full_of_le h, openProb_uniform hs]

end HStack

/-- **The bridge is satisfiable**: a single layer of `ε = S` fills the face. -/
def oneLayer (hX : X.Nonempty) : HStack X (capacity X) where
  faceOf n := if n = 0 then ProbDistribution.constant ⟨∅, Finset.empty_mem_powerset _⟩
    else ProbDistribution.uniform
  ε_pos := capacity_pos hX
  feed n := by
    simp only [Nat.add_one_ne_zero, ite_false, entropy_uniform]
    exact min_le_left _ _

/-! ## 2. The three topologies -/

variable {dx dy dz c : ℕ} {ε : ℝ}

/-- `R³`: `⌈dy dz log 2 / ε⌉` layers of light fill the wall. -/
theorem dark_openCube (hc : c + 1 < dx)
    (St : HStack (OpenCubeBoundary.openCrossSteps dx dy dz c) ε)
    (W : HWhiteBall (OpenCubeBoundary.openCrossSteps dx dy dz c)) {n : ℕ}
    (hn : ⌈((dy * dz : ℕ) : ℝ) * Real.log 2 / ε⌉₊ ≤ n) : W.lightShare (St.faceOf n) = 0 :=
  St.dark_ceil W (by rwa [capacity_openCube hc])

/-- `T³`: `⌈2 dy dz log 2 / ε⌉` layers of light fill the two walls. -/
theorem dark_torus (hc : c + 1 < dx) (hd : 3 ≤ dx)
    (St : HStack (TorusArea.crossSteps dx dy dz c) ε)
    (W : HWhiteBall (TorusArea.crossSteps dx dy dz c)) {n : ℕ}
    (hn : ⌈((2 * (dy * dz) : ℕ) : ℝ) * Real.log 2 / ε⌉₊ ≤ n) : W.lightShare (St.faceOf n) = 0 :=
  St.dark_ceil W (by rwa [capacity_torus hc hd])

/-- Fibred box across `x`: `⌈3 dy dz log 2 / ε⌉` layers of light fill the wall. -/
theorem dark_fiberX (hc : c + 1 < dx) (St : HStack (FiberBoundary.xSteps dx dy dz c) ε)
    (W : HWhiteBall (FiberBoundary.xSteps dx dy dz c)) {n : ℕ}
    (hn : ⌈((dy * dz * 3 : ℕ) : ℝ) * Real.log 2 / ε⌉₊ ≤ n) : W.lightShare (St.faceOf n) = 0 :=
  St.dark_ceil W (by rwa [capacity_fiberX hc])

/-- Fibred box across the fiber: `⌈2 dx dy dz log 2 / ε⌉` layers of light fill the two walls. -/
theorem dark_fiberW (hc : c + 1 < 3) (St : HStack (FiberBoundary.wSteps dx dy dz c) ε)
    (W : HWhiteBall (FiberBoundary.wSteps dx dy dz c)) {n : ℕ}
    (hn : ⌈((2 * (dx * dy * dz) : ℕ) : ℝ) * Real.log 2 / ε⌉₊ ≤ n) :
    W.lightShare (St.faceOf n) = 0 :=
  St.dark_ceil W (by rwa [capacity_fiberW hc])

end TorusStack
