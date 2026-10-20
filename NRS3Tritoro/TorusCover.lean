/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Linarith

/-!
# The closed axis is finite, and the path to a point is not

On a closed axis of `d` positions the space has `d` points. A path of `k` steps of the closed
transport, always in the same direction, ends at position `k mod d`. So the same point is reached
by paths of length `x`, `x + d`, `x + 2d`, …: seen along one direction, the axis repeats without
end. The unbounded extent is the covering of the ring by the line, not more space.

## Main results

- `TorusCover.finite_positions` : the axis has finitely many positions.
- `TorusCover.infinite_paths` : the paths of any number of steps that end at a given point form
  an infinite set.
- `TorusCover.exists_path_longer` : for every length there is a longer path to the same point.
- `TorusCover.distance_le` : the true distance on the axis never exceeds `d / 2`.
-/

@[expose] public section

namespace TorusCover

variable {d : ℕ} [NeZero d]

/-- A closed axis has finitely many positions. -/
theorem finite_positions : Finite (ZMod d) := inferInstance

/-- For every number of steps `N` there is a longer path of the closed transport that ends at the
same position `x`. -/
theorem exists_path_longer (x : ZMod d) (N : ℕ) : ∃ k : ℕ, N < k ∧ (k : ZMod d) = x := by
  refine ⟨N * d + x.val + d, ?_, ?_⟩
  · have : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    nlinarith [Nat.zero_le (x.val)]
  · push_cast
    simp

/-- **The paths to a given point of the closed axis form an infinite set.** -/
theorem infinite_paths (x : ZMod d) : {k : ℕ | (k : ZMod d) = x}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨N, hN⟩ => ?_
  obtain ⟨k, hk, hkx⟩ := exists_path_longer x N
  exact absurd (hN hkx) (not_le.2 hk)

/-- The distance on the closed axis between positions that differ by `k` steps is
`min (k mod d) (d - k mod d)`; it never exceeds `d / 2`. -/
theorem distance_le (k : ℕ) : min (k % d) (d - k % d) ≤ d / 2 := by
  have h := Nat.mod_lt k (Nat.pos_of_ne_zero (NeZero.ne d))
  omega

end TorusCover
