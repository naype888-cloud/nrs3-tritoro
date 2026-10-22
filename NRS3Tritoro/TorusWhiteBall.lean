/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSaturation
public import NRS3Tritoro.OpenCubeBoundary
public import NRS3Tritoro.FiberBoundary
public import NRS3Dark.Dark

/-!
# The white ball: a quantum that is not filled shines on its edge

`TorusSaturation` declares Nava's postulate: compress matter until a quantum is filled to
capacity, `H = S`, and the region becomes dark. This file declares its other half. If the
compression does not fill the quantum, the region becomes a ball of yarn whose thread glows: from
outside one sees a white point, the interior stays dark, and the face seen is the sum of all the
connections the boundary allows, `2^|X|` patterns laid over the quanta (`card_cutPatterns`).

**Nava's white ball (declared).** `HWhiteBall X`, on any finite boundary `X`: the dark share of a
region is positive (the interior stays dark), at most `1`, equal to `1` at saturation and below
`1` under capacity. From it, with `BoundaryBits.saturated_iff_uniform`:

  `0 < lightShare d ↔ d ≠ uniform`,

the white point is seen exactly when the quantum is not filled. The bridge is satisfiable with
the face giving at most `Ω_b` (`omegaPi`), in the proportion of the capacity left unused.

All of it holds on the three topologies: the open cube `R³` (one wall), `T³` (two walls, where
the white ball gives `TorusSaturation.HSaturationDark`) and the fibred box (across `x` and across
the fiber `w`).

## Main results

- `TorusWhiteBall.HWhiteBall` : Nava's white ball, declared.
- `TorusWhiteBall.HWhiteBall.darkShare_eq_one_iff` : dark exactly at the uniform distribution.
- `TorusWhiteBall.HWhiteBall.lightShare_pos_iff` : the white point iff the quantum is not full.
- `TorusWhiteBall.ofModel`, `TorusWhiteBall.ofModel_lightShare_le` : the witness, light `≤ Ω_b`.
- `TorusWhiteBall.capacity_openCube`, `capacity_torus`, `capacity_fiberX`, `capacity_fiberW` :
  the capacity on the three topologies.
- `TorusWhiteBall.toSaturationDark` : on `T³` the white ball gives Nava's saturation postulate.
-/

@[expose] public noncomputable section

open BoundaryBits NRS3Dark OmegaFromPi

namespace TorusWhiteBall

variable {α : Type*} {X : Finset α}

/-! ## 1. The white ball, declared -/

/-- The capacity of the boundary, `S = |X| log 2`. -/
abbrev capacity (X : Finset α) : ℝ := X.card * Real.log 2

lemma capacity_pos (hX : X.Nonempty) : 0 < capacity X :=
  mul_pos (by exact_mod_cast hX.card_pos) (Real.log_pos one_lt_two)

/-- **Nava's white ball (declared hypothesis).** The interior of a region stays dark, a full
quantum is all dark, and a quantum below capacity keeps some light on its edge. -/
structure HWhiteBall (X : Finset α) where
  darkShare : ProbDistribution (Config X) → ℝ
  interior : ∀ d, 0 < darkShare d
  darkShare_le_one : ∀ d, darkShare d ≤ 1
  saturation : ∀ d, Hₛ d = capacity X → darkShare d = 1
  below : ∀ d, Hₛ d < capacity X → darkShare d < 1

namespace HWhiteBall

variable (W : HWhiteBall X)

/-- The light share of a region: what its edge gives. -/
def lightShare (d : ProbDistribution (Config X)) : ℝ := 1 - W.darkShare d

theorem lightShare_nonneg (d : ProbDistribution (Config X)) : 0 ≤ W.lightShare d :=
  sub_nonneg.2 (W.darkShare_le_one d)

/-- The interior stays dark: the light share never reaches `1`. -/
theorem lightShare_lt_one (d : ProbDistribution (Config X)) : W.lightShare d < 1 :=
  sub_lt_self 1 (W.interior d)

/-- **Dark exactly when the quantum is full**, every configuration alike. -/
theorem darkShare_eq_one_iff {d : ProbDistribution (Config X)} :
    W.darkShare d = 1 ↔ d = ProbDistribution.uniform := by
  rw [← saturated_iff_uniform]
  refine ⟨fun h => ?_, W.saturation d⟩
  by_contra hne
  exact (W.below d (lt_of_le_of_ne (entropy_le d) hne)).ne h

/-- **The white point.** The edge shines iff the quantum is not filled. -/
theorem lightShare_pos_iff {d : ProbDistribution (Config X)} :
    0 < W.lightShare d ↔ d ≠ ProbDistribution.uniform := by
  rw [lightShare, sub_pos, Ne, ← W.darkShare_eq_one_iff]
  exact ⟨ne_of_lt, fun h => lt_of_le_of_ne (W.darkShare_le_one d) h⟩

end HWhiteBall

/-! ## 2. The witness: the face gives at most `Ω_b` -/

lemma fill_nonneg (d : ProbDistribution (Config X)) : 0 ≤ Hₛ d / capacity X :=
  div_nonneg (Hₛ_nonneg d) (by positivity)

lemma fill_le_one (hX : X.Nonempty) (d : ProbDistribution (Config X)) :
    Hₛ d / capacity X ≤ 1 :=
  (div_le_one (capacity_pos hX)).2 (entropy_le d)

/-- The dark share of the witness: the edge gives `Ω_b` times the capacity left unused. -/
def model (Ωb : ℝ) (X : Finset α) (d : ProbDistribution (Config X)) : ℝ :=
  1 - Ωb * (1 - Hₛ d / capacity X)

/-- **The white ball is satisfiable**, for any `0 < Ω_b < 1`. -/
def ofModel (hX : X.Nonempty) {Ωb : ℝ} (h0 : 0 < Ωb) (h1 : Ωb < 1) : HWhiteBall X where
  darkShare := model Ωb X
  interior d := by
    have := fill_nonneg d
    unfold model
    nlinarith
  darkShare_le_one d := by
    have := fill_le_one hX d
    unfold model
    nlinarith
  saturation d h := by
    rw [model, h, div_self (capacity_pos hX).ne', sub_self, mul_zero, sub_zero]
  below d h := by
    have : Hₛ d / capacity X < 1 := (div_lt_one (capacity_pos hX)).2 h
    unfold model
    nlinarith

section Witness

variable (hX : X.Nonempty) {Ωb : ℝ} (h0 : 0 < Ωb) (h1 : Ωb < 1)

/-- The light of the witness is `Ω_b` times the unused fraction of the capacity. -/
theorem ofModel_lightShare (d : ProbDistribution (Config X)) :
    (ofModel hX h0 h1).lightShare d = Ωb * (capacity X - Hₛ d) / capacity X := by
  simp only [HWhiteBall.lightShare, ofModel, model]
  field_simp [(capacity_pos hX).ne']
  ring

/-- **The edge never gives more than `Ω_b`.** -/
theorem ofModel_lightShare_le (d : ProbDistribution (Config X)) :
    (ofModel hX h0 h1).lightShare d ≤ Ωb := by
  have := fill_nonneg d
  simp only [HWhiteBall.lightShare, ofModel, model]
  nlinarith

/-- A single configuration, nothing superposed, gives the whole `Ω_b`. -/
theorem ofModel_lightShare_constant (S : Config X) :
    (ofModel hX h0 h1).lightShare (ProbDistribution.constant S) = Ωb := by
  simp [HWhiteBall.lightShare, ofModel, model, Hₛ_constant_eq_zero]

end Witness

/-- The white ball with the measured `Ω_b`. -/
def omegaWhiteBall (hX : X.Nonempty) : HWhiteBall X :=
  ofModel hX (Ωb := omegaPi) (by linarith [omegaPi_gt]) (by linarith [omegaPi_lt])

/-! ## 3. The three topologies -/

variable {dx dy dz c : ℕ}

/-- `R³`: one wall, `S = dy · dz · log 2`. -/
theorem capacity_openCube (hc : c + 1 < dx) :
    capacity (OpenCubeBoundary.openCrossSteps dx dy dz c) = ((dy * dz : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, OpenCubeBoundary.card_openCrossSteps hc]


/-- `T³`: two walls, `S = 2 · dy · dz · log 2`. -/
theorem capacity_torus (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    capacity (TorusArea.crossSteps dx dy dz c) = ((2 * (dy * dz) : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, TorusArea.card_crossSteps hc hd]


/-- **On `T³` the white ball gives Nava's saturation postulate.** -/
def toSaturationDark (W : HWhiteBall (TorusArea.crossSteps dx dy dz c)) :
    TorusSaturation.HSaturationDark dx dy dz c where
  darkShare := W.darkShare
  darkShare_le_one := W.darkShare_le_one
  saturation d h := W.saturation d (h.trans
    ((TorusBekenstein.log_card_config c).symm.trans (log_card_config _)))

/-- Fibred box across `x`: one wall, `S = dy · dz · 3 · log 2`. -/
theorem capacity_fiberX (hc : c + 1 < dx) :
    capacity (FiberBoundary.xSteps dx dy dz c) = ((dy * dz * 3 : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, FiberBoundary.card_xSteps hc]


/-- Fibred box across the fiber: two walls, `S = 2 · dx · dy · dz · log 2`. -/
theorem capacity_fiberW (hc : c + 1 < 3) :
    capacity (FiberBoundary.wSteps dx dy dz c) = ((2 * (dx * dy * dz) : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, FiberBoundary.card_wSteps hc]


end TorusWhiteBall
