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
outside one sees a white point, and the face seen is the sum of all the connections the boundary
allows, `2^|X|` patterns laid over the quanta (`card_cutPatterns`). The quantum itself is
transparent: its dark share is the dark field, which gives nothing to see, and behind it there is
only black, what has not happened. It turns black itself only when it is filled.

**Nava's white ball (declared).** `HWhiteBall X`, on any finite boundary `X`: the dark share of a
region is positive (the transparent dark field of the interior), at most `1`, equal to `1` at
saturation and below `1` under capacity. From it, with `BoundaryBits.saturated_iff_uniform`:

  `0 < lightShare d ↔ d ≠ uniform`,

the white point is seen exactly when the quantum is not filled. The bridge is satisfiable with
the face giving at most `Ω_b` (`omegaPi`), in the proportion of the capacity left unused.

**The mass of the core.** The Chandrasekhar mass `M_Ch = ω₃⁰ √(3π) m_P³ / (2 (μ_e m_H)²)` with
CODATA 2018 and IAU 2015 data is `1.43 M☉ < M_Ch < 1.44 M☉`. The core bridge `HCoreCollapse`
fills the quantum exactly when the core reaches its collapse mass, which the data place between
the heaviest measured neutron star, PSR J0740+6620 (`2.08 M☉`), and the causal bound of Rhoades
and Ruffini (`3.2 M☉`). So every white dwarf, Sirius B and PSR J0740+6620 are white points, and
Cygnus X-1 (`21.2 M☉`) and any core of `30 M☉` are dark. The threshold is on the core, not on
the star that formed it.

All of it holds on the three topologies: the open cube `R³` (one wall), `T³` (two walls, where
the white ball gives `TorusSaturation.HSaturationDark`) and the fibred box (across `x` and across
the fiber `w`).

## Main results

- `TorusWhiteBall.HWhiteBall` : Nava's white ball, declared.
- `TorusWhiteBall.HWhiteBall.darkShare_eq_one_iff` : dark exactly at the uniform distribution.
- `TorusWhiteBall.HWhiteBall.lightShare_pos_iff` : the white point iff the quantum is not full.
- `TorusWhiteBall.ofModel`, `TorusWhiteBall.ofModel_lightShare_le` : the witness, light `≤ Ω_b`.
- `TorusWhiteBall.chandrasekharSolar_gt`, `TorusWhiteBall.chandrasekharSolar_lt` :
  `1.43 < M_Ch / M☉ < 1.44`.
- `TorusWhiteBall.HCoreCollapse` : the core fills the quantum at its collapse mass, declared.
- `TorusWhiteBall.white_iff` : white point iff the core is below the collapse mass.
- `TorusWhiteBall.whiteDwarf_white`, `siriusB_white`, `psrJ0740_white`, `cygnusX1_dark`,
  `thirty_dark` : the data.
- `TorusWhiteBall.exists_white_and_dark` : the two bridges together are consistent, and
  `openCube_exists`, `torus_exists`, `fiberX_exists`, `fiberW_exists` on the three topologies.
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

/-- **Nava's white ball (declared hypothesis).** The interior of a region is transparent dark
field, a full quantum is all dark, and a quantum below capacity keeps some light on its edge. -/
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

/-- The interior is transparent dark field: the light share never reaches `1`. -/
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

/-! ## 3. The Chandrasekhar mass, from CODATA 2018 and IAU 2015 -/

/-- The Planck mass `√(ħ c / G)`, CODATA 2018, in kg. -/
def planckMass : ℝ := 2.176434e-8

/-- The mass of the hydrogen atom, `1.00782503223 u`, CODATA 2018, in kg. -/
def hydrogenMass : ℝ := 1.6735328e-27

/-- The nominal solar mass `GM☉ / G = 1.3271244e20 / 6.67430e-11`, IAU 2015, in kg. -/
def solarMass : ℝ := 1.98841e30

/-- `ω₃⁰`, the Lane–Emden constant of the polytrope `n = 3` (Chandrasekhar 1939). -/
def laneEmden3 : ℝ := 2.01824

/-- Nucleons per electron of a helium, carbon or oxygen core, `μ_e = 2` (iron has `56/26`). -/
def nucleonsPerElectron : ℝ := 2

/-- **The Chandrasekhar mass** (1931), `ω₃⁰ √(3π) m_P³ / (2 (μ_e m_H)²)`, in kg. -/
def chandrasekharMass : ℝ :=
  laneEmden3 * √(3 * Real.pi) / 2 * planckMass ^ 3 / (nucleonsPerElectron * hydrogenMass) ^ 2

/-- The Chandrasekhar mass in solar masses. -/
def chandrasekharSolar : ℝ := chandrasekharMass / solarMass

lemma sqrt_three_pi_gt : (3.0699 : ℝ) < √(3 * Real.pi) := by
  rw [Real.lt_sqrt (by norm_num)]
  nlinarith [Real.pi_gt_d6]

lemma sqrt_three_pi_lt : √(3 * Real.pi) < 3.07 := by
  rw [Real.sqrt_lt' (by norm_num)]
  nlinarith [Real.pi_lt_d6]

lemma chandrasekharSolar_eq : chandrasekharSolar = √(3 * Real.pi) *
    (laneEmden3 / 2 * planckMass ^ 3 / (nucleonsPerElectron * hydrogenMass) ^ 2 / solarMass) := by
  unfold chandrasekharSolar chandrasekharMass
  ring

theorem chandrasekharSolar_gt : (1.43 : ℝ) < chandrasekharSolar := by
  rw [chandrasekharSolar_eq]
  refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_right sqrt_three_pi_gt.le ?_)
  · norm_num [laneEmden3, planckMass, nucleonsPerElectron, hydrogenMass, solarMass]
  · norm_num [laneEmden3, planckMass, nucleonsPerElectron, hydrogenMass, solarMass]

theorem chandrasekharSolar_lt : chandrasekharSolar < 1.44 := by
  rw [chandrasekharSolar_eq]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right sqrt_three_pi_lt.le ?_) ?_
  · norm_num [laneEmden3, planckMass, nucleonsPerElectron, hydrogenMass, solarMass]
  · norm_num [laneEmden3, planckMass, nucleonsPerElectron, hydrogenMass, solarMass]

/-! ## 4. The core fills the quantum at its collapse mass -/

/-- Sirius B, `1.018 ± 0.011 M☉` (Bond et al. 2017, ApJ 840, 70). -/
def siriusB : ℝ := 1.018

/-- PSR J0740+6620, `2.08 ± 0.07 M☉` (Fonseca et al. 2021, ApJL 915, L12). -/
def psrJ0740 : ℝ := 2.08

/-- Cygnus X-1, `21.2 ± 2.2 M☉` (Miller-Jones et al. 2021, Science 371, 1046). -/
def cygnusX1 : ℝ := 21.2

/-- The causal bound on a neutron star, `3.2 M☉` (Rhoades and Ruffini 1974, PRL 32, 324). -/
def causalLimit : ℝ := 3.2

/-- **The core bridge (declared hypothesis).** A core of `M` solar masses sets the distribution
of the boundary; it fills the quantum exactly when `M` reaches the collapse mass. The measured
PSR J0740+6620 shines, so the collapse mass is above it, and it is below the causal bound. -/
structure HCoreCollapse (X : Finset α) where
  collapseMass : ℝ
  boundary : ℝ → ProbDistribution (Config X)
  saturated_iff : ∀ M, Hₛ (boundary M) = capacity X ↔ collapseMass ≤ M
  shining : psrJ0740 < collapseMass
  causal : collapseMass ≤ causalLimit

variable (W : HWhiteBall X) (C : HCoreCollapse X)

/-- **The white point iff the core is below the collapse mass.** -/
theorem white_iff {M : ℝ} : 0 < W.lightShare (C.boundary M) ↔ M < C.collapseMass := by
  rw [W.lightShare_pos_iff, Ne, ← saturated_iff_uniform, C.saturated_iff, not_le]

/-- A core at or above the collapse mass is dark. -/
theorem dark_of_le {M : ℝ} (h : C.collapseMass ≤ M) : W.lightShare (C.boundary M) = 0 := by
  rw [HWhiteBall.lightShare, W.darkShare_eq_one_iff.2 (saturated_iff_uniform.1
    ((C.saturated_iff M).2 h)), sub_self]

/-- Every white dwarf is below the collapse mass. -/
theorem chandrasekharSolar_lt_collapseMass : chandrasekharSolar < C.collapseMass := by
  have := C.shining
  unfold psrJ0740 at this
  linarith [chandrasekharSolar_lt]

/-- **Every white dwarf is a white point.** -/
theorem whiteDwarf_white {M : ℝ} (h : M ≤ chandrasekharSolar) :
    0 < W.lightShare (C.boundary M) :=
  (white_iff W C).2 (h.trans_lt (chandrasekharSolar_lt_collapseMass C))

theorem siriusB_white : 0 < W.lightShare (C.boundary siriusB) :=
  whiteDwarf_white W C (by unfold siriusB; linarith [chandrasekharSolar_gt])

theorem psrJ0740_white : 0 < W.lightShare (C.boundary psrJ0740) :=
  (white_iff W C).2 C.shining

/-- Above the causal bound every core is dark. -/
theorem dark_of_causalLimit_le {M : ℝ} (h : causalLimit ≤ M) : W.lightShare (C.boundary M) = 0 :=
  dark_of_le W C (C.causal.trans h)

theorem cygnusX1_dark : W.lightShare (C.boundary cygnusX1) = 0 :=
  dark_of_causalLimit_le W C (by norm_num [causalLimit, cygnusX1])

theorem thirty_dark : W.lightShare (C.boundary 30) = 0 :=
  dark_of_causalLimit_le W C (by norm_num [causalLimit])

/-- The core bridge is satisfiable: collapse mass `3 M☉`, a single configuration below it. -/
def coreModel (hX : X.Nonempty) : HCoreCollapse X where
  collapseMass := 3
  boundary M := if 3 ≤ M then ProbDistribution.uniform
    else ProbDistribution.constant ⟨∅, Finset.empty_mem_powerset _⟩
  saturated_iff M := by
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => entropy_uniform X⟩
    · rw [Hₛ_constant_eq_zero]
      exact ⟨fun h' => absurd h' (capacity_pos hX).ne, fun h' => absurd h' h⟩
  shining := by norm_num [psrJ0740]
  causal := by norm_num [causalLimit]

/-- **The two bridges together are consistent**: Sirius B shines, Cygnus X-1 is dark. -/
theorem exists_white_and_dark (hX : X.Nonempty) :
    ∃ (W : HWhiteBall X) (C : HCoreCollapse X),
      0 < W.lightShare (C.boundary siriusB) ∧ W.lightShare (C.boundary cygnusX1) = 0 :=
  ⟨omegaWhiteBall hX, coreModel hX, siriusB_white _ _, cygnusX1_dark _ _⟩

/-! ## 5. The three topologies -/

variable {dx dy dz c : ℕ}

/-- `R³`: one wall, `S = dy · dz · log 2`. -/
theorem capacity_openCube (hc : c + 1 < dx) :
    capacity (OpenCubeBoundary.openCrossSteps dx dy dz c) = ((dy * dz : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, OpenCubeBoundary.card_openCrossSteps hc]

theorem openCube_exists (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    ∃ (W : HWhiteBall (OpenCubeBoundary.openCrossSteps dx dy dz c))
      (C : HCoreCollapse (OpenCubeBoundary.openCrossSteps dx dy dz c)),
      0 < W.lightShare (C.boundary siriusB) ∧ W.lightShare (C.boundary cygnusX1) = 0 :=
  exists_white_and_dark (Finset.card_pos.1 (by
    rw [OpenCubeBoundary.card_openCrossSteps hc]; positivity))

/-- `T³`: two walls, `S = 2 · dy · dz · log 2`. -/
theorem capacity_torus (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    capacity (TorusArea.crossSteps dx dy dz c) = ((2 * (dy * dz) : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, TorusArea.card_crossSteps hc hd]

theorem torus_exists (hc : c + 1 < dx) (hd : 3 ≤ dx) (hy : 0 < dy) (hz : 0 < dz) :
    ∃ (W : HWhiteBall (TorusArea.crossSteps dx dy dz c))
      (C : HCoreCollapse (TorusArea.crossSteps dx dy dz c)),
      0 < W.lightShare (C.boundary siriusB) ∧ W.lightShare (C.boundary cygnusX1) = 0 :=
  exists_white_and_dark (Finset.card_pos.1 (by
    rw [TorusArea.card_crossSteps hc hd]; positivity))

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

theorem fiberX_exists (hc : c + 1 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    ∃ (W : HWhiteBall (FiberBoundary.xSteps dx dy dz c))
      (C : HCoreCollapse (FiberBoundary.xSteps dx dy dz c)),
      0 < W.lightShare (C.boundary siriusB) ∧ W.lightShare (C.boundary cygnusX1) = 0 :=
  exists_white_and_dark (Finset.card_pos.1 (by rw [FiberBoundary.card_xSteps hc]; positivity))

/-- Fibred box across the fiber: two walls, `S = 2 · dx · dy · dz · log 2`. -/
theorem capacity_fiberW (hc : c + 1 < 3) :
    capacity (FiberBoundary.wSteps dx dy dz c) = ((2 * (dx * dy * dz) : ℕ) : ℝ) * Real.log 2 := by
  rw [capacity, FiberBoundary.card_wSteps hc]

theorem fiberW_exists (hc : c + 1 < 3) (hx : 0 < dx) (hy : 0 < dy) (hz : 0 < dz) :
    ∃ (W : HWhiteBall (FiberBoundary.wSteps dx dy dz c))
      (C : HCoreCollapse (FiberBoundary.wSteps dx dy dz c)),
      0 < W.lightShare (C.boundary siriusB) ∧ W.lightShare (C.boundary cygnusX1) = 0 :=
  exists_white_and_dark (Finset.card_pos.1 (by rw [FiberBoundary.card_wSteps hc]; positivity))

end TorusWhiteBall
