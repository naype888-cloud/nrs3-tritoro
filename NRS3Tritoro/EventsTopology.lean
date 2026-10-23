/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.QuantumEvents
public import NRS3Tritoro.BoundaryBits
public import NRS3Tritoro.TorusUniverseRS

/-!
# Events in a topology: the boundary is Kolmogorov, the bulk is Robertson

`QuantumEvents` gives the probability of yes/no events on any Hilbert space. Here the events are
read on the spaces of the program.

**The boundary.** A cut `X` of any space (the open cube, the three-torus, the fibred box) has
`2^|X|` configurations (`BoundaryBits`). On `ℂ^{configurations}` the event "the step `s` is
open" is the diagonal projection onto the configurations that contain `s`, and a distribution `d`
is the state `ψ_d = Σ √d(S) e_S`. Then

* `p(s open) = openProb d s`: the boundary bits are events, with the probabilities of
  `BoundaryBits`;
* all of them commute: the boundary is a family of compatible events, so it is classical
  probability (Kolmogorov), with the bit variance `p (1 − p)` of `BoundaryBits`.

**The bulk.** On the axis of the universe `ZMod L` the event "the excitation is at `j`" is the
projection onto `e_j`, with `p_j = |ψ_j|²`. The transport `T°` moves it, and its rate is the
flow through the two links of `j`:

  `⟨i[T°, Π_j]⟩ = F_{j−1} − F_j`,  `F_k = Im(ψ̄_{k+1} ψ_k)`,

the continuity equation. The rates add up to `0` around the closed axis (nothing is lost), the
flows add up to the velocity `⟨K⟩`, and Robertson for bits bounds each rate,
`(F_{j−1} − F_j)² ≤ 4 Var T° · p_j (1 − p_j)`: a site that is certainly occupied or certainly
empty does not change.

## Main results

- `EventsTopology.prob_openEvent` : `p(s open) = openProb d s`.
- `EventsTopology.openEvent_comm` : the boundary events commute.
- `EventsTopology.variance_openEvent` : their variance is the bit variance.
- `EventsTopology.rate_siteEvent` : the continuity equation `rate_j = F_{j−1} − F_j`.
- `EventsTopology.sum_rate_siteEvent` : the rates add up to `0` on the closed axis.
- `EventsTopology.velocity_eq_sum_flow` : `⟨K⟩ = Σ F_j`.
- `EventsTopology.flow_sq_le` : `(F_{j−1} − F_j)² ≤ 4 Var T° · p_j (1 − p_j)`.
- `EventsTopology.flow_eq_of_decided` : a decided site does not change.
-/

@[expose] public noncomputable section

open Complex QuantumEvents

namespace EventsTopology

/-! ## 1. The boundary: compatible events -/

section Boundary

variable {α : Type*} [DecidableEq α] {X : Finset α}

/-- The states of the boundary: one amplitude per configuration. -/
abbrev HB (X : Finset α) := EuclideanSpace ℂ (BoundaryBits.Config X)

/-- The diagonal projection onto the configurations where `s` is open. -/
def openProj (s : α) : HB X →ₗ[ℂ] HB X where
  toFun ψ := WithLp.toLp 2 fun S => if s ∈ S.1 then ψ S else 0
  map_add' ψ φ := by ext S; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' z ψ := by ext S; simp only [PiLp.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem openProj_apply (s : α) (ψ : HB X) (S : BoundaryBits.Config X) :
    openProj s ψ S = if s ∈ S.1 then ψ S else 0 := rfl

/-- **The event "the step `s` is open".** -/
def openEvent (s : α) : Event (HB X) where
  P := openProj s
  symm φ ψ := by
    simp only [PiLp.inner_apply, openProj_apply]
    exact Finset.sum_congr rfl fun S _ => by split_ifs <;> simp
  idem ψ := by ext S; simp only [openProj_apply]; split_ifs <;> rfl

/-- The state of a distribution, `ψ_d = Σ √d(S) e_S`. -/
def bitState (d : ProbDistribution (BoundaryBits.Config X)) : HB X :=
  WithLp.toLp 2 fun S => ((Real.sqrt (d S) : ℝ) : ℂ)

omit [DecidableEq α] in
theorem norm_bitState (d : ProbDistribution (BoundaryBits.Config X)) : ‖bitState d‖ = 1 := by
  have h : ‖bitState d‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [bitState, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt Prob.zero_le_coe]
    exact d.normalized
  nlinarith [norm_nonneg (bitState d)]

/-- **The boundary bits are events**: `p(s open) = openProb d s`. -/
theorem prob_openEvent (d : ProbDistribution (BoundaryBits.Config X)) (s : α) :
    prob (openEvent s) (bitState d) = BoundaryBits.openProb d s := by
  rw [prob_eq_norm_sq, EuclideanSpace.norm_sq_eq, BoundaryBits.openProb]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [openEvent, openProj_apply, bitState]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt Prob.zero_le_coe]
  · simp

/-- **The boundary events commute**: the boundary is classical probability. -/
theorem openEvent_comm (s t : α) (ψ : HB X) :
    (openEvent s).P ((openEvent t).P ψ) = (openEvent t).P ((openEvent s).P ψ) := by
  ext S; simp only [openEvent, openProj_apply]; split_ifs <;> rfl

/-- Their variance is the bit variance of `BoundaryBits`. -/
theorem variance_openEvent (d : ProbDistribution (BoundaryBits.Config X)) (s : α) :
    variance (openEvent s).P (bitState d) =
      BoundaryBits.openProb d s * (1 - BoundaryBits.openProb d s) := by
  rw [variance_eq _ (norm_bitState d), prob_openEvent]

end Boundary

/-! ## 2. The bulk: the site events of the axis of the universe -/

section Bulk

open TorusUniverse

variable {L : ℕ} [NeZero L]

/-- The projection onto the site `j`. -/
def siteProj (j : ZMod L) : HU L →ₗ[ℂ] HU L where
  toFun ψ := WithLp.toLp 2 fun k => if k = j then ψ k else 0
  map_add' ψ φ := by ext k; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' z ψ := by ext k; simp only [PiLp.smul_apply, smul_eq_mul]; split_ifs <;> simp

omit [NeZero L] in
theorem siteProj_apply (j : ZMod L) (ψ : HU L) (k : ZMod L) :
    siteProj j ψ k = if k = j then ψ k else 0 := rfl

/-- **The event "the excitation is at `j`".** -/
def siteEvent (j : ZMod L) : Event (HU L) where
  P := siteProj j
  symm φ ψ := by
    simp only [PiLp.inner_apply, siteProj_apply]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  idem ψ := by ext k; simp only [siteProj_apply]; split_ifs <;> rfl

theorem siteEvent_P (j : ZMod L) : (siteEvent j).P = siteProj j := rfl

theorem inner_siteProj (j : ZMod L) (φ ψ : HU L) :
    inner ℂ φ (siteProj j ψ) = (starRingEnd ℂ) (φ j) * ψ j := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · simp [siteProj_apply, mul_comm]
  · intro k _ hk; simp [siteProj_apply, hk]
  · simp

/-- `p_j = |ψ_j|²`. -/
theorem prob_siteEvent (j : ZMod L) (ψ : HU L) : prob (siteEvent j) ψ = ‖ψ j‖ ^ 2 := by
  rw [prob, siteEvent, inner_siteProj, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The flow through the link `k → k + 1`, `F_k = Im(ψ̄_{k+1} ψ_k)`. -/
def flow (ψ : HU L) (k : ZMod L) : ℝ := ((starRingEnd ℂ) (ψ (k + 1)) * ψ k).im

/-- **The continuity equation**: the rate of the site event is the flow in minus the flow out,
`⟨i[T°, Π_j]⟩ = F_{j−1} − F_j`. -/
theorem rate_siteEvent (j : ZMod L) (ψ : HU L) :
    rate transport (siteEvent j) ψ = flow ψ (j - 1) - flow ψ j := by
  rw [rate_eq transport_isSymmetric, siteEvent_P, inner_siteProj, transport_apply, flow, flow,
    sub_add_cancel]
  simp only [Complex.conj_im, map_div₀, map_add, map_ofNat,
    Complex.mul_im, Complex.div_im, Complex.div_re, Complex.add_re, Complex.add_im,
    Complex.conj_re]
  norm_num
  ring

/-- **Nothing is lost**: the rates add up to `0` around the closed axis. -/
theorem sum_rate_siteEvent (ψ : HU L) : ∑ j, rate transport (siteEvent j) ψ = 0 := by
  simp only [rate_siteEvent, Finset.sum_sub_distrib]
  rw [sum_sub_one (fun k => flow ψ k), sub_self]

/-- **The velocity is the total flow**: `⟨K⟩ = Σ F_j`. -/
theorem velocity_eq_sum_flow (ψ : HU L) : velocity ψ = ∑ j, flow ψ j := by
  have h : velocity ψ = ∑ j, (flow ψ j + flow ψ (j - 1)) / 2 := by
    rw [velocity, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [current_apply, RCLike.inner_apply', flow, sub_add_cancel, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
      Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im]
    norm_num
    ring
  rw [h, ← Finset.sum_div, Finset.sum_add_distrib, sum_sub_one (fun k => flow ψ k)]
  ring

/-- **Robertson for the site**: `(F_{j−1} − F_j)² ≤ 4 Var T° · p_j (1 − p_j)`. -/
theorem flow_sq_le (j : ZMod L) {ψ : HU L} (hψ : ‖ψ‖ = 1) :
    (flow ψ (j - 1) - flow ψ j) ^ 2 ≤
      4 * variance transport ψ * (‖ψ j‖ ^ 2 * (1 - ‖ψ j‖ ^ 2)) := by
  rw [← rate_siteEvent, ← prob_siteEvent]
  exact rate_sq_le transport_isSymmetric (siteEvent j) hψ

/-- **A decided site does not change**: if `p_j ∈ {0, 1}`, the flow in equals the flow out. -/
theorem flow_eq_of_decided (j : ZMod L) {ψ : HU L} (hψ : ‖ψ‖ = 1)
    (hp : ‖ψ j‖ ^ 2 = 0 ∨ ‖ψ j‖ ^ 2 = 1) : flow ψ (j - 1) = flow ψ j := by
  have h := flow_sq_le j hψ
  have h0 : ‖ψ j‖ ^ 2 * (1 - ‖ψ j‖ ^ 2) = 0 := by rcases hp with hp | hp <;> rw [hp] <;> ring
  rw [h0, mul_zero] at h
  nlinarith only [h, sq_nonneg (flow ψ (j - 1) - flow ψ j)]

end Bulk

end EventsTopology
