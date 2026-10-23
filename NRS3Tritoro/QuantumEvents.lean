/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Events that happen or do not happen: the probability of physics

Kolmogorov (1933) axiomatized probability as a measure on a Boolean algebra of events. In physics
an event is a yes/no question, `1` or `0`, and the questions are the orthogonal projections of a
Hilbert space (von Neumann 1932; Birkhoff–von Neumann 1936). Its probability in a state `ψ` is
`⟨ψ, Pψ⟩`. This file proves, on any complex inner product space:

* **the axioms**: `0 ≤ p ≤ 1`, the certain event has `p = 1`, the impossible one `p = 0`, the
  complement has `1 − p`, and orthogonal events add.
* **every event is a bit**: its variance is `p (1 − p) ≤ 1/4`, the variance of a coin.
* **Kolmogorov is the compatible case**: two commuting events have a joint distribution on
  `{0, 1}²`, four probabilities `≥ 0` that add up to `1`, with the law of total probability.
* **incompatible events cannot both be decided**: `(Im ⟨Pψ, Qψ⟩)² ≤ p (1 − p) q (1 − q)`, and
  `⟨ψ, [P, Q] ψ⟩ = 2i Im ⟨Pψ, Qψ⟩` (Robertson 1929 for bits). If one of them is certain or
  impossible, the commutator vanishes in that state.
* **the time an event takes**: for a generator `G`, the rate of an event, `⟨ψ, i[G, P] ψ⟩`, is at
  most `2 ΔG √(p (1 − p))`: an event changes no faster than the spread of `G` times its own spread
  (Mandelstam–Tamm 1945, algebraic form).

The uncertainty bound is the elementary one; Physlib proves it for partial operators in
`Physlib.QuantumMechanics.Operators.Uncertainty`.

## Main results

- `QuantumEvents.Event`, `QuantumEvents.prob` : events and their probabilities.
- `QuantumEvents.prob_nonneg`, `QuantumEvents.prob_le_one`, `QuantumEvents.prob_top`,
  `QuantumEvents.prob_bot`, `QuantumEvents.prob_compl`, `QuantumEvents.prob_or` : the axioms.
- `QuantumEvents.variance_eq`, `QuantumEvents.variance_le` : every event is a bit.
- `QuantumEvents.joint_sum`, `QuantumEvents.prob_total` : compatible events are Kolmogorov.
- `QuantumEvents.robertson`, `QuantumEvents.robertson_events`, `QuantumEvents.commutator_eq` :
  incompatible events.
- `QuantumEvents.rate_sq_le` : the time an event takes.
-/

@[expose] public noncomputable section

open Complex

namespace QuantumEvents

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## 1. Events -/

/-- An event: a yes/no question, an orthogonal projection. -/
structure Event (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The projection. -/
  P : H →ₗ[ℂ] H
  symm : P.IsSymmetric
  idem : ∀ ψ, P (P ψ) = P ψ

/-- The probability of the event `E` in the state `ψ`, `⟨ψ, Pψ⟩`. -/
def prob (E : Event H) (ψ : H) : ℝ := (inner ℂ ψ (E.P ψ)).re

/-- The certain event. -/
def top : Event H := ⟨LinearMap.id, fun _ _ => rfl, fun _ => rfl⟩

/-- The impossible event. -/
def bot : Event H := ⟨0, LinearMap.IsSymmetric.zero, fun _ => by simp⟩

/-- The complement `1 − P`: the event does not happen. -/
def compl (E : Event H) : Event H where
  P := LinearMap.id - E.P
  symm := LinearMap.IsSymmetric.sub (fun _ _ => rfl) E.symm
  idem ψ := by simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, E.idem]; abel

theorem re_inner_self (ψ : H) : (inner ℂ ψ ψ).re = ‖ψ‖ ^ 2 := by
  simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) ψ

/-- `p = ‖Pψ‖²`. -/
theorem prob_eq_norm_sq (E : Event H) (ψ : H) : prob E ψ = ‖E.P ψ‖ ^ 2 := by
  rw [prob, ← E.idem ψ, ← E.symm, E.idem, re_inner_self]

theorem prob_nonneg (E : Event H) (ψ : H) : 0 ≤ prob E ψ := by
  rw [prob_eq_norm_sq]; positivity

theorem prob_top (ψ : H) : prob (top : Event H) ψ = ‖ψ‖ ^ 2 := re_inner_self ψ

theorem prob_bot (ψ : H) : prob (bot : Event H) ψ = 0 := by
  simp [prob, bot]

/-- **The complement**: `p(not E) = ‖ψ‖² − p(E)`. -/
theorem prob_compl (E : Event H) (ψ : H) : prob (compl E) ψ = ‖ψ‖ ^ 2 - prob E ψ := by
  simp only [prob, compl, LinearMap.sub_apply, LinearMap.id_apply, inner_sub_right,
    Complex.sub_re, re_inner_self]

/-- **`p ≤ 1`** in a unit state. -/
theorem prob_le_one (E : Event H) {ψ : H} (hψ : ‖ψ‖ = 1) : prob E ψ ≤ 1 := by
  have h := prob_nonneg (compl E) ψ
  rw [prob_compl, hψ] at h
  linarith

/-- Two events are orthogonal (mutually exclusive) when `P Q = 0`; then also `Q P = 0`. -/
theorem comp_eq_zero_symm {E F : Event H} (h : ∀ ψ, E.P (F.P ψ) = 0) (ψ : H) :
    F.P (E.P ψ) = 0 := by
  have : ∀ φ, inner ℂ φ (F.P (E.P ψ)) = 0 := fun φ => by
    rw [← F.symm, ← E.symm, h, inner_zero_left]
  simpa using this (F.P (E.P ψ))

/-- `E or F` for mutually exclusive events. -/
def or_ (E F : Event H) (h : ∀ ψ, E.P (F.P ψ) = 0) : Event H where
  P := E.P + F.P
  symm := E.symm.add F.symm
  idem ψ := by
    simp only [LinearMap.add_apply, map_add, E.idem, F.idem, h, comp_eq_zero_symm h]
    abel

/-- **Mutually exclusive events add.** -/
theorem prob_or (E F : Event H) (h : ∀ ψ, E.P (F.P ψ) = 0) (ψ : H) :
    prob (or_ E F h) ψ = prob E ψ + prob F ψ := by
  simp only [prob, or_, LinearMap.add_apply, inner_add_right, Complex.add_re]

/-- `⟨Aψ, ψ⟩` is real for symmetric `A`. -/
theorem inner_self_real {A : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (ψ : H) :
    inner ℂ (A ψ) ψ = ((inner ℂ ψ (A ψ)).re : ℂ) := by
  have h1 : inner ℂ (A ψ) ψ = inner ℂ ψ (A ψ) := hA ψ ψ
  have h2 : (starRingEnd ℂ) (inner ℂ ψ (A ψ)) = inner ℂ ψ (A ψ) := by
    rw [inner_conj_symm, h1]
  rw [h1]; exact (Complex.conj_eq_iff_re.1 h2).symm

/-! ## 2. Every event is a bit -/

/-- The variance `‖(A − ⟨A⟩)ψ‖²` of a symmetric operator. -/
def variance (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - ((inner ℂ ψ (A ψ)).re : ℂ) • ψ‖ ^ 2

/-- **The variance of an event is `p (1 − p)`**, the variance of a coin. -/
theorem variance_eq (E : Event H) {ψ : H} (hψ : ‖ψ‖ = 1) :
    variance E.P ψ = prob E ψ * (1 - prob E ψ) := by
  have hp := prob_eq_norm_sq E ψ
  have hPψ : inner ℂ (E.P ψ) ψ = ((prob E ψ : ℝ) : ℂ) := inner_self_real E.symm ψ
  show ‖E.P ψ - ((prob E ψ : ℝ) : ℂ) • ψ‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hPψ, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, hψ, ← hp]
  simp only [RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.ofReal_re, mul_one, sq_abs]
  ring

theorem variance_le (E : Event H) {ψ : H} (hψ : ‖ψ‖ = 1) : variance E.P ψ ≤ 1 / 4 := by
  rw [variance_eq E hψ]
  nlinarith [sq_nonneg (prob E ψ - 1 / 2)]

/-! ## 3. Compatible events: Kolmogorov -/

/-- `E and F` for compatible (commuting) events. -/
def and_ (E F : Event H) (h : ∀ ψ, E.P (F.P ψ) = F.P (E.P ψ)) : Event H where
  P := E.P ∘ₗ F.P
  symm x y := by
    simp only [LinearMap.comp_apply]
    rw [E.symm, F.symm, h]
  idem ψ := by simp only [LinearMap.comp_apply]; rw [← h (F.P ψ), F.idem, E.idem]

theorem comm_compl {E F : Event H} (h : ∀ ψ, E.P (F.P ψ) = F.P (E.P ψ)) (ψ : H) :
    E.P ((compl F).P ψ) = (compl F).P (E.P ψ) := by
  simp [compl, h]

theorem compl_comm {E F : Event H} (h : ∀ ψ, E.P (F.P ψ) = F.P (E.P ψ)) (ψ : H) :
    (compl E).P (F.P ψ) = F.P ((compl E).P ψ) := by
  simp [compl, h]

/-- **The law of total probability**: `p(E) = p(E and F) + p(E and not F)`. -/
theorem prob_total (E F : Event H) (h : ∀ ψ, E.P (F.P ψ) = F.P (E.P ψ)) (ψ : H) :
    prob E ψ = prob (and_ E F h) ψ + prob (and_ E (compl F) (comm_compl h)) ψ := by
  simp only [prob, and_, compl, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, inner_sub_right, Complex.sub_re]
  ring

/-- **Compatible events are Kolmogorov**: the four outcomes `11, 10, 01, 00` have probabilities
`≥ 0` that add up to `1` in a unit state. -/
theorem joint_sum (E F : Event H) (h : ∀ ψ, E.P (F.P ψ) = F.P (E.P ψ)) {ψ : H}
    (hψ : ‖ψ‖ = 1) :
    prob (and_ E F h) ψ + prob (and_ E (compl F) (comm_compl h)) ψ +
      prob (and_ (compl E) F (compl_comm h)) ψ +
      prob (and_ (compl E) (compl F) (comm_compl (compl_comm h))) ψ = 1 := by
  rw [← prob_total, add_assoc, ← prob_total (compl E) F (compl_comm h), prob_compl, hψ]
  ring

/-- For compatible events `Im ⟨Pψ, Qψ⟩ = 0`: nothing is left for uncertainty. -/
theorem im_inner_eq_zero (E F : Event H) (h : ∀ ψ, E.P (F.P ψ) = F.P (E.P ψ)) (ψ : H) :
    (inner ℂ (E.P ψ) (F.P ψ)).im = 0 := by
  have h1 : inner ℂ (E.P ψ) (F.P ψ) = inner ℂ ψ (E.P (F.P ψ)) := E.symm ψ (F.P ψ)
  have h2 : inner ℂ (F.P ψ) (E.P ψ) = inner ℂ ψ (F.P (E.P ψ)) := F.symm ψ (E.P ψ)
  rw [← h ψ, ← h1, ← inner_conj_symm] at h2
  have := congrArg Complex.im h2
  rw [Complex.conj_im] at this
  linarith

/-! ## 4. Incompatible events: Robertson for bits -/

/-- **Robertson**: for symmetric `A`, `B`, `(Im ⟨Aψ, Bψ⟩)² ≤ Var A · Var B` in a unit state. -/
theorem robertson {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : H}
    (hψ : ‖ψ‖ = 1) : (inner ℂ (A ψ) (B ψ)).im ^ 2 ≤ variance A ψ * variance B ψ := by
  set a := (inner ℂ ψ (A ψ)).re
  set b := (inner ℂ ψ (B ψ)).re
  have hψψ : inner ℂ ψ ψ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hAψ : inner ℂ (A ψ) ψ = (a : ℂ) := inner_self_real hA ψ
  have hψB : inner ℂ ψ (B ψ) = (b : ℂ) := by rw [← hB, inner_self_real hB ψ]
  have key : inner ℂ (A ψ - (a : ℂ) • ψ) (B ψ - (b : ℂ) • ψ) =
      inner ℂ (A ψ) (B ψ) - ((a * b : ℝ) : ℂ) := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hAψ, hψB,
      hψψ, Complex.conj_ofReal]
    push_cast; ring
  have him : (inner ℂ (A ψ - (a : ℂ) • ψ) (B ψ - (b : ℂ) • ψ)).im = (inner ℂ (A ψ) (B ψ)).im := by
    rw [key, Complex.sub_im, Complex.ofReal_im, sub_zero]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (A ψ - (a : ℂ) • ψ) (B ψ - (b : ℂ) • ψ)
  have h2 := (Complex.abs_im_le_norm (inner ℂ (A ψ - (a : ℂ) • ψ) (B ψ - (b : ℂ) • ψ))).trans h1
  rw [him] at h2
  rw [variance, variance, ← mul_pow, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h2 2

/-- **Robertson for bits**: `(Im ⟨Pψ, Qψ⟩)² ≤ p (1 − p) q (1 − q)`. -/
theorem robertson_events (E F : Event H) {ψ : H} (hψ : ‖ψ‖ = 1) :
    (inner ℂ (E.P ψ) (F.P ψ)).im ^ 2 ≤
      prob E ψ * (1 - prob E ψ) * (prob F ψ * (1 - prob F ψ)) := by
  rw [← variance_eq E hψ, ← variance_eq F hψ]
  exact robertson E.symm F.symm hψ

/-- The commutator: `⟨ψ, [A, B] ψ⟩ = 2i Im ⟨Aψ, Bψ⟩`. -/
theorem commutator_eq {A B : H →ₗ[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (ψ : H) :
    inner ℂ ψ (A (B ψ)) - inner ℂ ψ (B (A ψ)) =
      ((2 * (inner ℂ (A ψ) (B ψ)).im : ℝ) : ℂ) * I := by
  have h1 : inner ℂ ψ (A (B ψ)) = inner ℂ (A ψ) (B ψ) := (hA ψ (B ψ)).symm
  have h2 : inner ℂ ψ (B (A ψ)) = (starRingEnd ℂ) (inner ℂ (A ψ) (B ψ)) := by
    rw [← hB ψ (A ψ)]; exact (inner_conj_symm _ _).symm
  rw [h1, h2, Complex.sub_conj]

/-- **A decided event commutes in that state**: if `p ∈ {0, 1}`, `Im ⟨Pψ, Qψ⟩ = 0` for every
other event. -/
theorem im_inner_eq_zero_of_decided (E F : Event H) {ψ : H} (hψ : ‖ψ‖ = 1)
    (hp : prob E ψ = 0 ∨ prob E ψ = 1) : (inner ℂ (E.P ψ) (F.P ψ)).im = 0 := by
  have h := robertson_events E F hψ
  have h0 : prob E ψ * (1 - prob E ψ) = 0 := by rcases hp with hp | hp <;> rw [hp] <;> ring
  rw [h0, zero_mul] at h
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg _))

/-! ## 5. The time an event takes -/

/-- The rate of the event `E` under the generator `G`: `⟨ψ, i[G, P] ψ⟩`. -/
def rate (G : H →ₗ[ℂ] H) (E : Event H) (ψ : H) : ℝ :=
  (I * (inner ℂ ψ (G (E.P ψ)) - inner ℂ ψ (E.P (G ψ)))).re

theorem rate_eq {G : H →ₗ[ℂ] H} (hG : G.IsSymmetric) (E : Event H) (ψ : H) :
    rate G E ψ = -2 * (inner ℂ (G ψ) (E.P ψ)).im := by
  rw [rate, commutator_eq hG E.symm]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im]
  ring

/-- **An event changes no faster than the spread of the generator times its own spread**:
`rate² ≤ 4 Var G · p (1 − p)`, that is `|rate| ≤ 2 ΔG √(p (1 − p))`. -/
theorem rate_sq_le {G : H →ₗ[ℂ] H} (hG : G.IsSymmetric) (E : Event H) {ψ : H} (hψ : ‖ψ‖ = 1) :
    rate G E ψ ^ 2 ≤ 4 * variance G ψ * (prob E ψ * (1 - prob E ψ)) := by
  rw [rate_eq hG, ← variance_eq E hψ]
  have h := robertson hG E.symm hψ
  nlinarith only [h]

end QuantumEvents
