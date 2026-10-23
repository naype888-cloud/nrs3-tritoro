/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.QuantumEvents
public import NRS3MandelstamTammCramerRao.MandelstamTamm1945

/-!
# The clock of an event: from `0` to `1` takes at least `π / (2 ΔE)`

An event (`QuantumEvents.Event`) that has not happened, `Pψ = 0`, needs time to happen. Under the
Schrödinger evolution of a Hermitian `H` on `ℂ^d`, the part of `ψ(t)` that left `ψ` has weight
`1 − ‖⟨ψ, ψ(t)⟩‖²`, and the event sees only that part. Mandelstam–Tamm
(`MandelstamTamm1945.cos_le_norm_inner_evolve`) keeps `‖⟨ψ, ψ(t)⟩‖ ≥ cos (ΔE t)`, so

  `p(t) ≤ sin² (ΔE t)`  for `0 ≤ ΔE t ≤ π/2`,

and the event cannot become certain before `π / (2 ΔE)`: the tick of a clock. The event "the
state has left `ψ`" sees all of it; with two equal branches its probability is exactly
`sin² (ΔE t)`, so `π/2` is sharp.

The weights of `ψ` on the energies never change, so neither does `ΔE`: the tick of a state is
the same at every time, however far it has gone. Dividing every energy by `1 + z` would stretch
the tick by `1 + z`.

## Main results

- `EventClock.weight_evolve`, `EventClock.norm_evolve` : the spectrum of a state never changes.
- `EventClock.spreadOf_evolve` : the clock does not age, `ΔE` is the same at every time.
- `EventClock.spread_smul` : energies divided by `1 + z` stretch the tick by `1 + z`.
- `EventClock.leave`, `EventClock.prob_leave` : the event "left `ψ`", `p = ‖φ‖² − ‖⟨ψ, φ⟩‖²`.
- `EventClock.prob_le_prob_leave` : an event not yet happened sees only what left `ψ`.
- `EventClock.prob_le_sin_sq` : `p(t) ≤ sin² (ΔE t)` for `0 ≤ ΔE t ≤ π/2`.
- `EventClock.tick` : `p(t) = 1` forces `π/2 ≤ ΔE t`.
- `EventClock.leave_half` : two equal branches leave with probability `sin² (ΔE t)`.
-/

@[expose] public noncomputable section

open Real MandelstamTamm1945 QuantumEvents

namespace EventClock

/-! ## Leaving a state -/

section Leave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The event "the state has left `ψ`": the projection `φ ↦ φ − ⟨ψ, φ⟩ ψ` of a unit `ψ`. -/
def leave (ψ : V) (hψ : ‖ψ‖ = 1) : Event V where
  P := LinearMap.id - (innerₛₗ ℂ ψ).smulRight ψ
  symm φ χ := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      innerₛₗ_apply_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    rw [inner_conj_symm]
    ring
  idem φ := by
    have h1 : inner ℂ ψ ψ = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hψ]; simp
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      innerₛₗ_apply_apply, inner_sub_right, inner_smul_right, h1, mul_one, sub_self, zero_smul,
      sub_zero]

/-- **The probability of leaving `ψ`** is `‖φ‖² − ‖⟨ψ, φ⟩‖²`. -/
theorem prob_leave (ψ : V) (hψ : ‖ψ‖ = 1) (φ : V) :
    prob (leave ψ hψ) φ = ‖φ‖ ^ 2 - ‖inner ℂ ψ φ‖ ^ 2 := by
  simp only [prob, leave, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    innerₛₗ_apply_apply, inner_sub_right, inner_smul_right, Complex.sub_re, re_inner_self]
  rw [← inner_conj_symm φ ψ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

/-- **An event that has not happened sees only what left `ψ`**: `Pψ = 0` gives
`p(φ) ≤ ‖φ‖² − ‖⟨ψ, φ⟩‖²`. -/
theorem prob_le_prob_leave (E : Event V) {ψ : V} (hψ : ‖ψ‖ = 1) (h0 : E.P ψ = 0) (φ : V) :
    prob E φ ≤ prob (leave ψ hψ) φ := by
  have hP : E.P φ = E.P ((leave ψ hψ).P φ) := by
    simp [leave, h0]
  have h := prob_nonneg (compl E) ((leave ψ hψ).P φ)
  rw [prob_compl, ← prob_eq_norm_sq] at h
  rw [prob_eq_norm_sq, hP, ← prob_eq_norm_sq]
  linarith

end Leave

/-! ## The tick on `ℂ^d` -/

section Hilbert

variable {d : ℕ} {H : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)}
  (hH : H.IsSymmetric)

/-- The energy spread `ΔE` of `ψ` in the spectral weights of `H`. -/
abbrev spreadOf (ψ : EuclideanSpace ℂ (Fin d)) : ℝ :=
  spread (fun k => ‖inner ℂ (basis hH k) ψ‖ ^ 2) (energy hH)

theorem inner_basis_evolve (ψ : EuclideanSpace ℂ (Fin d)) (t : ℝ) (j : Fin d) :
    inner ℂ (basis hH j) (evolve hH ψ t) = phase (energy hH) j t * inner ℂ (basis hH j) ψ := by
  rw [evolve, (basis hH).orthonormal.inner_right_fintype]

/-- **The spectrum of a state never changes**: the weight on each energy is the same at every
time. -/
theorem weight_evolve (ψ : EuclideanSpace ℂ (Fin d)) (t : ℝ) (j : Fin d) :
    ‖inner ℂ (basis hH j) (evolve hH ψ t)‖ = ‖inner ℂ (basis hH j) ψ‖ := by
  rw [inner_basis_evolve, norm_mul, norm_phase, one_mul]

/-- **The evolution keeps the norm.** -/
theorem norm_evolve (ψ : EuclideanSpace ℂ (Fin d)) (t : ℝ) : ‖evolve hH ψ t‖ = ‖ψ‖ := by
  have h := (basis hH).sum_sq_norm_inner_right (evolve hH ψ t)
  simp only [weight_evolve, (basis hH).sum_sq_norm_inner_right] at h
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← h]

/-- **The clock does not age**: `ΔE` of `ψ(s)` is `ΔE` of `ψ`, so the tick `π / (2 ΔE)` is the
same at every time. -/
theorem spreadOf_evolve (ψ : EuclideanSpace ℂ (Fin d)) (s : ℝ) :
    spreadOf hH (evolve hH ψ s) = spreadOf hH ψ := by
  simp only [spreadOf, weight_evolve]

variable {hH}

/-- **An event that has not happened stays below `sin² (ΔE t)`** while `ΔE t ≤ π/2`. -/
theorem prob_le_sin_sq (E : Event (EuclideanSpace ℂ (Fin d))) {ψ : EuclideanSpace ℂ (Fin d)}
    (hψ : ‖ψ‖ = 1) (h0 : E.P ψ = 0) {t : ℝ} (ht0 : 0 ≤ t) (ht : spreadOf hH ψ * t ≤ π / 2) :
    prob E (evolve hH ψ t) ≤ sin (spreadOf hH ψ * t) ^ 2 := by
  have hl := prob_le_prob_leave E hψ h0 (evolve hH ψ t)
  rw [prob_leave, norm_evolve, hψ] at hl
  have hc := cos_le_norm_inner_evolve hH hψ ht0 ht
  have hnn : 0 ≤ spreadOf hH ψ * t := mul_nonneg (Real.sqrt_nonneg _) ht0
  have hcos : 0 ≤ cos (spreadOf hH ψ * t) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], ht⟩
  have := sin_sq_add_cos_sq (spreadOf hH ψ * t)
  nlinarith

/-- **The tick**: an event that has not happened becomes certain only after `π / (2 ΔE)`. -/
theorem tick (E : Event (EuclideanSpace ℂ (Fin d))) {ψ : EuclideanSpace ℂ (Fin d)}
    (hψ : ‖ψ‖ = 1) (h0 : E.P ψ = 0) {t : ℝ} (ht0 : 0 ≤ t) (h1 : prob E (evolve hH ψ t) = 1) :
    π / 2 ≤ spreadOf hH ψ * t := by
  have hl := prob_le_prob_leave E hψ h0 (evolve hH ψ t)
  rw [prob_leave, norm_evolve, hψ, h1] at hl
  have ha : inner ℂ ψ (evolve hH ψ t) = 0 := by
    rw [← norm_eq_zero]; nlinarith [norm_nonneg (inner ℂ ψ (evolve hH ψ t))]
  rw [inner_evolve] at ha
  exact orthogonality_time (fun _ => sq_nonneg _) (sum_weights hH hψ) ht0 ha

end Hilbert

/-- **Scaling every energy by `c` scales `ΔE` by `|c|`**: if all energies are divided by `1 + z`,
the tick `π / (2 ΔE)` is multiplied by `1 + z`. -/
theorem spread_smul {n : ℕ} (p E : Fin n → ℝ) (c : ℝ) :
    spread p (fun k => c * E k) = |c| * spread p E := by
  have hm : mean p (fun k => c * E k) = c * mean p E := by
    simp only [mean, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [spread, spread, hm, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The tick is sharp**: two equal branches leave their state with probability
`1 − ‖A(t)‖² = sin² (ΔE t)`, which reaches `1` at `ΔE t = π/2`. -/
theorem leave_half (E₀ E₁ t : ℝ) :
    1 - ‖amplitude half ![E₀, E₁] t‖ ^ 2 = sin (spread half ![E₀, E₁] * t) ^ 2 := by
  rw [norm_amplitude_half, sq_abs]
  linarith [sin_sq_add_cos_sq (spread half ![E₀, E₁] * t)]

end EventClock
