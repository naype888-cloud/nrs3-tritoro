/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.EventClock
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Redshift from the windings: one fraction per seam

On a closed axis of `L` positions the same point is reached by paths of `d₀, d₀ + L, d₀ + 2L, …`
steps (`TorusCover`): the image seen after `n` windings sits at the apparent distance
`D_n = d₀ + n L`. The windings alone do not change the colour of light: the spectrum of a state
never changes (`EventClock.weight_evolve`).

Route A: each crossing of a seam, the link that closes the axis and carries one quantum (`D16g`,
`HorizonCount`), leaves the light a fixed fraction `r` of its energy, `0 < r < 1`; the rest goes
to the dark share. This file takes `r` as a hypothesis and proves what follows from it:

* the light keeps `rⁿ` after `n` windings and the dark share `1 − rⁿ` grows; the total is the same,
  the light tends to `0` and never comes back;
* `1 + z = r⁻ⁿ = exp (κ (D_n − d₀))` with `κ = log (1/r) / L`: the redshift grows with the apparent
  distance, and `κ (D_n − d₀) ≤ z`, Hubble's law (1929), with equality to first order;
* the light runs slower: its survival amplitude at time `t` is the original one at `t / (1 + z)`,
  its spread is `ΔE / (1 + z)`, and no event in it goes from `0` to `1` before
  `(1 + z) π / (2 ΔE)`.

## Main results

- `SeamRedshift.light_add_dark`, `SeamRedshift.light_strictAnti`, `SeamRedshift.tendsto_light` :
  the light share after `n` windings.
- `SeamRedshift.image_cast` : the image after `n` windings is the same point of the axis.
- `SeamRedshift.onePlusZ_eq_exp` : `1 + z = exp (κ (D_n − d₀))`.
- `SeamRedshift.hubble_le`, `SeamRedshift.onePlusZ_strictMono` : Hubble's law as a lower bound.
- `SeamRedshift.amplitude_redshift` : the redshifted light is the original one in slow motion.
- `SeamRedshift.spread_redshift`, `SeamRedshift.orthogonality_time_redshift` : the tick is
  `1 + z` times longer.
-/

@[expose] public noncomputable section

open Real Filter Topology MandelstamTamm1945

namespace SeamRedshift

variable {r : ℝ}

/-! ## The light share -/

/-- The light share after `n` windings, a fraction `r` kept at each seam. -/
def light (r : ℝ) (n : ℕ) : ℝ := r ^ n

/-- The dark share after `n` windings. -/
def dark (r : ℝ) (n : ℕ) : ℝ := 1 - r ^ n

/-- **Nothing is lost**: light and dark add up to the energy that left. -/
theorem light_add_dark (n : ℕ) : light r n + dark r n = 1 := by
  simp [light, dark]

theorem light_pos (hr0 : 0 < r) (n : ℕ) : 0 < light r n := pow_pos hr0 n

/-- **The light share falls at every winding.** -/
theorem light_strictAnti (hr0 : 0 < r) (hr1 : r < 1) : StrictAnti (light r) :=
  fun _ _ h => pow_lt_pow_right_of_lt_one₀ hr0 hr1 h

/-- **The light share tends to `0`.** -/
theorem tendsto_light (hr0 : 0 < r) (hr1 : r < 1) : Tendsto (light r) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1

/-- **The dark share tends to `1`.** -/
theorem tendsto_dark (hr0 : 0 < r) (hr1 : r < 1) : Tendsto (dark r) atTop (𝓝 1) := by
  have h := (tendsto_light hr0 hr1).const_sub 1
  rw [sub_zero] at h
  exact h

/-! ## Redshift and apparent distance -/

/-- **The image after `n` windings is the same point**: `d₀ + n L` steps end at `d₀`. -/
theorem image_cast (d₀ n L : ℕ) : ((d₀ + n * L : ℕ) : ZMod L) = d₀ := by
  simp

/-- The apparent distance of the image after `n` windings, `D_n = d₀ + n L`. -/
def dist (d₀ L : ℝ) (n : ℕ) : ℝ := d₀ + n * L

/-- `1 + z`: the energy that left over the energy that arrives, `r⁻ⁿ`. -/
def onePlusZ (r : ℝ) (n : ℕ) : ℝ := (light r n)⁻¹

/-- The rate `κ = log (1/r) / L` of the redshift per unit of apparent distance. -/
def kappa (r L : ℝ) : ℝ := log r⁻¹ / L

/-- **`1 + z = exp (κ (D_n − d₀))`**: the redshift is exponential in the apparent distance. -/
theorem onePlusZ_eq_exp (hr0 : 0 < r) {L : ℝ} (hL : L ≠ 0) (d₀ : ℝ) (n : ℕ) :
    onePlusZ r n = exp (kappa r L * (dist d₀ L n - d₀)) := by
  have h : kappa r L * (dist d₀ L n - d₀) = n * log r⁻¹ := by
    simp only [kappa, dist]; field_simp; ring
  rw [h, exp_nat_mul, exp_log (inv_pos.2 hr0), onePlusZ, light, inv_pow]

/-- **Hubble's law**: `z ≥ κ (D_n − d₀)`, with equality to first order. -/
theorem hubble_le (hr0 : 0 < r) {L : ℝ} (hL : L ≠ 0) (d₀ : ℝ) (n : ℕ) :
    kappa r L * (dist d₀ L n - d₀) ≤ onePlusZ r n - 1 := by
  rw [onePlusZ_eq_exp hr0 hL]
  linarith [add_one_le_exp (kappa r L * (dist d₀ L n - d₀))]

/-- **The redshift grows at every winding.** -/
theorem onePlusZ_strictMono (hr0 : 0 < r) (hr1 : r < 1) : StrictMono (onePlusZ r) :=
  fun _ _ h => inv_strictAnti₀ (light_pos hr0 _) (light_strictAnti hr0 hr1 h)

theorem one_le_onePlusZ (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) : 1 ≤ onePlusZ r n := by
  rw [onePlusZ, light, ← inv_pow]
  exact one_le_pow₀ (one_le_inv_iff₀.2 ⟨hr0, hr1.le⟩)

/-! ## The light runs slower -/

/-- **The redshifted light is the original one in slow motion**: energies times `c` give at time
`t` the survival amplitude of the original at `c t`. -/
theorem amplitude_redshift {m : ℕ} (p E : Fin m → ℝ) (c t : ℝ) :
    amplitude p (fun k => c * E k) t = amplitude p E (c * t) := by
  simp only [amplitude, phase]
  exact Finset.sum_congr rfl fun k _ => by ring_nf

/-- **The spread of the redshifted light is `ΔE / (1 + z)`.** -/
theorem spread_redshift (hr0 : 0 < r) {m : ℕ} (p E : Fin m → ℝ) (n : ℕ) :
    spread p (fun k => light r n * E k) = spread p E / onePlusZ r n := by
  rw [EventClock.spread_smul, abs_of_pos (light_pos hr0 n), onePlusZ, div_inv_eq_mul, mul_comm]

/-- **Time dilation**: in the light after `n` windings no state becomes orthogonal to itself,
no event goes from `0` to `1`, before `(1 + z) π / (2 ΔE)`. -/
theorem orthogonality_time_redshift (hr0 : 0 < r) {m : ℕ} {p : Fin m → ℝ} (E : Fin m → ℝ)
    (hp : ∀ k, 0 ≤ p k) (h1 : ∑ k, p k = 1) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (h0 : amplitude p (fun k => light r n * E k) t = 0) :
    onePlusZ r n * (π / 2) ≤ spread p E * t := by
  have h := orthogonality_time hp h1 ht0 h0
  have hz : 0 < onePlusZ r n := inv_pos.2 (light_pos hr0 n)
  rw [spread_redshift hr0, div_mul_eq_mul_div, le_div_iff₀ hz] at h
  rwa [mul_comm]

end SeamRedshift
