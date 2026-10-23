/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.SeamRedshift
public import NRS3Tritoro.TorusDark
public import NRS3Tritoro.FiberDark
public import NRS3Tritoro.RingSzego

/-!
# The fraction of each seam is the light share of the closed axis

The bridge of route A (`SeamRedshift`): the fraction `r` that the light keeps at a seam is the
light share of the closed axis at its `c`, what the pair `(T°, P₃)` resolves (`DarkShare`). On
every axis of `T³` it is `4/5` (`TorusDark.lightShare_maxState`), and the closed fiber of the box
gives the same `4/5` (`FiberDark.lightShare_fiberMaxState`). With it:

* after `n` windings the light keeps `(4/5)ⁿ` and the dark share is `1 − (4/5)ⁿ`;
* `1 + z = (5/4)ⁿ`: one winding gives `z = 1/4`;
* `κ = log (5/4) / L`, Hubble's law `z ≥ log (5/4) (D − d₀) / L`, and `κ = H₀ / c` fixes the size
  of the axis, `L = log (5/4) c / H₀`;
* no event in the light goes from `0` to `1` before `(5/4)ⁿ π / (2 ΔE)`.

On a closed axis of many positions the light share at `c` tends to `1/2` (`RingSzego`): read on
such an axis, the seam would keep `1/2` and `1 + z = 2ⁿ`.

## Main results

- `SeamLightShare.seamFraction_eq` : the fraction of a seam of `T³` is `4/5`.
- `SeamLightShare.seamFraction_eq_fiber` : the closed fiber of the box gives the same fraction.
- `SeamLightShare.light_seam`, `SeamLightShare.onePlusZ_seam` : `(4/5)ⁿ` and `1 + z = (5/4)ⁿ`.
- `SeamLightShare.hubble_seam`, `SeamLightShare.size_of_hubble` : Hubble's law and the size.
- `SeamLightShare.orthogonality_time_seam` : the tick stretched by `(5/4)ⁿ`.
- `SeamLightShare.tendsto_lightShare_cState`, `SeamLightShare.onePlusZ_half` : many positions.
-/

@[expose] public noncomputable section

open Real Filter Topology MandelstamTamm1945 SeamRedshift
open TransportPosition PathGraph3DNRS DarkShare CubeInBox FourAxes

namespace SeamLightShare

/-! ## The fraction of a seam of `T³` -/

/-- The fraction of a seam: the light share of axis `i` of `T^k` at its `c`. -/
def seamFraction (k : ℕ) (i : Fin k) : ℝ :=
  lightShare (centeredG (Torus.torusPairs k (0, i)) (Torus.maxState k))
    (centeredG (Torus.torusPairs k (1, i)) (Torus.maxState k))

/-- **The fraction of a seam of `T³` is `4/5`.** -/
theorem seamFraction_eq {k : ℕ} (i : Fin k) : seamFraction k i = 4 / 5 :=
  TorusDark.lightShare_maxState i

/-- **The closed fiber of the box keeps the same fraction.** -/
theorem seamFraction_eq_fiber {k : ℕ} (i : Fin k) {dx dy dz : ℕ}
    {φ : EuclideanSpace ℂ (Fin dx × Fin dy × Fin dz)} (hφ : ‖φ‖ = 1) :
    lightShare (FiberDark.fib 0 (FiberDark.fiberMaxState φ))
      (FiberDark.fib 1 (FiberDark.fiberMaxState φ)) = seamFraction k i := by
  rw [FiberDark.lightShare_fiberMaxState hφ, seamFraction_eq]

/-! ## Route A with the fraction `4/5` -/

variable {k : ℕ} (i : Fin k)

/-- **After `n` windings the light keeps `(4/5)ⁿ`.** -/
theorem light_seam (n : ℕ) : light (seamFraction k i) n = (4 / 5) ^ n := by
  rw [seamFraction_eq, light]

/-- **After `n` windings the dark share is `1 − (4/5)ⁿ`.** -/
theorem dark_seam (n : ℕ) : dark (seamFraction k i) n = 1 - (4 / 5) ^ n := by
  rw [seamFraction_eq, dark]

/-- **`1 + z = (5/4)ⁿ`.** -/
theorem onePlusZ_seam (n : ℕ) : onePlusZ (seamFraction k i) n = (5 / 4) ^ n := by
  rw [onePlusZ, light_seam, ← inv_pow]
  norm_num

/-- **One winding: `z = 1/4`.** -/
theorem z_one : onePlusZ (seamFraction k i) 1 - 1 = 1 / 4 := by
  rw [onePlusZ_seam]
  norm_num

theorem kappa_seam (L : ℝ) : kappa (seamFraction k i) L = log (5 / 4) / L := by
  rw [seamFraction_eq, kappa]
  norm_num

include i in
/-- **Hubble's law with the fraction of the seam**: `z ≥ log (5/4) (D − d₀) / L`. -/
theorem hubble_seam {L : ℝ} (hL : L ≠ 0) (d₀ : ℝ) (n : ℕ) :
    log (5 / 4) / L * (dist d₀ L n - d₀) ≤ (5 / 4) ^ n - 1 := by
  have h := hubble_le (r := seamFraction k i) (by rw [seamFraction_eq]; norm_num) hL d₀ n
  rwa [kappa_seam, onePlusZ_seam] at h

/-- **The size of the axis**: `κ = H₀ / c` exactly when `L = log (5/4) c / H₀`. -/
theorem size_of_hubble {c H₀ L : ℝ} (hc : 0 < c) (hH : 0 < H₀) (hL : 0 < L) :
    kappa (seamFraction k i) L = H₀ / c ↔ L = log (5 / 4) * c / H₀ := by
  rw [kappa_seam, div_eq_div_iff hL.ne' hc.ne', eq_div_iff hH.ne']
  constructor <;> intro h <;> linarith

include i in
/-- **The tick stretched by `(5/4)ⁿ`**: in the light after `n` windings no event goes from `0`
to `1` before `(5/4)ⁿ π / (2 ΔE)`. -/
theorem orthogonality_time_seam {m : ℕ} {p : Fin m → ℝ} (E : Fin m → ℝ) (hp : ∀ k, 0 ≤ p k)
    (h1 : ∑ k, p k = 1) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (h0 : amplitude p (fun k => (4 / 5) ^ n * E k) t = 0) :
    (5 / 4) ^ n * (π / 2) ≤ spread p E * t := by
  rw [← light_seam i] at h0
  have h := orthogonality_time_redshift (by rw [seamFraction_eq]; norm_num) E hp h1 n ht0 h0
  rwa [onePlusZ_seam] at h

/-! ## A closed axis of many positions -/

/-- **On a closed axis of many positions the light share at `c` tends to `1/2`.** -/
theorem tendsto_lightShare_cState :
    Tendsto (fun n => lightShare (NRSInequality.centered (ClosedAxis.transport n)
      (RingSzego.cState n)) (NRSInequality.centered (PdOp (n + 3)) (RingSzego.cState n)))
      atTop (𝓝 (1 / 2)) :=
  RingSzego.tendsto_lightShare RingSzego.cState RingSzego.norm_cState
    RingSzego.one_le_abs_tension_cState

/-- With the fraction `1/2`, `1 + z = 2ⁿ`. -/
theorem onePlusZ_half (n : ℕ) : onePlusZ (1 / 2) n = 2 ^ n := by
  rw [onePlusZ, light, ← inv_pow]
  norm_num

end SeamLightShare
