/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Dark.Dark

/-!
# The baryon window `g_s e^{−η}` inside the measured `Ω_b`

For a coherence constant `c > 1` the window is `(1 − 1/c) e^{−1/c}`: the share of the quantum,
`g_s = 1 − 1/c`, times the Boltzmann factor `e^{−η}` with `η = 1/c`. With the Szegő limit of the
open axis, `c = C∞`, it is `omegaPi` (`D26a`), and `omegaPi` lies inside the measured `Ω_b`
(`NRS3Dark.omegaPi_mem_planck`).

The baryon density `Ω_b` enters as the measured datum (CMB, deuterium, BAO), as `c` enters as the
slope of the light cone, and the dark part is what is left, `1 − Ω_b` (`NRS3Dark.darkFraction`).
Nothing below is needed for that. The window is the number that lies inside the datum, and
`Postulate Ωb c` records that reading: `Ω_b = window c`, with `c` the coherence constant of the
quantum of the pair `(T_d, P_d)`.

The closed transport `T° = (A_d + S)/2` has its own tension `ClosedAxis.cMax`, which tends to `1`
while the defect of the closed axis stays: its dark share tends to `1/2`
(`RingSzego.tendsto_darkShare`) and is positive for every state in the band
(`TorusDark.darkShare_pos_of_band`). Closing the axis adds one link, one more quantum; the
Robertson bound is the same.

## Main results

- `BaryonWindow.window`, `BaryonWindow.Postulate` : the window and the postulate `Ω_b = window c`.
- `BaryonWindow.window_coherenceConstantInf` : on the open axis the window is `omegaPi`.
- `BaryonWindow.window_pos` : the window is positive for `c > 1`.
- `BaryonWindow.window_sqrt_two_pos`, `BaryonWindow.window_sqrt_two_gt_planck` : at the limit of the
  ring, `c = √2 > 1`, the window is positive, and it is above the measured `Ω_b` (it is not inside
  the datum, as `omegaPi` is).
-/

@[expose] public noncomputable section

open Gnomon OmegaFromPi

namespace BaryonWindow

/-- The window of a coherence constant `c`: `g_s e^{−η} = (1 − 1/c) e^{−1/c}`. -/
def window (c : ℝ) : ℝ := (1 - 1 / c) * Real.exp (-1 / c)

/-- The postulate: the baryon density is the window of the coherence constant. -/
def Postulate (Ωb c : ℝ) : Prop := Ωb = window c

/-- On the open axis the window is `omegaPi`. -/
theorem window_coherenceConstantInf : window CoherenceConstantInf = omegaPi := rfl

theorem window_one : window 1 = 0 := by
  simp [window]

/-- The window is positive for `c > 1`. -/
theorem window_pos {c : ℝ} (hc : 1 < c) : 0 < window c := by
  have h : 1 / c < 1 := (div_lt_one (by linarith)).2 hc
  exact mul_pos (by linarith) (Real.exp_pos _)

/-- At the limit of the ring, `c = √2`, the window is positive: the limit does not saturate. -/
theorem window_sqrt_two_pos : 0 < window (√2) :=
  window_pos (by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.sqrt_lt_sqrt (by norm_num) this)

/-- **The ring window is not inside the measured `Ω_b`.** At `c = √2` it is above the upper
Planck 2018 corner. The window's role on the torus is `c > 1`, not a match to the datum. -/
theorem window_sqrt_two_gt_planck : (0.02252 : ℝ) / 0.6682 ^ 2 < window (√2) := by
  have h1 : (1.414 : ℝ) < √2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : (1 : ℝ) < √2 := by linarith
  have hu : 1 / √2 < 1 / 1.414 := one_div_lt_one_div_of_lt (by norm_num) h1
  have hu1 : 1 / √2 < 0.7073 := hu.trans (by norm_num)
  have hu0 : 0 < 1 / √2 := by positivity
  have he : 1 - 1 / √2 ≤ Real.exp (-1 / √2) := by
    have := Real.add_one_le_exp (-1 / √2)
    rw [neg_div] at this ⊢
    linarith
  unfold window
  have hg : 0.2927 < 1 - 1 / √2 := by linarith
  have hge : 0.2927 < Real.exp (-1 / √2) := lt_of_lt_of_le hg he
  calc (0.02252 : ℝ) / 0.6682 ^ 2 < 0.2927 * 0.2927 := by norm_num
    _ < (1 - 1 / √2) * Real.exp (-1 / √2) := mul_lt_mul'' hg hge (by norm_num) (by norm_num)

end BaryonWindow
