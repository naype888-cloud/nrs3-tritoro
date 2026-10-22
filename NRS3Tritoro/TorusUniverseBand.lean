/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusUniverseIsolation

/-!
# The band of the axis of the universe

A state of the universe fluctuates: `Var T° > 0` and `Var X > 0`, a variance `0` would be a
perfect estimate. Among such states the ones that saturate Robertson–Schrödinger stay a fixed
distance below the cone: there is `ε > 0` with `|⟨K⟩| ≤ 1 − ε`. If `4 ∤ L` the shift has no
eigenvalue `±i` and `‖(S ∓ i)ψ‖² = 2 ± 2⟨K⟩` keeps every unit state away from `±1`; if `4 ∣ L`
this is `isolation`.

The band `Ϙ(L) = (v*(L), 1)` is the set of speeds above every saturating speed (`D44`). The cone
`1` is a limit, never a speed. The band is never empty, and in it the surplus is strictly
positive.

## Main results

- `TorusUniverse.exists_velocity_le` : `|⟨K⟩| ≤ 1 − ε` for saturating states with `Var T° > 0`.
- `TorusUniverse.threshold_lt_one`, `TorusUniverse.band_nonempty` : `v*(L) < 1`.
- `TorusUniverse.surplus_pos_of_mem_band` : in the band the surplus is strictly positive.
-/

@[expose] public noncomputable section

open Complex PathGraph3DNRS

namespace TorusUniverse

variable {L : ℕ} [NeZero L]

/-- **Saturating states with fluctuating transport stay below the cone**: `|⟨K⟩| ≤ 1 − ε`. -/
theorem exists_velocity_le : ∃ ε > 0, ∀ ψ : HU L, ‖ψ‖ = 1 → 0 < varianceG transport ψ →
    (∃ κ : ℂ, centeredG transport ψ = κ • centeredG (chart (univChart L)) ψ) →
      |velocity ψ| ≤ 1 - ε := by
  have side : ∀ u : ℂ, (u = I ∨ u = -I) → ∃ c > 0, ∀ ψ : HU L, ‖ψ‖ = 1 →
      0 < varianceG transport ψ →
      (∃ κ : ℂ, centeredG transport ψ = κ • centeredG (chart (univChart L)) ψ) →
        c ≤ ‖shift ψ - u • ψ‖ := by
    intro u hu
    by_cases h4 : 4 ∣ L
    · exact isolation h4 hu
    · obtain ⟨g, hg, hgap⟩ := exists_gap hu h4
      exact ⟨g, hg, fun ψ hψ _ _ => by simpa [hψ] using hgap ψ⟩
  obtain ⟨c₁, hc₁, h₁⟩ := side I (Or.inl rfl)
  obtain ⟨c₂, hc₂, h₂⟩ := side (-I) (Or.inr rfl)
  refine ⟨min (c₁ ^ 2) (c₂ ^ 2) / 2, by positivity, fun ψ hψ hT hs => ?_⟩
  have k₁ : c₁ ^ 2 ≤ 2 + 2 * velocity ψ := by
    rw [← norm_sq_shift_sub_I hψ]; exact pow_le_pow_left₀ hc₁.le (h₁ ψ hψ hT hs) 2
  have k₂ : c₂ ^ 2 ≤ 2 - 2 * velocity ψ := by
    rw [← norm_sq_shift_add_I hψ]; exact pow_le_pow_left₀ hc₂.le (h₂ ψ hψ hT hs) 2
  rw [abs_le]
  constructor <;> nlinarith [min_le_left (c₁ ^ 2) (c₂ ^ 2), min_le_right (c₁ ^ 2) (c₂ ^ 2)]

/-- The speeds of the saturating states of the universe whose two variances are positive. -/
def satSpeeds (L : ℕ) [NeZero L] : Set ℝ :=
  {s | ∃ ψ : HU L, ‖ψ‖ = 1 ∧ 0 < varianceG transport ψ ∧
    0 < varianceG (chart (univChart L)) ψ ∧ surplus (univChart L) ψ = 0 ∧ |velocity ψ| = s}

/-- The threshold `v*(L)`: the supremum of the saturating speeds. -/
def threshold (L : ℕ) [NeZero L] : ℝ := sSup (satSpeeds L)

/-- The band `Ϙ(L) = (v*(L), 1)`: the cone `1` is a limit, never a speed. -/
def band (L : ℕ) [NeZero L] : Set ℝ := Set.Ioo (threshold L) 1

theorem satSpeeds_le : ∃ ε > 0, ∀ s ∈ satSpeeds L, s ≤ 1 - ε := by
  obtain ⟨ε, hε, h⟩ := exists_velocity_le (L := L)
  refine ⟨ε, hε, fun s ⟨ψ, hψ, hT, hX, hs, hv⟩ => hv ▸ h ψ hψ hT ?_⟩
  refine exists_parallel_of_surplus_eq_zero _ hψ hs fun h0 => ?_
  simp [varianceG, h0] at hX

/-- **`v*(L) < 1`**: the saturating speeds stay a fixed distance below the cone. -/
theorem threshold_lt_one : threshold L < 1 := by
  obtain ⟨ε, hε, h⟩ := satSpeeds_le (L := L)
  have : threshold L ≤ 1 - min ε 1 :=
    Real.sSup_le (fun s hs => (h s hs).trans (by linarith [min_le_left ε 1]))
      (by linarith [min_le_right ε 1])
  linarith [lt_min hε one_pos]

/-- **The band is never empty.** -/
theorem band_nonempty : (band L).Nonempty :=
  ⟨(threshold L + 1) / 2, by constructor <;> linarith [threshold_lt_one (L := L)]⟩

/-- **In the band the surplus is strictly positive**: every state of the universe whose
variances are positive and whose speed lies in `Ϙ(L)` has a Robertson–Schrödinger surplus. -/
theorem surplus_pos_of_mem_band {ψ : HU L} (hψ : ‖ψ‖ = 1) (hT : 0 < varianceG transport ψ)
    (hX : 0 < varianceG (chart (univChart L)) ψ) (hb : |velocity ψ| ∈ band L) :
    0 < surplus (univChart L) ψ := by
  refine lt_of_le_of_ne (surplus_nonneg _ hψ) fun h => ?_
  have hbdd : BddAbove (satSpeeds L) :=
    ⟨1, fun s ⟨φ, hφ, _, _, _, hs⟩ => hs ▸ abs_velocity_le hφ⟩
  have := le_csSup hbdd ⟨ψ, hψ, hT, hX, h.symm, rfl⟩
  exact absurd hb.1 (not_lt.2 this)

end TorusUniverse
