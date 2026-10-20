/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedAxisQuantum
public import NRS3Dark.DarkShare

/-!
# The Szegő limit of the closed axis: the angle tends to `45°`

The closed axis with `d = n + 3` positions lives on `Hd d = ℂ^d`, with the closed transport
`T° = (A_d + S)/2` and the position `P_d` (`ClosedAxis`). Its `c` lies in `[1, 1 + 2/(d − 1)]`
and tends to `1` (`ClosedAxis.tendsto_cMax`). Here the angle follows the same road.

The open part of the tension is at most `2/(d − 1)` (`D38`), so a unit state with tension
`|t| ≥ 1`, in particular the state `c`, carries almost all its weight on the two seam positions.
Write `ψ = u + w` with `u = ψ₀ e₀ + ψ_{d−1} e_{d−1}` and `‖w‖² ≤ 2/(d − 1)`. Every moment of `ψ`
differs from the one of `u` by at most a constant times `‖w‖`, and the moments of `u` are read in
two coordinates: from `4` positions on, `‖T° u‖² = (|ψ₀|² + |ψ_{d−1}|²)/2`,
`⟨T°⟩_u = Re(ψ̄₀ψ_{d−1})`,
`‖P u‖² = |ψ₀|² + |ψ_{d−1}|²`, `⟨P⟩_u = |ψ_{d−1}|² − |ψ₀|²`, `⟪T° u, P u⟫ = i Im(ψ̄₀ψ_{d−1})`. As
`d → ∞`, `Var T° → 1/2`, `Var P_d → 1`, `|⟪δT°, δP⟫| → 1/2`: the light share tends to `1/2`, the
angle to `45°`, and `det Σ / |det Ω|` of the axis to `2`, the values of the seam state
(`ClosedAxis.ratio_seamState`). With `3` positions the angle is `arccos(2/√5)`
(`TorusDark.lightShare_maxState`).

## Main results

- `RingSzego.inner_centered_eq` : `⟪Ãψ, B̃ψ⟫ = ⟪Aψ, Bψ⟫ − ⟨A⟩⟨B⟩` for a unit state.
- `RingSzego.norm_transport_le` : `‖T° x‖ ≤ 2 ‖x‖`, uniformly in `d`.
- `RingSzego.seam_lower` : `|t| ≥ 1` forces `2 |Im(ψ̄₀ψ_{d−1})| ≥ 1 − 2/(d − 1)`.
- `RingSzego.seam_bounds` : the bounds at each size.
- `RingSzego.tendsto_variance_transport`, `tendsto_variance_PdOp`, `tendsto_covariance`,
  `tendsto_imPart_sq` : `Var T° → 1/2`, `Var P → 1`, `Cov → 0`, `Im² → 1/4`.
- `RingSzego.tendsto_lightShare`, `tendsto_darkShare` : light and dark tend to `1/2`.
- `RingSzego.tendsto_angle` : the angle tends to `π/4`.
- `RingSzego.tendsto_det_ratio` : `det Σ / |det Ω|` of the axis tends to `2`.
- `RingSzego.exists_cState`, `tendsto_angle_cState`, `tendsto_det_ratio_cState` : every size has
  its state `c`, and at `c` the angle tends to `45°` and the ratio to `2`.
-/

@[expose] public noncomputable section

open Complex Filter Topology NRSInequality TransportPosition SpectralExtremal
open EigenvectorSaturation PlatformBlindness ClosedAxis DarkShare

namespace RingSzego

/-! ## 1. Moments of a unit state -/

section Moments

variable {d : ℕ} {A B : Hd d →ₗ[ℂ] Hd d}

/-- `⟪Ãψ, B̃ψ⟫ = ⟪Aψ, Bψ⟫ − ⟨A⟩⟨B⟩` for symmetric `A`, `B` and a unit state. -/
theorem inner_centered_eq (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : Hd d} (hψ : ‖ψ‖ = 1) :
    inner ℂ (centered A ψ) (centered B ψ) =
      inner ℂ (A ψ) (B ψ) - ((mean A ψ * mean B ψ : ℝ) : ℂ) := by
  have ha : inner ℂ (A ψ) ψ = ((mean A ψ : ℝ) : ℂ) := by
    rw [← inner_conj_symm (A ψ) ψ, inner_self_apply_real hA]
    simp
  have hb : inner ℂ ψ (B ψ) = ((mean B ψ : ℝ) : ℂ) := inner_self_apply_real hB ψ
  have hn : inner ℂ ψ ψ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    simp
  simp only [centered, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, ha, hb,
    hn, Complex.conj_ofReal]
  push_cast
  ring

/-- `Var A = ‖Aψ‖² − ⟨A⟩²` for a unit state. -/
theorem variance_eq (hA : A.IsSymmetric) {ψ : Hd d} (hψ : ‖ψ‖ = 1) :
    variance A ψ = ‖A ψ‖ ^ 2 - mean A ψ ^ 2 := by
  have h := congrArg Complex.re (inner_centered_eq hA hA hψ)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖centered A ψ‖ ^ 2 = ‖A ψ‖ ^ 2 - mean A ψ * mean A ψ := by
    simpa [← Complex.ofReal_pow] using h
  rw [variance, h']
  ring

/-- Moving a state by `w` moves `⟪Aψ, Bψ⟫` by at most `C_A C_B ‖w‖ (‖u + w‖ + ‖u‖)`. -/
theorem norm_inner_sub_le {CA CB : ℝ} (hCA : 0 ≤ CA)
    (hA : ∀ x, ‖A x‖ ≤ CA * ‖x‖) (hB : ∀ x, ‖B x‖ ≤ CB * ‖x‖) (u w : Hd d) :
    ‖inner ℂ (A (u + w)) (B (u + w)) - inner ℂ (A u) (B u)‖ ≤
      CA * CB * ‖w‖ * (‖u + w‖ + ‖u‖) := by
  have e : inner ℂ (A (u + w)) (B (u + w)) - inner ℂ (A u) (B u) =
      inner ℂ (A w) (B (u + w)) + inner ℂ (A u) (B w) := by
    rw [map_add A u w, inner_add_left, map_add B u w, inner_add_right]
    ring
  rw [e]
  calc _ ≤ ‖A w‖ * ‖B (u + w)‖ + ‖A u‖ * ‖B w‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ (CA * ‖w‖) * (CB * ‖u + w‖) + (CA * ‖u‖) * (CB * ‖w‖) := by
        gcongr
        exacts [hA w, hB _, hA u, hB w]
    _ = CA * CB * ‖w‖ * (‖u + w‖ + ‖u‖) := by ring

end Moments

/-! ## 2. Uniform bounds on the closed axis -/

variable {n : ℕ}

theorem norm_seamOp_le (x : Hd (n + 3)) : ‖seamOp n x‖ ≤ 2 * ‖x‖ := by
  have e : seamOp n x = EuclideanSpace.single 0 (x (last n)) +
      EuclideanSpace.single (last n) (x 0) := by
    ext j
    simp [seamOp, mul_comm]
  rw [e]
  calc _ ≤ ‖EuclideanSpace.single (0 : Fin (n + 3)) (x (last n))‖ +
        ‖EuclideanSpace.single (last n) (x 0)‖ := norm_add_le _ _
    _ = ‖x (last n)‖ + ‖x 0‖ := by simp
    _ ≤ ‖x‖ + ‖x‖ := add_le_add (PiLp.norm_apply_le x _) (PiLp.norm_apply_le x _)
    _ = 2 * ‖x‖ := by ring

/-- **`‖T° x‖ ≤ 2 ‖x‖`**, uniformly in `d`. -/
theorem norm_transport_le (x : Hd (n + 3)) : ‖transport n x‖ ≤ 2 * ‖x‖ := by
  have hρ0 := (rho_pos (n + 3) (by omega)).le
  have hρ2 := rho_le_two (n := n)
  have hT := BandWidth.norm_TdOp_le (d := n + 3) (by omega) x
  have hS := norm_seamOp_le x
  rw [transport, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  calc _ ≤ ‖(((rho (n + 3) / 2 : ℝ) : ℂ)) • TdOp (n + 3) x‖ + ‖(1 / 2 : ℂ) • seamOp n x‖ :=
        norm_add_le _ _
    _ = rho (n + 3) / 2 * ‖TdOp (n + 3) x‖ + 1 / 2 * ‖seamOp n x‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        norm_num
    _ ≤ 1 * ‖x‖ + 1 / 2 * (2 * ‖x‖) := by
        gcongr
        · linarith
    _ = 2 * ‖x‖ := by ring

theorem norm_PdOp_le' (x : Hd (n + 3)) : ‖PdOp (n + 3) x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  exact BandWidth.norm_PdOp_le (by omega) x

/-- **`|t| ≥ 1` puts the weight on the seam**: `2 |Im(ψ̄₀ψ_{d−1})| ≥ 1 − 2/(d − 1)`. -/
theorem seam_lower {ψ : Hd (n + 3)} (hψ : ‖ψ‖ = 1) (ht : 1 ≤ |tension n ψ|) :
    1 - 2 / ((n : ℝ) + 2) ≤ 2 * |((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| := by
  have hρ0 := (rho_pos (n + 3) (by omega)).le
  have hρ2 := rho_le_two (n := n)
  have ho := GroupVelocity.abs_tension_le (d := n + 3) (by omega) ψ hψ
  have hd : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [hd] at ho
  have hop : |rho (n + 3) / 2 * NearMaxTension.tension (n + 3) ψ| ≤ 2 / ((n : ℝ) + 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc _ ≤ 1 * (2 / ((n : ℝ) + 2)) := by gcongr; linarith
      _ = _ := one_mul _
  rw [tension_eq] at ht
  have := abs_sub _ _ |>.trans' ht
  have h2 : |2 * ((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| =
      2 * |((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| := by
    rw [abs_mul, abs_two]
  linarith [abs_sub (rho (n + 3) / 2 * NearMaxTension.tension (n + 3) ψ)
    (2 * ((starRingEnd ℂ) (ψ 0) * ψ (last n)).im)]

/-! ## 3. The seam part of a state -/

section Seam

variable (ψ : Hd (n + 3))

/-- The seam part `u = ψ₀ e₀ + ψ_{d−1} e_{d−1}`. -/
def seamPart : Hd (n + 3) :=
  EuclideanSpace.single 0 (ψ 0) + EuclideanSpace.single (last n) (ψ (last n))

theorem seamPart_apply (j : Fin (n + 3)) :
    seamPart ψ j = (if j = 0 then ψ 0 else 0) + (if j = last n then ψ (last n) else 0) := by
  simp [seamPart, PiLp.single_apply]

/-- `‖ψ‖² = ‖ψ − u‖² + |ψ₀|² + |ψ_{d−1}|²`. -/
theorem norm_sq_split :
    ‖ψ‖ ^ 2 = ‖ψ - seamPart ψ‖ ^ 2 + (‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hp : ∀ j : Fin (n + 3), ‖ψ j‖ ^ 2 = ‖(ψ - seamPart ψ) j‖ ^ 2 +
      ((if j = 0 then ‖ψ 0‖ ^ 2 else 0) + (if j = last n then ‖ψ (last n)‖ ^ 2 else 0)) := by
    intro j
    rw [PiLp.sub_apply, seamPart_apply]
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases hl : j = last n
      · subst hl; simp [zero_ne_last.symm]
      · simp [h0, hl]
  rw [Finset.sum_congr rfl fun j _ => hp j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- `Σ_j ψ̄_j g_j` over the seam part picks the two seam coordinates. -/
theorem inner_seamPart_left (y : Hd (n + 3)) :
    inner ℂ (seamPart ψ) y = (starRingEnd ℂ) (ψ 0) * y 0 +
      (starRingEnd ℂ) (ψ (last n)) * y (last n) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, seamPart_apply, map_add, apply_ite (starRingEnd ℂ), map_zero,
    mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

theorem PdOp_seamPart_apply (j : Fin (n + 3)) :
    PdOp (n + 3) (seamPart ψ) j =
      -(if j = 0 then ψ 0 else 0) + (if j = last n then ψ (last n) else 0) := by
  rw [PdOp_apply_coord, seamPart_apply]
  by_cases h0 : j = 0
  · subst h0; simp [posCoord_zero]
  · by_cases hl : j = last n
    · subst hl; simp [zero_ne_last.symm, posCoord_last]
    · simp [h0, hl]

theorem inner_PdOp_seamPart_right (y : Hd (n + 3)) :
    inner ℂ y (PdOp (n + 3) (seamPart ψ)) = -((starRingEnd ℂ) (y 0) * ψ 0) +
      (starRingEnd ℂ) (y (last n)) * ψ (last n) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, PdOp_seamPart_apply, add_mul, neg_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

/-- `T°` on the seam part: `(α_j ψ₀ + β_j ψ_{d−1})/2`, with the columns `α`, `β` of the seam
positions. -/
theorem transport_seamPart_apply (j : Fin (n + 3)) :
    transport n (seamPart ψ) j =
      ((alpha n j : ℂ) * ψ 0 + (beta n j : ℂ) * ψ (last n)) / 2 := by
  have hρ : (rho (n + 3) : ℂ) ≠ 0 := by exact_mod_cast (rho_pos (n + 3) (by omega)).ne'
  have hT : TdOp (n + 3) (seamPart ψ) j =
      (Ad (n + 3) j 0 * ψ 0 + Ad (n + 3) j (last n) * ψ (last n)) / (rho (n + 3) : ℂ) := by
    rw [TdOp_apply_coord]
    simp only [seamPart_apply, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Td]
    ring
  have hS : seamOp n (seamPart ψ) j =
      (if j = 0 then ψ (last n) else 0) + (if j = last n then ψ 0 else 0) := by
    simp only [seamOp, LinearMap.add_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe, PiLp.proj_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, seamPart_apply, PiLp.single_apply, zero_ne_last, zero_ne_last.symm,
      ite_true, ite_false]
    split_ifs <;> ring
  simp only [transport, LinearMap.add_apply, LinearMap.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, hT, hS, Ad_zero, Ad_last, alpha, beta]
  push_cast
  field_simp
  split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_zero] <;> ring

end Seam

end RingSzego
