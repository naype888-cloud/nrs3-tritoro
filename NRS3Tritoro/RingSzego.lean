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

/-! ## 4. The moments of the seam part -/

section SeamMoments

variable (ψ : Hd (n + 3))

theorem seamPart_zero : seamPart ψ 0 = ψ 0 := by simp [seamPart_apply]

theorem seamPart_last : seamPart ψ (last n) = ψ (last n) := by
  simp [seamPart_apply, zero_ne_last.symm]

theorem norm_seamPart_sq : ‖seamPart ψ‖ ^ 2 = ‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2 := by
  have hp : ∀ j : Fin (n + 3), ‖seamPart ψ j‖ ^ 2 =
      (if j = 0 then ‖ψ 0‖ ^ 2 else 0) + (if j = last n then ‖ψ (last n)‖ ^ 2 else 0) := by
    intro j
    rw [seamPart_apply]
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases hl : j = last n
      · subst hl; simp [zero_ne_last.symm]
      · simp [h0, hl]
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_congr rfl fun j _ => hp j, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- `⟪u, T° u⟫ = (ψ̄₀ψ_{d−1} + ψ̄_{d−1}ψ₀)/2`. -/
theorem inner_seamPart_transport :
    inner ℂ (seamPart ψ) (transport n (seamPart ψ)) =
      ((starRingEnd ℂ) (ψ 0) * ψ (last n) + (starRingEnd ℂ) (ψ (last n)) * ψ 0) / 2 := by
  rw [inner_seamPart_left, transport_seamPart_apply, transport_seamPart_apply, alpha_zero,
    beta_zero, alpha_last, beta_last]
  push_cast
  ring

/-- `⟪u, P u⟫ = |ψ_{d−1}|² − |ψ₀|²`. -/
theorem inner_seamPart_PdOp :
    inner ℂ (seamPart ψ) (PdOp (n + 3) (seamPart ψ)) =
      ((‖ψ (last n)‖ ^ 2 - ‖ψ 0‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_PdOp_seamPart_right, seamPart_zero, seamPart_last, Complex.conj_mul',
    Complex.conj_mul']
  push_cast
  ring

/-- `‖P u‖² = |ψ₀|² + |ψ_{d−1}|²`. -/
theorem norm_PdOp_seamPart_sq :
    ‖PdOp (n + 3) (seamPart ψ)‖ ^ 2 = ‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2 := by
  have hp : ∀ j : Fin (n + 3), ‖PdOp (n + 3) (seamPart ψ) j‖ ^ 2 =
      (if j = 0 then ‖ψ 0‖ ^ 2 else 0) + (if j = last n then ‖ψ (last n)‖ ^ 2 else 0) := by
    intro j
    rw [PdOp_seamPart_apply]
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases hl : j = last n
      · subst hl; simp [zero_ne_last.symm]
      · simp [h0, hl]
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_congr rfl fun j _ => hp j, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- `⟪T° u, P u⟫ = i Im(ψ̄₀ψ_{d−1})`. -/
theorem inner_transport_PdOp_seamPart :
    inner ℂ (transport n (seamPart ψ)) (PdOp (n + 3) (seamPart ψ)) =
      ((((starRingEnd ℂ) (ψ 0) * ψ (last n)).im : ℝ) : ℂ) * I := by
  rw [inner_PdOp_seamPart_right, transport_seamPart_apply, transport_seamPart_apply, alpha_zero,
    beta_zero, alpha_last, beta_last]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;> ring

theorem sum_alpha : ∑ j, alpha n j = 2 := by
  simp [alpha, Finset.sum_add_distrib]; norm_num

theorem sum_beta : ∑ j, beta n j = 2 := by
  simp [beta, Finset.sum_add_distrib]; norm_num

/-- **From `4` positions on, `‖T° u‖² = (|ψ₀|² + |ψ_{d−1}|²)/2`**: the four neighbours of the
seam are distinct. -/
theorem norm_transport_seamPart_sq (hn : 1 ≤ n) :
    ‖transport n (seamPart ψ)‖ ^ 2 = (‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2) / 2 := by
  have h1p : (1 : Fin (n + 3)) ≠ prev n := by simp [Fin.ext_iff]; omega
  have h10 : (1 : Fin (n + 3)) ≠ 0 := by simp
  have hlp : last n ≠ prev n := by simp [Fin.ext_iff]
  have hp : ∀ j, ‖transport n (seamPart ψ) j‖ ^ 2 =
      (alpha n j * ‖ψ 0‖ ^ 2 + beta n j * ‖ψ (last n)‖ ^ 2) / 4 := by
    intro j
    rw [transport_seamPart_apply]
    by_cases hj1 : j = 1
    · subst hj1; simp [alpha, beta, one_ne_last, h1p, h10]; ring
    by_cases hjl : j = last n
    · subst hjl; simp [alpha, beta, one_ne_last.symm, hlp, zero_ne_last.symm]; ring
    by_cases hjp : j = prev n
    · subst hjp; simp [alpha, beta, h1p.symm, hlp.symm]; ring
    by_cases hj0 : j = 0
    · subst hj0; simp [alpha, beta, h10.symm, prev_ne_zero.symm]; ring
    simp [alpha, beta, hj1, hjl, hjp, hj0]
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_congr rfl fun j _ => hp j, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sum_alpha, sum_beta]
  ring

end SeamMoments

/-! ## 5. Bounds at each size -/

/-- **At each size**, with `ε = 2/(d − 1)`: the seam carries `1 − ε` of the weight, the rest
at most `ε`, and `Re(ψ̄₀ψ_{d−1})`, `|ψ_{d−1}|² − |ψ₀|²` and `|Im(ψ̄₀ψ_{d−1})| − 1/2` are small. -/
theorem seam_bounds {ψ : Hd (n + 3)} (hψ : ‖ψ‖ = 1) (ht : 1 ≤ |tension n ψ|) :
    (1 - 2 / ((n : ℝ) + 2) ≤ ‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2 ∧
        ‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2 ≤ 1) ∧
      ‖ψ - seamPart ψ‖ ^ 2 ≤ 2 / ((n : ℝ) + 2) ∧
      ((starRingEnd ℂ) (ψ 0) * ψ (last n)).re ^ 2 ≤ 2 / ((n : ℝ) + 2) / 2 ∧
      (‖ψ (last n)‖ ^ 2 - ‖ψ 0‖ ^ 2) ^ 2 ≤ 2 * (2 / ((n : ℝ) + 2)) ∧
      ((1 - 2 / ((n : ℝ) + 2)) / 2 ≤ |((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| ∧
        |((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| ≤ 1 / 2) := by
  set ε := 2 / ((n : ℝ) + 2) with hε
  set z := (starRingEnd ℂ) (ψ 0) * ψ (last n)
  set x := ‖ψ 0‖
  set y := ‖ψ (last n)‖
  have hsplit := norm_sq_split ψ
  rw [hψ, one_pow] at hsplit
  have hw0 : 0 ≤ ‖ψ - seamPart ψ‖ ^ 2 := by positivity
  have hsl := seam_lower hψ ht
  have hz : ‖z‖ = x * y := by rw [norm_mul, Complex.norm_conj]
  have hq : |z.im| ≤ x * y := hz ▸ Complex.abs_im_le_norm z
  have hmq : z.re ^ 2 + z.im ^ 2 = (x * y) ^ 2 := by
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]; ring
  have hamgm : 2 * (x * y) ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hS1 : x ^ 2 + y ^ 2 ≤ 1 := by linarith
  have hqlo : (1 - ε) / 2 ≤ |z.im| := by linarith
  have hqhi : |z.im| ≤ 1 / 2 := by linarith
  have hq2 : ((1 - ε) / 2) ^ 2 ≤ z.im ^ 2 := by
    rw [← sq_abs z.im]
    exact pow_le_pow_left₀ (by linarith) hqlo 2
  have hxy : x * y ≤ 1 / 2 := by linarith
  have hxy0 : 0 ≤ x * y := by positivity
  refine ⟨⟨by linarith, hS1⟩, by linarith, ?_, ?_, hqlo, hqhi⟩
  · nlinarith
  · have hD : (y ^ 2 - x ^ 2) ^ 2 = (x ^ 2 + y ^ 2) ^ 2 - 4 * (x * y) ^ 2 := by ring
    have hS2 : (x ^ 2 + y ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x ^ 2 + y ^ 2)]
    nlinarith

/-! ## 6. Symmetry of the closed transport -/

theorem seamOp_isSymmetric : (seamOp n).IsSymmetric := by
  intro x y
  simp only [seamOp, LinearMap.add_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe,
    PiLp.proj_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one, one_mul]
  ring

theorem transport_isSymmetric : (transport n).IsSymmetric := by
  refine LinearMap.IsSymmetric.add (LinearMap.IsSymmetric.smul ?_ (TdOp_isSymmetric _))
    (LinearMap.IsSymmetric.smul ?_ seamOp_isSymmetric)
  · exact Complex.conj_ofReal _
  · simp [map_ofNat]

/-- At each size the moments of `ψ` and of its seam part differ by `C_A C_B ‖ψ − u‖ · 2`. -/
theorem norm_inner_seam_sub_le {A B : Hd (n + 3) →ₗ[ℂ] Hd (n + 3)} {CA CB : ℝ} (hCA : 0 ≤ CA)
    (hCB : 0 ≤ CB) (hA : ∀ x, ‖A x‖ ≤ CA * ‖x‖) (hB : ∀ x, ‖B x‖ ≤ CB * ‖x‖) {ψ : Hd (n + 3)}
    (hψ : ‖ψ‖ = 1) (hS : ‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2 ≤ 1) :
    ‖inner ℂ (A ψ) (B ψ) - inner ℂ (A (seamPart ψ)) (B (seamPart ψ))‖ ≤
      CA * CB * ‖ψ - seamPart ψ‖ * 2 := by
  have hu : ‖seamPart ψ‖ ≤ 1 := by
    have := norm_seamPart_sq ψ
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp (by linarith)
  have h := norm_inner_sub_le hCA hA hB (seamPart ψ) (ψ - seamPart ψ)
  rw [add_sub_cancel, hψ] at h
  calc _ ≤ _ := h
    _ ≤ CA * CB * ‖ψ - seamPart ψ‖ * (1 + 1) := by gcongr
    _ = _ := by ring

end RingSzego
