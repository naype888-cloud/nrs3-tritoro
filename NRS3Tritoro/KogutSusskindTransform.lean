/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindHarnack

/-!
# The ground-state transform

With the positive ground state `r > 0`, `H r = m0 r`, write every state as `ψ = r · f`. Then
`H − m0` becomes the generator of a reversible Markov chain on the configurations: from `U` it
jumps to `shift h e U`, for every link `e` and `h ∈ G`, at rate `(λE / |G|) · r(U') / r(U)`,
and `r²` is its reversible measure. The identity below is exact.

## Main results

- `KogutSusskindTransform.ground_transform` :
  `Re ⟨ψ, H ψ⟩ − m0 ⟨ψ,ψ⟩ = (λE / 2|G|) · Σ_e Σ_U Σ_h r(U) r(U') ‖f(U) − f(U')‖²`
  with `U' = shift h e U` and `f = ψ / r`: the Dirichlet form of the chain.
- `KogutSusskindTransform.gap_of_poincare` : a Poincaré inequality for `r²` with that form gives
  the gap of `H` above `m0` on the states orthogonal to `r`.

The Harnack inequality alone does not give the Poincaré inequality (a measure whose logarithm is
`ε`-Lipschitz in every coordinate can still have an exponentially small gap), so a bound on the
mixed differences of `log r` is what is missing for a gap uniform in the volume.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindSpectrum KogutSusskindGround
  KogutSusskindHarnack

namespace KogutSusskindTransform

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-- Swapping the two ends of a jump. -/
theorem sum_swap (e : δ × ι) (g : Conf ι δ G → Conf ι δ G → ℝ) :
    ∑ U, ∑ h : G, g U (shift h e.1 e.2 U) = ∑ U, ∑ h : G, g (shift h e.1 e.2 U) U := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun U h => g (shift h e.1 e.2 U) U)]
  have step : ∀ h : G, ∑ U, g U (shift h e.1 e.2 U) = ∑ V, g (shift h⁻¹ e.1 e.2 V) V := by
    intro h
    rw [← Equiv.sum_comp (shiftEquiv h⁻¹ e.1 e.2)]
    refine Finset.sum_congr rfl fun V _ => ?_
    simp [shiftEquiv, shift_shift, shift_one]
  simp only [step]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun h => rfl

/-- The Dirichlet form of the transformed chain. -/
def Dform (lE : ℝ) (r : Conf ι δ G → ℝ) (f : State ι δ G) : ℝ :=
  lE / 2 * (Fintype.card G : ℝ)⁻¹ *
    ∑ e : δ × ι, ∑ U, ∑ h : G,
      r U * r (shift h e.1 e.2 U) * ‖f U - f (shift h e.1 e.2 U)‖ ^ 2

/-- Symmetrisation of one link: the antisymmetric part cancels. -/
theorem half_form (e : δ × ι) (r : Conf ι δ G → ℝ) (f : State ι δ G) :
    ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) *
        (‖f U‖ ^ 2 - (star (f U) * f (shift h e.1 e.2 U)).re)
      = (1 / 2 : ℝ) * ∑ U, ∑ h : G,
        r U * r (shift h e.1 e.2 U) * ‖f U - f (shift h e.1 e.2 U)‖ ^ 2 := by
  have hanti := sum_swap e
    (fun a b => r a * r b * (‖f a‖ ^ 2 - ‖f b‖ ^ 2))
  have h0 : ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) *
      (‖f U‖ ^ 2 - ‖f (shift h e.1 e.2 U)‖ ^ 2) = 0 := by
    have : ∑ U, ∑ h : G, r (shift h e.1 e.2 U) * r U *
        (‖f (shift h e.1 e.2 U)‖ ^ 2 - ‖f U‖ ^ 2)
        = -∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) * (‖f U‖ ^ 2 - ‖f (shift h e.1 e.2 U)‖ ^ 2) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun U _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun h _ => by ring
    have hanti' : ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) *
        (‖f U‖ ^ 2 - ‖f (shift h e.1 e.2 U)‖ ^ 2)
        = ∑ U, ∑ h : G, r (shift h e.1 e.2 U) * r U *
          (‖f (shift h e.1 e.2 U)‖ ^ 2 - ‖f U‖ ^ 2) := hanti
    linarith
  have hexp : ∀ U (h : G), r U * r (shift h e.1 e.2 U) *
      (‖f U‖ ^ 2 - (star (f U) * f (shift h e.1 e.2 U)).re)
      = (1 / 2 : ℝ) * (r U * r (shift h e.1 e.2 U) * ‖f U - f (shift h e.1 e.2 U)‖ ^ 2)
        + (1 / 2 : ℝ) * (r U * r (shift h e.1 e.2 U) *
          (‖f U‖ ^ 2 - ‖f (shift h e.1 e.2 U)‖ ^ 2)) := by
    intro U h
    have : ‖f U - f (shift h e.1 e.2 U)‖ ^ 2 = ‖f U‖ ^ 2 + ‖f (shift h e.1 e.2 U)‖ ^ 2
        - 2 * (star (f U) * f (shift h e.1 e.2 U)).re := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [this]; ring
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h0]; ring

/-- The per-link identity of the ground-state transform. -/
theorem link_identity (e : δ × ι) {r : Conf ι δ G → ℝ} (hr : ∀ U, 0 < r U) (ψ : State ι δ G) :
    nsq ψ - (ip ψ (elecProj e.1 e.2 ψ)).re
        - ∑ U, ‖ψ U / (r U : ℂ)‖ ^ 2 * r U * (r U - X r e U)
      = (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) *
          (‖ψ U / (r U : ℂ)‖ ^ 2
            - (star (ψ U / (r U : ℂ)) * (ψ (shift h e.1 e.2 U) / (r (shift h e.1 e.2 U) : ℂ))).re) := by
  set f : State ι δ G := fun U => ψ U / (r U : ℂ) with hf
  have hψ : ∀ U, ψ U = (r U : ℂ) * f U := by
    intro U
    have : (r U : ℂ) ≠ 0 := by exact_mod_cast (hr U).ne'
    simp only [hf]; field_simp
  have hnorm : ∀ U, ‖ψ U‖ ^ 2 = r U ^ 2 * ‖f U‖ ^ 2 := by
    intro U
    rw [hψ U, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hn : nsq ψ = ∑ U, ‖f U‖ ^ 2 * r U * r U := by
    unfold nsq
    exact Finset.sum_congr rfl fun U _ => by rw [hnorm U]; ring
  have hstar : ∀ U (h : G), (star (ψ U) * ψ (shift h e.1 e.2 U)).re
      = r U * r (shift h e.1 e.2 U) * (star (f U) * f (shift h e.1 e.2 U)).re := by
    intro U h
    rw [hψ U, hψ (shift h e.1 e.2 U)]
    have : star ((r U : ℂ) * f U) * ((r (shift h e.1 e.2 U) : ℂ) * f (shift h e.1 e.2 U))
        = ((r U * r (shift h e.1 e.2 U) : ℝ) : ℂ) * (star (f U) * f (shift h e.1 e.2 U)) := by
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  have hX : ∑ U, ‖f U‖ ^ 2 * r U * (r U - X r e U)
      = ∑ U, ‖f U‖ ^ 2 * r U * r U
        - (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G,
            r U * r (shift h e.1 e.2 U) * ‖f U‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun U _ => ?_
    unfold X
    have e1 : ∑ h : G, r U * r (shift h e.1 e.2 U) * ‖f U‖ ^ 2
        = (r U * ‖f U‖ ^ 2) * ∑ h : G, r (shift h e.1 e.2 U) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
    rw [e1]; ring
  have hP : (ip ψ (elecProj e.1 e.2 ψ)).re = (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G,
      r U * r (shift h e.1 e.2 U) * (star (f U) * f (shift h e.1 e.2 U)).re := by
    rw [re_ip_proj_eq]
    simp only [hstar]
  have hexpand : (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) *
        (‖f U‖ ^ 2 - (star (f U) * f (shift h e.1 e.2 U)).re)
      = (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) * ‖f U‖ ^ 2
        - (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G,
          r U * r (shift h e.1 e.2 U) * (star (f U) * f (shift h e.1 e.2 U)).re := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun h _ => by ring
  show nsq ψ - (ip ψ (elecProj e.1 e.2 ψ)).re - ∑ U, ‖f U‖ ^ 2 * r U * (r U - X r e U)
      = (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G, r U * r (shift h e.1 e.2 U) *
          (‖f U‖ ^ 2 - (star (f U) * f (shift h e.1 e.2 U)).re)
  rw [hexpand, hX, hP, hn]; ring

theorem norm_sq_eq {r : Conf ι δ G → ℝ} (hr : ∀ U, 0 < r U) (ψ : State ι δ G) (U : Conf ι δ G) :
    ‖ψ U‖ ^ 2 = r U ^ 2 * ‖ψ U / (r U : ℂ)‖ ^ 2 := by
  have : (r U : ℂ) ≠ 0 := by exact_mod_cast (hr U).ne'
  have hne : r U ≠ 0 := (hr U).ne'
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr U), div_pow]
  field_simp

/-- **The ground-state transform.** For `ψ = r f`:
`Re ⟨ψ, H ψ⟩ − m0 ⟨ψ,ψ⟩` is the Dirichlet form of `f`. -/
theorem ground_transform {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ} (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (ψ : State ι δ G) :
    (ip ψ (ham ρ τ R lE lB ψ)).re - m0 * nsq ψ
      = Dform lE r (fun U => ψ U / (r U : ℂ)) := by
  set f : State ι δ G := fun U => ψ U / (r U : ℂ) with hf
  have hnorm : ∀ U, ‖ψ U‖ ^ 2 = r U ^ 2 * ‖f U‖ ^ 2 := norm_sq_eq hr ψ
  have hm0 : m0 * nsq ψ = lE * ∑ e : δ × ι, ∑ U, ‖f U‖ ^ 2 * r U * (r U - X r e U)
      + lB * ∑ U, pot ρ τ R U * ‖ψ U‖ ^ 2 := by
    calc m0 * nsq ψ = ∑ U, (‖f U‖ ^ 2 * r U) * (m0 * r U) := by
          unfold nsq; rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun U _ => by rw [hnorm U]; ring
      _ = ∑ U, (‖f U‖ ^ 2 * r U) * (lE * ∑ e : δ × ι, (r U - X r e U)
            + lB * pot ρ τ R U * r U) := by
          refine Finset.sum_congr rfl fun U _ => ?_
          rw [eigen_real ρ τ R heig U]
      _ = _ := by
          have e1 : ∑ U, (‖f U‖ ^ 2 * r U) * (lE * ∑ e : δ × ι, (r U - X r e U))
              = lE * ∑ e : δ × ι, ∑ U, ‖f U‖ ^ 2 * r U * (r U - X r e U) := by
            have hU : ∀ U, (‖f U‖ ^ 2 * r U) * (lE * ∑ e : δ × ι, (r U - X r e U))
                = lE * ∑ e : δ × ι, ‖f U‖ ^ 2 * r U * (r U - X r e U) := by
              intro U
              simp only [Finset.mul_sum]
              exact Finset.sum_congr rfl fun e _ => by ring
            simp_rw [hU]
            rw [← Finset.mul_sum, Finset.sum_comm]
          have e2 : ∑ U, (‖f U‖ ^ 2 * r U) * (lB * pot ρ τ R U * r U)
              = lB * ∑ U, pot ρ τ R U * ‖ψ U‖ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun U _ => by rw [hnorm U]; ring
          simp only [mul_add, Finset.sum_add_distrib]
          rw [e1, e2]
  have hlink : ∀ e : δ × ι, nsq ψ - (ip ψ (elecProj e.1 e.2 ψ)).re
        - ∑ U, ‖f U‖ ^ 2 * r U * (r U - X r e U)
      = (Fintype.card G : ℝ)⁻¹ * ((1 / 2 : ℝ) * ∑ U, ∑ h : G,
        r U * r (shift h e.1 e.2 U) * ‖f U - f (shift h e.1 e.2 U)‖ ^ 2) := by
    intro e
    rw [link_identity e hr ψ, half_form e r f]
  rw [ham_form, re_ip_elecTotal, re_ip_mag, hm0, ← Fintype.sum_prod_type (f := fun e : δ × ι =>
    nsq ψ - (ip ψ (elecProj e.1 e.2 ψ)).re)]
  unfold Dform
  have hsum : ∑ e : δ × ι, (nsq ψ - (ip ψ (elecProj e.1 e.2 ψ)).re)
      = ∑ e : δ × ι, ((Fintype.card G : ℝ)⁻¹ * ((1 / 2 : ℝ) * ∑ U, ∑ h : G,
        r U * r (shift h e.1 e.2 U) * ‖f U - f (shift h e.1 e.2 U)‖ ^ 2)
        + ∑ U, ‖f U‖ ^ 2 * r U * (r U - X r e U)) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    have := hlink e
    linarith
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Poincaré for `r²` gives the gap of `H`.** If every `f` with zero mean for `r²` satisfies
`Σ r² ‖f‖² ≤ C · D(f)`, then every state `ψ` orthogonal to `r` satisfies
`⟨ψ,ψ⟩ ≤ C (Re ⟨ψ, H ψ⟩ − m0 ⟨ψ,ψ⟩)`, i.e. `Re ⟨ψ, H ψ⟩ ≥ (m0 + 1/C) ⟨ψ,ψ⟩`. -/
theorem gap_of_poincare {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ} (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    {C : ℝ}
    (hP : ∀ f : State ι δ G, ∑ U, (r U : ℂ) ^ 2 * f U = 0 →
      ∑ U, r U ^ 2 * ‖f U‖ ^ 2 ≤ C * Dform lE r f)
    (ψ : State ι δ G) (hψ : ∑ U, (r U : ℂ) * ψ U = 0) :
    nsq ψ ≤ C * ((ip ψ (ham ρ τ R lE lB ψ)).re - m0 * nsq ψ) := by
  have hne : ∀ U, (r U : ℂ) ≠ 0 := fun U => by exact_mod_cast (hr U).ne'
  have h0 : ∑ U, (r U : ℂ) ^ 2 * (ψ U / (r U : ℂ)) = 0 := by
    rw [← hψ]
    exact Finset.sum_congr rfl fun U _ => by field_simp [hne U]
  have h1 := hP (fun U => ψ U / (r U : ℂ)) h0
  have h2 : ∑ U, r U ^ 2 * ‖ψ U / (r U : ℂ)‖ ^ 2 = nsq ψ := by
    unfold nsq
    exact Finset.sum_congr rfl fun U _ => (norm_sq_eq hr ψ U).symm
  rw [h2, ← ground_transform ρ τ R hr heig ψ] at h1
  exact h1

/-- **The eigenvalues above `m0`**: under the Poincaré inequality, an eigenvector orthogonal to
`r` has eigenvalue at least `m0 + 1/C`. -/
theorem eigenvalue_gap_of_poincare {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ)
    (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ)) {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ}
    (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    {C : ℝ} (hC : 0 < C)
    (hP : ∀ f : State ι δ G, ∑ U, (r U : ℂ) ^ 2 * f U = 0 →
      ∑ U, r U ^ 2 * ‖f U‖ ^ 2 ≤ C * Dform lE r f)
    {ε : ℝ} (χ : State ι δ G) (hχ : ∀ U, ham ρ τ R lE lB χ U = (ε : ℂ) * χ U)
    (horth : ∑ U, (r U : ℂ) * χ U = 0) (hpos : 0 < nsq χ) :
    m0 + 1 / C ≤ ε := by
  have h := gap_of_poincare ρ τ R hr heig hP χ horth
  have hq : (ip χ (ham ρ τ R lE lB χ)).re = ε * nsq χ := by
    have : ip χ (ham ρ τ R lE lB χ) = (ε : ℂ) * ip χ χ := by
      unfold ip
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ => by rw [hχ U]; ring
    rw [this, ip_self]
    simp
  rw [hq] at h
  have h3 : nsq χ ≤ C * ((ε - m0) * nsq χ) := by nlinarith
  have h4 : 1 ≤ C * (ε - m0) := by
    by_contra hlt
    push_neg at hlt
    nlinarith
  have : 1 / C ≤ ε - m0 := by
    rw [div_le_iff₀ hC]; linarith
  linarith

end KogutSusskindTransform
