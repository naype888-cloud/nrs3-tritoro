/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindSecondDiff

/-!
# Uniqueness of the ground state

Let `r > 0` with `H r = m0 r` (`KogutSusskindGround`). Every state `χ` with `H χ = m0 χ` is a
multiple of `r`: the eigenvalue `m0` is simple.

The proof does not use that `m0` is the lowest eigenvalue. A real eigenvector `g` of eigenvalue
`m0` gives, for `t = min g / r`, the nonnegative eigenvector `g − t r` that vanishes somewhere, and
a nonnegative eigenvector that is not zero is strictly positive (`pos_of_nonneg_eigen`), so it is
zero. A complex eigenvector is split into its real and imaginary parts, which are eigenvectors
because `H` is real (`ham_conj`).

## Main results

- `KogutSusskindUnique.ham_conj` : `H` commutes with complex conjugation.
- `KogutSusskindUnique.real_eigen_unique` : a real eigenvector of eigenvalue `m0` is a real
  multiple of `r`.
- `KogutSusskindUnique.ground_unique` : any eigenvector of eigenvalue `m0` is a multiple of `r`.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindSpectrum KogutSusskindGround
  KogutSusskindHarnack

namespace KogutSusskindUnique

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))
  (lE lB : ℝ)

/-- **`H` is real**: it commutes with complex conjugation. -/
theorem ham_conj (ψ : State ι δ G) (U : Conf ι δ G) :
    ham ρ τ R lE lB (fun V => star (ψ V)) U = star (ham ρ τ R lE lB ψ U) := by
  simp [ham, elecTotal, elec, elecProj, mag, star_sum, star_mul', star_sub, star_add,
    Complex.star_def, map_sum]

/-- `H` applied to a combination of `χ` and its conjugate. -/
theorem ham_comb (a b : ℂ) (χ : State ι δ G) (U : Conf ι δ G) :
    ham ρ τ R lE lB (fun V => a * χ V + b * star (χ V)) U
      = a * ham ρ τ R lE lB χ U + b * star (ham ρ τ R lE lB χ U) := by
  have h1 : (fun V => a * χ V + b * star (χ V))
      = a • χ + b • (fun V => star (χ V)) := by
    funext V; simp
  have h2 := (Hlin ρ τ R lE lB).map_add (a • χ) (b • (fun V => star (χ V)))
  have h3 := (Hlin ρ τ R lE lB).map_smul a χ
  have h4 := (Hlin ρ τ R lE lB).map_smul b (fun V => star (χ V))
  rw [h1]
  have e : ham ρ τ R lE lB (a • χ + b • fun V => star (χ V))
      = a • ham ρ τ R lE lB χ + b • ham ρ τ R lE lB (fun V => star (χ V)) := by
    exact h2.trans (by rw [h3, h4]; rfl)
  rw [e]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ham_conj]

variable {lE lB}

/-- **A real eigenvector is a multiple of the ground state.** -/
theorem real_eigen_unique {m0 : ℝ} {r : Conf ι δ G → ℝ} (hE : 0 < lE) (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    {g : Conf ι δ G → ℝ}
    (hg : ∀ U, ham ρ τ R lE lB (fun U => (g U : ℂ)) U = (m0 : ℂ) * (g U : ℂ)) :
    ∃ t : ℝ, ∀ U, g U = t * r U := by
  haveI : Nonempty (Conf ι δ G) := ⟨fun _ _ => 1⟩
  obtain ⟨U0, -, hU0⟩ := Finset.exists_min_image Finset.univ (fun U => g U / r U)
    Finset.univ_nonempty
  set t : ℝ := g U0 / r U0 with ht
  set h : Conf ι δ G → ℝ := fun U => g U - t * r U with hh
  have hnn : ∀ U, 0 ≤ h U := fun U => by
    have := hU0 U (Finset.mem_univ U)
    have h2 : t * r U ≤ g U := by
      rw [← le_div_iff₀ (hr U)]; exact this
    simp only [hh]; linarith
  have hz : h U0 = 0 := by
    show g U0 - g U0 / r U0 * r U0 = 0
    rw [div_mul_cancel₀ _ (hr U0).ne', sub_self]
  have hcomb : (fun V => ((h V : ℝ) : ℂ))
      = (fun V => ((g V : ℝ) : ℂ)) + (-(t : ℂ)) • (fun V => ((r V : ℝ) : ℂ)) := by
    funext V; simp [hh]; ring
  have heigh : ∀ U, ham ρ τ R lE lB (fun U => (h U : ℂ)) U = (m0 : ℂ) * (h U : ℂ) := by
    intro U
    rw [hcomb]
    have e : ham ρ τ R lE lB ((fun V => ((g V : ℝ) : ℂ)) + (-(t : ℂ)) • fun V => ((r V : ℝ) : ℂ))
        = ham ρ τ R lE lB (fun V => ((g V : ℝ) : ℂ))
          + (-(t : ℂ)) • ham ρ τ R lE lB (fun V => ((r V : ℝ) : ℂ)) :=
      ((Hlin ρ τ R lE lB).map_add _ _).trans (by rw [(Hlin ρ τ R lE lB).map_smul]; rfl)
    rw [e]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hg U, heig U]
    simp only [hh]; push_cast; ring
  have hall : ∀ U, h U = 0 := by
    intro U
    by_contra hne
    have hpos := pos_of_nonneg_eigen ρ τ R hE hnn ⟨U, hne⟩ heigh U0
    linarith
  exact ⟨t, fun U => by have := hall U; simp only [hh] at this; linarith⟩

/-- **Uniqueness of the ground state**: every eigenvector of eigenvalue `m0` is a multiple
of `r`. -/
theorem ground_unique {m0 : ℝ} {r : Conf ι δ G → ℝ} (hE : 0 < lE) (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (χ : State ι δ G) (hχ : ∀ U, ham ρ τ R lE lB χ U = (m0 : ℂ) * χ U) :
    ∃ c : ℂ, ∀ U, χ U = c * (r U : ℂ) := by
  have hstar : ∀ U, star (ham ρ τ R lE lB χ U) = (m0 : ℂ) * star (χ U) := by
    intro U
    rw [hχ U, star_mul', Complex.star_def, Complex.conj_ofReal]
  -- real part
  have hre : ∀ U, ham ρ τ R lE lB (fun V => (((χ V).re : ℝ) : ℂ)) U
      = (m0 : ℂ) * (((χ U).re : ℝ) : ℂ) := by
    intro U
    have e : (fun V => (((χ V).re : ℝ) : ℂ))
        = fun V => (1 / 2 : ℂ) * χ V + (1 / 2 : ℂ) * star (χ V) := by
      funext V
      rw [Complex.re_eq_add_conj]; simp [Complex.star_def]; ring
    rw [e, ham_comb, hstar U, hχ U, Complex.re_eq_add_conj]
    simp [Complex.star_def]; ring
  have him : ∀ U, ham ρ τ R lE lB (fun V => (((χ V).im : ℝ) : ℂ)) U
      = (m0 : ℂ) * (((χ U).im : ℝ) : ℂ) := by
    intro U
    have e : (fun V => (((χ V).im : ℝ) : ℂ))
        = fun V => (-Complex.I / 2 : ℂ) * χ V + (Complex.I / 2 : ℂ) * star (χ V) := by
      funext V
      rw [Complex.im_eq_sub_conj]; simp [Complex.star_def]
      field_simp; ring_nf; simp [Complex.I_sq]; ring
    rw [e, ham_comb, hstar U, hχ U, Complex.im_eq_sub_conj]
    simp [Complex.star_def]
    field_simp
    linear_combination ((m0 : ℂ) * (starRingEnd ℂ) (χ U) - (m0 : ℂ) * χ U) * Complex.I_sq
  obtain ⟨t1, ht1⟩ := real_eigen_unique ρ τ R hE hr heig hre
  obtain ⟨t2, ht2⟩ := real_eigen_unique ρ τ R hE hr heig him
  refine ⟨(t1 : ℂ) + (t2 : ℂ) * Complex.I, fun U => ?_⟩
  apply Complex.ext
  · simp [ht1 U, ht2 U]
  · simp [ht1 U, ht2 U]

/-- **Every other eigenvalue is strictly above `m0`**: an eigenvector that is not a multiple of
`r` has eigenvalue `> m0`, if `m0` is the minimum of the Rayleigh quotient. -/
theorem eigenvalue_gt {m0 : ℝ} {r : Conf ι δ G → ℝ} (hE : 0 < lE) (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (hmin : ∀ ψ : State ι δ G, m0 * nsq ψ ≤ (ip ψ (ham ρ τ R lE lB ψ)).re)
    {ε : ℝ} (χ : State ι δ G) (hχ : ∀ U, ham ρ τ R lE lB χ U = (ε : ℂ) * χ U)
    (hpos : 0 < nsq χ) (hnot : ¬ ∃ c : ℂ, ∀ U, χ U = c * (r U : ℂ)) : m0 < ε := by
  have hq : (ip χ (ham ρ τ R lE lB χ)).re = ε * nsq χ := by
    have : ip χ (ham ρ τ R lE lB χ) = (ε : ℂ) * ip χ χ := by
      unfold ip
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun U _ => by rw [hχ U]; ring
    rw [this, ip_self]
    simp
  have h1 := hmin χ
  rw [hq] at h1
  have hle : m0 ≤ ε := by nlinarith
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hnot
    apply ground_unique ρ τ R hE hr heig χ
    intro U
    rw [hχ U, h]

end KogutSusskindUnique
