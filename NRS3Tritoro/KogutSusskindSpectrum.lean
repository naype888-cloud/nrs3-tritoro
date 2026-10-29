/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindGap
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The spectral gap of the Kogut-Susskind Hamiltonian at finite volume

`KogutSusskindGap` bounds the Rayleigh quotient. Here the Hamiltonian is a symmetric operator
of the finite-dimensional space `EuclideanSpace ℂ (Conf ι δ G)`, and the bounds become statements
about its eigenvalues, by the spectral theorem of Mathlib (min-max by hand, on two eigenvectors).

## Main results

- `KogutSusskindSpectrum.HE_isSymmetric` : `H` is a symmetric operator.
- `KogutSusskindSpectrum.two_eigenvalues_ge` : among any two eigenvalues (two different vectors of
  the eigenbasis) the larger is `≥ λE`.
- `KogutSusskindSpectrum.exists_eigenvalue_le` : some eigenvalue is `≤ λB · 2n · |R|`.
- `KogutSusskindSpectrum.spectral_gap` : if `λB · 2n · |R| < λE`, one eigenvalue is
  `≤ λB · 2n · |R|` and all the others are `≥ λE`: the gap is at least `λE − λB · 2n · |R|`.

The gap depends on `|R|`: it is a finite-volume gap, not a uniform one.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap

namespace KogutSusskindSpectrum

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))
  (lE lB : ℝ)

/-- The Hamiltonian as a linear map of the states. -/
def Hlin : State ι δ G →ₗ[ℂ] State ι δ G where
  toFun := ham ρ τ R lE lB
  map_add' a b := by
    funext U
    have h1 : ∀ μ p, elec μ p (a + b) U = elec μ p a U + elec μ p b U := by
      intro μ p
      simp only [elec, elecProj, Pi.add_apply, Finset.sum_add_distrib, mul_add]
      ring
    simp only [ham, elecTotal, mag, Pi.add_apply, h1, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    funext U
    have h1 : ∀ μ p, elec μ p (c • a) U = c * elec μ p a U := by
      intro μ p
      simp only [elec, elecProj, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    simp only [ham, elecTotal, mag, Pi.smul_apply, smul_eq_mul, h1, RingHom.id_apply,
      ← Finset.mul_sum]
    ring

/-- The Euclidean space of the states. -/
abbrev EH (ι δ G : Type*) [Fintype ι] [Fintype δ] [Fintype G] [DecidableEq δ] :=
  EuclideanSpace ℂ (Conf ι δ G)

/-- The Hamiltonian on the Euclidean space of the states. -/
def HE : EH ι δ G →ₗ[ℂ] EH ι δ G :=
  (WithLp.linearEquiv 2 ℂ (Conf ι δ G → ℂ)).symm.toLinearMap ∘ₗ Hlin ρ τ R lE lB ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Conf ι δ G → ℂ)).toLinearMap

variable {ρ τ R lE lB}

theorem inner_eq_ip (x y : EH ι δ G) : inner ℂ x y = ip (WithLp.ofLp x) (WithLp.ofLp y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [ip, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun U _ => mul_comm _ _

theorem ofLp_HE (x : EH ι δ G) :
    WithLp.ofLp (HE ρ τ R lE lB x) = ham ρ τ R lE lB (WithLp.ofLp x) := rfl

theorem HE_isSymmetric : (HE ρ τ R lE lB).IsSymmetric := by
  intro x y
  rw [inner_eq_ip, inner_eq_ip, ofLp_HE, ofLp_HE]
  exact (ham_symm ρ τ R lE lB (WithLp.ofLp x) (WithLp.ofLp y)).symm

theorem nsq_eq_norm_sq (x : EH ι δ G) : nsq (WithLp.ofLp x) = ‖x‖ ^ 2 := by
  have h := ip_self (WithLp.ofLp x)
  rw [← inner_eq_ip, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h.symm)

theorem re_inner_HE (x : EH ι δ G) :
    (inner ℂ x (HE ρ τ R lE lB x)).re = (ip (WithLp.ofLp x) (ham ρ τ R lE lB (WithLp.ofLp x))).re := by
  rw [inner_eq_ip, ofLp_HE]

variable {m : ℕ}

/-- **Two eigenvalues**: of any two different vectors of the eigenbasis, the larger eigenvalue is
at least `λE`. (Min-max on the two-dimensional span, which meets the zero-sum states.) -/
theorem two_eigenvalues_ge (hE : 0 ≤ lE) (hB : 0 ≤ lB)
    (hm : Module.finrank ℂ (EH ι δ G) = m) {i j : Fin m} (hij : i ≠ j) :
    lE ≤ max ((HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i)
      ((HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm j) := by
  set hT := HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) with hTdef
  set b := hT.eigenvectorBasis hm with hb
  set μ := hT.eigenvalues hm with hμ
  have hon := orthonormal_iff_ite.mp b.orthonormal
  have hii : inner ℂ (b i) (b i) = 1 := by simpa using hon i i
  have hjj : inner ℂ (b j) (b j) = 1 := by simpa using hon j j
  have hij' : inner ℂ (b i) (b j) = 0 := by simpa [hij] using hon i j
  have hji' : inner ℂ (b j) (b i) = 0 := by simpa [Ne.symm hij] using hon j i
  set si : ℂ := ∑ U, (b i).ofLp U with hsi
  set sj : ℂ := ∑ U, (b j).ofLp U with hsj
  obtain ⟨a, c, hac, hs⟩ : ∃ a c : ℂ, (a ≠ 0 ∨ c ≠ 0) ∧ a * si + c * sj = 0 := by
    by_cases h : si = 0 ∧ sj = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h.1]⟩
    · refine ⟨sj, -si, ?_, by ring⟩
      by_contra hc
      push_neg at hc
      exact h ⟨by simpa using hc.2, hc.1⟩
  set ψ : EH ι δ G := a • b i + c • b j with hψ
  have h0 : ∑ U, (ψ.ofLp) U = 0 := by
    have : ∑ U, (ψ.ofLp) U = a * si + c * sj := by
      simp only [hψ, hsi, hsj, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [this, hs]
  have hHψ : HE ρ τ R lE lB ψ = (a * (μ i : ℂ)) • b i + (c * (μ j : ℂ)) • b j := by
    simp only [hψ, map_add, map_smul, hb, hμ, hT.apply_eigenvectorBasis, smul_smul]
    rfl
  have hnorm : inner ℂ ψ ψ = ((‖a‖ ^ 2 + ‖c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hψ, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hii, hjj,
      hij', hji']
    have ea : a * (starRingEnd ℂ) a = (‖a‖ : ℂ) ^ 2 := Complex.mul_conj' a
    have ec : c * (starRingEnd ℂ) c = (‖c‖ : ℂ) ^ 2 := Complex.mul_conj' c
    simp only [mul_one, mul_zero, add_zero, zero_add, ea, ec]
    push_cast; ring
  have hq : inner ℂ ψ (HE ρ τ R lE lB ψ)
      = ((‖a‖ ^ 2 * μ i + ‖c‖ ^ 2 * μ j : ℝ) : ℂ) := by
    rw [hHψ]
    simp only [hψ, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hii, hjj,
      hij', hji']
    push_cast
    have e1 : a * (μ i : ℂ) * (starRingEnd ℂ) a = (‖a‖ : ℂ) ^ 2 * μ i := by
      rw [mul_right_comm, Complex.mul_conj']
    have e2 : c * (μ j : ℂ) * (starRingEnd ℂ) c = (‖c‖ : ℂ) ^ 2 * μ j := by
      rw [mul_right_comm, Complex.mul_conj']
    simp only [mul_one, mul_zero, add_zero, zero_add, e1, e2]
  have hpos : 0 < ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    rcases hac with h | h
    · have := norm_pos_iff.mpr h; positivity
    · have := norm_pos_iff.mpr h; positivity
  have hnsq : nsq (WithLp.ofLp ψ) = ‖a‖ ^ 2 + ‖c‖ ^ 2 := by
    have := ip_self (WithLp.ofLp ψ)
    rw [← inner_eq_ip, hnorm] at this
    exact_mod_cast this.symm
  have hgap := gap_ham ρ τ R hE hB (WithLp.ofLp ψ) h0
  rw [hnsq, ← re_inner_HE, hq, Complex.ofReal_re] at hgap
  have hmax : ‖a‖ ^ 2 * μ i + ‖c‖ ^ 2 * μ j ≤ max (μ i) (μ j) * (‖a‖ ^ 2 + ‖c‖ ^ 2) := by
    nlinarith [le_max_left (μ i) (μ j), le_max_right (μ i) (μ j), sq_nonneg ‖a‖, sq_nonneg ‖c‖]
  by_contra hlt
  push_neg at hlt
  nlinarith

/-- **The lowest eigenvalue is at most the vacuum energy bound**: some eigenvalue is
`≤ λB · 2n · |R|`. -/
theorem exists_eigenvalue_le (hB : 0 ≤ lB) (hm : Module.finrank ℂ (EH ι δ G) = m) :
    ∃ i : Fin m, (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i
      ≤ lB * (2 * n * R.card) := by
  set hT := HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) with hTdef
  set b := hT.eigenvectorBasis hm with hb
  set μ := hT.eigenvalues hm with hμ
  set x : EH ι δ G := WithLp.toLp 2 (one : State ι δ G) with hx
  have hxn : ‖x‖ ^ 2 = Fintype.card (Conf ι δ G) := by
    rw [← nsq_eq_norm_sq]
    simp [nsq, hx, one]
  have hcard : 0 < Fintype.card (Conf ι δ G) := Fintype.card_pos_iff.mpr ⟨fun _ _ => 1⟩
  have hx0 : x ≠ 0 := by
    intro h
    have h0 : (Fintype.card (Conf ι δ G) : ℝ) = 0 := by rw [← hxn, h]; simp
    exact hcard.ne' (Nat.cast_eq_zero.mp h0)
  haveI : Nontrivial (EH ι δ G) := nontrivial_of_ne x 0 hx0
  have hmpos : 0 < m := hm ▸ Module.finrank_pos
  haveI : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ μ Finset.univ_nonempty
  refine ⟨i0, ?_⟩
  -- Rayleigh quotient of `x` in the eigenbasis
  have hrq : (inner ℂ x (HE ρ τ R lE lB x)).re = ∑ i, μ i * ‖inner ℂ (b i) x‖ ^ 2 := by
    rw [← b.sum_inner_mul_inner x (HE ρ τ R lE lB x), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : inner ℂ (b i) (HE ρ τ R lE lB x) = (μ i : ℂ) * inner ℂ (b i) x := by
      rw [← hT (b i) x]
      simp only [hb, hμ, hT.apply_eigenvectorBasis, inner_smul_left, Complex.conj_ofReal,
        RCLike.conj_ofReal]
      rfl
    rw [h1]
    have : inner ℂ x (b i) * ((μ i : ℂ) * inner ℂ (b i) x)
        = ((μ i * ‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_conj_symm x (b i)]
      push_cast
      rw [show (starRingEnd ℂ) (inner ℂ (b i) x) * ((μ i : ℂ) * inner ℂ (b i) x)
          = (μ i : ℂ) * ((starRingEnd ℂ) (inner ℂ (b i) x) * inner ℂ (b i) x) by ring,
        Complex.conj_mul']
    rw [this, Complex.ofReal_re]
  have hsum : ∑ i, ‖inner ℂ (b i) x‖ ^ 2 = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x
  have hlow : μ i0 * ‖x‖ ^ 2 ≤ (inner ℂ x (HE ρ τ R lE lB x)).re := by
    rw [hrq, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hi0 i (Finset.mem_univ i)) (sq_nonneg _)
  have hup := vacuum_energy_le ρ τ R (lE := lE) (lB := lB) (G := G) (ι := ι) (δ := δ) hB
  have hupx : (inner ℂ x (HE ρ τ R lE lB x)).re ≤ lB * (2 * n * R.card) * ‖x‖ ^ 2 := by
    rw [re_inner_HE, ← nsq_eq_norm_sq]; exact hup
  have hxpos : 0 < ‖x‖ ^ 2 := by rw [hxn]; exact_mod_cast hcard
  by_contra hlt
  push_neg at hlt
  nlinarith

/-- **Spectral gap at finite volume**: if `λB · 2n · |R| < λE`, one eigenvalue is at most
`λB · 2n · |R|` and all the others are at least `λE`. -/
theorem spectral_gap (hE : 0 ≤ lE) (hB : 0 ≤ lB) (hsmall : lB * (2 * n * R.card) < lE)
    (hm : Module.finrank ℂ (EH ι δ G) = m) :
    ∃ i0 : Fin m,
      (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i0
        ≤ lB * (2 * n * R.card) ∧
      ∀ i, i ≠ i0 →
        lE ≤ (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i := by
  obtain ⟨i0, hi0⟩ := exists_eigenvalue_le (ρ := ρ) (τ := τ) (R := R) (lE := lE) hB hm
  refine ⟨i0, hi0, fun i hi => ?_⟩
  have h2 := two_eigenvalues_ge (ρ := ρ) (τ := τ) (R := R) hE hB hm hi
  rcases le_max_iff.mp h2 with h | h
  · exact h
  · linarith

end KogutSusskindSpectrum
