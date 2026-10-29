/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindSpectrum

/-!
# The ground state of the Kogut-Susskind Hamiltonian is positive

The Hamiltonian is stoquastic: in the configuration basis its off-diagonal entries are `≤ 0`
(they are minus the entries of the averaging projectors). Three consequences, at finite volume
and fixed spacing:

- replacing a state `ψ` by its modulus `|ψ|` does not raise the energy,
  `Re ⟨|ψ|, H |ψ|⟩ ≤ Re ⟨ψ, H ψ⟩` (`ham_abs_le`);
- a state that reaches the lowest eigenvalue is an eigenvector (`eigen_of_minimiser`);
- the ground state may be taken with all its entries `> 0`
  (`exists_positive_ground_state`), because the zeros of a nonnegative eigenvector are closed
  under the translations of one link, and any two configurations are joined by such translations.

No gap is claimed here: the point is the positive vector `Ω` that a uniform bound will need
(Harnack for `Ω`, then Poincaré for `Ω²`).
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindSpectrum

namespace KogutSusskindGround

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-- The modulus of a state, as a state with real nonnegative entries. -/
def absS (ψ : State ι δ G) : State ι δ G := fun U => ((‖ψ U‖ : ℝ) : ℂ)

theorem nsq_absS (ψ : State ι δ G) : nsq (absS ψ) = nsq ψ := by
  simp [nsq, absS]

theorem re_ip_proj_eq (μ : δ) (p : ι) (a b : State ι δ G) :
    (ip a (elecProj μ p b)).re
      = (Fintype.card G : ℝ)⁻¹ * ∑ U, ∑ h : G, (star (a U) * b (shift h μ p U)).re := by
  have hc : (Fintype.card G : ℂ)⁻¹ = (((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  unfold ip elecProj
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [hc, mul_left_comm, Complex.re_ofReal_mul]
  congr 1
  rw [Finset.mul_sum, Complex.re_sum]

/-- **The modulus does not raise the projector term.** -/
theorem re_ip_proj_le (μ : δ) (p : ι) (ψ : State ι δ G) :
    (ip ψ (elecProj μ p ψ)).re ≤ (ip (absS ψ) (elecProj μ p (absS ψ))).re := by
  rw [re_ip_proj_eq, re_ip_proj_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun U _ => Finset.sum_le_sum fun h _ => ?_
  have h1 : (star (ψ U) * ψ (shift h μ p U)).re ≤ ‖ψ U‖ * ‖ψ (shift h μ p U)‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_star]
  have h2 : (star (absS ψ U) * absS ψ (shift h μ p U)).re = ‖ψ U‖ * ‖ψ (shift h μ p U)‖ := by
    simp [absS, Complex.star_def, ← Complex.ofReal_mul]
  rw [h2]; exact h1

/-- `⟨ψ, (1−P) ψ⟩ = ⟨ψ,ψ⟩ − ⟨ψ, P ψ⟩`. -/
theorem ip_elec_eq (μ : δ) (p : ι) (ψ : State ι δ G) :
    ip ψ (elec μ p ψ) = ip ψ ψ - ip ψ (elecProj μ p ψ) := by
  unfold ip elec
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun U _ => by ring

theorem re_ip_elecTotal (ψ : State ι δ G) :
    (ip ψ (elecTotal ψ)).re
      = ∑ μ : δ, ∑ p : ι, (nsq ψ - (ip ψ (elecProj μ p ψ)).re) := by
  rw [ip_elecTotal, Complex.re_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ip_elec_eq, ip_self]; simp

theorem re_ip_mag {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) (ψ : State ι δ G) :
    (ip ψ (mag ρ τ R ψ)).re = ∑ U, pot ρ τ R U * ‖ψ U‖ ^ 2 := by
  unfold ip mag
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  have : star (ψ U) * ((pot ρ τ R U : ℂ) * ψ U) = ((pot ρ τ R U * ‖ψ U‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [this, Complex.ofReal_re]

/-- **The modulus does not raise the energy**: the Hamiltonian is stoquastic. -/
theorem ham_abs_le {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) {lE lB : ℝ} (hE : 0 ≤ lE) (ψ : State ι δ G) :
    (ip (absS ψ) (ham ρ τ R lE lB (absS ψ))).re ≤ (ip ψ (ham ρ τ R lE lB ψ)).re := by
  rw [ham_form, ham_form, re_ip_elecTotal, re_ip_elecTotal, re_ip_mag, re_ip_mag, nsq_absS]
  have hm : ∑ U, pot ρ τ R U * ‖absS ψ U‖ ^ 2 = ∑ U, pot ρ τ R U * ‖ψ U‖ ^ 2 := by
    simp [absS]
  rw [hm]
  have : ∑ μ : δ, ∑ p : ι, (nsq ψ - (ip (absS ψ) (elecProj μ p (absS ψ))).re)
      ≤ ∑ μ : δ, ∑ p : ι, (nsq ψ - (ip ψ (elecProj μ p ψ)).re) :=
    Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun p _ => by
      linarith [re_ip_proj_le μ p ψ]
  nlinarith [mul_le_mul_of_nonneg_left this hE]

/-! ## 2. Positivity of a nonnegative eigenvector -/

/-- **Connectedness**: a property closed under the translations of one link, true at one
configuration, is true at every configuration. -/
theorem reach {Z : Conf ι δ G → Prop}
    (hZ : ∀ (μ : δ) (p : ι) (k : G) (U : Conf ι δ G), Z U → Z (shift k μ p U))
    {U : Conf ι δ G} (h : Z U) (U' : Conf ι δ G) : Z U' := by
  have key : ∀ S : Finset (δ × ι), ∀ U : Conf ι δ G, Z U → ∀ U' : Conf ι δ G,
      (∀ μ p, (μ, p) ∉ S → U μ p = U' μ p) → Z U' := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro U hU U' h
      have : U = U' := funext fun μ => funext fun p => h μ p (by simp)
      rw [← this]; exact hU
    | insert e S heS ih =>
      intro U hU U' h
      set U'' := shift (U' e.1 e.2 * (U e.1 e.2)⁻¹) e.1 e.2 U with hU''
      have hZ'' : Z U'' := hZ e.1 e.2 _ U hU
      refine ih U'' hZ'' U' fun μ p hp => ?_
      by_cases hep : (μ, p) = e
      · have hμ : μ = e.1 := congrArg Prod.fst hep
        have hp2 : p = e.2 := congrArg Prod.snd hep
        rw [hμ, hp2]
        simp [hU'', shift]
      · have hn : (μ, p) ∉ insert e S := by
          simp only [Finset.mem_insert, not_or]; exact ⟨hep, hp⟩
        have : U'' μ p = U μ p := by
          have hne : ¬ (μ = e.1 ∧ p = e.2) := fun ⟨h1, h2⟩ => hep (by ext <;> simp [h1, h2])
          by_cases hμ : μ = e.1
          · have hp' : p ≠ e.2 := fun h' => hne ⟨hμ, h'⟩
            subst hμ; simp [hU'', shift, hp']
          · simp [hU'', shift, hμ]
        rw [this]; exact h μ p hn
  exact key Finset.univ U h U' fun μ p h => absurd (Finset.mem_univ _) h

/-- **A nonnegative eigenvector, not zero, is strictly positive.** -/
theorem pos_of_nonneg_eigen {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) {lE lB : ℝ} (hE : 0 < lE) {r : Conf ι δ G → ℝ}
    (hr : ∀ U, 0 ≤ r U) (hne : ∃ U, r U ≠ 0) {m0 : ℝ}
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ)) :
    ∀ U, 0 < r U := by
  have hcpos : (0 : ℝ) < (Fintype.card G : ℝ)⁻¹ := by
    have : 0 < Fintype.card G := Fintype.card_pos
    positivity
  -- the zeros of `r` are closed under the translations of one link
  have hclosed : ∀ (μ : δ) (p : ι) (k : G) (U : Conf ι δ G),
      r U = 0 → r (shift k μ p U) = 0 := by
    intro μ p k U hU
    have h := heig U
    simp only [ham, elecTotal, elec, elecProj, mag, hU, Complex.ofReal_zero, mul_zero,
      zero_sub, Finset.sum_neg_distrib, add_zero] at h
    have hS : ∑ μ' : δ, ∑ p' : ι, ∑ h : G, r (shift h μ' p' U) = 0 := by
      have h1 : ((∑ μ' : δ, ∑ p' : ι, ∑ h : G, r (shift h μ' p' U) : ℝ) : ℂ) = 0 := by
        have hc : (Fintype.card G : ℂ)⁻¹ ≠ 0 := by simp
        have hl : (lE : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
        simp only [← Finset.mul_sum] at h
        push_cast
        have : (lE : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
            ∑ μ' : δ, ∑ p' : ι, ∑ h : G, (r (shift h μ' p' U) : ℂ)) = 0 := by
          linear_combination (-1 : ℂ) * h
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hl
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' hc
          · exact h''
      exact_mod_cast h1
    have hnn : ∀ μ' p' h', 0 ≤ r (shift h' μ' p' U) := fun _ _ _ => hr _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun μ' _ =>
      Finset.sum_nonneg fun p' _ => Finset.sum_nonneg fun h' _ => hnn μ' p' h').mp hS μ
      (Finset.mem_univ μ)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun p' _ =>
      Finset.sum_nonneg fun h' _ => hnn μ p' h').mp h1 p (Finset.mem_univ p)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun h' _ => hnn μ p h').mp h2 k (Finset.mem_univ k)
  intro U
  rcases (hr U).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨U1, hU1⟩ := hne
    exact hU1 (reach (Z := fun V => r V = 0) hclosed h.symm U1)

/-! ## 3. A minimiser of the Rayleigh quotient is an eigenvector -/

section Spectral

variable {n : ℕ} {ρ : G →* Matrix.unitaryGroup (Fin n) ℂ} {τ : δ → ι ≃ ι}
  {R : Finset (ι × δ × δ)} {lE lB : ℝ} {m : ℕ}

theorem rayleigh_sum (hm : Module.finrank ℂ (EH ι δ G) = m) (x : EH ι δ G) :
    (inner ℂ x (HE ρ τ R lE lB x)).re
      = ∑ i, (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i
          * ‖inner ℂ ((HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE)
            (lB := lB)).eigenvectorBasis hm i) x‖ ^ 2 := by
  set hT := HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) with hTdef
  set b := hT.eigenvectorBasis hm with hb
  set μ := hT.eigenvalues hm with hμ
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

/-- **A minimiser of the Rayleigh quotient is an eigenvector.** -/
theorem eigen_of_minimiser (hm : Module.finrank ℂ (EH ι δ G) = m) {i0 : Fin m}
    (hmin : ∀ i, (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i0
      ≤ (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i)
    (x : EH ι δ G)
    (hx : (inner ℂ x (HE ρ τ R lE lB x)).re
      ≤ (HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i0
        * ‖x‖ ^ 2) :
    HE ρ τ R lE lB x
      = (((HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB)).eigenvalues hm i0
        : ℝ) : ℂ) • x := by
  set hT := HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) with hTdef
  set b := hT.eigenvectorBasis hm with hb
  set μ := hT.eigenvalues hm with hμ
  have hsum : ∑ i, ‖inner ℂ (b i) x‖ ^ 2 = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x
  have hrs := rayleigh_sum (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) hm x
  have hz : ∑ i, (μ i - μ i0) * ‖inner ℂ (b i) x‖ ^ 2 = 0 := by
    have e : ∑ i, (μ i - μ i0) * ‖inner ℂ (b i) x‖ ^ 2
        = (inner ℂ x (HE ρ τ R lE lB x)).re - μ i0 * ‖x‖ ^ 2 := by
      rw [hrs, ← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnn : 0 ≤ ∑ i, (μ i - μ i0) * ‖inner ℂ (b i) x‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hmin i)) (sq_nonneg _)
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_nonneg (sub_nonneg.mpr (hmin i)) (sq_nonneg _)).mp hz
  have hc : ∀ i, inner ℂ (b i) x * (μ i : ℂ) = inner ℂ (b i) x * (μ i0 : ℂ) := by
    intro i
    have := hterm i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · have : μ i = μ i0 := by linarith
      rw [this]
    · have : inner ℂ (b i) x = 0 := by simpa using h
      rw [this]; simp
  conv_lhs => rw [← b.sum_repr' x]
  rw [map_sum]
  conv_rhs => rw [← b.sum_repr' x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  have : HE ρ τ R lE lB (b i) = (μ i : ℂ) • b i := hT.apply_eigenvectorBasis hm i
  rw [this, smul_smul, smul_smul, hc i, mul_comm]

end Spectral

/-! ## 4. The positive ground state -/

/-- **The ground state is positive.** At finite volume and fixed spacing, for `λE > 0` and
`λB ≥ 0`: there are `m0 ∈ ℝ` and a function `r > 0` with `H r = m0 r`, and `m0` is the minimum of
the Rayleigh quotient, `m0 ⟨ψ,ψ⟩ ≤ Re ⟨ψ, H ψ⟩` for every state `ψ`. -/
theorem exists_positive_ground_state {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ)
    (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ)) {lE lB : ℝ} (hE : 0 < lE) (hB : 0 ≤ lB) :
    ∃ (m0 : ℝ) (r : Conf ι δ G → ℝ), (∀ U, 0 < r U) ∧
      (∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ)) ∧
      ∀ ψ : State ι δ G, m0 * nsq ψ ≤ (ip ψ (ham ρ τ R lE lB ψ)).re := by
  set m := Module.finrank ℂ (EH ι δ G) with hmdef
  have hm : Module.finrank ℂ (EH ι δ G) = m := rfl
  set hT := HE_isSymmetric (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) with hTdef
  set b := hT.eigenvectorBasis hm with hb
  set μ := hT.eigenvalues hm with hμ
  have hcard : 0 < Fintype.card (Conf ι δ G) := Fintype.card_pos_iff.mpr ⟨fun _ _ => 1⟩
  have hmpos : 0 < m := by
    rw [hmdef, finrank_euclideanSpace]; exact hcard
  haveI : Nonempty (Fin m) := ⟨⟨0, hmpos⟩⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ μ Finset.univ_nonempty
  have hmin : ∀ i, μ i0 ≤ μ i := fun i => hi0 i (Finset.mem_univ i)
  -- the Rayleigh quotient is bounded below by `μ i0`
  have hvar : ∀ ψ : State ι δ G, μ i0 * nsq ψ ≤ (ip ψ (ham ρ τ R lE lB ψ)).re := by
    intro ψ
    set x : EH ι δ G := WithLp.toLp 2 ψ with hx
    have hsum : ∑ i, ‖inner ℂ (b i) x‖ ^ 2 = ‖x‖ ^ 2 := b.sum_sq_norm_inner_right x
    have h1 := rayleigh_sum (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) hm x
    have h2 : (inner ℂ x (HE ρ τ R lE lB x)).re = (ip ψ (ham ρ τ R lE lB ψ)).re := by
      rw [re_inner_HE]
    have h3 : nsq ψ = ‖x‖ ^ 2 := by
      have := nsq_eq_norm_sq x; simpa [hx] using this
    rw [← h2, h3, h1, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
  -- the modulus of the lowest eigenvector
  set χ : EH ι δ G := b i0 with hχ
  have hχn : ‖χ‖ = 1 := b.orthonormal.1 i0
  have hHχ : HE ρ τ R lE lB χ = (μ i0 : ℂ) • χ := hT.apply_eigenvectorBasis hm i0
  set ψ0 : State ι δ G := WithLp.ofLp χ with hψ0
  set φ : State ι δ G := absS ψ0 with hφ
  have hnψ : nsq ψ0 = 1 := by rw [hψ0, nsq_eq_norm_sq, hχn]; norm_num
  have hnφ : nsq φ = 1 := by rw [hφ, nsq_absS, hnψ]
  have hRχ : (ip ψ0 (ham ρ τ R lE lB ψ0)).re = μ i0 := by
    rw [← re_inner_HE, hHχ, inner_smul_right, inner_self_eq_norm_sq_to_K, hχn]
    simp
  have hle : (ip φ (ham ρ τ R lE lB φ)).re ≤ μ i0 := by
    rw [← hRχ]; exact ham_abs_le ρ τ R hE.le ψ0
  set xφ : EH ι δ G := WithLp.toLp 2 φ with hxφ
  have hxφn : ‖xφ‖ ^ 2 = 1 := by rw [← nsq_eq_norm_sq]; simpa [hxφ] using hnφ
  have heigφ : HE ρ τ R lE lB xφ = (μ i0 : ℂ) • xφ := by
    refine eigen_of_minimiser (ρ := ρ) (τ := τ) (R := R) (lE := lE) (lB := lB) hm hmin xφ ?_
    rw [re_inner_HE, hxφn]
    simpa [hxφ] using hle
  have hpt : ∀ U, ham ρ τ R lE lB φ U = (μ i0 : ℂ) * φ U := by
    intro U
    have := congrArg (fun y : EH ι δ G => WithLp.ofLp y U) heigφ
    simpa [ofLp_HE, hxφ] using this
  set r : Conf ι δ G → ℝ := fun U => ‖ψ0 U‖ with hr
  have hrφ : (fun U => (r U : ℂ)) = φ := rfl
  have hr0 : ∀ U, 0 ≤ r U := fun U => norm_nonneg _
  have hne : ∃ U, r U ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∀ U, ‖ψ0 U‖ = 0 := hcon
    have : nsq ψ0 = 0 := by simp [nsq, hz]
    rw [hnψ] at this; norm_num at this
  refine ⟨μ i0, r, pos_of_nonneg_eigen ρ τ R (lB := lB) (m0 := μ i0) hE hr0 hne (fun U => ?_), fun U => ?_, ?_⟩
  · rw [hrφ]; exact hpt U
  · rw [hrφ]; exact hpt U
  · exact hvar

end KogutSusskindGround
