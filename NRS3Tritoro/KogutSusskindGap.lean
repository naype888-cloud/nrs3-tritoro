/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskind

/-!
# Strong-coupling gap of the Kogut-Susskind Hamiltonian at finite volume

Efron-Stein for the electric term: on the states with zero sum (orthogonal to the constants,
the vacuum of `λB = 0`), `⟨ψ, E ψ⟩ ≥ ⟨ψ, ψ⟩` with `E = Σ_links (1 − P)`. It follows from
`‖ψ − P_a P_b ψ‖² ≤ ‖ψ − P_a ψ‖² + ‖ψ − P_b ψ‖²`, which needs only that `P` is a symmetric
idempotent, and from the fact that the product of all the `P` is the projector onto constants.

## Main results

- `KogutSusskindGap.gap_elec` : if `Σ_U ψ U = 0` then `⟨ψ,ψ⟩ ≤ Re ⟨ψ, E ψ⟩`.
- `KogutSusskindGap.gap_ham` : if `Σ_U ψ U = 0` then `λE ⟨ψ,ψ⟩ ≤ Re ⟨ψ, H ψ⟩`.
- `KogutSusskindGap.vacuum_energy_le` : `Re ⟨1, H 1⟩ ≤ λB · 2n · |R| · ⟨1,1⟩`.

By min-max, these two inequalities give a gap of at least `λE − λB · 2n · |R|` above the lowest
eigenvalue; the min-max step itself is not formalised here. The bound on the vacuum energy grows
with the number `|R|` of plaquettes, so nothing here is uniform in the volume.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind

namespace KogutSusskindGap

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. Invariance under the translations of the links -/

/-- Translations of different links commute. -/
theorem shift_comm {μ ν : δ} {p q : ι} (hne : (μ, p) ≠ (ν, q)) (h k : G) (U : Conf ι δ G) :
    shift h μ p (shift k ν q U) = shift k ν q (shift h μ p U) := by
  funext a b
  by_cases ha : a = μ
  · subst ha
    by_cases hb : b = p
    · subst hb
      have hn : ¬ (a = ν ∧ b = q) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
      by_cases h1 : a = ν
      · have h2 : b ≠ q := fun h2 => hn ⟨h1, h2⟩
        subst h1; simp [shift, h2]
      · simp [shift, h1]
    · by_cases h1 : a = ν
      · subst h1
        by_cases h2 : b = q
        · subst h2; simp [shift, hb]
        · simp [shift, hb, h2]
      · simp [shift, hb, h1]
  · by_cases h1 : a = ν
    · subst h1
      by_cases h2 : b = q
      · subst h2; simp [shift, ha]
      · simp [shift, ha, h2]
    · simp [shift, ha, h1]

/-- A state is invariant under the translations of the link `e`. -/
def Inv (e : δ × ι) (χ : State ι δ G) : Prop := ∀ (k : G) (U : Conf ι δ G), χ (shift k e.1 e.2 U) = χ U

/-- The projector of a link makes the state invariant under that link. -/
theorem inv_elecProj (e : δ × ι) (χ : State ι δ G) : Inv e (elecProj e.1 e.2 χ) := by
  intro k U
  unfold elecProj
  congr 1
  simp only [shift_shift]
  exact Fintype.sum_equiv (Equiv.mulRight k) _ _ fun h => rfl

/-- The projector of another link keeps the invariance. -/
theorem inv_elecProj_of_ne {e e' : δ × ι} (hne : e ≠ e') {χ : State ι δ G} (hχ : Inv e χ) :
    Inv e (elecProj e'.1 e'.2 χ) := by
  intro k U
  unfold elecProj
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  have hne' : (e'.1, e'.2) ≠ (e.1, e.2) := by simpa using Ne.symm hne
  rw [shift_comm hne']
  exact hχ k _

/-- A function invariant under the translations of every link is constant. -/
theorem const_of_inv {f : State ι δ G} (hf : ∀ e : δ × ι, Inv e f) (U U' : Conf ι δ G) :
    f U = f U' := by
  have key : ∀ S : Finset (δ × ι), ∀ U U' : Conf ι δ G,
      (∀ μ p, (μ, p) ∉ S → U μ p = U' μ p) → f U = f U' := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro U U' h
      have : U = U' := funext fun μ => funext fun p => h μ p (by simp)
      rw [this]
    | insert e S heS ih =>
      intro U U' h
      set U'' := shift (U' e.1 e.2 * (U e.1 e.2)⁻¹) e.1 e.2 U with hU''
      have h1 : f U'' = f U := hf e _ U
      have h2 : f U'' = f U' := by
        refine ih U'' U' fun μ p hp => ?_
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
      rw [← h1, h2]
  exact key Finset.univ U U' fun μ p h => absurd (Finset.mem_univ _) h

/-! ## 2. Efron-Stein -/

/-- The product of the projectors of the links in a list. -/
def projList : List (δ × ι) → State ι δ G → State ι δ G
  | [], ψ => ψ
  | e :: L, ψ => elecProj e.1 e.2 (projList L ψ)

theorem inv_projList (L : List (δ × ι)) (ψ : State ι δ G) :
    ∀ e ∈ L, Inv e (projList L ψ) := by
  induction L with
  | nil => intro e he; simp at he
  | cons e0 L ih =>
    intro e he
    by_cases h : e = e0
    · subst h; exact inv_elecProj e _
    · exact inv_elecProj_of_ne h (ih e (by simpa [h] using he))

/-- The squared norm. -/
def nsq (ψ : State ι δ G) : ℝ := ∑ U, ‖ψ U‖ ^ 2

theorem ip_self (ψ : State ι δ G) : ip ψ ψ = (nsq ψ : ℂ) := by
  unfold ip nsq
  push_cast
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem nsq_nonneg (ψ : State ι δ G) : 0 ≤ nsq ψ := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem nsq_add (u w : State ι δ G) :
    nsq (fun U => u U + w U) = nsq u + nsq w + 2 * (ip u w).re := by
  unfold nsq ip
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun U _ => ?_
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem elecProj_sub (μ : δ) (p : ι) (a b : State ι δ G) :
    elecProj μ p (fun U => a U - b U) = fun U => elecProj μ p a U - elecProj μ p b U := by
  funext U
  unfold elecProj
  rw [← mul_sub, ← Finset.sum_sub_distrib]

theorem elec_elecProj (μ : δ) (p : ι) (v : State ι δ G) : elec μ p (elecProj μ p v) = 0 := by
  funext U
  have := congrFun (elecProj_idem μ p v) U
  simp [elec, this]

theorem cross_zero (μ : δ) (p : ι) (χ v : State ι δ G) :
    ip (elec μ p χ) (elecProj μ p v) = 0 := by
  rw [← ip_elec_symm, elec_elecProj]
  unfold ip; simp

/-- The projector does not increase the norm. -/
theorem nsq_proj_le (μ : δ) (p : ι) (v : State ι δ G) : nsq (elecProj μ p v) ≤ nsq v := by
  have h : v = fun U => elec μ p v U + elecProj μ p v U := by funext U; simp [elec]
  have h2 := nsq_add (elec μ p v) (elecProj μ p v)
  rw [cross_zero] at h2
  simp only [Complex.zero_re, mul_zero, add_zero] at h2
  have h3 : nsq v = nsq (elec μ p v) + nsq (elecProj μ p v) := by rw [← h2]; congr 1
  linarith [nsq_nonneg (elec μ p v)]

/-- **One step of Efron-Stein**. -/
theorem es_step (μ : δ) (p : ι) (χ b : State ι δ G) :
    nsq (fun U => χ U - elecProj μ p b U)
      ≤ nsq (elec μ p χ) + nsq (fun U => χ U - b U) := by
  have h : (fun U => χ U - elecProj μ p b U)
      = fun U => elec μ p χ U + elecProj μ p (fun U => χ U - b U) U := by
    funext U
    have := congrFun (elecProj_sub μ p χ b) U
    simp only [elec]
    rw [this]; ring
  rw [h, nsq_add, cross_zero]
  simp only [Complex.zero_re, mul_zero, add_zero]
  linarith [nsq_proj_le μ p (fun U => χ U - b U)]

/-- **Efron-Stein**: the distance to the product of the projectors is at most the sum of the
electric terms. -/
theorem es_list (L : List (δ × ι)) (ψ : State ι δ G) :
    nsq (fun U => ψ U - projList L ψ U) ≤ (L.map fun e => nsq (elec e.1 e.2 ψ)).sum := by
  induction L with
  | nil => simp [projList, nsq]
  | cons e L ih =>
    have := es_step e.1 e.2 ψ (projList L ψ)
    simp only [projList, List.map_cons, List.sum_cons]
    linarith

/-! ## 3. The gap of the electric term -/

theorem nsq_elec_eq (μ : δ) (p : ι) (ψ : State ι δ G) :
    nsq (elec μ p ψ) = (ip ψ (elec μ p ψ)).re := by
  rw [ip_elec_self, ip_self]; simp

theorem elecTotal_form (ψ : State ι δ G) :
    (ip ψ (elecTotal ψ)).re = ∑ e : δ × ι, nsq (elec e.1 e.2 ψ) := by
  rw [ip_elecTotal, Complex.re_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun p _ => (nsq_elec_eq μ p ψ).symm

/-- **Gap of the electric term**: on the states with zero sum, `⟨ψ,ψ⟩ ≤ Re ⟨ψ, E ψ⟩`. -/
theorem gap_elec (ψ : State ι δ G) (h0 : ∑ U, ψ U = 0) :
    nsq ψ ≤ (ip ψ (elecTotal ψ)).re := by
  set L : List (δ × ι) := (Finset.univ : Finset (δ × ι)).toList with hL
  have hinv : ∀ e : δ × ι, Inv e (projList L ψ) := fun e =>
    inv_projList L ψ e (Finset.mem_toList.mpr (Finset.mem_univ e))
  have U0 : Conf ι δ G := fun _ _ => 1
  set c : ℂ := projList L ψ U0 with hc
  have hconst : ∀ U, projList L ψ U = c := fun U => const_of_inv hinv U U0
  have hES := es_list L ψ
  have hsum : (L.map fun e => nsq (elec e.1 e.2 ψ)).sum = ∑ e : δ × ι, nsq (elec e.1 e.2 ψ) :=
    Finset.sum_map_toList _ _
  have hdist : nsq ψ ≤ nsq (fun U => ψ U - projList L ψ U) := by
    unfold nsq
    have hterm : ∀ U, ‖ψ U - projList L ψ U‖ ^ 2
        = ‖ψ U‖ ^ 2 + ‖c‖ ^ 2 - 2 * (ψ U * (starRingEnd ℂ) c).re := by
      intro U
      rw [hconst U]
      simp only [Complex.sq_norm, Complex.normSq_sub]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.re_sum,
      ← Finset.sum_mul, h0]
    simp only [zero_mul, Complex.zero_re, mul_zero, sub_zero]
    have : 0 ≤ ∑ _U : Conf ι δ G, ‖c‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  rw [elecTotal_form]
  linarith

/-! ## 4. The Hamiltonian -/

theorem ham_form {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) (lE lB : ℝ) (ψ : State ι δ G) :
    (ip ψ (ham ρ τ R lE lB ψ)).re
      = lE * (ip ψ (elecTotal ψ)).re + lB * (ip ψ (mag ρ τ R ψ)).re := by
  have e : ip ψ (ham ρ τ R lE lB ψ)
      = (lE : ℂ) * ip ψ (elecTotal ψ) + (lB : ℂ) * ip ψ (mag ρ τ R ψ) := by
    unfold ip ham
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun U _ => by ring
  rw [e]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

/-- **Strong-coupling gap above the constants**: on the states with zero sum,
`λE ⟨ψ,ψ⟩ ≤ Re ⟨ψ, H ψ⟩`, for `λE, λB ≥ 0`. -/
theorem gap_ham {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) {lE lB : ℝ} (hE : 0 ≤ lE) (hB : 0 ≤ lB) (ψ : State ι δ G)
    (h0 : ∑ U, ψ U = 0) : lE * nsq ψ ≤ (ip ψ (ham ρ τ R lE lB ψ)).re := by
  rw [ham_form]
  have := gap_elec ψ h0
  have := mag_nonneg ρ τ R ψ
  nlinarith [mul_nonneg hB this, mul_le_mul_of_nonneg_left (gap_elec ψ h0) hE]

end KogutSusskindGap

namespace GaugeWilson

/-- The Wilson density of a unitary plaquette is at most `2n`. -/
theorem density_le {n : ℕ} (P : Matrix.unitaryGroup (Fin n) ℂ) : density P ≤ 2 * n := by
  have : -(n : ℝ) ≤ (Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ)).re := by
    have hre : (Matrix.trace (P : Matrix (Fin n) (Fin n) ℂ)).re
        = ∑ i, ((P : Matrix (Fin n) (Fin n) ℂ) i i).re := by
      simp [Matrix.trace, Complex.re_sum]
    rw [hre]
    calc -(n : ℝ) = ∑ _i : Fin n, (-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
        have h1 := Complex.abs_re_le_norm ((P : Matrix (Fin n) (Fin n) ℂ) i i)
        have h2 := norm_diag_le P i
        linarith [neg_abs_le ((P : Matrix (Fin n) (Fin n) ℂ) i i).re]
  unfold density; linarith

end GaugeWilson

namespace KogutSusskindGap

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-- The constant state. -/
def one : State ι δ G := fun _ => 1

theorem elec_one (μ : δ) (p : ι) : elec μ p (one : State ι δ G) = 0 := by
  funext U
  have hc : (Fintype.card G : ℂ) ≠ 0 := by simp
  simp [elec, elecProj, one, hc]

theorem elecTotal_one : elecTotal (one : State ι δ G) = 0 := by
  funext U
  simp [elecTotal, elec_one]

/-- **The vacuum energy is bounded by the number of plaquettes**: this bound is extensive
(it grows with `|R|`), so it is not uniform in the volume. -/
theorem vacuum_energy_le {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
    (R : Finset (ι × δ × δ)) {lE lB : ℝ} (hB : 0 ≤ lB) :
    (ip (one : State ι δ G) (ham ρ τ R lE lB one)).re
      ≤ lB * (2 * n * R.card) * nsq (one : State ι δ G) := by
  rw [ham_form, elecTotal_one]
  have hz : (ip (one : State ι δ G) (0 : State ι δ G)).re = 0 := by simp [ip]
  rw [hz, mul_zero, zero_add]
  have hpot : ∀ U, pot ρ τ R U ≤ 2 * n * R.card := by
    intro U
    unfold pot GaugeWilson.action
    calc _ ≤ ∑ _r ∈ R, (2 * (n : ℝ)) :=
          Finset.sum_le_sum fun r _ => GaugeWilson.density_le _
      _ = _ := by simp; ring
  have : (ip (one : State ι δ G) (mag ρ τ R one)).re ≤ (2 * n * R.card) * nsq (one : State ι δ G) := by
    unfold ip mag nsq one
    rw [Complex.re_sum]
    calc _ ≤ ∑ _U : Conf ι δ G, (2 * (n : ℝ) * R.card) :=
          Finset.sum_le_sum fun U _ => by simpa using hpot U
      _ = _ := by simp; ring
  nlinarith

end KogutSusskindGap
