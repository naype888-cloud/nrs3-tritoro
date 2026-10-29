/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindGround

/-!
# Harnack inequality for the ground state, uniform in the volume

Let `r > 0` be the positive ground state of the Kogut-Susskind Hamiltonian,
`H r = m0 r` (`KogutSusskindGround`). Let `Δ` bound the number of plaquettes of `R` that contain a
given link. Then, for `κ = |G| · λB · 2n · Δ / λE < 1`, changing the variable of a single link
changes `r` by a factor of at most `1 / (1 − κ)`:

  `r (shift k e U) · (1 − κ) ≤ r U`.

The constant depends on `|G|`, `n`, `Δ` and `λB / λE`, and on nothing else: not on the number of
links, not on the number `|R|` of plaquettes. This is the first estimate that does not grow with
the volume.

The proof takes the maximum `ρ` of the ratio `r (shift k e U) / r U`, which exists because
everything is finite, subtracts the two eigenvalue equations at `U` and `shift k e U`, and uses
that the term of the link `e` itself is the same at both points and is at least `r U / |G|`.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindSpectrum KogutSusskindGround

namespace KogutSusskindHarnack

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. The potential is local -/

/-- The four links of the plaquette `q = (p, μ, ν)`. -/
def links (τ : δ → ι ≃ ι) (q : ι × δ × δ) : Finset (δ × ι) :=
  {(q.2.1, q.1), (q.2.2, τ q.2.1 q.1), (q.2.1, τ q.2.2 q.1), (q.2.2, q.1)}

theorem shift_apply_of_ne {e : δ × ι} {a : δ} {b : ι} (h : (a, b) ≠ e) (k : G)
    (U : Conf ι δ G) : shift k e.1 e.2 U a b = U a b := by
  by_cases ha : a = e.1
  · have hb : b ≠ e.2 := fun hb => h (by rw [ha, hb])
    simp [shift, ha, hb]
  · simp [shift, ha]

variable {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)

/-- The Wilson density of the plaquette `q` for the links `U`. -/
def dens (U : Conf ι δ G) (q : ι × δ × δ) : ℝ :=
  GaugeWilson.density (GaugeWilson.plaquette τ (fun μ p => ρ (U μ p)) q.2.1 q.2.2 q.1)

theorem pot_eq_sum (R : Finset (ι × δ × δ)) (U : Conf ι δ G) :
    pot ρ τ R U = ∑ q ∈ R, dens ρ τ U q := rfl

theorem dens_shift_eq {e : δ × ι} {q : ι × δ × δ} (hq : e ∉ links τ q) (k : G)
    (U : Conf ι δ G) : dens ρ τ (shift k e.1 e.2 U) q = dens ρ τ U q := by
  have h1 : (q.2.1, q.1) ≠ e := fun h => hq (by simp [links, h])
  have h2 : (q.2.2, τ q.2.1 q.1) ≠ e := fun h => hq (by simp [links, h])
  have h3 : (q.2.1, τ q.2.2 q.1) ≠ e := fun h => hq (by simp [links, h])
  have h4 : (q.2.2, q.1) ≠ e := fun h => hq (by simp [links, h])
  unfold dens GaugeWilson.plaquette
  simp only [shift_apply_of_ne h1, shift_apply_of_ne h2, shift_apply_of_ne h3,
    shift_apply_of_ne h4]

/-- **Locality of the potential**: changing one link changes the Wilson potential by at most
`2n` for each plaquette that contains that link. -/
theorem pot_sub_le (R : Finset (ι × δ × δ)) {Δ : ℕ}
    (hΔ : ∀ e : δ × ι, (R.filter fun q => e ∈ links τ q).card ≤ Δ)
    (e : δ × ι) (k : G) (U : Conf ι δ G) :
    pot ρ τ R U - pot ρ τ R (shift k e.1 e.2 U) ≤ 2 * n * Δ := by
  rw [pot_eq_sum, pot_eq_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not R (fun q => e ∈ links τ q)]
  have h0 : ∑ q ∈ R.filter (fun q => e ∉ links τ q),
      (dens ρ τ U q - dens ρ τ (shift k e.1 e.2 U) q) = 0 :=
    Finset.sum_eq_zero fun q hq => by
      rw [dens_shift_eq ρ τ (Finset.mem_filter.mp hq).2]; ring
  rw [h0, add_zero]
  calc ∑ q ∈ R.filter (fun q => e ∈ links τ q),
        (dens ρ τ U q - dens ρ τ (shift k e.1 e.2 U) q)
      ≤ ∑ _q ∈ R.filter (fun q => e ∈ links τ q), (2 * (n : ℝ)) :=
        Finset.sum_le_sum fun q _ => by
          have := GaugeWilson.density_le
            (GaugeWilson.plaquette τ (fun μ p => ρ (U μ p)) q.2.1 q.2.2 q.1)
          have h2 := GaugeWilson.density_nonneg
            (GaugeWilson.plaquette τ (fun μ p => ρ ((shift k e.1 e.2 U) μ p)) q.2.1 q.2.2 q.1)
          unfold dens; linarith
    _ = (R.filter fun q => e ∈ links τ q).card * (2 * (n : ℝ)) := by simp
    _ ≤ Δ * (2 * (n : ℝ)) := by
        have := hΔ e
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (by positivity)
    _ = 2 * n * Δ := by ring

/-! ## 2. The eigenvalue equation in real form -/

/-- The average of `r` over the translations of the link `e`. -/
def X (r : Conf ι δ G → ℝ) (e : δ × ι) (U : Conf ι δ G) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ h : G, r (shift h e.1 e.2 U)

theorem eigen_real (R : Finset (ι × δ × δ)) {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ}
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (U : Conf ι δ G) :
    lE * (∑ e : δ × ι, (r U - X r e U)) + lB * pot ρ τ R U * r U = m0 * r U := by
  have h := heig U
  have h' : ((lE * (∑ e : δ × ι, (r U - X r e U)) + lB * pot ρ τ R U * r U : ℝ) : ℂ)
      = ((m0 * r U : ℝ) : ℂ) := by
    rw [Fintype.sum_prod_type]
    simp only [ham, elecTotal, elec, elecProj, mag] at h
    push_cast [X]
    rw [← h]
    ring
  exact_mod_cast h'

/-! ## 3. Harnack -/

/-- The constant `κ = |G| · λB · 2n · Δ / λE`. -/
def kappa (n Δ : ℕ) (lE lB : ℝ) : ℝ := (Fintype.card G : ℝ) * lB * (2 * n * Δ) / lE

theorem sum_X_le {r : Conf ι δ G → ℝ} (hr : ∀ U, 0 < r U) {ρ0 : ℝ}
    (hρ : ∀ (U : Conf ι δ G) (e : δ × ι) (k : G), r (shift k e.1 e.2 U) ≤ ρ0 * r U)
    {e0 : δ × ι} {k : G} (U : Conf ι δ G) :
    ∑ e : δ × ι, X r e (shift k e0.1 e0.2 U)
      ≤ X r e0 U + ρ0 * (∑ e : δ × ι, X r e U - X r e0 U) := by
  have hc : (0 : ℝ) ≤ (Fintype.card G : ℝ)⁻¹ := by positivity
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0),
    ← Finset.add_sum_erase _ (fun e => X r e U) (Finset.mem_univ e0)]
  have h1 : X r e0 (shift k e0.1 e0.2 U) = X r e0 U := by
    unfold X
    congr 1
    simp only [shift_shift]
    exact Fintype.sum_equiv (Equiv.mulRight k) _ _ fun h => rfl
  have h2 : ∑ e ∈ Finset.univ.erase e0, X r e (shift k e0.1 e0.2 U)
      ≤ ρ0 * ∑ e ∈ Finset.univ.erase e0, X r e U := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    have hne : (e.1, e.2) ≠ (e0.1, e0.2) := by simpa using (Finset.mem_erase.mp he).1
    unfold X
    calc (Fintype.card G : ℝ)⁻¹ * ∑ h : G, r (shift h e.1 e.2 (shift k e0.1 e0.2 U))
        ≤ (Fintype.card G : ℝ)⁻¹ * ∑ h : G, ρ0 * r (shift h e.1 e.2 U) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => by
            rw [shift_comm hne]; exact hρ _ e0 k) hc
      _ = ρ0 * ((Fintype.card G : ℝ)⁻¹ * ∑ h : G, r (shift h e.1 e.2 U)) := by
          rw [← Finset.mul_sum]; ring
  rw [h1]
  linarith

/-- **Harnack inequality for the ground state, uniform in the volume.**

Let `r > 0` with `H r = m0 r`. If `Δ` bounds the number of plaquettes of `R` through any link and
`κ = |G| · λB · 2n · Δ / λE < 1`, then changing one link variable changes `r` by at most the
factor `1 / (1 − κ)`:
`r (shift k e U) · (1 − κ) ≤ r U`. -/
theorem harnack (R : Finset (ι × δ × δ)) {lE lB m0 : ℝ} (hE : 0 < lE) (hB : 0 ≤ lB)
    {r : Conf ι δ G → ℝ} (hr : ∀ U, 0 < r U)
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    {Δ : ℕ} (hΔ : ∀ e : δ × ι, (R.filter fun q => e ∈ links τ q).card ≤ Δ)
    (hκ : kappa (G := G) n Δ lE lB < 1) (U : Conf ι δ G) (e : δ × ι) (k : G) :
    r (shift k e.1 e.2 U) * (1 - kappa (G := G) n Δ lE lB) ≤ r U := by
  haveI : Nonempty (δ × ι) := ⟨e⟩
  set κ := kappa (G := G) n Δ lE lB with hκdef
  have hκ0 : 0 ≤ κ :=
    show 0 ≤ (Fintype.card G : ℝ) * lB * (2 * n * Δ) / lE by positivity
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  -- the maximum of the one-link ratios
  set f : Conf ι δ G × (δ × ι) × G → ℝ :=
    fun t => r (shift t.2.2 t.2.1.1 t.2.1.2 t.1) / r t.1 with hf
  haveI : Nonempty (Conf ι δ G × (δ × ι) × G) := ⟨(fun _ _ => 1, e, 1)⟩
  obtain ⟨t0, -, ht0⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  set ρ0 := f t0 with hρ0
  have hρ : ∀ (U : Conf ι δ G) (e : δ × ι) (k : G), r (shift k e.1 e.2 U) ≤ ρ0 * r U := by
    intro U e k
    have := ht0 (U, e, k) (Finset.mem_univ _)
    simp only [hf] at this
    rw [div_le_iff₀ (hr U)] at this
    exact this
  have hbound : ρ0 * (1 - κ) ≤ 1 := by
    by_cases h1 : ρ0 ≤ 1
    · have := mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ 1 - κ)
      linarith
    · push_neg at h1
      obtain ⟨U0, e0, k0⟩ := t0
      have hρ0' : r (shift k0 e0.1 e0.2 U0) = ρ0 * r U0 := by
        simp only [hρ0, hf]; field_simp [(hr U0).ne']
      set U' := shift k0 e0.1 e0.2 U0 with hU'
      set rU := r U0 with hrU
      have hrU : 0 < rU := hr U0
      -- the two eigenvalue equations
      have E1 := eigen_real ρ τ R heig U0
      have E2 := eigen_real ρ τ R heig U'
      have hsum : ∀ V : Conf ι δ G, ∑ e : δ × ι, (r V - X r e V)
          = (Fintype.card (δ × ι) : ℝ) * r V - ∑ e : δ × ι, X r e V := by
        intro V; simp [Finset.sum_sub_distrib]
      rw [hsum] at E1 E2
      rw [hρ0'] at E2
      have hs' := sum_X_le hr hρ (e0 := e0) (k := k0) U0
      have hx0 : X r e0 U' = X r e0 U0 := by
        unfold X
        congr 1
        simp only [hU', shift_shift]
        exact Fintype.sum_equiv (Equiv.mulRight k0) _ _ fun h => rfl
      have hX : rU / Fintype.card G ≤ X r e0 U0 := by
        unfold X
        have : r (shift 1 e0.1 e0.2 U0) ≤ ∑ h : G, r (shift h e0.1 e0.2 U0) :=
          Finset.single_le_sum (f := fun h => r (shift h e0.1 e0.2 U0))
            (fun h _ => (hr _).le) (Finset.mem_univ 1)
        rw [shift_one] at this
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have hP := pot_sub_le ρ τ R hΔ e0 k0 U0
      set S := ∑ e : δ × ι, X r e U0 with hS
      set S' := ∑ e : δ × ι, X r e U' with hS'
      set x := X r e0 U0 with hx
      set L : ℝ := (Fintype.card (δ × ι) : ℝ) with hL
      have A := mul_le_mul_of_nonneg_left hs' hE.le
      have C : ρ0 * (lE * (L * rU - S) + lB * pot ρ τ R U0 * rU) = ρ0 * (m0 * rU) := by
        rw [E1]
      have key : lE * x * (ρ0 - 1) ≤ ρ0 * lB * rU * (pot ρ τ R U0 - pot ρ τ R U') := by
        nlinarith [A, E2, C]
      have h1' : lE * (rU / Fintype.card G) * (ρ0 - 1) ≤ lE * x * (ρ0 - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hE.le) (by linarith)
      have h2' : ρ0 * lB * rU * (pot ρ τ R U0 - pot ρ τ R U')
          ≤ ρ0 * lB * rU * (2 * n * Δ) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      have h3 := h1'.trans (key.trans h2')
      have h4 : lE * (ρ0 - 1) ≤ Fintype.card G * (ρ0 * lB * (2 * n * Δ)) := by
        have hpos : 0 < rU / Fintype.card G := by positivity
        have e1 : (rU / Fintype.card G) * (Fintype.card G * (ρ0 * lB * (2 * n * Δ)))
            = ρ0 * lB * rU * (2 * n * Δ) := by field_simp
        refine le_of_mul_le_mul_left ?_ hpos
        nlinarith [h3, e1]
      have h5 : ρ0 - 1 ≤ ρ0 * κ := by
        have : κ = Fintype.card G * lB * (2 * n * Δ) / lE := rfl
        rw [this]
        rw [← mul_div_assoc, le_div_iff₀ hE]
        nlinarith [h4]
      nlinarith
  calc r (shift k e.1 e.2 U) * (1 - κ) ≤ (ρ0 * r U) * (1 - κ) :=
        mul_le_mul_of_nonneg_right (hρ U e k) (by linarith)
    _ = (ρ0 * (1 - κ)) * r U := by ring
    _ ≤ 1 * r U := mul_le_mul_of_nonneg_right hbound (hr U).le
    _ = r U := one_mul _

end KogutSusskindHarnack
