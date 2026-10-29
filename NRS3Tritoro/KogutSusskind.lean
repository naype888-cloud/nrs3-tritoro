/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.GaugeWilson
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# Kogut-Susskind Hamiltonian for a finite gauge group on a finite lattice

The states are the functions of the link configurations `U : δ → ι → G` with `G` a finite group
and `ι`, `δ` finite, with the inner product `⟨φ, ψ⟩ = ∑_U conj (φ U) ψ U` (the counting measure
of `G`, i.e. its normalised Haar measure up to a constant). The spacing is fixed; nothing is sent
to the continuum.

The electric term of a link `(μ, p)` is `1 − P_{μ,p}`, with `P_{μ,p}` the average over `G` of the
left translations of that link: the projector onto the states that do not depend on the
orientation of the link variable. It is the finite-group form of the Casimir `E²` of the link.

## Main results

- `KogutSusskind.elecProj_hermitian` : `⟨φ, P ψ⟩ = ⟨P φ, ψ⟩`.
- `KogutSusskind.elecProj_idem` : `P (P ψ) = P ψ`.
- `KogutSusskind.elec_nonneg` : `⟨ψ, (1 − P) ψ⟩ ≥ 0`, as a real number.
- `KogutSusskind.ham` : `H = λE · Σ_links (1 − P) + λB · (Wilson potential)`.
- `KogutSusskind.ham_symm`, `KogutSusskind.ham_nonneg` : `H` is symmetric and `⟨ψ, Hψ⟩ ≥ 0`
  for `λE, λB ≥ 0`.
- `KogutSusskind.ham_gauge` : **Gauss law**, `H` commutes with every gauge transformation.

No gap is claimed here: no lower bound on the first excitation, and nothing uniform in the volume.
-/

@[expose] public noncomputable section

open Complex Finset

namespace KogutSusskind

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-- The link configurations. -/
abbrev Conf (ι δ G : Type*) := δ → ι → G

/-- The states. -/
abbrev State (ι δ G : Type*) := Conf ι δ G → ℂ

/-- Left translation of the single link `(μ, p)` by `h`. -/
def shift (h : G) (μ : δ) (p : ι) (U : Conf ι δ G) : Conf ι δ G :=
  Function.update U μ (Function.update (U μ) p (h * U μ p))

theorem shift_shift (k h : G) (μ : δ) (p : ι) (U : Conf ι δ G) :
    shift k μ p (shift h μ p U) = shift (k * h) μ p U := by
  funext ν q
  by_cases hν : ν = μ
  · subst hν
    by_cases hq : q = p
    · subst hq; simp [shift, mul_assoc]
    · simp [shift, hq]
  · simp [shift, hν]

theorem shift_one (μ : δ) (p : ι) (U : Conf ι δ G) : shift 1 μ p U = U := by
  funext ν q
  by_cases hν : ν = μ
  · subst hν
    by_cases hq : q = p
    · subst hq; simp [shift]
    · simp [shift, hq]
  · simp [shift, hν]

/-- Left translation of the link `(μ, p)` as a bijection of the configurations. -/
def shiftEquiv (h : G) (μ : δ) (p : ι) : Conf ι δ G ≃ Conf ι δ G where
  toFun := shift h μ p
  invFun := shift h⁻¹ μ p
  left_inv U := by rw [shift_shift, inv_mul_cancel, shift_one]
  right_inv U := by rw [shift_shift, mul_inv_cancel, shift_one]

/-- The inner product of the states. -/
def ip (φ ψ : State ι δ G) : ℂ := ∑ U, star (φ U) * ψ U

/-- The projector of the link `(μ, p)`: the average of the translations over `G`. -/
def elecProj (μ : δ) (p : ι) (ψ : State ι δ G) : State ι δ G :=
  fun U => (Fintype.card G : ℂ)⁻¹ * ∑ h : G, ψ (shift h μ p U)

/-- The electric term of the link `(μ, p)`: `1 − P`. -/
def elec (μ : δ) (p : ι) (ψ : State ι δ G) : State ι δ G :=
  fun U => ψ U - elecProj μ p ψ U

/-- One translation moved from one side of the inner product to the other. -/
theorem sum_shift (μ : δ) (p : ι) (φ ψ : State ι δ G) (h : G) :
    ∑ U, star (φ U) * ψ (shift h μ p U) = ∑ V, star (φ (shift h⁻¹ μ p V)) * ψ V := by
  rw [← Equiv.sum_comp (shiftEquiv h μ p) (fun V => star (φ (shift h⁻¹ μ p V)) * ψ V)]
  refine Finset.sum_congr rfl fun U _ => ?_
  simp [shiftEquiv, shift_shift, shift_one]

/-- The projector is symmetric for the inner product. -/
theorem elecProj_hermitian (μ : δ) (p : ι) (φ ψ : State ι δ G) :
    ip φ (elecProj μ p ψ) = ip (elecProj μ p φ) ψ := by
  unfold ip elecProj
  have hs : star ((Fintype.card G : ℂ)⁻¹) = (Fintype.card G : ℂ)⁻¹ := by simp
  have L : ∑ U, star (φ U) * ((Fintype.card G : ℂ)⁻¹ * ∑ h : G, ψ (shift h μ p U))
      = (Fintype.card G : ℂ)⁻¹ * ∑ h : G, ∑ V, star (φ (shift h⁻¹ μ p V)) * ψ V := by
    calc _ = ∑ U, (Fintype.card G : ℂ)⁻¹ * ∑ h : G, star (φ U) * ψ (shift h μ p U) := by
            refine Finset.sum_congr rfl fun U _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun h _ => by ring
      _ = (Fintype.card G : ℂ)⁻¹ * ∑ h : G, ∑ U, star (φ U) * ψ (shift h μ p U) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
      _ = _ := by simp only [sum_shift]
  have R : ∑ U, star ((Fintype.card G : ℂ)⁻¹ * ∑ h : G, φ (shift h μ p U)) * ψ U
      = (Fintype.card G : ℂ)⁻¹ * ∑ h : G, ∑ V, star (φ (shift h μ p V)) * ψ V := by
    simp only [star_mul', hs, star_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun V _ => ?_
    ring
  rw [L, R]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun h => rfl

/-- The projector is idempotent. -/
theorem elecProj_idem (μ : δ) (p : ι) (ψ : State ι δ G) :
    elecProj μ p (elecProj μ p ψ) = elecProj μ p ψ := by
  funext U
  have hc : (Fintype.card G : ℂ) ≠ 0 := by simp
  unfold elecProj
  have step : ∀ k : G, ∑ h : G, ψ (shift h μ p (shift k μ p U)) = ∑ h : G, ψ (shift h μ p U) := by
    intro k
    simp only [shift_shift]
    exact Fintype.sum_equiv (Equiv.mulRight k) _ _ fun h => rfl
  simp only [← Finset.mul_sum, step, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- `(1 − P)` squares to itself on the inner product: `⟨ψ, (1−P) ψ⟩ = ⟨(1−P) ψ, (1−P) ψ⟩`. -/
theorem ip_elec_self (μ : δ) (p : ι) (ψ : State ι δ G) :
    ip ψ (elec μ p ψ) = ip (elec μ p ψ) (elec μ p ψ) := by
  have h1 : ip (elecProj μ p ψ) ψ = ip ψ (elecProj μ p ψ) := (elecProj_hermitian μ p ψ ψ).symm
  have h2 : ip (elecProj μ p ψ) (elecProj μ p ψ) = ip ψ (elecProj μ p ψ) := by
    rw [← elecProj_hermitian, elecProj_idem]
  have e1 : ip ψ (elec μ p ψ) = ip ψ ψ - ip ψ (elecProj μ p ψ) := by
    unfold ip elec; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun U _ => by ring
  have e2 : ip (elec μ p ψ) (elec μ p ψ)
      = ip ψ ψ - ip ψ (elecProj μ p ψ) - ip (elecProj μ p ψ) ψ
        + ip (elecProj μ p ψ) (elecProj μ p ψ) := by
    unfold ip elec
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun U _ => by simp only [star_sub]; ring
  rw [e1, e2, h1, h2]; ring

/-- **The electric term is nonnegative**: `⟨ψ, (1 − P) ψ⟩ = ∑ |((1−P) ψ) U|² ≥ 0`. -/
theorem elec_nonneg (μ : δ) (p : ι) (ψ : State ι δ G) :
    0 ≤ (ip ψ (elec μ p ψ)).re := by
  rw [ip_elec_self]
  unfold ip
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun U _ => ?_
  rw [show star (elec μ p ψ U) * elec μ p ψ U = ((‖elec μ p ψ U‖ ^ 2 : ℝ) : ℂ) by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl]
  simp only [Complex.ofReal_re]
  positivity

/-! ## 2. The Hamiltonian -/

/-- The electric term summed over all links. -/
def elecTotal (ψ : State ι δ G) : State ι δ G :=
  fun U => ∑ μ : δ, ∑ p : ι, elec μ p ψ U

theorem ip_elec_symm (μ : δ) (p : ι) (φ ψ : State ι δ G) :
    ip φ (elec μ p ψ) = ip (elec μ p φ) ψ := by
  have h := elecProj_hermitian μ p φ ψ
  unfold ip elec at *
  have e1 : ∑ U, star (φ U) * (ψ U - elecProj μ p ψ U)
      = ∑ U, star (φ U) * ψ U - ∑ U, star (φ U) * elecProj μ p ψ U := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun U _ => by ring
  have e2 : ∑ U, star (φ U - elecProj μ p φ U) * ψ U
      = ∑ U, star (φ U) * ψ U - ∑ U, star (elecProj μ p φ U) * ψ U := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun U _ => by simp only [star_sub]; ring
  rw [e1, e2, h]

theorem ip_elecTotal (φ ψ : State ι δ G) :
    ip φ (elecTotal ψ) = ∑ μ : δ, ∑ p : ι, ip φ (elec μ p ψ) := by
  unfold ip elecTotal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]

theorem ip_elecTotal_symm (φ ψ : State ι δ G) :
    ip φ (elecTotal ψ) = ip (elecTotal φ) ψ := by
  have hr : ip (elecTotal φ) ψ = ∑ μ : δ, ∑ p : ι, ip (elec μ p φ) ψ := by
    unfold ip elecTotal
    simp only [star_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
  rw [ip_elecTotal, hr]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun p _ => ip_elec_symm μ p φ ψ

theorem elecTotal_nonneg (ψ : State ι δ G) : 0 ≤ (ip ψ (elecTotal ψ)).re := by
  rw [ip_elecTotal, Complex.re_sum]
  refine Finset.sum_nonneg fun μ _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun p _ => elec_nonneg μ p ψ

section Magnetic

variable {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))

/-- The Wilson potential of a configuration: the Wilson action of the links `ρ ∘ U`. -/
def pot (U : Conf ι δ G) : ℝ := GaugeWilson.action τ R (fun μ p => ρ (U μ p))

theorem pot_nonneg (U : Conf ι δ G) : 0 ≤ pot ρ τ R U := GaugeWilson.action_nonneg τ R _

/-- The magnetic term: multiplication by the Wilson potential. -/
def mag (ψ : State ι δ G) : State ι δ G := fun U => (pot ρ τ R U : ℂ) * ψ U

/-- **The Kogut-Susskind Hamiltonian** at fixed spacing: `λE · (electric) + λB · (magnetic)`. -/
def ham (lE lB : ℝ) (ψ : State ι δ G) : State ι δ G :=
  fun U => (lE : ℂ) * elecTotal ψ U + (lB : ℂ) * mag ρ τ R ψ U

theorem ip_mag_symm (φ ψ : State ι δ G) : ip φ (mag ρ τ R ψ) = ip (mag ρ τ R φ) ψ := by
  unfold ip mag
  refine Finset.sum_congr rfl fun U _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

theorem mag_nonneg (ψ : State ι δ G) : 0 ≤ (ip ψ (mag ρ τ R ψ)).re := by
  unfold ip mag
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun U _ => ?_
  have : star (ψ U) * ((pot ρ τ R U : ℂ) * ψ U) = ((pot ρ τ R U * ‖ψ U‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [this, Complex.ofReal_re]
  exact mul_nonneg (pot_nonneg ρ τ R U) (sq_nonneg _)

/-- **The Hamiltonian is symmetric.** -/
theorem ham_symm (lE lB : ℝ) (φ ψ : State ι δ G) :
    ip φ (ham ρ τ R lE lB ψ) = ip (ham ρ τ R lE lB φ) ψ := by
  have e : ∀ (a b : State ι δ G) (x y : ℝ),
      ip a (fun U => (x : ℂ) * elecTotal b U + (y : ℂ) * mag ρ τ R b U)
        = (x : ℂ) * ip a (elecTotal b) + (y : ℂ) * ip a (mag ρ τ R b) := by
    intro a b x y
    unfold ip
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun U _ => by ring
  have e' : ∀ (a b : State ι δ G) (x y : ℝ),
      ip (fun U => (x : ℂ) * elecTotal a U + (y : ℂ) * mag ρ τ R a U) b
        = (x : ℂ) * ip (elecTotal a) b + (y : ℂ) * ip (mag ρ τ R a) b := by
    intro a b x y
    unfold ip
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun U _ => by
      simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal]; ring
  unfold ham
  rw [e, e', ip_elecTotal_symm, ip_mag_symm]

/-- **The Hamiltonian is nonnegative** for `λE, λB ≥ 0`. -/
theorem ham_nonneg {lE lB : ℝ} (hE : 0 ≤ lE) (hB : 0 ≤ lB) (ψ : State ι δ G) :
    0 ≤ (ip ψ (ham ρ τ R lE lB ψ)).re := by
  have e : ip ψ (ham ρ τ R lE lB ψ)
      = (lE : ℂ) * ip ψ (elecTotal ψ) + (lB : ℂ) * ip ψ (mag ρ τ R ψ) := by
    unfold ip ham
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun U _ => by ring
  rw [e]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  exact add_nonneg (mul_nonneg hE (elecTotal_nonneg ψ)) (mul_nonneg hB (mag_nonneg ρ τ R ψ))

end Magnetic

/-! ## 3. Gauss law: the Hamiltonian commutes with the gauge transformations -/

section Gauss

variable (τ : δ → ι ≃ ι)

/-- A gauge transformation `g` acting on the states. -/
def gaugeState (g : ι → G) (ψ : State ι δ G) : State ι δ G :=
  fun U => ψ (GaugeWilson.gaugeAct τ g U)

/-- Translating a link and then gauge transforming is gauge transforming and then translating
by the conjugate. -/
theorem gaugeAct_shift (g : ι → G) (h : G) (μ : δ) (p : ι) (U : Conf ι δ G) :
    GaugeWilson.gaugeAct τ g (shift h μ p U)
      = shift (g p * h * (g p)⁻¹) μ p (GaugeWilson.gaugeAct τ g U) := by
  funext ν q
  by_cases hν : ν = μ
  · subst hν
    by_cases hq : q = p
    · subst hq; simp [GaugeWilson.gaugeAct, shift]; group
    · simp [GaugeWilson.gaugeAct, shift, hq]
  · simp [GaugeWilson.gaugeAct, shift, hν]

/-- The electric term of a link commutes with the gauge transformations. -/
theorem elecProj_gauge (g : ι → G) (μ : δ) (p : ι) (ψ : State ι δ G) :
    elecProj μ p (gaugeState τ g ψ) = gaugeState τ g (elecProj μ p ψ) := by
  funext U
  unfold elecProj gaugeState
  congr 1
  simp only [gaugeAct_shift]
  exact Fintype.sum_equiv (MulAut.conj (g p)).toEquiv _ _ fun h => rfl

theorem elecTotal_gauge (g : ι → G) (ψ : State ι δ G) :
    elecTotal (gaugeState τ g ψ) = gaugeState τ g (elecTotal ψ) := by
  funext U
  unfold elecTotal elec gaugeState
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun p _ => ?_
  have := congrFun (elecProj_gauge τ g μ p ψ) U
  exact congrArg (fun x => ψ (GaugeWilson.gaugeAct τ g U) - x) this

variable {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (R : Finset (ι × δ × δ))

/-- **The Wilson potential is gauge invariant** when the steps of the plaquettes commute. -/
theorem pot_gauge (g : ι → G) (U : Conf ι δ G)
    (h : ∀ r ∈ R, τ r.2.2 (τ r.2.1 r.1) = τ r.2.1 (τ r.2.2 r.1)) :
    pot ρ τ R (GaugeWilson.gaugeAct τ g U) = pot ρ τ R U := by
  unfold pot
  have : (fun μ p => ρ (GaugeWilson.gaugeAct τ g U μ p))
      = GaugeWilson.gaugeAct τ (fun q => ρ (g q)) (fun μ p => ρ (U μ p)) := by
    funext μ p; simp [GaugeWilson.gaugeAct]
  rw [this]
  exact GaugeWilson.action_gauge τ R _ _ h

/-- **Gauss law**: the Kogut-Susskind Hamiltonian commutes with every gauge transformation. -/
theorem ham_gauge (lE lB : ℝ) (g : ι → G) (ψ : State ι δ G)
    (h : ∀ r ∈ R, τ r.2.2 (τ r.2.1 r.1) = τ r.2.1 (τ r.2.2 r.1)) :
    ham ρ τ R lE lB (gaugeState τ g ψ) = gaugeState τ g (ham ρ τ R lE lB ψ) := by
  funext U
  unfold ham mag
  have e := congrFun (elecTotal_gauge τ g ψ) U
  rw [e]
  simp only [gaugeState, pot_gauge τ ρ R g U h]

end Gauss

end KogutSusskind
