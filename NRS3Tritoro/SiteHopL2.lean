/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Hops and currents on `ℓ²` of an infinite set of sites

The same hops and currents as `SiteHop`, now on `ℓ²(ι)` with `ι` allowed to be infinite (the
sites `ℤ³`, for example). A bijection `τ` of the sites and a real weight `c` with `|c| ≤ 1` give
the hop `(c p)(χ(τ p) + χ(τ⁻¹ p))/2` and the current `(i/2)(χ(τ p) − χ(τ⁻¹ p))`. The shift
along a bijection is a unitary of `ℓ²`, so the relations of `SiteHop` hold word for word:

- `SiteHopL2.hop_isSymmetric`, `SiteHopL2.cur_isSymmetric` : symmetric (weight invariant
  under `τ`).
- `SiteHopL2.hop_cur`, `SiteHopL2.cur_sq_add_hop_sq` : along one `τ`, `[T, K] = 0` and
  `K² + T² = 1`.
- `SiteHopL2.hop_hop_anticomm`, `SiteHopL2.cur_hop_anticomm` : along commuting `τ`, `σ`, they
  anticommute when the weight of the second changes sign under `τ`.
-/

@[expose] public noncomputable section

open Complex

namespace SiteHopL2

/-- The states: `ℓ²` of the sites. -/
abbrev L2 (ι : Type*) := lp (fun _ : ι => ℂ) 2

variable {ι : Type*} (τ σ : ι ≃ ι)

/-- A weighted shift keeps a state square summable. -/
theorem memℓp_shift {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) (χ : L2 ι) :
    Memℓp (fun p => (c p : ℂ) * χ (τ p)) 2 := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have hχ := (memℓp_gen_iff h2).mp (lp.memℓp χ)
  refine (memℓp_gen_iff h2).mpr ((τ.summable_iff.mpr hχ).of_nonneg_of_le
    (fun _ => by positivity) fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact Real.rpow_le_rpow (by positivity) (mul_le_of_le_one_left (norm_nonneg _) (hc p))
    (by positivity)

/-- The weighted shift `χ ↦ c · χ ∘ τ`. -/
def shift {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) : L2 ι →ₗ[ℂ] L2 ι where
  toFun χ := ⟨fun p => (c p : ℂ) * χ (τ p), memℓp_shift τ hc χ⟩
  map_add' χ η := lp.ext <| funext fun p => by
    simp only [lp.coeFn_add, Pi.add_apply]
    show (c p : ℂ) * (χ (τ p) + η (τ p)) = _
    ring
  map_smul' s χ := lp.ext <| funext fun p => by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    show (c p : ℂ) * (s * χ (τ p)) = _
    ring

theorem shift_apply {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) (χ : L2 ι) (p : ι) :
    shift τ hc χ p = (c p : ℂ) * χ (τ p) := rfl

theorem abs_one_le : ∀ p : ι, |(1 : ι → ℝ) p| ≤ 1 := fun _ => by simp

/-- The adjoint of the shift along `τ` is the shift along `τ⁻¹`. -/
theorem inner_shift {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) (hτ : ∀ p, c (τ p) = c p)
    (φ χ : L2 ι) : inner ℂ (shift τ hc φ) χ = inner ℂ φ (shift τ.symm hc χ) := by
  have hc' : ∀ q, c (τ.symm q) = c q := fun q => by rw [← hτ (τ.symm q), Equiv.apply_symm_apply]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← τ.symm.tsum_eq]
  refine tsum_congr fun q => ?_
  simp only [shift_apply, Equiv.apply_symm_apply, RCLike.inner_apply', map_mul,
    Complex.conj_ofReal, hc']
  ring

/-- The hop along `τ` with the real weight `c`: `(c p) (χ(τ p) + χ(τ⁻¹ p))/2`. -/
def hop {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) : L2 ι →ₗ[ℂ] L2 ι :=
  (1 / 2 : ℂ) • (shift τ hc + shift τ.symm hc)

/-- The current along `τ`: `(i/2)(χ(τ p) − χ(τ⁻¹ p))`. -/
def cur : L2 ι →ₗ[ℂ] L2 ι :=
  (I / 2) • (shift τ (c := 1) abs_one_le - shift τ.symm (c := 1) abs_one_le)

theorem hop_apply {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) (χ : L2 ι) (p : ι) :
    hop τ hc χ p = (c p : ℂ) * ((χ (τ p) + χ (τ.symm p)) / 2) := by
  simp only [hop, LinearMap.smul_apply, LinearMap.add_apply, lp.coeFn_smul, lp.coeFn_add,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, shift_apply]
  ring

theorem cur_apply (χ : L2 ι) (p : ι) :
    cur τ χ p = I / 2 * (χ (τ p) - χ (τ.symm p)) := by
  simp only [cur, LinearMap.smul_apply, LinearMap.sub_apply, lp.coeFn_smul, lp.coeFn_sub,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, shift_apply, Pi.one_apply, Complex.ofReal_one,
    one_mul]

/-- A hop with a weight invariant under `τ` is symmetric. -/
theorem hop_isSymmetric {c : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) (hτ : ∀ p, c (τ p) = c p) :
    (hop τ hc).IsSymmetric := by
  have hτ' : ∀ q, c (τ.symm q) = c q := fun q => by
    rw [← hτ (τ.symm q), Equiv.apply_symm_apply]
  intro φ χ
  have e := inner_shift τ.symm hc hτ'
  rw [Equiv.symm_symm] at e
  simp only [hop, LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_shift τ hc hτ, e]
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-- The current is symmetric. -/
theorem cur_isSymmetric : (cur τ).IsSymmetric := by
  intro φ χ
  have h1 : ∀ p, (1 : ι → ℝ) (τ p) = (1 : ι → ℝ) p := fun _ => rfl
  have h1' : ∀ p, (1 : ι → ℝ) (τ.symm p) = (1 : ι → ℝ) p := fun _ => rfl
  have e := inner_shift τ.symm abs_one_le h1'
  rw [Equiv.symm_symm] at e
  simp only [cur, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, inner_shift τ abs_one_le h1, e]
  simp only [map_div₀, Complex.conj_I, map_ofNat]
  ring

/-- The hop and the current along the same `τ` commute. -/
theorem hop_cur (χ : L2 ι) :
    hop τ (c := 1) abs_one_le (cur τ χ) = cur τ (hop τ (c := 1) abs_one_le χ) := by
  refine lp.ext <| funext fun p => ?_
  simp only [hop_apply, cur_apply, Pi.one_apply, Complex.ofReal_one, one_mul,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  ring

/-- `K² + T² = 1` along `τ`. -/
theorem cur_sq_add_hop_sq (χ : L2 ι) :
    cur τ (cur τ χ) + hop τ (c := 1) abs_one_le (hop τ (c := 1) abs_one_le χ) = χ := by
  refine lp.ext <| funext fun p => ?_
  simp only [lp.coeFn_add, Pi.add_apply, hop_apply, cur_apply, Pi.one_apply, Complex.ofReal_one,
    one_mul, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  linear_combination ((χ (τ (τ p)) + χ (τ.symm (τ.symm p))) / 4 - χ p / 2) * Complex.I_sq

variable {τ σ} {c c' : ι → ℝ} (hc : ∀ p, |c p| ≤ 1) (hc' : ∀ p, |c' p| ≤ 1)
  (h1 : ∀ p, σ (τ p) = τ (σ p)) (h2 : ∀ p, σ.symm (τ p) = τ (σ.symm p))
  (h3 : ∀ p, σ (τ.symm p) = τ.symm (σ p)) (h4 : ∀ p, σ.symm (τ.symm p) = τ.symm (σ.symm p))
include h1 h2 h3 h4

/-- Two hops anticommute when each weight is invariant under the other hop and the second weight
changes sign under the first hop. -/
theorem hop_hop_anticomm (hcσ : ∀ p, c (σ p) = c p) (hcσs : ∀ p, c (σ.symm p) = c p)
    (hτ : ∀ p, c' (τ p) = -c' p) (hτs : ∀ p, c' (τ.symm p) = -c' p) (χ : L2 ι) :
    hop τ hc (hop σ hc' χ) = -hop σ hc' (hop τ hc χ) := by
  refine lp.ext <| funext fun p => ?_
  simp only [lp.coeFn_neg, Pi.neg_apply, hop_apply, hcσ, hcσs, hτ, hτs, h1, h2, h3, h4,
    Complex.ofReal_neg]
  ring

/-- The current along `τ` anticommutes with a hop whose weight changes sign under `τ`. -/
theorem cur_hop_anticomm (hτ : ∀ p, c' (τ p) = -c' p) (hτs : ∀ p, c' (τ.symm p) = -c' p)
    (χ : L2 ι) : cur τ (hop σ hc' χ) = -hop σ hc' (cur τ χ) := by
  refine lp.ext <| funext fun p => ?_
  simp only [lp.coeFn_neg, Pi.neg_apply, hop_apply, cur_apply, hτ, hτs, h1, h2, h3, h4,
    Complex.ofReal_neg]
  ring

end SiteHopL2
