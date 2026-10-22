/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hops and currents along a bijection of the sites

On `EuclideanSpace ℂ ι` and a bijection `τ` of the sites, the hop with a real weight `c`,
`(c p)(χ(τ p) + χ(τ⁻¹ p))/2`, and the current `(i/2)(χ(τ p) − χ(τ⁻¹ p))`. Every transport,
staggered term and current of the torus and of the fiber is one of them, so the relations are
proved once:

- `SiteHop.hop_isSymmetric`, `SiteHop.cur_isSymmetric` : symmetric (weight invariant under `τ`).
- `SiteHop.hop_cur`, `SiteHop.cur_sq_add_hop_sq` : along one `τ`, `[T, K] = 0` and `K² + T² = 1`.
- `SiteHop.hop_hop_anticomm`, `SiteHop.cur_hop_anticomm` : along commuting `τ`, `σ`, they
  anticommute when the weight of the second changes sign under `τ`.
- `SiteHop.curw` : the current with a sign weight, the velocity of a staggered axis;
  `curw_isSymmetric`, `hop_curw`, `curw_sq_add_hop_sq`, `curw_hop_anticomm`,
  `hop_curw_anticomm`.
-/

@[expose] public noncomputable section

open Complex

namespace SiteHop

variable {ι : Type*} (τ σ : ι ≃ ι)

/-- The hop along `τ` with the real weight `c`: `(c p) (χ(τ p) + χ(τ⁻¹ p))/2`. -/
def hop (c : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun χ := WithLp.toLp 2 fun p => (c p : ℂ) * ((χ (τ p) + χ (τ.symm p)) / 2)
  map_add' χ η := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' s χ := by
    ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The current along `τ`: `(i/2)(χ(τ p) − χ(τ⁻¹ p))`. -/
def cur : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun χ := WithLp.toLp 2 fun p => I / 2 * (χ (τ p) - χ (τ.symm p))
  map_add' χ η := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' s χ := by
    ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem hop_apply (c : ι → ℝ) (χ : EuclideanSpace ℂ ι) (p : ι) :
    hop τ c χ p = (c p : ℂ) * ((χ (τ p) + χ (τ.symm p)) / 2) := rfl

theorem cur_apply (χ : EuclideanSpace ℂ ι) (p : ι) :
    cur τ χ p = I / 2 * (χ (τ p) - χ (τ.symm p)) := rfl

/-- A hop with a weight invariant under `τ` is symmetric. -/
theorem hop_isSymmetric [Fintype ι] {c : ι → ℝ} (hc : ∀ p, c (τ p) = c p) :
    (hop τ c).IsSymmetric := by
  intro φ χ
  have hc' : ∀ q, c (τ.symm q) = c q := fun q => by rw [← hc (τ.symm q), Equiv.apply_symm_apply]
  have e1 := Equiv.sum_comp τ
    (fun q => (starRingEnd ℂ) (φ q) * ((c q : ℂ) * χ (τ.symm q)))
  have e2 := Equiv.sum_comp τ.symm
    (fun q => (starRingEnd ℂ) (φ q) * ((c q : ℂ) * χ (τ q)))
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, hc, hc'] at e1 e2
  simp only [PiLp.inner_apply, RCLike.inner_apply', hop_apply, map_mul, map_div₀, map_add,
    Complex.conj_ofReal, map_ofNat]
  calc ∑ p, (c p : ℂ) * (((starRingEnd ℂ) (φ (τ p)) + (starRingEnd ℂ) (φ (τ.symm p))) / 2) * χ p
      = (∑ p, (starRingEnd ℂ) (φ (τ p)) * ((c p : ℂ) * χ p) +
          ∑ p, (starRingEnd ℂ) (φ (τ.symm p)) * ((c p : ℂ) * χ p)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = (∑ p, (starRingEnd ℂ) (φ p) * ((c p : ℂ) * χ (τ.symm p)) +
          ∑ p, (starRingEnd ℂ) (φ p) * ((c p : ℂ) * χ (τ p))) / 2 := by rw [e1, e2]
    _ = ∑ p, (starRingEnd ℂ) (φ p) * ((c p : ℂ) * ((χ (τ p) + χ (τ.symm p)) / 2)) := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- The current is symmetric. -/
theorem cur_isSymmetric [Fintype ι] : (cur τ).IsSymmetric := by
  intro φ χ
  have e1 := Equiv.sum_comp τ (fun q => (starRingEnd ℂ) (φ q) * χ (τ.symm q))
  have e2 := Equiv.sum_comp τ.symm (fun q => (starRingEnd ℂ) (φ q) * χ (τ q))
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at e1 e2
  simp only [PiLp.inner_apply, RCLike.inner_apply', cur_apply, map_mul, map_div₀, map_sub,
    Complex.conj_I, map_ofNat]
  calc ∑ p, -I / 2 * ((starRingEnd ℂ) (φ (τ p)) - (starRingEnd ℂ) (φ (τ.symm p))) * χ p
      = -I / 2 * (∑ p, (starRingEnd ℂ) (φ (τ p)) * χ p -
          ∑ p, (starRingEnd ℂ) (φ (τ.symm p)) * χ p) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = -I / 2 * (∑ p, (starRingEnd ℂ) (φ p) * χ (τ.symm p) -
          ∑ p, (starRingEnd ℂ) (φ p) * χ (τ p)) := by rw [e1, e2]
    _ = ∑ p, (starRingEnd ℂ) (φ p) * (I / 2 * (χ (τ p) - χ (τ.symm p))) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- The hop and the current along the same `τ` commute. -/
theorem hop_cur (χ : EuclideanSpace ℂ ι) : hop τ 1 (cur τ χ) = cur τ (hop τ 1 χ) := by
  ext p
  simp only [hop_apply, cur_apply, Pi.one_apply, Complex.ofReal_one, one_mul,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  ring

/-- `K² + T² = 1` along `τ`. -/
theorem cur_sq_add_hop_sq (χ : EuclideanSpace ℂ ι) :
    cur τ (cur τ χ) + hop τ 1 (hop τ 1 χ) = χ := by
  ext p
  simp only [PiLp.add_apply, hop_apply, cur_apply, Pi.one_apply, Complex.ofReal_one, one_mul,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  linear_combination ((χ (τ (τ p)) + χ (τ.symm (τ.symm p))) / 4 - χ p / 2) * Complex.I_sq

/-- The current along `τ` with the real weight `c`: `(c p)(i/2)(χ(τ p) − χ(τ⁻¹ p))`. -/
def curw (c : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun χ := WithLp.toLp 2 fun p => (c p : ℂ) * (I / 2 * (χ (τ p) - χ (τ.symm p)))
  map_add' χ η := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' s χ := by
    ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem curw_apply (c : ι → ℝ) (χ : EuclideanSpace ℂ ι) (p : ι) :
    curw τ c χ p = (c p : ℂ) * (I / 2 * (χ (τ p) - χ (τ.symm p))) := rfl

/-- A weighted current with a weight invariant under `τ` is symmetric. -/
theorem curw_isSymmetric [Fintype ι] {c : ι → ℝ} (hc : ∀ p, c (τ p) = c p) :
    (curw τ c).IsSymmetric := by
  intro φ χ
  have hc' : ∀ q, c (τ.symm q) = c q := fun q => by rw [← hc (τ.symm q), Equiv.apply_symm_apply]
  have e1 := Equiv.sum_comp τ
    (fun q => (starRingEnd ℂ) (φ q) * ((c q : ℂ) * χ (τ.symm q)))
  have e2 := Equiv.sum_comp τ.symm
    (fun q => (starRingEnd ℂ) (φ q) * ((c q : ℂ) * χ (τ q)))
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, hc, hc'] at e1 e2
  simp only [PiLp.inner_apply, RCLike.inner_apply', curw_apply, map_mul, map_div₀, map_sub,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  calc ∑ p, (c p : ℂ) * (-I / 2 * ((starRingEnd ℂ) (φ (τ p)) -
        (starRingEnd ℂ) (φ (τ.symm p)))) * χ p
      = -I / 2 * (∑ p, (starRingEnd ℂ) (φ (τ p)) * ((c p : ℂ) * χ p) -
          ∑ p, (starRingEnd ℂ) (φ (τ.symm p)) * ((c p : ℂ) * χ p)) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = -I / 2 * (∑ p, (starRingEnd ℂ) (φ p) * ((c p : ℂ) * χ (τ.symm p)) -
          ∑ p, (starRingEnd ℂ) (φ p) * ((c p : ℂ) * χ (τ p))) := by rw [e1, e2]
    _ = ∑ p, (starRingEnd ℂ) (φ p) * ((c p : ℂ) * (I / 2 * (χ (τ p) - χ (τ.symm p)))) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- The hop and the current along the same `τ` with the same invariant weight commute. -/
theorem hop_curw {c : ι → ℝ} (hc : ∀ p, c (τ p) = c p) (hcs : ∀ p, c (τ.symm p) = c p)
    (χ : EuclideanSpace ℂ ι) : hop τ c (curw τ c χ) = curw τ c (hop τ c χ) := by
  ext p
  simp only [hop_apply, curw_apply, hc, hcs, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  ring

/-- `K² + T² = 1` along `τ`, with a sign weight. -/
theorem curw_sq_add_hop_sq {c : ι → ℝ} (hc : ∀ p, c (τ p) = c p)
    (hcs : ∀ p, c (τ.symm p) = c p) (h1 : ∀ p, c p * c p = 1) (χ : EuclideanSpace ℂ ι) :
    curw τ c (curw τ c χ) + hop τ c (hop τ c χ) = χ := by
  ext p
  have h1' : (c p : ℂ) * (c p : ℂ) = 1 := by exact_mod_cast h1 p
  simp only [PiLp.add_apply, hop_apply, curw_apply, hc, hcs, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]
  linear_combination ((c p : ℂ) * (c p : ℂ) / 4 *
      (χ (τ (τ p)) - 2 * χ p + χ (τ.symm (τ.symm p)))) * Complex.I_sq + χ p * h1'

variable {τ σ} {c c' : ι → ℝ}
  (h1 : ∀ p, σ (τ p) = τ (σ p)) (h2 : ∀ p, σ.symm (τ p) = τ (σ.symm p))
  (h3 : ∀ p, σ (τ.symm p) = τ.symm (σ p)) (h4 : ∀ p, σ.symm (τ.symm p) = τ.symm (σ.symm p))
include h1 h2 h3 h4

/-- Two hops anticommute when each weight is invariant under its own hop and the second weight
changes sign under the first hop. -/
theorem hop_hop_anticomm (hc : ∀ p, c (σ p) = c p) (hcs : ∀ p, c (σ.symm p) = c p)
    (hc' : ∀ p, c' (τ p) = -c' p) (hc's : ∀ p, c' (τ.symm p) = -c' p)
    (χ : EuclideanSpace ℂ ι) : hop τ c (hop σ c' χ) = -hop σ c' (hop τ c χ) := by
  ext p
  simp only [PiLp.neg_apply, hop_apply, hc, hcs, hc', hc's, h1, h2, h3, h4,
    Complex.ofReal_neg]
  ring

/-- The current along `τ` anticommutes with a hop whose weight changes sign under `τ`. -/
theorem cur_hop_anticomm (hc' : ∀ p, c' (τ p) = -c' p) (hc's : ∀ p, c' (τ.symm p) = -c' p)
    (χ : EuclideanSpace ℂ ι) : cur τ (hop σ c' χ) = -hop σ c' (cur τ χ) := by
  ext p
  simp only [PiLp.neg_apply, hop_apply, cur_apply, hc', hc's, h1, h2, h3, h4, Complex.ofReal_neg]
  ring

/-- A weighted current anticommutes with a hop whose weight changes sign under it. -/
theorem curw_hop_anticomm (hc : ∀ p, c (σ p) = c p) (hcs : ∀ p, c (σ.symm p) = c p)
    (hc' : ∀ p, c' (τ p) = -c' p) (hc's : ∀ p, c' (τ.symm p) = -c' p)
    (χ : EuclideanSpace ℂ ι) : curw τ c (hop σ c' χ) = -hop σ c' (curw τ c χ) := by
  ext p
  simp only [PiLp.neg_apply, hop_apply, curw_apply, hc, hcs, hc', hc's, h1, h2, h3, h4,
    Complex.ofReal_neg]
  ring

/-- A hop anticommutes with a weighted current whose weight changes sign under the hop. -/
theorem hop_curw_anticomm (hc : ∀ p, c (σ p) = c p) (hcs : ∀ p, c (σ.symm p) = c p)
    (hc' : ∀ p, c' (τ p) = -c' p) (hc's : ∀ p, c' (τ.symm p) = -c' p)
    (χ : EuclideanSpace ℂ ι) : hop τ c (curw σ c' χ) = -curw σ c' (hop τ c χ) := by
  ext p
  simp only [PiLp.neg_apply, hop_apply, curw_apply, hc, hcs, hc', hc's, h1, h2, h3, h4,
    Complex.ofReal_neg]
  ring

end SiteHop
