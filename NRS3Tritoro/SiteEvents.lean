/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.QuantumEvents
public import NRS3Tritoro.SiteHop
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# Site events on any lattice: continuity, conservation and Robertson

On `ℂ^ι` (`ι` finite, any lattice) the event "the excitation is at `p`" is the projection `Π_p`,
with `p_p = |ψ_p|²`. For any symmetric generator `G`:

* the rate of the site is `⟨i[G, Π_p]⟩ = −2 Im(conj((Gψ)_p) ψ_p)`;
* the rates add up to `0` over all sites, because `Σ_p Π_p = 1` (nothing is lost);
* Robertson for bits: `rate_p² ≤ 4 Var G · p_p (1 − p_p)`; a decided site does not change.

When `G` is a Hermitian matrix the rate is a sum of **link flows**,
`rate_p = Σ_q J_{p q}`, `J_{p q} = −2 Im(conj(G_{pq}) ψ̄_q ψ_p)`, antisymmetric, `J_{qp} = −J_{pq}`,
and zero where `G_{pq} = 0`: the lattice — which sites are linked — is the support of `G`.
For a hop along a bijection `τ` the flow is `F_τ(τ⁻¹ p) − F_τ(p)`, `F_τ(q) = Im(ψ̄_{τq} ψ_q)`.

None of this depends on the topology; the topology decides only which links exist
(`SiteEventsTopologies`).

## Main results

- `SiteEvents.rate_site`, `SiteEvents.sum_rate_site`, `SiteEvents.rate_site_sq_le`,
  `SiteEvents.rate_eq_zero_of_decided` : continuity, conservation, Robertson, decided sites.
- `SiteEvents.rate_matrix`, `SiteEvents.linkFlow_antisymm`, `SiteEvents.linkFlow_eq_zero` : the
  link flows of a Hermitian matrix.
- `SiteEvents.rate_hop` : the flows of a hop.
- `SiteEvents.rate_add` : rates add over the terms of `G`.
-/

@[expose] public noncomputable section

open Complex QuantumEvents

namespace SiteEvents

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Site events -/

/-- The projection onto the site `p`. -/
def siteProj (p : ι) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun ψ := WithLp.toLp 2 fun q => if q = p then ψ q else 0
  map_add' ψ φ := by ext q; simp only [PiLp.add_apply]; split_ifs <;> simp
  map_smul' z ψ := by ext q; simp only [PiLp.smul_apply, smul_eq_mul]; split_ifs <;> simp

omit [Fintype ι] in
theorem siteProj_apply (p : ι) (ψ : EuclideanSpace ℂ ι) (q : ι) :
    siteProj p ψ q = if q = p then ψ q else 0 := rfl

/-- **The event "the excitation is at `p`".** -/
def siteEvent (p : ι) : Event (EuclideanSpace ℂ ι) where
  P := siteProj p
  symm φ ψ := by
    simp only [PiLp.inner_apply, siteProj_apply]
    exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
  idem ψ := by ext q; simp only [siteProj_apply]; split_ifs <;> rfl

theorem siteEvent_P (p : ι) : (siteEvent p).P = siteProj p := rfl

theorem inner_siteProj (p : ι) (φ ψ : EuclideanSpace ℂ ι) :
    inner ℂ φ (siteProj p ψ) = (starRingEnd ℂ) (φ p) * ψ p := by
  rw [PiLp.inner_apply, Finset.sum_eq_single p]
  · simp [siteProj_apply, mul_comm]
  · intro q _ hq; simp [siteProj_apply, hq]
  · simp

/-- `p_p = |ψ_p|²`. -/
theorem prob_siteEvent (p : ι) (ψ : EuclideanSpace ℂ ι) : prob (siteEvent p) ψ = ‖ψ p‖ ^ 2 := by
  rw [prob, siteEvent_P, inner_siteProj, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The sites exhaust the lattice: `Σ_p Π_p = 1`. -/
theorem sum_siteProj (ψ : EuclideanSpace ℂ ι) : ∑ p, siteProj p ψ = ψ := by
  ext q
  simp only [WithLp.ofLp_sum, Finset.sum_apply, siteProj_apply, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-! ## 2. Continuity, conservation, Robertson -/

variable {G : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}

/-- **The rate of a site**: `⟨i[G, Π_p]⟩ = −2 Im(conj((Gψ)_p) ψ_p)`. -/
theorem rate_site (hG : G.IsSymmetric) (p : ι) (ψ : EuclideanSpace ℂ ι) :
    rate G (siteEvent p) ψ = -2 * ((starRingEnd ℂ) (G ψ p) * ψ p).im := by
  rw [rate_eq hG, siteEvent_P, inner_siteProj]

/-- **Nothing is lost**: the rates of all sites add up to `0`, on any lattice. -/
theorem sum_rate_site (hG : G.IsSymmetric) (ψ : EuclideanSpace ℂ ι) :
    ∑ p, rate G (siteEvent p) ψ = 0 := by
  simp only [rate_site hG, ← Finset.mul_sum, ← Complex.im_sum]
  have h : ∑ p, (starRingEnd ℂ) (G ψ p) * ψ p = inner ℂ (G ψ) ψ := by
    rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun p _ => by simp [mul_comm]
  rw [h, inner_self_real hG, Complex.ofReal_im, mul_zero]

/-- **Robertson for a site**: `rate_p² ≤ 4 Var G · p_p (1 − p_p)`. -/
theorem rate_site_sq_le (hG : G.IsSymmetric) (p : ι) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    rate G (siteEvent p) ψ ^ 2 ≤ 4 * variance G ψ * (‖ψ p‖ ^ 2 * (1 - ‖ψ p‖ ^ 2)) := by
  rw [← prob_siteEvent]
  exact rate_sq_le hG (siteEvent p) hψ

/-- **A decided site does not change.** -/
theorem rate_eq_zero_of_decided (hG : G.IsSymmetric) (p : ι) {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) (hp : ‖ψ p‖ ^ 2 = 0 ∨ ‖ψ p‖ ^ 2 = 1) : rate G (siteEvent p) ψ = 0 := by
  have h := rate_site_sq_le hG p hψ
  have h0 : ‖ψ p‖ ^ 2 * (1 - ‖ψ p‖ ^ 2) = 0 := by rcases hp with hp | hp <;> rw [hp] <;> ring
  rw [h0, mul_zero] at h
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg _))

/-- Rates add over the terms of the generator. -/
theorem rate_add (G₁ G₂ : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (p : ι)
    (ψ : EuclideanSpace ℂ ι) :
    rate (G₁ + G₂) (siteEvent p) ψ = rate G₁ (siteEvent p) ψ + rate G₂ (siteEvent p) ψ := by
  simp only [rate, LinearMap.add_apply, map_add, inner_add_right]
  rw [← Complex.add_re]
  ring_nf

/-! ## 3. Link flows of a Hermitian matrix: the lattice is the support of `G` -/

/-- The flow into `p` through the link `{p, q}`: `J_{pq} = −2 Im(conj(G_{pq}) ψ̄_q ψ_p)`. -/
def linkFlow (G : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) (p q : ι) : ℝ :=
  -2 * ((starRingEnd ℂ) (G p q) * (starRingEnd ℂ) (ψ q) * ψ p).im

/-- **The rate is the sum of the link flows.** -/
theorem rate_matrix {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (p : ι) (ψ : EuclideanSpace ℂ ι) :
    rate (Matrix.toEuclideanLin G) (siteEvent p) ψ = ∑ q, linkFlow G ψ p q := by
  rw [rate_site (Matrix.isSymmetric_toEuclideanLin_iff.mpr hG)]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.sum_mul, Complex.im_sum, Finset.mul_sum, linkFlow]

omit [Fintype ι] [DecidableEq ι] in
/-- **The flow is antisymmetric**: what enters `p` from `q` leaves `q` to `p`. -/
theorem linkFlow_antisymm {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (ψ : EuclideanSpace ℂ ι)
    (p q : ι) : linkFlow G ψ q p = -linkFlow G ψ p q := by
  have h : G q p = (starRingEnd ℂ) (G p q) := (hG.apply q p).symm
  simp only [linkFlow, h, Complex.conj_conj]
  rw [show G p q * (starRingEnd ℂ) (ψ p) * ψ q =
      (starRingEnd ℂ) ((starRingEnd ℂ) (G p q) * (starRingEnd ℂ) (ψ q) * ψ p) by
    simp only [map_mul, Complex.conj_conj]; ring, Complex.conj_im]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **No link, no flow**: where `G_{pq} = 0` nothing passes. -/
theorem linkFlow_eq_zero {G : Matrix ι ι ℂ} (ψ : EuclideanSpace ℂ ι) {p q : ι} (h : G p q = 0) :
    linkFlow G ψ p q = 0 := by
  simp [linkFlow, h]

/-! ## 4. The flows of a hop -/

/-- The flow of a hop along `τ` through the link `q → τ q`, `F_τ(q) = Im(ψ̄_{τq} ψ_q)`. -/
def hopFlow (τ : ι ≃ ι) (ψ : EuclideanSpace ℂ ι) (q : ι) : ℝ :=
  ((starRingEnd ℂ) (ψ (τ q)) * ψ q).im

/-- **The flows of a hop**: `rate_p = F_τ(τ⁻¹ p) − F_τ(p)`. -/
theorem rate_hop (τ : ι ≃ ι) (p : ι) (ψ : EuclideanSpace ℂ ι) :
    rate (SiteHop.hop τ 1) (siteEvent p) ψ = hopFlow τ ψ (τ.symm p) - hopFlow τ ψ p := by
  rw [rate_site (SiteHop.hop_isSymmetric τ fun _ => rfl), SiteHop.hop_apply, hopFlow, hopFlow,
    Equiv.apply_symm_apply]
  simp only [Pi.one_apply, Complex.ofReal_one, one_mul, map_div₀, map_add, map_ofNat,
    Complex.mul_im, Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  norm_num
  ring

end SiteEvents
