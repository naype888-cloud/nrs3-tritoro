/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSpeed
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The exact spectrum of the ring

The closed transport of the ring of `d ≥ 3` positions is a circulant: its eigenvectors are the
plane waves `w_m(j) = ζ^(m j)`, `ζ = e^(2πi/d)`, and its eigenvalues are

  `λ_m = cos (2π m / d)`,  `m = 0, …, d − 1`.

The `d` waves are the columns of a Vandermonde matrix on the `d` distinct roots of unity, so they
span `ℂ^d` and there is no other eigenvalue: the spectrum is exactly `{cos (2π m / d)}`. It
reaches `1` at the uniform wave `m = 0`, so the bound `|E| ≤ 1` of `TorusSpeed` is attained.

## Main results

- `TorusSpectrum.ring_mulVec_wave` : `ring d` sends `w_m` to `cos (2π m / d) • w_m`.
- `TorusSpectrum.eigenvalue_of_diag` : if `H W = W diag λ` with `W` invertible, every eigenvalue
  of `H` is some `λ_m`.
- `TorusSpectrum.eq_cos_of_eigenvector` : every eigenvalue of the ring is `cos (2π m / d)`.
- `TorusSpectrum.exists_energy_eq_one` : the eigenvalue `1` occurs.
-/

@[expose] public noncomputable section

open TransportPosition TorusArea TorusTime Complex

namespace TorusSpectrum

/-- If `H W = W diag λ` with `W` invertible, every eigenvalue of `H` is a `λ_m`. -/
theorem eigenvalue_of_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {H W : Matrix ι ι ℂ}
    {lam : ι → ℂ} (hW : IsUnit W.det) (h : H * W = W * Matrix.diagonal lam) {μ : ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (hμ : H.mulVec v = μ • v) : ∃ m, μ = lam m := by
  set c := (W⁻¹).mulVec v with hc
  have hWc : W.mulVec c = v := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hW, Matrix.one_mulVec]
  have h1 : W.mulVec (Matrix.diagonal lam |>.mulVec c) = W.mulVec (μ • c) := by
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hWc, hμ, Matrix.mulVec_smul, hWc]
  have h2 := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det W).mpr hW) h1
  by_contra hne
  push Not at hne
  apply hv
  rw [← hWc]
  have : c = 0 := by
    funext m
    have := congrFun h2 m
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    have h3 : (lam m - μ) * c m = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (hne m).symm)
  rw [this, Matrix.mulVec_zero]

/-! ## The plane waves of the ring -/

section Ring

variable {d : ℕ} [NeZero d]

/-- The position after `i` on the ring. -/
def nxt (i : Fin d) : Fin d :=
  if h : i.val + 1 < d then ⟨i.val + 1, h⟩ else ⟨0, Nat.pos_of_neZero d⟩

/-- The position before `i` on the ring. -/
def prv (i : Fin d) : Fin d :=
  if h : 0 < i.val then ⟨i.val - 1, by omega⟩ else ⟨d - 1, by have := Nat.pos_of_neZero d; omega⟩

lemma links_iff (i j : Fin d) :
    (MinStep i j ∨ Seam d i j) ↔ (j = nxt i ∨ j = prv i) := by
  unfold MinStep Seam nxt prv
  split_ifs <;> simp only [Fin.ext_iff] <;> omega

lemma nxt_ne_prv (hd : 3 ≤ d) (i : Fin d) : nxt i ≠ prv i := by
  unfold nxt prv
  split_ifs <;> simp only [ne_eq, Fin.ext_iff] <;> omega

/-- **The ring acts on a function by the mean of the two neighbours.** -/
theorem ring_mulVec (hd : 3 ≤ d) (f : Fin d → ℂ) (i : Fin d) :
    (ring d).mulVec f i = (f (nxt i) + f (prv i)) / 2 := by
  have h : ∀ j, ring d i j = (if j = nxt i then 1 / 2 else 0) + (if j = prv i then 1 / 2 else 0) := by
    intro j
    rw [TorusSpeed.ring_eq_half hd]
    by_cases h1 : j = nxt i
    · have : j ≠ prv i := h1 ▸ nxt_ne_prv hd i
      simp [h1, nxt_ne_prv hd i, links_iff]
    · by_cases h2 : j = prv i
      · simp [h2, (nxt_ne_prv hd i).symm, links_iff]
      · simp [h1, h2, links_iff]
  simp only [Matrix.mulVec, dotProduct, h, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The primitive root `ζ = e^(2πi/d)`. -/
def zeta (d : ℕ) : ℂ := exp (2 * Real.pi * I / d)

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta d) d :=
  isPrimitiveRoot_exp d (NeZero.ne d)

lemma zeta_ne_zero (d : ℕ) : zeta d ≠ 0 := exp_ne_zero _

/-- The plane wave `w_m(j) = ζ^(m j)`. -/
def wave (d m : ℕ) (j : Fin d) : ℂ := zeta d ^ (m * j.val)

lemma wave_nxt (m : ℕ) (i : Fin d) : wave d m (nxt i) = zeta d ^ m * wave d m i := by
  have h1 : zeta d ^ d = 1 := isPrimitiveRoot_zeta.pow_eq_one
  unfold wave nxt
  split_ifs with h
  · simp only [← pow_add]; congr 1; ring
  · have : i.val + 1 = d := by have := i.2; omega
    simp only [Nat.mul_zero, pow_zero, ← pow_add]
    have e : m + m * i.val = d * m := by
      generalize i.val = k at this ⊢
      subst this; ring
    rw [e, pow_mul, h1, one_pow]

lemma wave_prv (m : ℕ) (i : Fin d) : zeta d ^ m * wave d m (prv i) = wave d m i := by
  have h1 : zeta d ^ d = 1 := isPrimitiveRoot_zeta.pow_eq_one
  unfold wave prv
  split_ifs with h
  · simp only [← pow_add]; congr 1
    obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
    simp only [hk, Nat.add_sub_cancel]; ring
  · have : i.val = 0 := by omega
    simp only [this, Nat.mul_zero, pow_zero, ← pow_add]
    rw [show m + m * (d - 1) = d * m by
      have := Nat.pos_of_neZero d
      obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      subst hk; simp; ring, pow_mul, h1, one_pow]

/-- The eigenvalue `cos (2π m / d)` of the wave `m`. -/
def lam (d m : ℕ) : ℂ := ((Real.cos (2 * Real.pi * m / d) : ℝ) : ℂ)

lemma lam_eq (d m : ℕ) : lam d m = (zeta d ^ m + (zeta d ^ m)⁻¹) / 2 := by
  have h : zeta d ^ m = exp ((2 * Real.pi * m / d : ℝ) * I) := by
    rw [zeta, ← exp_nat_mul]; congr 1; push_cast; ring
  have h2 : (zeta d ^ m)⁻¹ = exp (-(2 * Real.pi * m / d : ℝ) * I) := by
    rw [h, ← exp_neg]; congr 1; ring
  rw [h2, h, lam, ofReal_cos, cos]

/-- **The ring sends the wave `m` to `cos (2π m / d)` times itself.** -/
theorem ring_mulVec_wave (hd : 3 ≤ d) (m : ℕ) :
    (ring d).mulVec (wave d m) = lam d m • wave d m := by
  funext i
  have hz : zeta d ^ m ≠ 0 := pow_ne_zero _ (zeta_ne_zero d)
  have hp : wave d m (prv i) = (zeta d ^ m)⁻¹ * wave d m i := by
    rw [eq_inv_mul_iff_mul_eq₀ hz, wave_prv]
  rw [ring_mulVec hd, wave_nxt, hp, Pi.smul_apply, smul_eq_mul, lam_eq]
  ring

/-- The matrix of the waves: `W j m = ζ^(m j)`, a Vandermonde matrix on the roots of unity. -/
def waves (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun j m => wave d m.val j

lemma det_waves_ne_zero : (waves d).det ≠ 0 := by
  have h : waves d = Matrix.transpose (Matrix.vandermonde fun m : Fin d => zeta d ^ m.val) := by
    ext j m
    simp [waves, wave, Matrix.vandermonde, ← pow_mul]
  rw [h, Matrix.det_transpose, Ne, Matrix.det_vandermonde_eq_zero_iff]
  push Not
  intro a b hab
  exact Fin.ext (isPrimitiveRoot_zeta.pow_inj a.2 b.2 hab)

theorem ring_mul_waves (hd : 3 ≤ d) :
    ring d * waves d = waves d * Matrix.diagonal fun m : Fin d => lam d m.val := by
  ext j m
  have := congrFun (ring_mulVec_wave hd m.val) j
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, waves, mul_comm] using this

/-- **Every eigenvalue of the ring is `cos (2π m / d)`**: the spectrum is exactly the cosines. -/
theorem eq_cos_of_eigenvector (hd : 3 ≤ d) {μ : ℂ} {v : Fin d → ℂ} (hv : v ≠ 0)
    (hμ : (ring d).mulVec v = μ • v) : ∃ m : Fin d, μ = lam d m.val :=
  eigenvalue_of_diag (isUnit_iff_ne_zero.mpr det_waves_ne_zero) (ring_mul_waves hd) hv hμ

/-- The eigenvalue `1` occurs: the uniform wave. -/
theorem exists_eigenvector_one (hd : 3 ≤ d) :
    ∃ v : Fin d → ℂ, v ≠ 0 ∧ (ring d).mulVec v = (1 : ℂ) • v := by
  refine ⟨wave d 0, fun h => ?_, ?_⟩
  · have := congrFun h ⟨0, Nat.pos_of_neZero d⟩
    simp [wave] at this
  · rw [ring_mulVec_wave hd, lam]
    simp

end Ring

/-! ## The three-torus -/

section Torus

open PathGraph3DNRS LightCone
open PathGraph3D (Site3D)
open scoped Kronecker

variable {dx dy dz : ℕ} [NeZero dx] [NeZero dy] [NeZero dz]

omit [NeZero dx] [NeZero dy] [NeZero dz] in
lemma liftAlong_mulVec {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (e : ι ≃ α × β) (A : Matrix α α ℂ) (f : ι → ℂ) (p : ι) :
    (liftAlong e A).mulVec f p = ∑ a, A (e p).1 a * f (e.symm (a, (e p).2)) := by
  simp only [Matrix.mulVec, dotProduct, liftAlong, Matrix.of_apply]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Finset.sum_ite_eq]

/-- The plane wave of the torus with wave numbers `m = (m₁, m₂, m₃)`. -/
def wave3 (m : Fin dx × Fin dy × Fin dz) (p : Site3D dx dy dz) : ℂ :=
  wave dx m.1.val p.1 * (wave dy m.2.1.val p.2.1 * wave dz m.2.2.val p.2.2)

/-- The eigenvalue `cos (2π m₁/dx) + cos (2π m₂/dy) + cos (2π m₃/dz)`. -/
def lam3 (m : Fin dx × Fin dy × Fin dz) : ℂ :=
  lam dx m.1.val + lam dy m.2.1.val + lam dz m.2.2.val

/-- **The torus sends the wave `m` to the sum of the three cosines times itself.** -/
theorem T3c_mulVec_wave3 (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz)
    (m : Fin dx × Fin dy × Fin dz) : (T3c dx dy dz).mulVec (wave3 m) = lam3 m • wave3 m := by
  funext p
  obtain ⟨a, b, c⟩ := p
  have h1 := congrFun (ring_mulVec_wave hx m.1.val) a
  have h2 := congrFun (ring_mulVec_wave hy m.2.1.val) b
  have h3 := congrFun (ring_mulVec_wave hz m.2.2.val) c
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  simp only [T3c, Matrix.add_mulVec, Pi.add_apply, liftAlong_mulVec, eX, eY, eZ, wave3, lam3,
    Equiv.refl_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Pi.smul_apply, smul_eq_mul]
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  have s1 : ∑ a', ring dx a a' * (wave dx m.1.val a' * (wave dy m.2.1.val b *
      wave dz m.2.2.val c)) = (∑ a', ring dx a a' * wave dx m.1.val a') *
      (wave dy m.2.1.val b * wave dz m.2.2.val c) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  have s2 : ∑ a', ring dy b a' * (wave dx m.1.val a * (wave dy m.2.1.val a' *
      wave dz m.2.2.val c)) = (∑ a', ring dy b a' * wave dy m.2.1.val a') *
      (wave dx m.1.val a * wave dz m.2.2.val c) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  have s3 : ∑ a', ring dz c a' * (wave dx m.1.val a * (wave dy m.2.1.val b *
      wave dz m.2.2.val a')) = (∑ a', ring dz c a' * wave dz m.2.2.val a') *
      (wave dx m.1.val a * wave dy m.2.1.val b) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2, s3, h1, h2, h3]
  ring

/-- The matrix of the waves of the torus: the Kronecker product of the three Vandermonde
matrices. -/
def waves3 (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Fin dx × Fin dy × Fin dz) ℂ :=
  waves dx ⊗ₖ (waves dy ⊗ₖ waves dz)

lemma det_waves3_ne_zero : (waves3 dx dy dz).det ≠ 0 := by
  rw [waves3, Matrix.det_kronecker, Matrix.det_kronecker]
  simp [det_waves_ne_zero]

theorem T3c_mul_waves3 (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz) :
    T3c dx dy dz * waves3 dx dy dz = waves3 dx dy dz * Matrix.diagonal lam3 := by
  ext p m
  have := congrFun (T3c_mulVec_wave3 hx hy hz m) p
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, waves3, waves, Matrix.kroneckerMap_apply,
    wave3, mul_comm, mul_assoc] using this

/-- **Every eigenvalue of the three-torus is a sum of three cosines**,
`cos (2π a/dx) + cos (2π b/dy) + cos (2π c/dz)`: this is the whole spectrum. -/
theorem eq_lam3_of_eigenvector (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz) {μ : ℂ}
    {v : Site3D dx dy dz → ℂ} (hv : v ≠ 0) (hμ : (T3c dx dy dz).mulVec v = μ • v) :
    ∃ m : Fin dx × Fin dy × Fin dz, μ = lam3 m :=
  eigenvalue_of_diag (isUnit_iff_ne_zero.mpr det_waves3_ne_zero) (T3c_mul_waves3 hx hy hz) hv hμ

end Torus

end TorusSpectrum
