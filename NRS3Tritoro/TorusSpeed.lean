/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusTime
public import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# The energy spread of the ring is at most `1`

Every row of the closed transport `(A_d + S)/2` of a ring has two links of weight `1/2`: the
first and the last position meet through the seam, every other position through its two
neighbours. By Gershgorin every eigenvalue has modulus at most `1`, so the energy spread of
every state satisfies `ΔE ≤ 1`, and Mandelstam–Tamm gives a time that no longer depends on the
state: no unit state of the ring is orthogonal to itself before `t = π/2`.

## Main results

- `TorusSpeed.row_sum_le_one` : `∑ⱼ ‖ring d i j‖ ≤ 1`.
- `TorusSpeed.abs_energy_le_one` : every eigenvalue of the ring has modulus at most `1`.
- `TorusSpeed.spread_le` : a spread of energies in `[-B, B]` is at most `B`.
- `TorusSpeed.ringSpread_le_one` : `ΔE ≤ 1` for every state of the ring.
- `TorusSpeed.pi_div_two_le_time_ring` : orthogonality on the ring needs `t ≥ π/2`.
- `TorusSpeed.abs_energy_torus_le_three`, `TorusSpeed.pi_div_six_le_time_torus` : on `T³` the
  rows sum to `3`, so `|E| ≤ 3` and orthogonality needs `t ≥ π/6`.
-/

@[expose] public noncomputable section

open TransportPosition MandelstamTamm1945 TorusArea TorusTime

namespace TorusSpeed

variable {d : ℕ}

lemma ring_eq_half (hd : 3 ≤ d) (i j : Fin d) :
    ring d i j = if MinStep i j ∨ Seam d i j then 1 / 2 else 0 := by
  have hr : (rho d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (rho_pos d (by omega)).ne'
  by_cases hm : MinStep i j
  · have := not_seam_of_minStep hd hm
    simp [ring, Td, Ad, hm, this]
    field_simp
  · by_cases hs : Seam d i j <;> simp [ring, Td, Ad, hm, hs]

/-- At most two positions are linked to a given one. -/
lemma card_links_le_two (hd : 3 ≤ d) (i : Fin d) :
    (Finset.univ.filter fun j : Fin d => MinStep i j ∨ Seam d i j).card ≤ 2 := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v : ℕ, ∀ j : Fin d, (MinStep i j ∨ Seam d i j) → j.val = u ∨ j.val = v := by
    by_cases h0 : i.val = 0
    · exact ⟨1, d - 1, fun j hj => by unfold MinStep Seam at hj; omega⟩
    · by_cases hl : i.val + 1 = d
      · exact ⟨d - 2, 0, fun j hj => by unfold MinStep Seam at hj; omega⟩
      · exact ⟨i.val - 1, i.val + 1, fun j hj => by unfold MinStep Seam at hj; omega⟩
  calc _ ≤ ({u, v} : Finset ℕ).card :=
        Finset.card_le_card_of_injOn (fun j : Fin d => j.val)
          (fun j hj => by
            have := huv j (Finset.mem_filter.mp hj).2
            simpa using this)
          (fun a _ b _ h => Fin.ext h)
    _ ≤ 2 := Finset.card_le_two

/-- **Every row of the closed transport sums to at most `1`.** -/
theorem row_sum_le_one (hd : 3 ≤ d) (i : Fin d) : ∑ j, ‖ring d i j‖ ≤ 1 := by
  classical
  have : ∀ j, ‖ring d i j‖ = if MinStep i j ∨ Seam d i j then 1 / 2 else 0 := fun j => by
    rw [ring_eq_half hd]
    split_ifs <;> simp
  simp only [this, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have := card_links_le_two hd i
  have h2 : ((Finset.univ.filter fun j : Fin d => MinStep i j ∨ Seam d i j).card : ℝ) ≤ 2 := by
    exact_mod_cast this
  linarith

lemma ring_diag (hd : 3 ≤ d) (k : Fin d) : ring d k k = 0 := by
  rw [ring_eq_half hd, ite_eq_right_iff]
  intro h
  exfalso
  revert h
  unfold MinStep Seam
  omega

/-- **Every eigenvalue of the ring has modulus at most `1`** (Gershgorin). -/
theorem abs_energy_le_one (hd : 3 ≤ d) (k : Fin d) :
    |energy (isSymmetric_ring d) k| ≤ 1 := by
  set hH := isSymmetric_ring d
  set μ := energy hH k
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (ring d)) (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (basis hH k).ofLp) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      have h := congrArg WithLp.ofLp (hH.apply_eigenvectorBasis (finrank_euclideanSpace_fin) k)
      exact h
    · exact fun h => (basis hH).orthonormal.ne_zero k (by ext i; simpa using congrFun h i)
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, ring_diag hd, dist_zero_right, Complex.norm_real,
    Real.norm_eq_abs] at hi
  refine hi.trans ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    fun _ _ _ => norm_nonneg _) (row_sum_le_one hd i)

/-- **Energies in `[-B, B]` have spread at most `B`**, for every probability weights. -/
theorem spread_le {n : ℕ} {p E : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B) (hp : ∀ k, 0 ≤ p k)
    (h1 : ∑ k, p k = 1) (hE : ∀ k, |E k| ≤ B) : spread p E ≤ B := by
  refine Real.sqrt_le_iff.mpr ⟨hB, ?_⟩
  have e : ∀ k, p k * (E k - mean p E) ^ 2 =
      p k * E k ^ 2 - 2 * mean p E * (p k * E k) + mean p E ^ 2 * p k := fun k => by ring
  have hm : ∑ k, p k * E k = mean p E := rfl
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, hm]
  have h2 : ∑ k, p k * E k ^ 2 ≤ B ^ 2 := by
    calc ∑ k, p k * E k ^ 2 ≤ ∑ k, p k * B ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
            (by nlinarith [abs_nonneg (E k), hE k, sq_abs (E k)]) (hp k)
      _ = B ^ 2 := by simp [← Finset.sum_mul, h1]
  nlinarith [sq_nonneg (mean p E)]

/-- **`ΔE ≤ 1` for every state of the ring.** -/
theorem ringSpread_le_one (hd : 3 ≤ d) {ψ : EuclideanSpace ℂ (Fin d)} (hψ : ‖ψ‖ = 1) :
    ringSpread ψ ≤ 1 :=
  spread_le zero_le_one (fun _ => sq_nonneg _) (sum_weights (isSymmetric_ring d) hψ)
    (abs_energy_le_one hd)

/-- **No unit state of the ring is orthogonal to itself before `t = π/2`**, whatever the state:
the speed limit of the ring does not depend on it. -/
theorem pi_div_two_le_time_ring (hd : 3 ≤ d) {ψ : EuclideanSpace ℂ (Fin d)} (hψ : ‖ψ‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (h0 : inner ℂ ψ (evolve (isSymmetric_ring d) ψ t) = 0) :
    Real.pi / 2 ≤ t :=
  (orthogonality_time_ring hψ ht0 h0).trans
    (mul_le_of_le_one_left ht0 (ringSpread_le_one hd hψ))

/-! ## The three-torus -/

section Torus

open PathGraph3D (Site3D)
open PathGraph3DNRS

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq α]
  [DecidableEq β]

omit [DecidableEq ι] [DecidableEq α] in
/-- A lifted operator keeps the row sums of the axis. -/
lemma row_sum_liftAlong (e : ι ≃ α × β) (A : Matrix α α ℂ) (p : ι) :
    ∑ q, ‖liftAlong e A p q‖ = ∑ a, ‖A (e p).1 a‖ := by
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [liftAlong, apply_ite norm, Finset.sum_ite_eq]

omit [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq α] in
lemma liftAlong_diag (e : ι ≃ α × β) {A : Matrix α α ℂ} (hA : ∀ a, A a a = 0) (p : ι) :
    liftAlong e A p p = 0 := by
  simp [liftAlong, hA]

variable {dx dy dz : ℕ}

/-- **Every row of the torus transport sums to at most `3`**: one per axis. -/
theorem row_sum_T3c_le_three (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz) (p : Site3D dx dy dz) :
    ∑ q, ‖T3c dx dy dz p q‖ ≤ 3 := by
  have h : ∀ q, ‖T3c dx dy dz p q‖ ≤ ‖liftAlong (eX dx dy dz) (ring dx) p q‖ +
      ‖liftAlong (eY dx dy dz) (ring dy) p q‖ + ‖liftAlong (eZ dx dy dz) (ring dz) p q‖ :=
    fun q => by
      simp only [T3c, Matrix.add_apply]
      exact (norm_add₃_le).trans_eq rfl
  refine (Finset.sum_le_sum fun q _ => h q).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, row_sum_liftAlong, row_sum_liftAlong,
    row_sum_liftAlong]
  linarith [row_sum_le_one hx (eX dx dy dz p).1, row_sum_le_one hy (eY dx dy dz p).1,
    row_sum_le_one hz (eZ dx dy dz p).1]

lemma T3c_diag (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz) (p : Site3D dx dy dz) :
    T3c dx dy dz p p = 0 := by
  simp only [T3c, Matrix.add_apply, liftAlong_diag _ (ring_diag hx), liftAlong_diag _ (ring_diag hy),
    liftAlong_diag _ (ring_diag hz), add_zero]

/-- **Every eigenvalue of the three-torus has modulus at most `3`** (Gershgorin). -/
theorem abs_energy_torus_le_three (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz)
    (k : Fin (Fintype.card (Site3D dx dy dz))) :
    |energy (isSymmetric_T3cFin dx dy dz) k| ≤ 3 := by
  set hH := isSymmetric_T3cFin dx dy dz
  set μ := energy hH k
  have hev : Module.End.HasEigenvalue (Matrix.toLin' (T3cFin dx dy dz)) (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (basis hH k).ofLp) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      have h := congrArg WithLp.ofLp (hH.apply_eigenvectorBasis (finrank_euclideanSpace_fin) k)
      exact h
    · exact fun h => (basis hH).orthonormal.ne_zero k (by ext i; simpa using congrFun h i)
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hev
  have hd : T3cFin dx dy dz i i = 0 := T3c_diag hx hy hz _
  rw [Metric.mem_closedBall, hd, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hi
  refine hi.trans ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    fun _ _ _ => norm_nonneg _) ?_
  have := row_sum_T3c_le_three hx hy hz ((Fintype.equivFin (Site3D dx dy dz)).symm i)
  rwa [← Equiv.sum_comp (Fintype.equivFin (Site3D dx dy dz)).symm] at this

/-- **No unit state of the three-torus is orthogonal to itself before `t = π/6`**, whatever the
state. -/
theorem pi_div_six_le_time_torus (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz)
    {ψ : EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz)))} (hψ : ‖ψ‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (h0 : inner ℂ ψ (evolve (isSymmetric_T3cFin dx dy dz) ψ t) = 0) :
    Real.pi / 6 ≤ t := by
  have hs := spread_le (by norm_num : (0 : ℝ) ≤ 3) (fun _ => sq_nonneg _)
    (sum_weights (isSymmetric_T3cFin dx dy dz) hψ) (abs_energy_torus_le_three hx hy hz)
  have h := orthogonality_time_torus hψ ht0 h0
  have := mul_le_mul_of_nonneg_right hs ht0
  linarith [Real.pi_pos]

end Torus

end TorusSpeed
