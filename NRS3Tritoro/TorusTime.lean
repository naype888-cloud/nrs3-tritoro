/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusArea
public import NRS3MandelstamTammCramerRao.MandelstamTamm1945

/-!
# Mandelstam–Tamm on the ring and on the three-torus

The closed transport `(A_d + S)/2` of a ring (`TorusArea.ring`) and the transport `T3c` of the
three-torus are Hermitian: they are the Hamiltonian of a free walker on the ring and on `T³`.
The Mandelstam–Tamm bound of 1945 (`MandelstamTamm1945`) therefore holds for them as it holds
on every `ℂ^d`: no state is orthogonal to itself before `π / (2 ΔE)`, the survival amplitude of
a unit state stays above `cos (ΔE t)`.

## Main results

- `TorusTime.isHermitian_ring`, `TorusTime.isHermitian_T3c` : both transports are Hermitian.
- `TorusTime.cos_le_norm_ring` : Mandelstam–Tamm on the ring.
- `TorusTime.orthogonality_time_ring` : orthogonality on the ring needs `π/2 ≤ ΔE · t`.
- `TorusTime.cos_le_norm_torus`, `TorusTime.orthogonality_time_torus` : the same on `T³`.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone MandelstamTamm1945
open PathGraph3D (Site3D)

namespace TorusTime

open TorusArea

lemma minStep_symm {d : ℕ} {i j : Fin d} : MinStep j i ↔ MinStep i j := by
  unfold MinStep
  omega

lemma seam_symm {d : ℕ} {i j : Fin d} : Seam d j i ↔ Seam d i j := by
  unfold Seam
  omega

lemma ring_comm (d : ℕ) (i j : Fin d) : ring d j i = ring d i j := by
  simp only [ring, Td, Ad, minStep_symm, seam_symm]

lemma conj_ring (d : ℕ) (i j : Fin d) : (starRingEnd ℂ) (ring d i j) = ring d i j := by
  by_cases hm : MinStep i j <;> by_cases hs : Seam d i j <;>
    simp [ring, Td, Ad, hm, hs, Complex.conj_ofReal, map_ofNat]

/-- **The closed transport of a ring is Hermitian.** -/
lemma isHermitian_ring (d : ℕ) : (ring d).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, ring_comm]
  exact conj_ring d i j

lemma isSymmetric_ring (d : ℕ) : (Matrix.toEuclideanLin (ring d)).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (isHermitian_ring d)

section Ring

variable {d : ℕ}

/-- The energy spread of a state of the ring, in the spectral weights of the closed transport. -/
abbrev ringSpread (ψ : EuclideanSpace ℂ (Fin d)) : ℝ :=
  spread (fun k => ‖inner ℂ (basis (isSymmetric_ring d) k) ψ‖ ^ 2) (energy (isSymmetric_ring d))

/-- **Mandelstam–Tamm on the ring**: `cos (ΔE t) ≤ ‖⟨ψ, ψ(t)⟩‖` for `0 ≤ ΔE t ≤ π/2`. -/
theorem cos_le_norm_ring {ψ : EuclideanSpace ℂ (Fin d)} (hψ : ‖ψ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ringSpread ψ * t ≤ Real.pi / 2) :
    Real.cos (ringSpread ψ * t) ≤ ‖inner ℂ ψ (evolve (isSymmetric_ring d) ψ t)‖ :=
  cos_le_norm_inner_evolve (isSymmetric_ring d) hψ ht0 ht

/-- **A state of the ring is not orthogonal to itself before `π / (2 ΔE)`.** -/
theorem orthogonality_time_ring {ψ : EuclideanSpace ℂ (Fin d)} (hψ : ‖ψ‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (h0 : inner ℂ ψ (evolve (isSymmetric_ring d) ψ t) = 0) :
    Real.pi / 2 ≤ ringSpread ψ * t := by
  rw [inner_evolve] at h0
  exact orthogonality_time (fun _ => sq_nonneg _) (sum_weights (isSymmetric_ring d) hψ) ht0 h0

end Ring

/-! ## The three-torus -/

section Torus

variable {dx dy dz : ℕ}

lemma isHermitian_liftAlong {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (e : ι ≃ α × β) {A : Matrix α α ℂ} (hA : A.IsHermitian) :
    (liftAlong e A).IsHermitian := by
  ext p q
  have h := congr_fun (congr_fun hA (e p).1) (e q).1
  simp only [Matrix.conjTranspose_apply, liftAlong, Matrix.of_apply, star_mul']
  rw [← h, eq_comm]
  simp only [Matrix.conjTranspose_apply, eq_comm]
  by_cases hb : (e p).2 = (e q).2 <;> simp [hb]

/-- **The transport of the three-torus is Hermitian.** -/
lemma isHermitian_T3c (dx dy dz : ℕ) : (T3c dx dy dz).IsHermitian :=
  ((isHermitian_liftAlong _ (isHermitian_ring dx)).add
    (isHermitian_liftAlong _ (isHermitian_ring dy))).add
    (isHermitian_liftAlong _ (isHermitian_ring dz))

/-- The torus transport written on `Fin (dx dy dz)`, the form on which Mandelstam–Tamm is
stated. -/
def T3cFin (dx dy dz : ℕ) : Matrix (Fin (Fintype.card (Site3D dx dy dz)))
    (Fin (Fintype.card (Site3D dx dy dz))) ℂ :=
  (T3c dx dy dz).submatrix (Fintype.equivFin (Site3D dx dy dz)).symm
    (Fintype.equivFin (Site3D dx dy dz)).symm

lemma isSymmetric_T3cFin (dx dy dz : ℕ) :
    (Matrix.toEuclideanLin (T3cFin dx dy dz)).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr ((isHermitian_T3c dx dy dz).submatrix _)

/-- **Mandelstam–Tamm on the three-torus**: `cos (ΔE t) ≤ ‖⟨ψ, ψ(t)⟩‖` for `0 ≤ ΔE t ≤ π/2`. -/
theorem cos_le_norm_torus {ψ : EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz)))}
    (hψ : ‖ψ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : spread (fun k => ‖inner ℂ (basis (isSymmetric_T3cFin dx dy dz) k) ψ‖ ^ 2)
      (energy (isSymmetric_T3cFin dx dy dz)) * t ≤ Real.pi / 2) :
    Real.cos (spread (fun k => ‖inner ℂ (basis (isSymmetric_T3cFin dx dy dz) k) ψ‖ ^ 2)
      (energy (isSymmetric_T3cFin dx dy dz)) * t) ≤
      ‖inner ℂ ψ (evolve (isSymmetric_T3cFin dx dy dz) ψ t)‖ :=
  cos_le_norm_inner_evolve (isSymmetric_T3cFin dx dy dz) hψ ht0 ht

/-- **A state of the three-torus is not orthogonal to itself before `π / (2 ΔE)`.** -/
theorem orthogonality_time_torus {ψ : EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz)))}
    (hψ : ‖ψ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (h0 : inner ℂ ψ (evolve (isSymmetric_T3cFin dx dy dz) ψ t) = 0) :
    Real.pi / 2 ≤ spread (fun k => ‖inner ℂ (basis (isSymmetric_T3cFin dx dy dz) k) ψ‖ ^ 2)
      (energy (isSymmetric_T3cFin dx dy dz)) * t := by
  rw [inner_evolve] at h0
  exact orthogonality_time (fun _ => sq_nonneg _)
    (sum_weights (isSymmetric_T3cFin dx dy dz) hψ) ht0 h0

end Torus

end TorusTime
