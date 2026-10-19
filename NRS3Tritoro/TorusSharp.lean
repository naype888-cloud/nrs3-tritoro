/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusSpectrum
public import NRS3Tritoro.TorusSpeed

/-!
# The speed limits of the ring and of the torus are attained

With an even number of positions the ring has the eigenvalues `1` (the uniform wave) and `-1`
(the alternating wave). The state `(u + w)/√2` of the two waves is two equal branches of energies
`±1`, and the Mandelstam–Tamm bound is attained by two equal branches: its survival amplitude is
`cos t`, which vanishes at `t = π/2`. So `π/2` of `TorusSpeed` is the exact orthogonality time
of the ring. On `T³` the uniform wave has energy `3` and the checkerboard `-3`, the amplitude
is `cos 3t`, and `π/6` is exact.

## Main results

- `TorusSharp.evolve_eigenvector` : an eigenvector only gets a phase.
- `TorusSharp.inner_evolve_two_branches` : the amplitude of `(u + w)/√2` is `(e^(-iE₁t) +
  e^(-iE₂t))/2`.
- `TorusSharp.ring_orthogonality_exact` : on an even ring, a unit state is orthogonal to itself
  at `t = π/2`, and at no earlier time.
-/

@[expose] public noncomputable section

open MandelstamTamm1945 Complex

namespace TorusSharp

section General

variable {n : ℕ} {H : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)}
  (hH : H.IsSymmetric)

include hH

/-- Eigenvectors of different eigenvalues of a symmetric operator are orthogonal. -/
lemma inner_eq_zero_of_eigenvalues {u w : EuclideanSpace ℂ (Fin n)} {E₁ E₂ : ℝ}
    (hu : H u = (E₁ : ℂ) • u) (hw : H w = (E₂ : ℂ) • w) (hne : E₁ ≠ E₂) :
    inner ℂ u w = 0 := by
  have h := hH u w
  rw [hu, hw, inner_smul_left, inner_smul_right] at h
  simp only [Complex.conj_ofReal] at h
  have : ((E₁ : ℂ) - E₂) * inner ℂ u w = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hne))

/-- **An eigenvector only gets a phase**: `ψ(t) = e^(-iEt) ψ`. -/
theorem evolve_eigenvector {v : EuclideanSpace ℂ (Fin n)} {E : ℝ} (hv : H v = (E : ℂ) • v)
    (t : ℝ) : evolve hH v t = phase (fun _ : Fin 1 => E) 0 t • v := by
  unfold evolve
  have h : ∀ k, phase (energy hH) k t * inner ℂ (basis hH k) v =
      phase (fun _ : Fin 1 => E) 0 t * inner ℂ (basis hH k) v := by
    intro k
    by_cases hk : energy hH k = E
    · simp [phase, hk]
    · have := inner_eq_zero_of_eigenvalues hH (hH.apply_eigenvectorBasis finrank_euclideanSpace_fin k) hv hk
      simp [this]
  simp only [h, mul_smul, ← Finset.smul_sum]
  congr 1
  exact (basis hH).sum_repr' v

omit hH in
/-- The evolution is additive and homogeneous in the state. -/
theorem evolve_add_smul (hH : H.IsSymmetric) (a b : ℂ) (x y : EuclideanSpace ℂ (Fin n)) (t : ℝ) :
    evolve hH (a • x + b • y) t = a • evolve hH x t + b • evolve hH y t := by
  simp only [evolve, inner_add_right, inner_smul_right, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [← add_smul]; congr 1; ring

/-- **Two equal branches of energies `±E`**: the amplitude of `(u + w)/√2`, for orthonormal
eigenvectors `u`, `w` of energies `E` and `-E`, is `cos (E t)`. -/
theorem inner_evolve_two_branches {u w : EuclideanSpace ℂ (Fin n)} {E : ℝ} (hE : 0 < E)
    (hu : H u = (E : ℂ) • u) (hw : H w = ((-E : ℝ) : ℂ) • w) (hu1 : ‖u‖ = 1) (hw1 : ‖w‖ = 1)
    (t : ℝ) :
    inner ℂ (((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w)
        (evolve hH (((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w) t) =
      (Real.cos (E * t) : ℂ) := by
  have h0 : inner ℂ u w = 0 := inner_eq_zero_of_eigenvalues hH hu hw (by linarith)
  have h0' : inner ℂ w u = 0 := by rw [← inner_conj_symm, h0, map_zero]
  rw [evolve_add_smul hH, evolve_eigenvector hH hu, evolve_eigenvector hH hw]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h0, h0',
    inner_self_eq_norm_sq_to_K, hu1, hw1]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [phase, map_div₀, map_one, Complex.conj_ofReal]
  rw [Complex.ofReal_cos, Complex.cos]
  field_simp
  have e1 : cexp (↑(-(E * t)) * I) = cexp (-(I * ↑(E * t))) := by congr 1; push_cast; ring
  rw [e1, h2]
  ring

/-- **The state `(u + w)/√2` is a unit**, and at `t = π / (2E)` it is orthogonal to its
evolution. -/
theorem two_branches_orthogonal {u w : EuclideanSpace ℂ (Fin n)} {E : ℝ} (hE : 0 < E)
    (hu : H u = (E : ℂ) • u) (hw : H w = ((-E : ℝ) : ℂ) • w) (hu1 : ‖u‖ = 1) (hw1 : ‖w‖ = 1) :
    ∃ ψ : EuclideanSpace ℂ (Fin n), ‖ψ‖ = 1 ∧
      inner ℂ ψ (evolve hH ψ (Real.pi / (2 * E))) = 0 := by
  refine ⟨((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w, ?_, ?_⟩
  · have h0 : inner ℂ u w = 0 := inner_eq_zero_of_eigenvalues hH hu hw (by linarith)
    have h0' : inner ℂ w u = 0 := by rw [← inner_conj_symm, h0, map_zero]
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hu2 : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu1]; norm_num
    have hw2 : inner ℂ w w = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; norm_num
    have h3 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have h : inner ℂ (((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w)
        (((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w) = 1 := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h0, h0',
        hu2, hw2, map_div₀, map_one, Complex.conj_ofReal]
      field_simp
      rw [h2]; norm_num
    rw [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w‖ ^ 2 = 1 := by
      have h1 : (((‖((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w‖ ^ 2 : ℝ)) : ℂ) =
          ((1 : ℝ) : ℂ) := by push_cast; exact h
      exact Complex.ofReal_injective h1
    nlinarith [norm_nonneg (((1 : ℂ) / Real.sqrt 2) • u + ((1 : ℂ) / Real.sqrt 2) • w)]
  · rw [inner_evolve_two_branches hH hE hu hw hu1 hw1]
    have : E * (Real.pi / (2 * E)) = Real.pi / 2 := by field_simp
    rw [this, Real.cos_pi_div_two]; simp

end General

/-! ## The ring -/

section Ring

open TorusSpectrum TorusArea TorusTime

variable {d : ℕ}

lemma norm_zeta : ‖zeta d‖ = 1 := by
  have : zeta d = exp (((2 * Real.pi / d : ℝ) : ℂ) * I) := by
    rw [zeta]; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_wave (m : ℕ) (j : Fin d) : ‖wave d m j‖ = 1 := by
  rw [wave, norm_pow, norm_zeta, one_pow]

/-- The wave `m`, normalized, as a state of the ring. -/
def waveState (d m : ℕ) : EuclideanSpace ℂ (Fin d) :=
  ((1 : ℂ) / Real.sqrt d) • WithLp.toLp 2 (wave d m)

lemma norm_waveState (hd : 0 < d) (m : ℕ) : ‖waveState d m‖ = 1 := by
  have h : ‖(WithLp.toLp 2 (wave d m) : EuclideanSpace ℂ (Fin d))‖ = Real.sqrt d := by
    rw [EuclideanSpace.norm_eq]
    simp only [norm_wave, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  rw [waveState, norm_smul, h]
  simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  field_simp

lemma ring_waveState (hd : 3 ≤ d) [NeZero d] (m : ℕ) :
    Matrix.toEuclideanLin (ring d) (waveState d m) =
      ((Real.cos (2 * Real.pi * m / d) : ℝ) : ℂ) • waveState d m := by
  have h : Matrix.toEuclideanLin (ring d) (WithLp.toLp 2 (wave d m)) =
      ((Real.cos (2 * Real.pi * m / d) : ℝ) : ℂ) • (WithLp.toLp 2 (wave d m) :
        EuclideanSpace ℂ (Fin d)) := by
    ext j
    exact congrFun (ring_mulVec_wave hd m) j
  rw [waveState, map_smul, h, smul_comm]

/-- **On an even ring `π/2` is exact**: the uniform wave has energy `1` and the alternating wave
`-1`; the state of the two equal branches is orthogonal to its evolution at `t = π/2`. With
`TorusSpeed.pi_div_two_le_time_ring`, no unit state does it sooner. -/
theorem ring_orthogonality_exact (hd : 3 ≤ d) (he : Even d) :
    ∃ ψ : EuclideanSpace ℂ (Fin d), ‖ψ‖ = 1 ∧
      inner ℂ ψ (evolve (isSymmetric_ring d) ψ (Real.pi / 2)) = 0 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨k, hk⟩ := he
  have hd0 : 0 < d := by omega
  have hdk : (d : ℝ) = 2 * k := by rw [hk]; push_cast; ring
  have hk0 : (0 : ℝ) < k := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hu : Matrix.toEuclideanLin (ring d) (waveState d 0) = ((1 : ℝ) : ℂ) • waveState d 0 := by
    rw [ring_waveState hd]; simp
  have hw : Matrix.toEuclideanLin (ring d) (waveState d k) = ((-1 : ℝ) : ℂ) • waveState d k := by
    rw [ring_waveState hd]
    have : 2 * Real.pi * k / d = Real.pi := by rw [hdk]; field_simp
    rw [this, Real.cos_pi]
  have := two_branches_orthogonal (isSymmetric_ring d) one_pos hu hw (norm_waveState hd0 0)
    (norm_waveState hd0 k)
  simpa using this

end Ring

/-! ## The three-torus -/

section Torus

open TorusSpectrum TorusArea TorusTime
open PathGraph3D (Site3D)

variable {dx dy dz : ℕ} [NeZero dx] [NeZero dy] [NeZero dz]

omit [NeZero dx] [NeZero dy] [NeZero dz] in
lemma norm_wave3 (m : Fin dx × Fin dy × Fin dz) (p : Site3D dx dy dz) : ‖wave3 m p‖ = 1 := by
  simp [wave3, norm_wave]

/-- The wave `m` of the torus, normalized, as a state on `Fin (dx dy dz)`. -/
def wave3State (m : Fin dx × Fin dy × Fin dz) :
    EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz))) :=
  ((1 : ℂ) / Real.sqrt (Fintype.card (Site3D dx dy dz))) •
    WithLp.toLp 2 (fun j => wave3 m ((Fintype.equivFin (Site3D dx dy dz)).symm j))

lemma norm_wave3State (m : Fin dx × Fin dy × Fin dz) : ‖wave3State m‖ = 1 := by
  have hN : 0 < Fintype.card (Site3D dx dy dz) := Fintype.card_pos
  have h : ‖(WithLp.toLp 2 (fun j => wave3 m ((Fintype.equivFin (Site3D dx dy dz)).symm j)) :
      EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz))))‖ =
      Real.sqrt (Fintype.card (Site3D dx dy dz)) := by
    rw [EuclideanSpace.norm_eq]
    simp only [norm_wave3, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hs : 0 < Real.sqrt (Fintype.card (Site3D dx dy dz)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hN)
  rw [wave3State, norm_smul, h]
  simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  field_simp

lemma T3cFin_wave3State (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz) (m : Fin dx × Fin dy × Fin dz) :
    Matrix.toEuclideanLin (T3cFin dx dy dz) (wave3State m) =
      (lam3 m) • wave3State m := by
  have h : Matrix.toEuclideanLin (T3cFin dx dy dz)
      (WithLp.toLp 2 (fun j => wave3 m ((Fintype.equivFin (Site3D dx dy dz)).symm j))) =
      (lam3 m) • (WithLp.toLp 2 (fun j => wave3 m ((Fintype.equivFin (Site3D dx dy dz)).symm j)) :
        EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz)))) := by
    ext j
    have := congrFun (T3c_mulVec_wave3 hx hy hz m) ((Fintype.equivFin (Site3D dx dy dz)).symm j)
    simpa [T3cFin, Matrix.mulVec, dotProduct, Function.comp_def] using this
  rw [wave3State, map_smul, h, smul_comm]

omit [NeZero dx] [NeZero dy] [NeZero dz] in
/-- **On an even three-torus `π/6` is exact**: the uniform wave has energy `3` and the
checkerboard `-3`; the state of the two equal branches is orthogonal to its evolution at
`t = π/6`. With `TorusSpeed.pi_div_six_le_time_torus`, no unit state does it sooner. -/
theorem torus_orthogonality_exact (hx : 3 ≤ dx) (hy : 3 ≤ dy) (hz : 3 ≤ dz) (ex : Even dx)
    (ey : Even dy) (ez : Even dz) :
    ∃ ψ : EuclideanSpace ℂ (Fin (Fintype.card (Site3D dx dy dz))), ‖ψ‖ = 1 ∧
      inner ℂ ψ (evolve (isSymmetric_T3cFin dx dy dz) ψ (Real.pi / 6)) = 0 := by
  have : NeZero dx := ⟨by omega⟩
  have : NeZero dy := ⟨by omega⟩
  have : NeZero dz := ⟨by omega⟩
  obtain ⟨a, ha⟩ := ex
  obtain ⟨b, hb⟩ := ey
  obtain ⟨c, hc⟩ := ez
  have hcos : ∀ {d k : ℕ}, d = k + k → 0 < d →
      Real.cos (2 * Real.pi * k / d) = -1 := fun {d k} h hd => by
    have hd' : (d : ℝ) = 2 * k := by rw [h]; push_cast; ring
    have hk : (0 : ℝ) < k := by
      have : 0 < k := by omega
      exact_mod_cast this
    have : 2 * Real.pi * k / d = Real.pi := by rw [hd']; field_simp
    rw [this, Real.cos_pi]
  have ha' : a < dx := by omega
  have hb' : b < dy := by omega
  have hc' : c < dz := by omega
  have hu : Matrix.toEuclideanLin (T3cFin dx dy dz) (wave3State (⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩)) =
      ((3 : ℝ) : ℂ) • wave3State (⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩) := by
    rw [T3cFin_wave3State hx hy hz]
    simp [lam3, lam]
    norm_num
  have hw : Matrix.toEuclideanLin (T3cFin dx dy dz) (wave3State (⟨a, ha'⟩, ⟨b, hb'⟩, ⟨c, hc'⟩)) =
      ((-3 : ℝ) : ℂ) • wave3State (⟨a, ha'⟩, ⟨b, hb'⟩, ⟨c, hc'⟩) := by
    rw [T3cFin_wave3State hx hy hz]
    simp only [lam3, lam, hcos ha (by omega), hcos hb (by omega), hcos hc (by omega)]
    push_cast
    norm_num
  have := two_branches_orthogonal (isSymmetric_T3cFin dx dy dz) (by norm_num : (0 : ℝ) < 3) hu hw
    (norm_wave3State _) (norm_wave3State _)
  have e : Real.pi / (2 * 3) = Real.pi / 6 := by norm_num
  rwa [e] at this

end Torus

end TorusSharp
