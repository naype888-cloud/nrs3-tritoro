/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.OpenDiracVelocity
public import NRS3Tritoro.DiracSpeed
public import NavaRobertsonIndependent.Mathematics.D23d_BandWidth
public import NavaRobertsonIndependent.Mathematics.D49b_RobertsonDeterminant3D
public import NavaRobertsonIndependent.Mathematics.D23f_MinUncertaintyTensionFour

/-!
# The dispersion of the transport in a Dirac state

`OpenDiracVelocity` shows that a stationary Dirac state has mean current `0`. The transport does
not vanish with it: it fluctuates, and the fluctuation is fixed by the mass. Let `A` and `B` be
symmetric and anticommute, `‖Bχ‖² = m² ‖χ‖²`, and `(A + B) ψ = E ψ` with `‖ψ‖ = 1`. Put
`a = ‖A ψ‖²`. Then

* `E² = a + m²`, and `Re ⟨A ψ, B ψ⟩ = 0` because `A` and `B` anticommute;
* `E ψ = A ψ + B ψ` gives `E ⟨A⟩ = ⟨ψ, A (A ψ + B ψ)⟩ = a + ⟨A ψ, B ψ⟩`, so `E ⟨A⟩ = a`;
* `Var A = a − ⟨A⟩² = a − a²/E² = a m² / (a + m²)`.

On the open axis `A = T_d` has `a ≤ 1`, so the dispersion of the transport is at most
`m²/(1 + m²)`. It is positive as soon as `T_d ψ ≠ 0`, and it never closes: the transport of a
stationary massive state keeps its fluctuation.

## Main results

- `OpenDiracDispersion.variance_mul_energy_sq` : `Var A · (a + m²) = a m²`, for any Hilbert space.
- `OpenDiracDispersion.variance_mul_Td_dirac` : `Var T_d · (a + m²) = a m²` for an eigenvector of
  `D_m`.
- `OpenDiracDispersion.variance_Td_dirac_le` : `Var T_d ≤ m² / (1 + m²)`.
- `OpenDiracDispersion.variance_Td_dirac_ge` : with a gap `‖T_d χ‖² ≥ μ² ‖χ‖²`,
  `Var T_d ≥ μ² m² / (μ² + m²)`.
- `OpenDiracDispersion.gap_TdOp_four` : `T_4` has a gap, `((3 − √5)/2)² ‖χ‖² ≤ ‖T_4 χ‖²`
  (smallest eigenvalue in modulus `φ⁻²`).
- `OpenDiracDispersion.variance_T_four_dirac` : on `d = 4`,
  `c² m²/(c² + m²) ≤ Var T_4 ≤ m²/(1 + m²)` with `c = (3 − √5)/2`.
- `OpenDiracDispersion.kinetic_chirality_anticomm`, `OpenDiracDispersion.chirality_sq` : on the
  open cube, `K ε + ε K = 0` and `ε² = 1`, for the kinetic part `K = T_x + σ_x T_y + σ_x σ_y T_z`
  and `ε = σ_x σ_y σ_z` of `OpenDirac.dirac`.
- `OpenDiracDispersion.dispersion_kinetic_dirac` : the same identity on the open cube of any
  size: `(‖K ψ‖² − ⟨K⟩²)(‖K ψ‖² + m²) = ‖K ψ‖² m²` for a unit eigenvector of `D_m`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition NRSInequality BandWidth PathGraph3DNRS
open PathGraph3D (Site3D)

namespace OpenDiracDispersion

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {A B : H →ₗ[ℂ] H}

/-- **Dispersion of an eigenvector of `A + B`.** For symmetric anticommuting `A`, `B` with
`‖Bχ‖² = m² ‖χ‖²`, a unit eigenvector `(A + B) ψ = E ψ` has `E ⟨A⟩ = ‖A ψ‖²`, hence
`(‖A ψ‖² − ⟨A⟩²) (‖A ψ‖² + m²) = ‖A ψ‖² m²`. -/
theorem variance_mul_energy_sq (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : ∀ χ, A (B χ) = -B (A χ)) {m : ℝ} (hBm : ∀ χ, ‖B χ‖ ^ 2 = m ^ 2 * ‖χ‖ ^ 2)
    {E : ℝ} {ψ : H} (hψ : ‖ψ‖ = 1) (hE : A ψ + B ψ = (E : ℂ) • ψ) :
    (‖A ψ‖ ^ 2 - (inner ℂ ψ (A ψ)).re ^ 2) * (‖A ψ‖ ^ 2 + m ^ 2) = ‖A ψ‖ ^ 2 * m ^ 2 := by
  set a := ‖A ψ‖ ^ 2
  set μ := (inner ℂ ψ (A ψ)).re
  have hb : ‖B ψ‖ ^ 2 = m ^ 2 := by simpa [hψ] using hBm ψ
  have hE2 : E ^ 2 = a + m ^ 2 := by
    have h := DiracSpeed.norm_sq_add_of_anticomm hA hB hAB ψ
    rw [hE, norm_smul, Complex.norm_real, Real.norm_eq_abs, hψ, mul_one, sq_abs, hb] at h
    exact h
  -- `Re ⟨A ψ, B ψ⟩ = 0`
  have h0 : (inner ℂ (A ψ) (B ψ)).re = 0 := by
    have h1 : inner ℂ (A ψ) (B ψ) = inner ℂ ψ (A (B ψ)) := hA ψ (B ψ)
    have h2 : inner ℂ (B ψ) (A ψ) = inner ℂ ψ (B (A ψ)) := hB ψ (A ψ)
    have h3 : inner ℂ (B ψ) (A ψ) = (starRingEnd ℂ) (inner ℂ (A ψ) (B ψ)) :=
      (inner_conj_symm (B ψ) (A ψ)).symm
    rw [hAB, inner_neg_right, ← h2, h3] at h1
    have := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at this
    linarith
  -- `E ⟨A⟩ = a`
  have hEμ : E * μ = a := by
    have hEψ : (E : ℂ) • A ψ = A (A ψ) + A (B ψ) := by
      rw [← map_smul, ← hE, map_add]
    have h1 : (E : ℂ) * inner ℂ ψ (A ψ) = inner ℂ (A ψ) (A ψ) + inner ℂ (A ψ) (B ψ) := by
      rw [← inner_smul_right, hEψ, inner_add_right, ← hA ψ (A ψ), ← hA ψ (B ψ)]
    have h2 := congrArg Complex.re h1
    have hself : inner ℂ (A ψ) (A ψ) = ((‖A ψ‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [Complex.re_ofReal_mul, Complex.add_re, h0, hself, Complex.ofReal_re, add_zero] at h2
    exact h2
  have hm : 0 ≤ a := by positivity
  have : (a - μ ^ 2) * (a + m ^ 2) = a * m ^ 2 := by
    rw [← hE2]
    have : (a - μ ^ 2) * E ^ 2 = a * E ^ 2 - (E * μ) ^ 2 := by ring
    rw [this, hEμ]
    nlinarith only [hE2]
  exact this

end Abstract

section Axis

variable {d : ℕ}

/-- `Var T_d = ‖T_d ψ‖² − ⟨T_d⟩²` on a unit state. -/
theorem variance_eq (A : Hd d →ₗ[ℂ] Hd d) {ψ : Hd d} (hψ : ‖ψ‖ = 1) :
    variance A ψ = ‖A ψ‖ ^ 2 - (inner ℂ ψ (A ψ)).re ^ 2 := by
  have hcross : (inner ℂ (A ψ) ψ).re = (inner ℂ ψ (A ψ)).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) (A ψ) ψ, Complex.conj_re]
  unfold variance centered mean
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex, norm_smul, inner_smul_right, Complex.norm_real,
    Real.norm_eq_abs, hψ, mul_one, sq_abs, Complex.re_ofReal_mul, hcross]
  ring

open OpenDiracVelocity

/-- `σ` is an isometry: `‖σ χ‖² = ‖χ‖²`. -/
theorem norm_sq_staggerOp (χ : Hd d) : ‖staggerOp d χ‖ ^ 2 = ‖χ‖ ^ 2 := by
  have h : staggerOp d (staggerOp d χ) = χ := by
    simp only [staggerOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      OpenDirac.stagger_mul_self, Matrix.one_mulVec]
  have h1 := staggerOp_isSymmetric d (staggerOp d χ) χ
  rw [h] at h1
  have h3 : (inner ℂ (staggerOp d χ) (staggerOp d χ)).re = ‖staggerOp d χ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) (staggerOp d χ)
  have h4 : (inner ℂ χ χ).re = ‖χ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) χ
  rw [← h3, ← h4]
  exact (congrArg Complex.re h1).symm

/-- `T_d` and `σ` anticommute, as operators. -/
theorem TdOp_staggerOp (χ : Hd d) : TdOp d (staggerOp d χ) = -staggerOp d (TdOp d χ) := by
  have h : Td d * OpenDirac.stagger d = -(OpenDirac.stagger d * Td d) := by
    rw [OpenDirac.stagger_mul_Td, neg_neg]
  simp only [TdOp, staggerOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
    h, Matrix.neg_mulVec]
  rfl

/-- **The dispersion of the transport in a stationary Dirac state**: for a unit eigenvector of
`D_m = T_d + m σ` and `a = ‖T_d ψ‖²`, `Var T_d · (a + m²) = a m²`. -/
theorem variance_mul_Td_dirac (m : ℝ) {E : ℝ} {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (hE : diracOp d m ψ = (E : ℂ) • ψ) :
    variance (TdOp d) ψ * (‖TdOp d ψ‖ ^ 2 + m ^ 2) = ‖TdOp d ψ‖ ^ 2 * m ^ 2 := by
  have hB : ((m : ℂ) • staggerOp d).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [staggerOp_isSymmetric d x y]
  have hAB : ∀ χ, TdOp d (((m : ℂ) • staggerOp d) χ) = -((m : ℂ) • staggerOp d) (TdOp d χ) := by
    intro χ
    simp only [LinearMap.smul_apply, map_smul, TdOp_staggerOp, smul_neg]
  have hBm : ∀ χ, ‖((m : ℂ) • staggerOp d) χ‖ ^ 2 = m ^ 2 * ‖χ‖ ^ 2 := by
    intro χ
    simp only [LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, norm_sq_staggerOp]
  rw [variance_eq (TdOp d) hψ]
  exact variance_mul_energy_sq (TdOp_isSymmetric d) hB hAB hBm hψ hE

/-- The dispersion of the transport is at most `m`-squared: `Var T_d ≤ m²` for `m ≠ 0`. -/
theorem variance_Td_dirac_le_sq {m : ℝ} (hm : m ≠ 0) {E : ℝ} {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (hE : diracOp d m ψ = (E : ℂ) • ψ) : variance (TdOp d) ψ ≤ m ^ 2 := by
  have h := variance_mul_Td_dirac m hψ hE
  have hm2 : 0 < m ^ 2 := by positivity
  have ha : 0 ≤ ‖TdOp d ψ‖ ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith only [h, hc, hm2, ha]

/-- **The dispersion of the transport is at most `m² / (1 + m²)`** (`d ≥ 2`, `m ≠ 0`). -/
theorem variance_Td_dirac_le (hd : 2 ≤ d) {m : ℝ} (hm : m ≠ 0) {E : ℝ} {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (hE : diracOp d m ψ = (E : ℂ) • ψ) : variance (TdOp d) ψ ≤ m ^ 2 / (1 + m ^ 2) := by
  have h := variance_mul_Td_dirac m hψ hE
  have hv := variance_Td_dirac_le_sq hm hψ hE
  have h1 : ‖TdOp d ψ‖ ≤ 1 := by simpa [hψ] using norm_TdOp_le hd ψ
  have ha : ‖TdOp d ψ‖ ^ 2 ≤ 1 := by nlinarith only [h1, norm_nonneg (TdOp d ψ)]
  rw [le_div_iff₀ (by positivity)]
  nlinarith only [h, hv, ha]

/-- **The dispersion of the transport never closes**: if `‖T_d χ‖² ≥ μ² ‖χ‖²` for every `χ`
(`T_d` has a gap), then `Var T_d ≥ μ² m² / (μ² + m²)` (`m ≠ 0`). -/
theorem variance_Td_dirac_ge {m μ : ℝ} (hm : m ≠ 0)
    (hμ : ∀ χ : Hd d, μ ^ 2 * ‖χ‖ ^ 2 ≤ ‖TdOp d χ‖ ^ 2) {E : ℝ} {ψ : Hd d} (hψ : ‖ψ‖ = 1)
    (hE : diracOp d m ψ = (E : ℂ) • ψ) :
    μ ^ 2 * m ^ 2 / (μ ^ 2 + m ^ 2) ≤ variance (TdOp d) ψ := by
  have h := variance_mul_Td_dirac m hψ hE
  have hv := variance_Td_dirac_le_sq hm hψ hE
  have ha : μ ^ 2 ≤ ‖TdOp d ψ‖ ^ 2 := by simpa [hψ] using hμ ψ
  have hm2 : 0 < m ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [h, hv, ha, hm2]

end Axis

section Cube

variable (dx dy dz : ℕ)

/-- The signs and transports of the three axes of the open cube. -/
abbrev sx : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (OpenDirac.stagger dx)
abbrev sy : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eY dx dy dz) (OpenDirac.stagger dy)
abbrev sz : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eZ dx dy dz) (OpenDirac.stagger dz)
abbrev tx : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ := liftAlong (eX dx dy dz) (Td dx)
abbrev ty : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ := liftAlong (eY dx dy dz) (Td dy)
abbrev tz : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ := liftAlong (eZ dx dy dz) (Td dz)

/-- The kinetic part of the Dirac operator of the cube, `T_x + σ_x T_y + σ_x σ_y T_z`. -/
def kinetic : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  tx dx dy dz + sx dx dy dz * ty dx dy dz + sx dx dy dz * sy dx dy dz * tz dx dy dz

/-- The chirality `ε = σ_x σ_y σ_z`. -/
def chirality : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  sx dx dy dz * sy dx dy dz * sz dx dy dz

theorem stagger_isHermitian (d : ℕ) : (OpenDirac.stagger d).IsHermitian := by
  rw [OpenDirac.stagger, Matrix.isHermitian_diagonal_iff]
  intro j
  simp [IsSelfAdjoint, star_pow]

variable {dx dy dz}

theorem sy_sx : sy dx dy dz * sx dx dy dz = sx dx dy dz * sy dx dy dz :=
  (liftAlong_xy_comm dx dy dz (OpenDirac.stagger dx) (OpenDirac.stagger dy)).symm

theorem sz_sx : sz dx dy dz * sx dx dy dz = sx dx dy dz * sz dx dy dz :=
  (liftAlong_xz_comm dx dy dz (OpenDirac.stagger dx) (OpenDirac.stagger dz)).symm

theorem sz_sy : sz dx dy dz * sy dx dy dz = sy dx dy dz * sz dx dy dz :=
  (liftAlong_yz_comm dx dy dz (OpenDirac.stagger dy) (OpenDirac.stagger dz)).symm

theorem ty_sx : ty dx dy dz * sx dx dy dz = sx dx dy dz * ty dx dy dz :=
  (liftAlong_xy_comm dx dy dz (OpenDirac.stagger dx) (Td dy)).symm

theorem tz_sx : tz dx dy dz * sx dx dy dz = sx dx dy dz * tz dx dy dz :=
  (liftAlong_xz_comm dx dy dz (OpenDirac.stagger dx) (Td dz)).symm

theorem tz_sy : tz dx dy dz * sy dx dy dz = sy dx dy dz * tz dx dy dz :=
  (liftAlong_yz_comm dx dy dz (OpenDirac.stagger dy) (Td dz)).symm

theorem sx_isHermitian : (sx dx dy dz).IsHermitian :=
  RobertsonDeterminant3D.liftAlong_isHermitian _ (stagger_isHermitian _)

theorem sy_isHermitian : (sy dx dy dz).IsHermitian :=
  RobertsonDeterminant3D.liftAlong_isHermitian _ (stagger_isHermitian _)

theorem sz_isHermitian : (sz dx dy dz).IsHermitian :=
  RobertsonDeterminant3D.liftAlong_isHermitian _ (stagger_isHermitian _)

theorem tx_isHermitian : (tx dx dy dz).IsHermitian :=
  RobertsonDeterminant3D.liftAlong_isHermitian _ (Td_isHermitian _)

theorem ty_isHermitian : (ty dx dy dz).IsHermitian :=
  RobertsonDeterminant3D.liftAlong_isHermitian _ (Td_isHermitian _)

theorem tz_isHermitian : (tz dx dy dz).IsHermitian :=
  RobertsonDeterminant3D.liftAlong_isHermitian _ (Td_isHermitian _)

/-- **The chirality is hermitian.** -/
theorem chirality_isHermitian : (chirality dx dy dz).IsHermitian := by
  unfold chirality
  have hx := (sx_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have hy := (sy_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have hz := (sz_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have h1 : sz dx dy dz * (sy dx dy dz * sx dx dy dz) =
      sx dx dy dz * (sy dx dy dz * sz dx dy dz) := by
    rw [sy_sx, ← mul_assoc, sz_sx, mul_assoc, sz_sy, ← mul_assoc]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hx, hy, hz,
    ← mul_assoc, mul_assoc (sz dx dy dz), h1]
  simp only [mul_assoc]

/-- **`ε² = 1`.** -/
theorem chirality_sq : chirality dx dy dz * chirality dx dy dz = 1 := by
  have hx := OpenDirac.liftAlong_stagger_mul_self (eX dx dy dz)
  have hy := OpenDirac.liftAlong_stagger_mul_self (eY dx dy dz)
  have hz := OpenDirac.liftAlong_stagger_mul_self (eZ dx dy dz)
  have h1 : sz dx dy dz * (sx dx dy dz * sy dx dy dz) =
      (sx dx dy dz * sy dx dy dz) * sz dx dy dz := by
    rw [← mul_assoc, sz_sx, mul_assoc, sz_sy, ← mul_assoc]
  have h2 : (sx dx dy dz * sy dx dy dz) * (sx dx dy dz * sy dx dy dz) = 1 := by
    calc (sx dx dy dz * sy dx dy dz) * (sx dx dy dz * sy dx dy dz)
        = sx dx dy dz * (sy dx dy dz * sx dx dy dz) * sy dx dy dz := by simp only [mul_assoc]
      _ = sx dx dy dz * (sx dx dy dz * sy dx dy dz) * sy dx dy dz := by rw [sy_sx]
      _ = (sx dx dy dz * sx dx dy dz) * (sy dx dy dz * sy dx dy dz) := by simp only [mul_assoc]
      _ = 1 := by rw [hx, hy, one_mul]
  unfold chirality
  calc sx dx dy dz * sy dx dy dz * sz dx dy dz * (sx dx dy dz * sy dx dy dz * sz dx dy dz)
      = (sx dx dy dz * sy dx dy dz) * (sz dx dy dz * (sx dx dy dz * sy dx dy dz)) *
          sz dx dy dz := by simp only [mul_assoc]
    _ = ((sx dx dy dz * sy dx dy dz) * (sx dx dy dz * sy dx dy dz)) *
          (sz dx dy dz * sz dx dy dz) := by rw [h1]; simp only [mul_assoc]
    _ = 1 := by rw [h2, hz, one_mul]

/-- **The kinetic part of the Dirac operator is hermitian.** -/
theorem kinetic_isHermitian : (kinetic dx dy dz).IsHermitian := by
  have hx := (sx_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have hy := (sy_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have htx := (tx_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have hty := (ty_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have htz := (tz_isHermitian (dx := dx) (dy := dy) (dz := dz)).eq
  have h2 : (sx dx dy dz * ty dx dy dz)ᴴ = sx dx dy dz * ty dx dy dz := by
    rw [Matrix.conjTranspose_mul, hx, hty, ty_sx]
  have h3 : (sx dx dy dz * sy dx dy dz * tz dx dy dz)ᴴ =
      sx dx dy dz * sy dx dy dz * tz dx dy dz := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hx, hy, htz, sy_sx, ← mul_assoc,
      tz_sx, mul_assoc, tz_sy, ← mul_assoc]
  unfold kinetic
  rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_add, htx, h2, h3]

/-- **The kinetic part and the chirality anticommute**: `K ε + ε K = 0`. -/
theorem kinetic_chirality_anticomm :
    kinetic dx dy dz * chirality dx dy dz + chirality dx dy dz * kinetic dx dy dz = 0 := by
  have h0 := OpenDirac.dirac_sq (dx := dx) (dy := dy) (dz := dz) 0
  have h1 := OpenDirac.dirac_sq (dx := dx) (dy := dy) (dz := dz) 1
  have hK : kinetic dx dy dz * kinetic dx dy dz = tx dx dy dz * tx dx dy dz +
      ty dx dy dz * ty dx dy dz + tz dx dy dz * tz dx dy dz := by
    simpa [OpenDirac.dirac, kinetic] using h0
  have hD : (kinetic dx dy dz + chirality dx dy dz) * (kinetic dx dy dz + chirality dx dy dz) =
      tx dx dy dz * tx dx dy dz + ty dx dy dz * ty dx dy dz + tz dx dy dz * tz dx dy dz + 1 := by
    simpa [OpenDirac.dirac, kinetic, chirality] using h1
  rw [add_mul, mul_add, mul_add, hK, chirality_sq] at hD
  have : kinetic dx dy dz * chirality dx dy dz + chirality dx dy dz * kinetic dx dy dz =
      (tx dx dy dz * tx dx dy dz + ty dx dy dz * ty dx dy dz + tz dx dy dz * tz dx dy dz +
        kinetic dx dy dz * chirality dx dy dz + (chirality dx dy dz * kinetic dx dy dz + 1)) -
      (tx dx dy dz * tx dx dy dz + ty dx dy dz * ty dx dy dz + tz dx dy dz * tz dx dy dz + 1) := by
    abel
  rw [this, ← hD]
  abel


/-- A hermitian matrix with `U² = 1` is an isometry. -/
theorem norm_sq_toEuclideanLin_of_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U.IsHermitian) (h : U * U = 1) (χ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin U χ‖ ^ 2 = ‖χ‖ ^ 2 := by
  have hs : (Matrix.toEuclideanLin U).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hU
  have hUU : Matrix.toEuclideanLin U (Matrix.toEuclideanLin U χ) = χ := by
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, h,
      Matrix.one_mulVec]
  have h1 := hs (Matrix.toEuclideanLin U χ) χ
  rw [hUU] at h1
  have h3 : (inner ℂ (Matrix.toEuclideanLin U χ) (Matrix.toEuclideanLin U χ)).re =
      ‖Matrix.toEuclideanLin U χ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      inner_self_eq_norm_sq (𝕜 := ℂ) (Matrix.toEuclideanLin U χ)
  have h4 : (inner ℂ χ χ).re = ‖χ‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜 := ℂ) χ
  rw [← h3, ← h4]
  exact (congrArg Complex.re h1).symm

/-- **The dispersion of the kinetic part in a stationary Dirac state of the open cube.** For a
unit eigenvector of `D_m = K + m ε` (`OpenDirac.dirac`, any sizes) and `a = ‖K ψ‖²`,
`(a − ⟨K⟩²)(a + m²) = a m²`: the same identity as on one axis. -/
theorem dispersion_kinetic_dirac (m : ℝ) {E : ℝ} {ψ : H3D dx dy dz} (hψ : ‖ψ‖ = 1)
    (hE : Matrix.toEuclideanLin (OpenDirac.dirac dx dy dz (m : ℂ)) ψ = (E : ℂ) • ψ) :
    (‖Matrix.toEuclideanLin (kinetic dx dy dz) ψ‖ ^ 2 -
        (inner ℂ ψ (Matrix.toEuclideanLin (kinetic dx dy dz) ψ)).re ^ 2) *
      (‖Matrix.toEuclideanLin (kinetic dx dy dz) ψ‖ ^ 2 + m ^ 2) =
      ‖Matrix.toEuclideanLin (kinetic dx dy dz) ψ‖ ^ 2 * m ^ 2 := by
  have hA : (Matrix.toEuclideanLin (kinetic dx dy dz)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr kinetic_isHermitian
  have hU : (Matrix.toEuclideanLin (chirality dx dy dz)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr chirality_isHermitian
  have hB : ((m : ℂ) • Matrix.toEuclideanLin (chirality dx dy dz)).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [hU x y]
  have hKe : kinetic dx dy dz * chirality dx dy dz = -(chirality dx dy dz * kinetic dx dy dz) :=
    eq_neg_of_add_eq_zero_left kinetic_chirality_anticomm
  have hAB : ∀ χ, Matrix.toEuclideanLin (kinetic dx dy dz)
      (((m : ℂ) • Matrix.toEuclideanLin (chirality dx dy dz)) χ) =
      -((m : ℂ) • Matrix.toEuclideanLin (chirality dx dy dz))
        (Matrix.toEuclideanLin (kinetic dx dy dz) χ) := by
    intro χ
    simp only [LinearMap.smul_apply, map_smul]
    rw [← smul_neg]
    congr 1
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hKe,
      Matrix.neg_mulVec]
    rfl
  have hBm : ∀ χ, ‖((m : ℂ) • Matrix.toEuclideanLin (chirality dx dy dz)) χ‖ ^ 2 =
      m ^ 2 * ‖χ‖ ^ 2 := by
    intro χ
    simp only [LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, norm_sq_toEuclideanLin_of_sq chirality_isHermitian chirality_sq]
  have hE' : Matrix.toEuclideanLin (kinetic dx dy dz) ψ +
      ((m : ℂ) • Matrix.toEuclideanLin (chirality dx dy dz)) ψ = (E : ℂ) • ψ := by
    rw [← hE]
    change _ = Matrix.toEuclideanLin (kinetic dx dy dz + (m : ℂ) • chirality dx dy dz) ψ
    rw [map_add, map_smul]
    rfl
  exact variance_mul_energy_sq hA hB hAB hBm hψ hE'

end Cube

section Four

/-- The smaller root `c = (3 − √5)/2 = φ⁻²` of `c² − 3c + 1 = 0`. -/
theorem sq_sub_three_add_one : ((3 - √5) / 2) ^ 2 - 3 * ((3 - √5) / 2) + 1 = 0 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith only [h5]

theorem three_sub_sqrt_five_lt : (3 - √5) / 2 < 1 := by
  have : 1 < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **One sector of `A_4²`**: for `c² − 3c + 1 = 0` and `c < 1`,
`c (|a|² + |b|²) ≤ |b|² + |a + b|²`. -/
theorem sector_ge {c : ℝ} (hc : c ^ 2 - 3 * c + 1 = 0) (hc1 : c < 1) (a1 a2 b1 b2 : ℝ) :
    c * (a1 ^ 2 + a2 ^ 2 + (b1 ^ 2 + b2 ^ 2)) ≤
      b1 ^ 2 + b2 ^ 2 + ((a1 + b1) ^ 2 + (a2 + b2) ^ 2) := by
  have key : b1 ^ 2 + b2 ^ 2 + ((a1 + b1) ^ 2 + (a2 + b2) ^ 2) -
      c * (a1 ^ 2 + a2 ^ 2 + (b1 ^ 2 + b2 ^ 2)) =
      (1 - c) * ((a1 + (2 - c) * b1) ^ 2 + (a2 + (2 - c) * b2) ^ 2) -
        (2 * (a1 * b1 + a2 * b2) + (2 - c) * (b1 ^ 2 + b2 ^ 2)) * (c ^ 2 - 3 * c + 1) := by
    ring
  rw [hc, mul_zero, sub_zero] at key
  have : 0 ≤ (1 - c) * ((a1 + (2 - c) * b1) ^ 2 + (a2 + (2 - c) * b2) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- **`T_4` has a gap**: its smallest eigenvalue in modulus is `φ⁻² = (3 − √5)/2`, so
`((3 − √5)/2)² ‖χ‖² ≤ ‖T_4 χ‖²`. -/
theorem gap_TdOp_four (χ : Hd 4) :
    ((3 - √5) / 2) ^ 2 * ‖χ‖ ^ 2 ≤ ‖TdOp 4 χ‖ ^ 2 := by
  set c : ℝ := (3 - √5) / 2 with hcdef
  have hc := sq_sub_three_add_one
  have hc1 := three_sub_sqrt_five_lt
  rw [← hcdef] at hc hc1
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hρ : (rho 4) ^ 2 * c = 1 := by
    rw [MinUncertaintyFour.rho_four, hcdef]
    nlinarith only [h5]
  have hρpos := MinUncertaintyFour.rho_four_pos
  rw [MinUncertaintyFour.TdOp_four_apply, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  have hn : ∀ z : ℂ, ‖z / (rho 4 : ℂ)‖ ^ 2 = c * ‖z‖ ^ 2 := by
    intro z
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, div_pow]
    have : c = 1 / rho 4 ^ 2 := by
      field_simp
      linarith only [hρ]
    rw [this]
    ring
  simp only [hn]
  have hc0 : 0 ≤ c := by
    rw [hcdef]
    have : √5 ≤ 3 := by
      rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have e : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have s1 := sector_ge hc hc1 (χ.ofLp 0).re (χ.ofLp 0).im (χ.ofLp 2).re (χ.ofLp 2).im
  have s2 := sector_ge hc hc1 (χ.ofLp 3).re (χ.ofLp 3).im (χ.ofLp 1).re (χ.ofLp 1).im
  simp only [e, Complex.add_re, Complex.add_im]
  nlinarith only [s1, s2, hc0, mul_le_mul_of_nonneg_left (add_le_add s1 s2) hc0]

/-- **The dispersion of the transport on the open axis `d = 4`, both ways.** For a unit
eigenvector of `D_m = T_4 + m σ` with `m ≠ 0` and `c = (3 − √5)/2 = φ⁻²`,
`c² m² / (c² + m²) ≤ Var T_4 ≤ m² / (1 + m²)`. -/
theorem variance_T_four_dirac {m : ℝ} (hm : m ≠ 0) {E : ℝ} {ψ : Hd 4} (hψ : ‖ψ‖ = 1)
    (hE : OpenDiracVelocity.diracOp 4 m ψ = (E : ℂ) • ψ) :
    ((3 - √5) / 2) ^ 2 * m ^ 2 / (((3 - √5) / 2) ^ 2 + m ^ 2) ≤ variance (TdOp 4) ψ ∧
      variance (TdOp 4) ψ ≤ m ^ 2 / (1 + m ^ 2) :=
  ⟨variance_Td_dirac_ge hm gap_TdOp_four hψ hE, variance_Td_dirac_le (by norm_num) hm hψ hE⟩

end Four

end OpenDiracDispersion
