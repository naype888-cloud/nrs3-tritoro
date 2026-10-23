/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.DiracSpeed
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Dirac qubit at one momentum, and the state of every speed

On a closed axis the Dirac operator `D_m = T° + m Σ` keeps the two waves `e_u`, `e_{−u}`
(`u = e^{ik}`) together: `T°` is `c = cos k` on `e_u` and `−c` on `e_{−u}`, `Σ` exchanges them, and
the current is `−s` and `s`, `s = sin k`. On `ℂ²` this is the qubit

  `H = c σ_z + m σ_x`,  `V = −s σ_z`,  `c² + s² = 1`.

It satisfies the hypotheses of `DiracSpeed` (`H = A + B` with `A = c σ_z`, `B = m σ_x`), so its
states move at most at `r = √(1 + m²) − |m|`. Here the limit is reached, and every speed below
it is reached by one explicit eigenstate:

* `speedState a s m`: the upper eigenstate of `H` at `c = √a`, velocity `−s √a / E`,
  `E = √(a + m²)`.
* `speedParam t m`: for `0 ≤ t ≤ r` the root `a` of `a² − (1 − t²) a + t² m² = 0`; the state at
  `a = speedParam t m`, `s = −√(1 − a)` moves exactly at `t`.
* the speed `r` is reached at `a = |m| r` and only there (`eq_of_velocity_eq_speedLimit`).

## Main results

- `DiracQubit.dirac_speedState`, `DiracQubit.norm_speedState` : a unit eigenvector of `H`.
- `DiracQubit.velocity_speedState` : its velocity is `−s √a / E`.
- `DiracQubitParam` : the state of every speed `0 ≤ t ≤ r`, and the fastest one.
- `DiracQubit.abs_velocity_le` : every unit eigenvector of `H` moves at most at `r`.
-/

@[expose] public noncomputable section

open Complex

namespace DiracQubit

/-- The states of the qubit. -/
abbrev Q := EuclideanSpace ℂ (Fin 2)

/-- `A = c σ_z`. -/
def opA (c : ℝ) : Q →ₗ[ℂ] Q where
  toFun χ := WithLp.toLp 2 ![(c : ℂ) * χ 0, -((c : ℂ) * χ 1)]
  map_add' χ η := by ext i; fin_cases i <;> simp <;> ring
  map_smul' z χ := by ext i; fin_cases i <;> simp <;> ring

/-- `B = m σ_x`. -/
def opB (m : ℝ) : Q →ₗ[ℂ] Q where
  toFun χ := WithLp.toLp 2 ![(m : ℂ) * χ 1, (m : ℂ) * χ 0]
  map_add' χ η := by ext i; fin_cases i <;> simp <;> ring
  map_smul' z χ := by ext i; fin_cases i <;> simp <;> ring

/-- The velocity `V = −s σ_z`. -/
def opV (s : ℝ) : Q →ₗ[ℂ] Q := opA (-s)

/-- The Dirac qubit `H = c σ_z + m σ_x`. -/
def dirac (c m : ℝ) : Q →ₗ[ℂ] Q := opA c + opB m

/-- The velocity of a state. -/
def velocity (s : ℝ) (χ : Q) : ℝ := (inner ℂ χ (opV s χ)).re

theorem opA_apply (c : ℝ) (χ : Q) : opA c χ = WithLp.toLp 2 ![(c : ℂ) * χ 0, -((c : ℂ) * χ 1)] :=
  rfl

theorem opB_apply (m : ℝ) (χ : Q) : opB m χ = WithLp.toLp 2 ![(m : ℂ) * χ 1, (m : ℂ) * χ 0] :=
  rfl

theorem velocity_eq (s : ℝ) (χ : Q) : velocity s χ = s * (‖χ 1‖ ^ 2 - ‖χ 0‖ ^ 2) := by
  simp only [velocity, opV, opA_apply, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply',
    Complex.add_re]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_neg]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.neg_re, Complex.mul_im, Complex.neg_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem norm_sq_eq (χ : Q) : ‖χ‖ ^ 2 = ‖χ 0‖ ^ 2 + ‖χ 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-! ## 1. The relations of `DiracSpeed` -/

theorem opA_isSymmetric (c : ℝ) : (opA c).IsSymmetric := by
  intro φ χ
  simp only [opA_apply, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply',
    Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_neg,
    Complex.conj_ofReal]
  ring

theorem opB_isSymmetric (m : ℝ) : (opB m).IsSymmetric := by
  intro φ χ
  simp only [opB_apply, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply',
    Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, Complex.conj_ofReal]
  ring

theorem opA_opA (c c' : ℝ) (χ : Q) : opA c (opA c' χ) = opA c' (opA c χ) := by
  ext i; fin_cases i <;> simp [opA_apply] <;> ring

theorem opA_opB (c m : ℝ) (χ : Q) : opA c (opB m χ) = -opB m (opA c χ) := by
  ext i; fin_cases i <;> simp [opA_apply, opB_apply] <;> ring

theorem opV_opV_add (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (χ : Q) :
    opV s (opV s χ) + opA c (opA c χ) = χ := by
  have h : ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) = 1 := by exact_mod_cast hcs
  ext i; fin_cases i <;> simp [opV, opA_apply] <;> linear_combination χ _ * h

theorem norm_opB (m : ℝ) (χ : Q) : ‖opB m χ‖ ^ 2 = m ^ 2 * ‖χ‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq]
  simp only [opB_apply, Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **Every unit eigenvector of the qubit moves at most at `√(1 + m²) − |m|`** (`DiracSpeed`). -/
theorem abs_velocity_le {c s m E : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hm : m ≠ 0) {χ : Q}
    (hχ : ‖χ‖ = 1) (hE : dirac c m χ = (E : ℂ) • χ) :
    |velocity s χ| ≤ Real.sqrt (1 + m ^ 2) - |m| :=
  DiracSpeed.abs_velocity_le (opA_isSymmetric c) (opB_isSymmetric m) (opA_isSymmetric (-s))
    (fun χ => opA_opA c (-s) χ) (fun χ => opA_opB (-s) m χ) (opA_opB c m) (opV_opV_add c s hcs)
    hm (fun χ => (norm_opB m χ).ge) hχ hE

/-! ## 2. The state of every speed -/

section State

variable {a m : ℝ}

/-- `E = √(a + m²)`. -/
def energy (a m : ℝ) : ℝ := Real.sqrt (a + m ^ 2)

/-- The normalization `N = √(2E(E − √a))`. -/
def normConst (a m : ℝ) : ℝ := Real.sqrt (2 * energy a m * (energy a m - Real.sqrt a))

/-- The upper eigenstate of `H` at `c = √a`: `(m, E − √a)/N`. -/
def speedState (a m : ℝ) : Q :=
  WithLp.toLp 2 ![((m / normConst a m : ℝ) : ℂ),
    (((energy a m - Real.sqrt a) / normConst a m : ℝ) : ℂ)]

theorem energy_sq (ha : 0 ≤ a) : energy a m ^ 2 = a + m ^ 2 := Real.sq_sqrt (by positivity)

theorem sqrt_lt_energy (ha : 0 ≤ a) (hm : m ≠ 0) : Real.sqrt a < energy a m := by
  apply Real.sqrt_lt_sqrt ha
  have : 0 < m ^ 2 := by positivity
  linarith

theorem normConst_sq (ha : 0 ≤ a) (hm : m ≠ 0) :
    normConst a m ^ 2 = 2 * energy a m * (energy a m - Real.sqrt a) := by
  have h1 := sqrt_lt_energy ha hm
  have h0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  exact Real.sq_sqrt (by nlinarith)

theorem normConst_pos (ha : 0 ≤ a) (hm : m ≠ 0) : 0 < normConst a m := by
  have h1 := sqrt_lt_energy ha hm
  have h0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  exact Real.sqrt_pos.2 (by nlinarith)

/-- The state is an eigenvector of `H` with energy `E`. -/
theorem dirac_speedState (ha : 0 ≤ a) :
    dirac (Real.sqrt a) m (speedState a m) = ((energy a m : ℝ) : ℂ) • speedState a m := by
  have hE := energy_sq (m := m) ha
  have hs := Real.sq_sqrt ha
  set E := energy a m
  set N := normConst a m
  have h0 : Real.sqrt a * (m / N) + m * ((E - Real.sqrt a) / N) = E * (m / N) := by ring
  have h1 : -(Real.sqrt a * ((E - Real.sqrt a) / N)) + m * (m / N) =
      E * ((E - Real.sqrt a) / N) := by
    have h : -(Real.sqrt a * (E - Real.sqrt a)) + m * m = E * (E - Real.sqrt a) := by
      linear_combination hs - hE
    calc -(Real.sqrt a * ((E - Real.sqrt a) / N)) + m * (m / N)
        = (-(Real.sqrt a * (E - Real.sqrt a)) + m * m) / N := by ring
      _ = E * ((E - Real.sqrt a) / N) := by rw [h]; ring
  ext i; fin_cases i
  · simp only [dirac, LinearMap.add_apply, opA_apply, opB_apply, speedState, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
      Fin.isValue]
    exact_mod_cast h0
  · simp only [dirac, LinearMap.add_apply, opA_apply, opB_apply, speedState, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_one,
      Fin.isValue]
    exact_mod_cast h1

theorem norm_speedState (ha : 0 ≤ a) (hm : m ≠ 0) : ‖speedState a m‖ = 1 := by
  have hE := energy_sq (m := m) ha
  have hs := Real.sq_sqrt ha
  have hN := normConst_sq ha hm
  have hN0 := (normConst_pos ha hm).ne'
  have h : ‖speedState a m‖ ^ 2 = 1 := by
    rw [norm_sq_eq]
    simp only [speedState, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hN0), hN]
    nlinarith only [hE, hs]
  have := norm_nonneg (speedState a m)
  nlinarith only [h, this]

/-- **The velocity of the state**: `−s √a / E`. -/
theorem velocity_speedState (ha : 0 ≤ a) (hm : m ≠ 0) (s : ℝ) :
    velocity s (speedState a m) = -s * Real.sqrt a / energy a m := by
  have hE := energy_sq (m := m) ha
  have hs := Real.sq_sqrt ha
  have hN := normConst_sq ha hm
  have hN0 := (normConst_pos ha hm).ne'
  have hE0 : energy a m ≠ 0 := (lt_of_le_of_lt (Real.sqrt_nonneg a) (sqrt_lt_energy ha hm)).ne'
  have hd : energy a m - Real.sqrt a ≠ 0 := (sub_pos.2 (sqrt_lt_energy ha hm)).ne'
  have key : (energy a m - Real.sqrt a) ^ 2 - m ^ 2 =
      -(2 * Real.sqrt a * (energy a m - Real.sqrt a)) := by
    linear_combination hE - hs
  rw [velocity_eq]
  simp only [speedState, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rw [div_pow, div_pow, ← sub_div, hN, key]
  field_simp

end State

end DiracQubit
