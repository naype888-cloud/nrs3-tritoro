/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusCommute
public import NRS3Hopf.BoxStrict

/-!
# Robertson 1934 is strict on the three-torus, for every state

On `T³ = x × y × z` with every axis closed with three positions, take a unit state with every
axis in its band, `|⟨i[T°, P₃]⟩| > 1`. Then `|det Ω₆| < det Σ₆`, entangled across the axes or
not.

Suppose equality. Every axis has a positive defect (`ClosedAxisEntangled`), so the relations,
of dimension at least `3` (`RobertsonEquality.le_finrank_ker`), cross every axis in both
directions (`RobertsonEqualityPlane`). `Φ` is an eigenvector of the Lie algebra `𝔤` they
generate, axis by axis, and every bracket of `𝔤` annihilates `Φ`.

* **An element on `z` alone.** Take a relation `r` that vanishes on `x` and a relation `t` that
  vanishes on `y`. Neither vanishes on `z`: a relation on one axis alone makes the two
  fluctuations of that axis parallel, against its defect. Take `s` whose part on `z` is
  independent of that of `r`. Then `[[r, s], t]` vanishes on `x` and on `y`, and on `z` it is
  `[[T°, P₃], t_z]` up to a nonzero factor, which is never `0` for `t_z ≠ 0`.
* **Every `E_ij` on `z`.** The `z` parts of the elements of `𝔤` vanishing on `x` and `y` form a
  nonzero subspace of traceless matrices stable under `T°` and `P₃`, so they contain every
  `E_ij` (`ClosedThreeIdeal`).
* **No state.** `[E₀₁, E₁₀] = E₀₀ − E₁₁` and `[E₁₂, E₂₁] = E₁₁ − E₂₂` on `z` annihilate `Φ`, and
  they have no common kernel: `Φ = 0`.

The open axes of the box needed equal steps (`EqualSteps`) to leave the fiber alone; on the
torus every axis is closed, and the double bracket does it.

## Main results

- `TorusStrict.lie_lie_ne_zero` : `[[T°, P₃], w₀T° + w₁P₃] ≠ 0` for `w ≠ 0`.
- `TorusStrict.eig`, `TorusStrict.kill` : `Φ` is an eigenvector of the algebra of the
  relations, and its brackets annihilate `Φ`.
- `TorusStrict.eq_zero_of_det_eq` : equality with every axis in its band leaves no state.
- `TorusStrict.robertson_det_torus_lt` : **strict for every unit state with every axis in its
  band.**
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant StackedFibers CubeInBox
open RobertsonEquality BoxFiberLine ClosedThreeIdeal BoxTwoRelations CauchyGram

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace TorusStrict

/-! ## 1. The double bracket on a closed axis -/

/-- **`[[T°, P₃], w₀T° + w₁P₃]` vanishes only for `w = 0`.** Its `(0, 0)` entry is `(3/2) w₀`,
its `(0, 2)` entry is `2 w₁`. -/
theorem lie_lie_ne_zero {w₀ w₁ : ℂ} (hw : w₀ ≠ 0 ∨ w₁ ≠ 0) :
    ⁅⁅ClosedThree.Tc, Pd 3⁆, w₀ • ClosedThree.Tc + w₁ • Pd 3⁆ ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have h02 := congrFun (congrFun h 0) 2
  have hT : ClosedThree.Tc = !![0, 1 / 2, 1 / 2; 1 / 2, 0, 1 / 2; 1 / 2, 1 / 2, 0] :=
    ClosedAxisAlgebra.T_eq
  have hP : Pd 3 = !![-1, 0, 0; 0, 0, 0; 0, 0, 1] := ClosedAxisAlgebra.P_eq
  rw [hT, hP] at h00 h02
  simp [Ring.lie_def] at h00 h02
  rcases hw with hw | hw
  · exact hw (by linear_combination (2 / 3 : ℂ) * h00)
  · exact hw (by linear_combination (1 / 2 : ℂ) * h02)

/-- Two combinations of `T°`, `P₃` bracket to `Δ [T°, P₃]`. -/
theorem lie_comb (u₀ u₁ v₀ v₁ : ℂ) :
    ⁅u₀ • ClosedThree.Tc + u₁ • Pd 3, v₀ • ClosedThree.Tc + v₁ • Pd 3⁆ =
      (u₀ * v₁ - u₁ * v₀) • ⁅ClosedThree.Tc, Pd 3⁆ := by
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero, zero_add]
  rw [← lie_skew (Pd 3)]
  module

/-! ## 2. The algebra of the relations on the torus -/

/-- One matrix per axis of the torus. -/
abbrev TAxes := Fin 3 → Matrix (Fin 3) (Fin 3) ℂ

theorem lie_apply (X Y : TAxes) (i : Fin 3) : (⁅X, Y⁆) i = ⁅X i, Y i⁆ := by
  simp [Ring.lie_def]

/-- The sum over the axes of the lifted matrices. -/
def lam : TAxes →+ Matrix (Fin 3 → Fin 3) (Fin 3 → Fin 3) ℂ where
  toFun X := ∑ i, liftAlong (split i) (X i)
  map_zero' := by simp [liftAlong_zero]
  map_add' X Y := by simp [liftAlong_add, Finset.sum_add_distrib]

theorem lam_apply (X : TAxes) : lam X = ∑ i, liftAlong (split i) (X i) := rfl

theorem lam_smul (c : ℂ) (X : TAxes) : lam (c • X) = c • lam X := by
  simp [lam_apply, liftAlong_smul, Finset.smul_sum]

/-- **The sum over the axes respects the bracket**, since different axes commute. -/
theorem lam_lie (X Y : TAxes) : lam ⁅X, Y⁆ = ⁅lam X, lam Y⁆ := by
  rw [Ring.lie_def (lam X), lam_apply, lam_apply, lam_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x i => liftAlong (split i) (X i) * liftAlong (split x) (Y x))]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [lie_apply, Ring.lie_def, liftAlong_sub, liftAlong_mul, liftAlong_mul]
  · intro j _ hji
    rw [TorusCommute.liftAlong_split_comm hji.symm, sub_self]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- An element on axis `i` alone. -/
theorem lam_single {Z : TAxes} {i : Fin 3} (hZ : ∀ j, j ≠ i → Z j = 0) :
    lam Z = liftAlong (split i) (Z i) := by
  rw [lam_apply, Finset.sum_eq_single i]
  · intro j _ hji; rw [hZ j hji, liftAlong_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The matrices of a combination `Σ_p a_p A_p`, axis by axis. -/
def axesOf (a : Fin 2 × Fin 3 → ℂ) : TAxes :=
  fun i => a (0, i) • ClosedThree.Tc + a (1, i) • Pd 3

/-- Matrices to operators, as an additive map. -/
def toOp : Matrix (Fin 3 → Fin 3) (Fin 3 → Fin 3) ℂ →+ Module.End ℂ (Torus.HT 3) where
  toFun A := Matrix.toEuclideanLin A
  map_zero' := map_zero _
  map_add' := map_add _

theorem toOp_apply (A : Matrix (Fin 3 → Fin 3) (Fin 3 → Fin 3) ℂ) :
    toOp A = Matrix.toEuclideanLin A := rfl

theorem toOp_lie (A B : Matrix (Fin 3 → Fin 3) (Fin 3 → Fin 3) ℂ) :
    toOp ⁅A, B⁆ = ⁅toOp A, toOp B⁆ := by
  simp only [toOp_apply, Ring.lie_def, map_sub]
  congr 1 <;> exact Matrix.toLpLin_mul_same _ _ _

/-- The combination `Σ_p a_p A_p` of the six observables is the sum over the axes. -/
theorem sum_torusPairs (a : Fin 2 × Fin 3 → ℂ) :
    ∑ p, a p • Torus.torusPairs 3 p = toOp (lam (axesOf a)) := by
  simp only [Torus.torusPairs, ops, Fintype.sum_prod_type, Fin.sum_univ_two, toOp_apply,
    lam_apply, axesOf, liftAlong_add, liftAlong_smul, map_sum, map_add, map_smul,
    Finset.sum_add_distrib, closedPair, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **A relation makes `Φ` an eigenvector of the combination.** -/
theorem eig_of_relation {Φ : Torus.HT 3} {a : Fin 2 × Fin 3 → ℂ}
    (ha : ∑ p, a p • centeredG (Torus.torusPairs 3 p) Φ = 0) :
    toOp (lam (axesOf a)) Φ = (∑ p, a p * (meanG (Torus.torusPairs 3 p) Φ : ℂ)) • Φ := by
  have h : ∑ p, a p • Torus.torusPairs 3 p Φ =
      ∑ p, (a p * (meanG (Torus.torusPairs 3 p) Φ : ℂ)) • Φ := by
    simpa only [centeredG, smul_sub, Finset.sum_sub_distrib, sub_eq_zero, smul_smul] using ha
  rw [← sum_torusPairs, LinearMap.sum_apply, Finset.sum_smul]
  simpa only [LinearMap.smul_apply] using h

variable (Φ : Torus.HT 3)

/-- The relations at `Φ`. -/
abbrev rel : Submodule ℂ (Fin 2 × Fin 3 → ℂ) :=
  LinearMap.ker (gram ℂ (fluct (Torus.torusPairs 3) Φ)).mulVecLin

/-- The Lie algebra generated by the relations, axis by axis. -/
def alg : LieSubalgebra ℂ TAxes := LieSubalgebra.lieSpan ℂ _ (axesOf '' (rel Φ : Set _))

/-- **`Φ` is an eigenvector of the whole algebra.** -/
theorem eig {Z : TAxes} (hZ : Z ∈ alg Φ) : ∃ μ : ℂ, toOp (lam Z) Φ = μ • Φ := by
  induction hZ using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨_, eig_of_relation (sum_eq_zero_of_mulVec _ Φ (LinearMap.mem_ker.mp hc))⟩
  | zero => exact ⟨0, by simp [toOp_apply]⟩
  | add x y _ _ hx hy =>
    obtain ⟨μ, hμ⟩ := hx
    obtain ⟨ν, hν⟩ := hy
    exact ⟨μ + ν, by rw [map_add, map_add, LinearMap.add_apply, hμ, hν, add_smul]⟩
  | smul a x _ hx =>
    obtain ⟨μ, hμ⟩ := hx
    refine ⟨a * μ, ?_⟩
    rw [lam_smul, toOp_apply, map_smul, LinearMap.smul_apply, ← toOp_apply, hμ, smul_smul]
  | lie x y _ _ hx hy =>
    obtain ⟨μ, hμ⟩ := hx
    obtain ⟨ν, hν⟩ := hy
    exact ⟨0, by rw [lam_lie, toOp_lie, zero_smul]; exact lie_apply_eq_zero hμ hν⟩

/-- **Every bracket of the algebra annihilates `Φ`.** -/
theorem kill {X Y : TAxes} (hX : X ∈ alg Φ) (hY : Y ∈ alg Φ) : toOp (lam ⁅X, Y⁆) Φ = 0 := by
  obtain ⟨μ, hμ⟩ := eig Φ hX
  obtain ⟨ν, hν⟩ := eig Φ hY
  rw [lam_lie, toOp_lie]
  exact lie_apply_eq_zero hμ hν

/-- Every element of the algebra is traceless on every axis. -/
theorem trace_apply {Z : TAxes} (hZ : Z ∈ alg Φ) (i : Fin 3) : (Z i).trace = 0 := by
  induction hZ using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    obtain ⟨c, -, rfl⟩ := hx
    simp [axesOf, Matrix.trace_fin_three, ClosedThree.Tc, Pd, posCoord]
    norm_num
  | zero => simp
  | add x y _ _ hx hy => rw [Pi.add_apply, Matrix.trace_add, hx, hy, add_zero]
  | smul a x _ hx => rw [Pi.smul_apply, Matrix.trace_smul, hx, smul_zero]
  | lie x y _ _ _ _ =>
    rw [lie_apply, Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-! ## 3. Equality leaves no state -/

variable {Φ}

/-- A relation on one axis alone makes the defect of that axis vanish. -/
theorem defect_eq_zero_of_single {c : Fin 2 × Fin 3 → ℂ} (hc : c ∈ rel Φ) {i : Fin 3}
    (hi : c (0, i) ≠ 0 ∨ c (1, i) ≠ 0) (hoff : ∀ s j, j ≠ i → c (s, j) = 0) :
    gramDefectC (fluct (Torus.torusPairs 3) Φ (0, i)) (fluct (Torus.torusPairs 3) Φ (1, i)) =
      0 := by
  refine gramDefectC_eq_zero_of_rel ?_ hi
  have h := sum_eq_zero_of_mulVec _ Φ (LinearMap.mem_ker.mp hc)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_eq_single i, Finset.sum_eq_single i]
    at h
  · exact h
  all_goals first
    | (intro j _ hji; rw [hoff _ j hji, zero_smul])
    | (intro h'; exact absurd (Finset.mem_univ _) h')

/-- A nonzero relation vanishing on axis `a` does not vanish on axis `m`, when the third axis
`b` has a defect. -/
theorem part_ne_zero {c : Fin 2 × Fin 3 → ℂ} (hc : c ∈ rel Φ) (hc0 : c ≠ 0) {a b m : Fin 3}
    (hab : a ≠ b) (hbm : b ≠ m) (ham : a ≠ m)
    (hb : 0 < gramDefectC (fluct (Torus.torusPairs 3) Φ (0, b))
      (fluct (Torus.torusPairs 3) Φ (1, b)))
    (ha : fiberPart a c = 0) : fiberPart m c ≠ 0 := by
  intro hm
  have hall (j : Fin 3) : j = a ∨ j = b ∨ j = m := by
    fin_cases a <;> fin_cases b <;> fin_cases m <;> fin_cases j <;> simp_all
  have hoff : ∀ s j, j ≠ b → c (s, j) = 0 := by
    intro s j hj
    rcases hall j with rfl | rfl | rfl
    · exact congrFun ha s
    · exact absurd rfl hj
    · exact congrFun hm s
  have hi : c (0, b) ≠ 0 ∨ c (1, b) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc0
    funext ⟨s, j⟩
    by_cases hj : j = b
    · subst hj; fin_cases s; exacts [h.1, h.2]
    · exact hoff s j hj
  exact hb.ne' (defect_eq_zero_of_single hc hi hoff)

/-- A nonzero relation vanishing on a chosen axis. -/
theorem exists_rel_zero (hdim : 3 ≤ Module.finrank ℂ (rel Φ)) (a : Fin 3) :
    ∃ c ∈ rel Φ, c ≠ 0 ∧ fiberPart a c = 0 := by
  set f := fiberPart a ∘ₗ (rel Φ).subtype
  have hr : Module.finrank ℂ (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrn
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hx⟩

/-- The `z` parts of the elements of `𝔤` vanishing on `x` and `y`. -/
def zPart (Φ : Torus.HT 3) : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  ((alg Φ).toSubmodule ⊓ LinearMap.ker (LinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 3 => Matrix (Fin 3) (Fin 3) ℂ) 0) ⊓
    LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Matrix (Fin 3) (Fin 3) ℂ) 1)).map
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Matrix (Fin 3) (Fin 3) ℂ) 2)

theorem mem_zPart {F : Matrix (Fin 3) (Fin 3) ℂ} :
    F ∈ zPart Φ ↔ ∃ Z ∈ alg Φ, Z 0 = 0 ∧ Z 1 = 0 ∧ Z 2 = F := by
  simp only [zPart, Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker,
    LieSubalgebra.mem_toSubmodule, LinearMap.proj_apply]
  constructor
  · rintro ⟨Z, ⟨⟨hZ, h0⟩, h1⟩, rfl⟩; exact ⟨Z, hZ, h0, h1, rfl⟩
  · rintro ⟨Z, hZ, h0, h1, rfl⟩; exact ⟨Z, ⟨⟨hZ, h0⟩, h1⟩, rfl⟩

theorem no_common_kernel (v : Fin 3 → ℂ) (h₁ : (E 0 0 - E 1 1) *ᵥ v = 0)
    (h₂ : (E 1 1 - E 2 2) *ᵥ v = 0) : v = 0 := by
  have a0 := congrFun h₁ 0
  have a1 := congrFun h₁ 1
  have b2 := congrFun h₂ 2
  simp [Matrix.mulVec, dotProduct, single_apply] at a0 a1 b2
  funext i
  fin_cases i
  exacts [a0, a1, b2]

/-- **Equality on the torus leaves no state**: with every axis in its band, `det Ω ≠ 0` and
`det Σ = |det Ω|`, no unit state is left. -/
theorem eq_zero_of_det_eq (hΦ : ‖Φ‖ = 1)
    (hb : ∀ i, 1 < |tensionG (Torus.torusPairs 3 (0, i)) (Torus.torusPairs 3 (1, i)) Φ|)
    (hΩ : (imMatrix (Torus.torusPairs 3) Φ).det ≠ 0)
    (heq : (covMatrix (Torus.torusPairs 3) Φ).det = |(imMatrix (Torus.torusPairs 3) Φ).det|) :
    False := by
  have hd (i : Fin 3) : 0 < gramDefectC (fluct (Torus.torusPairs 3) Φ (0, i))
      (fluct (Torus.torusPairs 3) Φ (1, i)) := Torus.gramDefect_pos i hΦ (hb i)
  have hcomm := TorusCommute.torusPairs_comm (k := 3)
  have hsym := TorusCommute.torusPairs_isSymmetric (k := 3)
  have htop (i : Fin 3) := RobertsonEqualityPlane.map_fiberPart_eq_top
    (fun s t i j h ψ => hcomm s t i j h ψ) hsym i (hd i) hΩ heq
  have hdim : 3 ≤ Module.finrank ℂ (rel Φ) := le_finrank_ker hΩ heq
  -- a relation with a prescribed part on `z`
  have hpre (u : Fin 2 → ℂ) : ∃ c ∈ rel Φ, fiberPart 2 c = u := by
    have : u ∈ (rel Φ).map (fiberPart 2) := (htop 2) ▸ trivial
    obtain ⟨c, hc, hcu⟩ := this
    exact ⟨c, hc, hcu⟩
  -- `r` vanishes on `x`, `t` on `y`; neither on `z`
  obtain ⟨r, hr, hr0, hrx⟩ := exists_rel_zero hdim 0
  obtain ⟨t, ht, ht0, hty⟩ := exists_rel_zero hdim 1
  have hrz := part_ne_zero hr hr0 (a := 0) (b := 1) (m := 2) (by decide) (by decide) (by decide)
    (hd 1) hrx
  have htz := part_ne_zero ht ht0 (a := 1) (b := 0) (m := 2) (by decide) (by decide) (by decide)
    (hd 0) hty
  -- `s` independent of `r` on `z`
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → ℂ, r (0, 2) * u 1 - r (1, 2) * u 0 ≠ 0 := by
    by_cases h1 : r (1, 2) = 0
    · have h0 : r (0, 2) ≠ 0 := by
        intro h0; apply hrz; funext s; fin_cases s; exacts [h0, h1]
      exact ⟨![0, 1], by simpa [h1] using h0⟩
    · exact ⟨![1, 0], by simpa using h1⟩
  obtain ⟨s, hs, hsu⟩ := hpre u
  have mem (c : Fin 2 × Fin 3 → ℂ) (hc : c ∈ rel Φ) : axesOf c ∈ alg Φ :=
    LieSubalgebra.subset_lieSpan ⟨c, hc, rfl⟩
  -- the element on `z` alone
  set Z := ⁅⁅axesOf r, axesOf s⁆, axesOf t⁆
  have hZ : Z ∈ alg Φ :=
    LieSubalgebra.lie_mem _ (LieSubalgebra.lie_mem _ (mem r hr) (mem s hs)) (mem t ht)
  have hr0' : axesOf r 0 = 0 := by
    simp [axesOf, show r (0, 0) = 0 from congrFun hrx 0, show r (1, 0) = 0 from congrFun hrx 1]
  have ht1' : axesOf t 1 = 0 := by
    simp [axesOf, show t (0, 1) = 0 from congrFun hty 0, show t (1, 1) = 0 from congrFun hty 1]
  have hZ0 : Z 0 = 0 := by simp [Z, hr0']
  have hZ1 : Z 1 = 0 := by simp [Z, ht1']
  have hZ2 : Z 2 ≠ 0 := by
    have hsu0 : s (0, 2) = u 0 := congrFun hsu 0
    have hsu1 : s (1, 2) = u 1 := congrFun hsu 1
    simp only [Z, lie_apply, axesOf, lie_comb, smul_lie, hsu0, hsu1]
    refine smul_ne_zero hu (lie_lie_ne_zero ?_)
    by_contra h
    push Not at h
    apply htz; funext s; fin_cases s; exacts [h.1, h.2]
  -- the `z` parts contain every `E_ij`
  have stable {L : TAxes} (hL : L ∈ alg Φ) : ∀ F ∈ zPart Φ, ⁅L 2, F⁆ ∈ zPart Φ := by
    intro F hF
    obtain ⟨W, hW, h0, h1, rfl⟩ := mem_zPart.mp hF
    exact mem_zPart.mpr ⟨⁅L, W⁆, LieSubalgebra.lie_mem _ hL hW,
      by rw [lie_apply, h0, lie_zero], by rw [lie_apply, h1, lie_zero], lie_apply _ _ _⟩
  obtain ⟨a, ha, ha2⟩ := hpre ![1, 0]
  obtain ⟨b, hb', hb2⟩ := hpre ![0, 1]
  have hTa : axesOf a 2 = ClosedThree.Tc := by
    simp [axesOf, show a (0, 2) = 1 from congrFun ha2 0, show a (1, 2) = 0 from congrFun ha2 1]
  have hPb : axesOf b 2 = Pd 3 := by
    simp [axesOf, show b (0, 2) = 0 from congrFun hb2 0, show b (1, 2) = 1 from congrFun hb2 1]
  have hT : ∀ F ∈ zPart Φ, ⁅ClosedThree.Tc, F⁆ ∈ zPart Φ := hTa ▸ stable (mem a ha)
  have hP : ∀ F ∈ zPart Φ, ⁅Pd 3, F⁆ ∈ zPart Φ := hPb ▸ stable (mem b hb')
  have htr : ∀ F ∈ zPart Φ, F.trace = 0 := by
    intro F hF
    obtain ⟨W, hW, -, -, rfl⟩ := mem_zPart.mp hF
    exact trace_apply Φ hW 2
  have hne : zPart Φ ≠ ⊥ := by
    intro hbot
    have : Z 2 ∈ zPart Φ := mem_zPart.mpr ⟨Z, hZ, hZ0, hZ1, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hZ2 this
  have single {i j : Fin 3} (hij : i ≠ j) := mem_zPart.mp (single_mem hT hP htr hne hij)
  obtain ⟨Z01, hZ01, a0, a1, a2⟩ := single (i := 0) (j := 1) (by decide)
  obtain ⟨Z10, hZ10, b0, b1, b2⟩ := single (i := 1) (j := 0) (by decide)
  obtain ⟨Z12, hZ12, c0, c1, c2⟩ := single (i := 1) (j := 2) (by decide)
  obtain ⟨Z21, hZ21, d0, d1, d2⟩ := single (i := 2) (j := 1) (by decide)
  -- the two brackets on `z` annihilate `Φ`
  have onZ {X Y : TAxes} (x0 : X 0 = 0) (x1 : X 1 = 0) :
      lam ⁅X, Y⁆ = liftAlong (split 2) ⁅X 2, Y 2⁆ := by
    rw [lam_single (i := 2) fun j hj => ?_, lie_apply]
    have hj' : j = 0 ∨ j = 1 := by fin_cases j <;> simp_all
    rcases hj' with rfl | rfl
    · rw [lie_apply, x0, zero_lie]
    · rw [lie_apply, x1, zero_lie]
  have k₁ := kill Φ hZ01 hZ10
  have k₂ := kill Φ hZ12 hZ21
  rw [onZ a0 a1, a2, b2, Ring.lie_def, single_mul_single_same, single_mul_single_same, mul_one,
    toOp_apply] at k₁
  rw [onZ c0 c1, c2, d2, Ring.lie_def, single_mul_single_same, single_mul_single_same, mul_one,
    toOp_apply] at k₂
  have h0 := eq_zero_of_lift₂ (split 2) (fun v h₁ h₂ => no_common_kernel v h₁ h₂) k₁ k₂
  rw [h0, norm_zero] at hΦ
  exact zero_ne_one hΦ

/-- **Robertson 1934 is strict on the three-torus**: every unit state with every axis in its
band has `|det Ω₆| < det Σ₆`, entangled across the axes or not. -/
theorem robertson_det_torus_lt {Φ : Torus.HT 3} (hΦ : ‖Φ‖ = 1)
    (hb : ∀ i, 1 < |tensionG (Torus.torusPairs 3 (0, i)) (Torus.torusPairs 3 (1, i)) Φ|) :
    |(imMatrix (Torus.torusPairs 3) Φ).det| < (covMatrix (Torus.torusPairs 3) Φ).det := by
  have hΩ : (imMatrix (Torus.torusPairs 3) Φ).det ≠ 0 := by
    intro hΩ
    have h := BoxStrict.abs_det_imMatrix_eq Φ
      (fun s t i j h ψ => TorusCommute.torusPairs_comm s t i j h ψ)
      TorusCommute.torusPairs_isSymmetric
    rw [hΩ, abs_zero, eq_comm] at h
    have hne (i : Fin 3) :
        tensionG (Torus.torusPairs 3 (0, i)) (Torus.torusPairs 3 (1, i)) Φ / 2 ≠ 0 := by
      refine div_ne_zero (fun h0 => ?_) two_ne_zero
      have := hb i
      rw [h0, abs_zero] at this
      norm_num at this
    exact pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun i _ => hne i) h
  exact (robertson_det _ Φ).lt_of_ne fun heq => eq_zero_of_det_eq hΦ hb hΩ heq.symm

end TorusStrict
