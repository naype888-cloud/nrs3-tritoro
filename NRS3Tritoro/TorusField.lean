/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusArea
public import PhyslibAlpha.Mathematics.LadderSystem.Vacuum

/-!
# The three-torus at the level of the quantized field

Give each position `p` of the torus a mode, through a bijection `e` of the positions with
`Fin d`, and let `L` be a ladder system of `d` modes (`LadderSystem`, the canonical commutation
relations of Physlib). Second quantization sends a matrix `M` of the torus to
`dΓ M = Σ M_pq a†_p a_q`. It respects brackets in every excitation sector,
`⁅dΓ T3c, dΓ P_x⁆ = dΓ [T3c, P_x]`: the bracket of the field is the field of the bracket.

The sector of one excitation over a vacuum `Ω` is the torus itself: `ψ ↦ Σ ψ_p a†_p Ω` carries
`M ψ` to `dΓ M`. To speak of variances the field needs a star structure: a sesquilinear form `β`
for which `a†` is the adjoint of `a`, with `β(Ω, Ω) = 1`. Physlib still lists that adjointness
as a TODO for the harmonic oscillator, so here it is a hypothesis, `IsStar`, and nothing else is
assumed. Under it the embedding preserves `β`, every expectation of `dΓ M`, `dΓ M dΓ N` and
`⁅dΓ M, dΓ N⁆` equals the one of the torus, and the uncertainty field
`𝒰 = Var · Var − |⟨[A, B]⟩|² / 4` of the field is the one of the torus.

The sections 1 and 2 are the construction of `NRS3DefectCurvature.FieldLevel` for the cube,
which holds for any finite set of positions; it is restated here because the two repositories pin
different versions of `NavaRobertsonIndependent`.

On the torus the bracket `[T3c, P_x]` is `T3c p q (x_q − x_p)`. Across the region `{x ≤ c}` it is
nonzero exactly on the `2 · dy · dz` boundary steps, the plane and the seam: the bracket of the
field sees the same cut as the entropy.

## Main results

- `TorusField.secondQuant_lie` : `dΓ ⁅M, N⁆ = ⁅dΓ M, dΓ N⁆`, on all of `V`.
- `TorusField.secondQuant_oneExcitation` : `dΓ M (Σ ψ_p a†_p Ω) = Σ (M ψ)_p a†_p Ω`.
- `TorusField.form_oneExcitation` : with the star structure, `β` restricts to `ψ̄ · φ`.
- `TorusField.uncertainty_oneExcitation` : the uncertainty field of the one-excitation field
  state is the uncertainty field of the torus state.
- `TorusField.lie_secondQuant_torus` : `⁅dΓ T3c, dΓ P_x⁆ = dΓ [T3c, P_x]` in every sector.
- `TorusField.bracketX_apply` : the bracket is `T3c p q (x_q − x_p)`.
- `TorusField.bracketCrossSteps_eq` : across the region `{x ≤ c}` the bracket is nonzero
  exactly on the boundary steps, so `card_bracketCrossSteps` : it sees `2 · dy · dz` steps.
- `TorusField.uncertainty_torus` : the uncertainty field of the field state for the transport
  and the position of the torus is the one of the torus state.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS LightCone TorusArea
open scoped Matrix
open PathGraph3D (Site3D)

namespace TorusField

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-! ## 1. Second quantization -/

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (L : LadderSystem ℂ V d) (e : ι ≃ Fin d)

/-- Second quantization of a matrix on the positions: `dΓ M = Σ M_pq a†_{e p} a_{e q}`. -/
def secondQuant : Matrix ι ι ℂ →ₗ[ℂ] Module.End ℂ V :=
  L.toGlHomLinear ∘ₗ (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap

omit [DecidableEq ι] in
lemma secondQuant_eq_sum (M : Matrix ι ι ℂ) :
    secondQuant L e M = ∑ p, ∑ q, M p q • L.E (e p) (e q) := by
  rw [secondQuant, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Matrix.matrix_eq_sum_single (Matrix.reindexLinearEquiv ℂ ℂ e e M)]
  simp only [map_sum]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_one (Matrix.reindexLinearEquiv ℂ ℂ e e M (e p) (e q)), ← smul_eq_mul,
    ← Matrix.smul_single, map_smul, LadderSystem.toGlHomLinear_single]
  simp

omit [DecidableEq ι] in
/-- **The bracket of the field is the field of the bracket.** -/
theorem secondQuant_lie (M N : Matrix ι ι ℂ) :
    secondQuant L e ⁅M, N⁆ = ⁅secondQuant L e M, secondQuant L e N⁆ := by
  simp only [secondQuant, LinearMap.comp_apply, LinearEquiv.coe_coe, ← L.toGlHomLinear_lie]
  congr 1
  simp only [Ring.lie_def, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rfl

variable {L}

lemma a_ac_vacuum {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (i j : Fin d) :
    L.a i (L.ac j Ω) = if i = j then Ω else 0 := by
  have h := congrArg (fun f : Module.End ℂ V => f Ω) (L.comm_a_ac i j)
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    hΩ, map_zero, sub_zero] at h
  rw [h]
  split_ifs <;> simp

lemma E_ac_vacuum {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (i j k : Fin d) :
    L.E i j (L.ac k Ω) = if j = k then L.ac i Ω else 0 := by
  change (L.ac i * L.a j) _ = _
  rw [Module.End.mul_apply, a_ac_vacuum hΩ]
  split_ifs <;> simp

variable (L)

/-- The sector of one excitation: the cube state `ψ` as the field state `Σ ψ_p a†_{e p} Ω`. -/
def oneExcitation (Ω : V) : (ι → ℂ) →ₗ[ℂ] V where
  toFun ψ := ∑ p, ψ p • L.ac (e p) Ω
  map_add' ψ φ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r ψ := by simp [Finset.smul_sum, smul_smul]

lemma secondQuant_ac {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ) (r : ι) :
    secondQuant L e M (L.ac (e r) Ω) = ∑ p, M p r • L.ac (e p) Ω := by
  simp only [secondQuant_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply, E_ac_vacuum hΩ,
    EmbeddingLike.apply_eq_iff_eq, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-- **The sector of one excitation is the cube.** `dΓ M` acts on it as `M`. -/
theorem secondQuant_oneExcitation {Ω : V} (hΩ : ∀ i, L.a i Ω = 0) (M : Matrix ι ι ℂ)
    (ψ : ι → ℂ) :
    secondQuant L e M (oneExcitation L e Ω ψ) = oneExcitation L e Ω (M *ᵥ ψ) := by
  simp only [oneExcitation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    secondQuant_ac L e hΩ, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [mul_comm]

end Algebraic

/-! ## 2. The star structure and the uncertainty field -/

section Star

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (L : LadderSystem ℂ V d) (e : ι ≃ Fin d)
  (β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

/-- The star structure of the field: `a†` is the adjoint of `a` for `β`. -/
def IsStar : Prop := ∀ i x y, β (L.ac i x) y = β x (L.a i y)

/-- The uncertainty field of a vector `v` for two operators, with the expectations of `β`:
`Var A · Var B − |⟨[A, B]⟩|² / 4`. -/
def uncertainty {W : Type*} [AddCommGroup W] [Module ℂ W] (β : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (v : W)
    (A B : Module.End ℂ W) : ℝ :=
  (β v ((A * A) v) - β v (A v) ^ 2).re * (β v ((B * B) v) - β v (B v) ^ 2).re -
    ‖β v (⁅A, B⁆ v)‖ ^ 2 / 4

/-- The uncertainty field of a state `ψ` of the cube for two matrices. -/
def matUncertainty (ψ : ι → ℂ) (M N : Matrix ι ι ℂ) : ℝ :=
  (star ψ ⬝ᵥ ((M * M) *ᵥ ψ) - (star ψ ⬝ᵥ (M *ᵥ ψ)) ^ 2).re *
      (star ψ ⬝ᵥ ((N * N) *ᵥ ψ) - (star ψ ⬝ᵥ (N *ᵥ ψ)) ^ 2).re -
    ‖star ψ ⬝ᵥ (⁅M, N⁆ *ᵥ ψ)‖ ^ 2 / 4

variable {L β}
variable {Ω : V} (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1)
include hL hΩ hn

lemma form_ac_vacuum (i j : Fin d) :
    β (L.ac i Ω) (L.ac j Ω) = if i = j then 1 else 0 := by
  rw [hL, a_ac_vacuum hΩ]
  split_ifs <;> simp [hn]

/-- **The star structure restricts to the cube:** `β(Σ ψ_p a†_p Ω, Σ φ_q a†_q Ω) = ψ̄ · φ`. -/
theorem form_oneExcitation (ψ φ : ι → ℂ) :
    β (oneExcitation L e Ω ψ) (oneExcitation L e Ω φ) = star ψ ⬝ᵥ φ := by
  simp only [oneExcitation, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.map_smulₛₗ₂,
    LinearMap.sum_apply, map_smul, form_ac_vacuum hL hΩ hn,
    EmbeddingLike.apply_eq_iff_eq, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [Complex.star_def, mul_comm]

lemma form_secondQuant (M : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    β (oneExcitation L e Ω ψ) (secondQuant L e M (oneExcitation L e Ω ψ)) =
      star ψ ⬝ᵥ (M *ᵥ ψ) := by
  rw [secondQuant_oneExcitation L e hΩ, form_oneExcitation e hL hΩ hn]

lemma form_secondQuant_mul (M N : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    β (oneExcitation L e Ω ψ)
        ((secondQuant L e M * secondQuant L e N) (oneExcitation L e Ω ψ)) =
      star ψ ⬝ᵥ ((M * N) *ᵥ ψ) := by
  rw [Module.End.mul_apply, secondQuant_oneExcitation L e hΩ, secondQuant_oneExcitation L e hΩ,
    form_oneExcitation e hL hΩ hn, Matrix.mulVec_mulVec]

/-- **The bracket of the field reads the bracket of the cube.** -/
theorem form_lie_secondQuant (M N : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    β (oneExcitation L e Ω ψ) (⁅secondQuant L e M, secondQuant L e N⁆ (oneExcitation L e Ω ψ)) =
      star ψ ⬝ᵥ (⁅M, N⁆ *ᵥ ψ) := by
  rw [← secondQuant_lie, form_secondQuant e hL hΩ hn]

/-- **The uncertainty field of the field is the one of the cube.** -/
theorem uncertainty_oneExcitation (M N : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    uncertainty β (oneExcitation L e Ω ψ) (secondQuant L e M) (secondQuant L e N) =
      matUncertainty ψ M N := by
  rw [uncertainty, matUncertainty, form_secondQuant_mul e hL hΩ hn,
    form_secondQuant_mul e hL hΩ hn, form_secondQuant e hL hΩ hn, form_secondQuant e hL hΩ hn,
    form_lie_secondQuant e hL hΩ hn]

end Star

/-! ## 3. The cut of the torus at the level of the field -/

section Torus

variable {dx dy dz : ℕ}

/-- The `x` position of the torus: `P_d` on the `x` axis, identity on `y, z`. -/
def posX (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  liftAlong (eX dx dy dz) (Pd dx)

/-- The bracket of the torus transport with the `x` position: `[T3c, P_x]`. -/
def bracketX (dx dy dz : ℕ) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  T3c dx dy dz * posX dx dy dz - posX dx dy dz * T3c dx dy dz

lemma posX_apply (p q : Site3D dx dy dz) :
    posX dx dy dz p q = if p = q then (posCoord dx p.1 : ℂ) else 0 := by
  obtain ⟨i, j, k⟩ := p
  obtain ⟨i', j', k'⟩ := q
  by_cases h : i = i' <;> by_cases h' : (j, k) = (j', k') <;>
    simp_all [posX, liftAlong, eX, Pd]

/-- **The bracket on a step is the step times the distance it moves in `x`.** -/
theorem bracketX_apply (p q : Site3D dx dy dz) :
    bracketX dx dy dz p q = T3c dx dy dz p q * ((posCoord dx q.1 : ℂ) - posCoord dx p.1) := by
  simp only [bracketX, Matrix.sub_apply, Matrix.mul_apply, posX_apply, mul_ite, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- Distinct positions have distinct coordinates. -/
lemma posCoord_ne (hd : 2 ≤ dx) {i j : Fin dx} (h : i ≠ j) : posCoord dx i ≠ posCoord dx j := by
  intro h'
  have hd1 : (dx : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < dx := by exact_mod_cast (show 1 < dx by omega)
    linarith
  unfold posCoord at h'
  rw [div_left_inj' hd1] at h'
  exact h (Fin.ext (by exact_mod_cast (by linarith : (i.val : ℝ) = j.val)))

/-- **Across the region `{x ≤ c}` the bracket is nonzero exactly where the transport is.** -/
theorem bracketX_ne_zero_iff (hd : 2 ≤ dx) {c : ℕ} {p q : Site3D dx dy dz} (hp : p.1.val ≤ c)
    (hq : c < q.1.val) : bracketX dx dy dz p q ≠ 0 ↔ T3c dx dy dz p q ≠ 0 := by
  have hne : q.1 ≠ p.1 := fun h => by rw [h] at hq; omega
  have hs : (posCoord dx q.1 : ℂ) - posCoord dx p.1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast posCoord_ne hd hne)
  rw [bracketX_apply, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

open Classical in
/-- The steps out of the region `{x ≤ c}` on which the bracket is nonzero. -/
def bracketCrossSteps (dx dy dz c : ℕ) : Finset (Site3D dx dy dz × Site3D dx dy dz) :=
  Finset.univ.filter fun pq => pq.1.1.val ≤ c ∧ c < pq.2.1.val ∧ bracketX dx dy dz pq.1 pq.2 ≠ 0

/-- **The bracket sees the boundary of the region**: the plane and the seam. -/
theorem bracketCrossSteps_eq (hd : 3 ≤ dx) (c : ℕ) :
    bracketCrossSteps dx dy dz c = crossSteps dx dy dz c := by
  ext ⟨p, q⟩
  simp only [bracketCrossSteps, crossSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hq, h⟩
    exact ⟨hp, hq, (bracketX_ne_zero_iff (by omega) hp hq).mp h⟩
  · rintro ⟨hp, hq, h⟩
    exact ⟨hp, hq, (bracketX_ne_zero_iff (by omega) hp hq).mpr h⟩

/-- **The bracket sees `2 · dy · dz` steps**: the area of the two faces of the cut. -/
theorem card_bracketCrossSteps {c : ℕ} (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (bracketCrossSteps dx dy dz c).card = 2 * (dy * dz) := by
  rw [bracketCrossSteps_eq hd, card_crossSteps hc hd]

variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] (L : LadderSystem ℂ V d)
  (e : Site3D dx dy dz ≃ Fin d)

/-- **`⁅dΓ T3c, dΓ P_x⁆ = dΓ [T3c, P_x]`**, in every excitation sector. -/
theorem lie_secondQuant_torus :
    ⁅secondQuant L e (T3c dx dy dz), secondQuant L e (posX dx dy dz)⁆ =
      secondQuant L e (bracketX dx dy dz) := by
  rw [← secondQuant_lie, bracketX, Ring.lie_def]

variable {L} {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Ω : V}

/-- **The uncertainty field of the field is the one of the torus**, for the transport and the
`x` position. -/
theorem uncertainty_torus (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1)
    (ψ : Site3D dx dy dz → ℂ) :
    uncertainty β (oneExcitation L e Ω ψ) (secondQuant L e (T3c dx dy dz))
        (secondQuant L e (posX dx dy dz)) =
      matUncertainty ψ (T3c dx dy dz) (posX dx dy dz) :=
  uncertainty_oneExcitation e hL hΩ hn _ _ ψ

/-- **The bracket of the field reads the bracket of the torus** on the one-excitation sector. -/
theorem form_bracket_torus (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1)
    (ψ : Site3D dx dy dz → ℂ) :
    β (oneExcitation L e Ω ψ)
        (⁅secondQuant L e (T3c dx dy dz), secondQuant L e (posX dx dy dz)⁆
          (oneExcitation L e Ω ψ)) = star ψ ⬝ᵥ (bracketX dx dy dz *ᵥ ψ) := by
  rw [lie_secondQuant_torus, form_secondQuant e hL hΩ hn]

end Torus

end TorusField
