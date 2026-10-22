/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import NRS3Tritoro.TorusField
public import NRS3Tritoro.TorusSaturation

/-!
# The bits of the boundary are carried by the field

`TorusField` showed that the bracket of the field, `⁅dΓ T3c, dΓ P_x⁆ = dΓ [T3c, P_x]`, is nonzero
across the region `{x ≤ c}` exactly on the `2 · dy · dz` boundary steps that `TorusArea` counts.
Here each configuration `S` of the cut, the set of its open steps, becomes a field operator: the
bracket kept on the open steps,

  `F(S) = Σ_{(p, q) ∈ S} [T3c, P_x]_pq a†_p a_q`,

so an open step is a step on which the field moves an excitation across the cut, and a closed
step is one on which it does not.

With the star structure (`IsStar`) the sector of one excitation is a faithful copy of the
positions, so second quantization is injective: different matrices give different field
operators. Different configurations give different brackets, because the bracket does not vanish
on any boundary step. So `S ↦ F(S)` is injective: the field carries exactly `2^(2 · dy · dz)`
configurations, and the log of their number is the entropy `S` of the cut. The Bekenstein bound
of `TorusBekenstein` and the saturation of `TorusSaturation` are statements about the field.

## Main results

- `TorusBoundaryField.oneExcitation_injective` : the one-excitation sector is faithful.
- `TorusBoundaryField.secondQuant_injective` : `M ↦ dΓ M` is injective.
- `TorusBoundaryField.cutBracket_injective` : configurations have distinct brackets.
- `TorusBoundaryField.configField_eq_sum` : `F(S) = Σ_{(p, q) ∈ S} [T3c, P_x]_pq a†_p a_q`.
- `TorusBoundaryField.configField_injective` : `S ↦ F(S)` is injective.
- `TorusBoundaryField.card_fieldConfigs` : the field carries `2^(2 · dy · dz)` configurations.
- `TorusBoundaryField.log_card_fieldConfigs` : their log is the entropy of the cut.
-/

@[expose] public noncomputable section

open TorusArea TorusBekenstein TorusField
open PathGraph3D (Site3D)
open scoped ComplexOrder

namespace TorusBoundaryField

/-! ## 1. Second quantization is faithful -/

section Faithful

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} {V : Type*} [AddCommGroup V]
  [Module ℂ V] {L : LadderSystem ℂ V d} (e : ι ≃ Fin d) {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Ω : V}

/-- With the star structure the sector of one excitation is a faithful copy of the positions. -/
theorem oneExcitation_injective (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1) :
    Function.Injective (oneExcitation L e Ω) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ h
  have hf := form_oneExcitation e hL hΩ hn ψ ψ
  simp only [h, map_zero] at hf
  exact dotProduct_star_self_eq_zero.1 hf.symm

/-- **Second quantization is faithful**: different matrices give different field operators. -/
theorem secondQuant_injective (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1) :
    Function.Injective (secondQuant L e) := by
  intro M N h
  refine Matrix.ext_iff_mulVec.2 fun ψ => oneExcitation_injective e hL hΩ hn ?_
  rw [← secondQuant_oneExcitation L e hΩ, ← secondQuant_oneExcitation L e hΩ, h]

end Faithful

/-! ## 2. The field operator of a configuration -/

variable {dx dy dz c : ℕ}

/-- The bracket of a configuration: `[T3c, P_x]` on its open steps, `0` elsewhere. -/
def cutBracket (S : Config dx dy dz c) : Matrix (Site3D dx dy dz) (Site3D dx dy dz) ℂ :=
  fun p q => if (p, q) ∈ S.1 then bracketX dx dy dz p q else 0

/-- An open step is exactly a step where the bracket of the configuration does not vanish. -/
lemma mem_iff_cutBracket_ne_zero (hd : 3 ≤ dx) (S : Config dx dy dz c)
    (p q : Site3D dx dy dz) : (p, q) ∈ S.1 ↔ cutBracket S p q ≠ 0 := by
  unfold cutBracket
  by_cases hm : (p, q) ∈ S.1
  · have hc := Finset.mem_powerset.1 S.2 hm
    rw [← bracketCrossSteps_eq hd] at hc
    simpa [hm] using (Finset.mem_filter.1 hc).2.2.2
  · simp [hm]

/-- **Different configurations have different brackets.** -/
theorem cutBracket_injective (hd : 3 ≤ dx) :
    Function.Injective (cutBracket : Config dx dy dz c → _) := by
  intro S T h
  apply Subtype.ext
  ext ⟨p, q⟩
  rw [mem_iff_cutBracket_ne_zero hd, mem_iff_cutBracket_ne_zero hd, h]

variable {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] (L : LadderSystem ℂ V d)
  (e : Site3D dx dy dz ≃ Fin d)

/-- The field operator of a configuration: the bracket of the field kept on its open steps. -/
def configField (S : Config dx dy dz c) : Module.End ℂ V :=
  secondQuant L e (cutBracket S)

/-- **Each open step moves an excitation across the cut**:
`F(S) = Σ_{(p, q) ∈ S} [T3c, P_x]_pq a†_p a_q`. -/
theorem configField_eq_sum (S : Config dx dy dz c) :
    configField L e S = ∑ s ∈ S.1, bracketX dx dy dz s.1 s.2 • L.E (e s.1) (e s.2) := by
  rw [configField, secondQuant_eq_sum, ← Finset.sum_product' (s := Finset.univ)
    (t := Finset.univ) (f := fun p q => cutBracket S p q • L.E (e p) (e q)),
    Finset.univ_product_univ]
  simp only [cutBracket, ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

variable {L} {β : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {Ω : V}

/-- **The bits of the boundary are carried by the field**: `S ↦ F(S)` is injective. -/
theorem configField_injective (hd : 3 ≤ dx) (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0)
    (hn : β Ω Ω = 1) : Function.Injective (configField L e : Config dx dy dz c → _) :=
  (secondQuant_injective e hL hΩ hn).comp (cutBracket_injective hd)

open Classical in
/-- The field carries `2^(2 · dy · dz)` configurations of the cut. -/
theorem card_fieldConfigs (hc : c + 1 < dx) (hd : 3 ≤ dx) (hL : IsStar L β)
    (hΩ : ∀ i, L.a i Ω = 0) (hn : β Ω Ω = 1) :
    (Finset.univ.image (configField L e : Config dx dy dz c → _)).card = 2 ^ (2 * (dy * dz)) := by
  rw [Finset.card_image_of_injective _ (configField_injective e hd hL hΩ hn), Finset.card_univ,
    Fintype.card_coe, Finset.card_powerset, card_crossSteps hc hd]

open Classical in
/-- **The entropy of the cut counts field operators**: `log #F = S`. -/
theorem log_card_fieldConfigs (hd : 3 ≤ dx) (hL : IsStar L β) (hΩ : ∀ i, L.a i Ω = 0)
    (hn : β Ω Ω = 1) :
    Real.log (Finset.univ.image (configField L e : Config dx dy dz c → _)).card =
      cutEntropy dx dy dz c := by
  rw [Finset.card_image_of_injective _ (configField_injective e hd hL hΩ hn), Finset.card_univ,
    log_card_config]

end TorusBoundaryField
