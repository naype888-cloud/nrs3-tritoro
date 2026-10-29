/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindUnique
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The geometry of the links, from their algebra

The geometry is not an extra structure: it is the non-commutation graph of the link algebra.
The electric term of a link `e` is the projector `P_e`; the magnetic term of a plaquette `q` is
a multiplication operator that depends only on the four links of `q`. The two commute unless
`e` is a link of `q` (`elecProj_mul_comm`). So two links interact exactly when they are links of a
common plaquette of `R`, and the distance between links is the number of such steps. It is the
discrete form of the NRS cone: one link per step, `|⟨K⟩| ≤ 1`.

## Main results

- `KogutSusskindGeometry.linkGraph` : the interaction graph on the links; its `edist` is the
  distance.
- `KogutSusskindGeometry.elecProj_mul_comm` : `P_e` commutes with the multiplication by a function
  that does not depend on the link `e`.
- `KogutSusskindGeometry.pot_mixed_diff_zero` : if no plaquette of `R` contains both links `e` and
  `e'`, the mixed second difference of the Wilson potential vanishes.
- `KogutSusskindGeometry.adj_card_le` : a link has at most `3 Δ` neighbours.

The mixed difference of the potential is the source of the recursion for the second difference of
`log r`: it is zero beyond distance one, and bounded by `4 n` (per shared plaquette) at distance
one. The bounded degree is what makes the number of links at distance `d` grow at most like
`(3 Δ)^d`.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindHarnack

namespace KogutSusskindGeometry

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]

/-! ## 1. The algebra: the projector of a link commutes with what does not touch it -/

/-- **The projector of the link `e` commutes with a function that does not depend on `e`.** -/
theorem elecProj_mul_comm (e : δ × ι) (f : Conf ι δ G → ℂ)
    (hf : ∀ (k : G) (U : Conf ι δ G), f (shift k e.1 e.2 U) = f U) (ψ : State ι δ G) :
    elecProj e.1 e.2 (fun U => f U * ψ U) = fun U => f U * elecProj e.1 e.2 ψ U := by
  funext U
  unfold elecProj
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  beta_reduce
  rw [hf h U]; ring

/-! ## 2. The interaction graph -/

variable {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι)
  (R : Finset (ι × δ × δ))

/-- Two links interact when they are two different links of a common plaquette of `R`. -/
def linkGraph : SimpleGraph (δ × ι) where
  Adj e e' := e ≠ e' ∧ ∃ q ∈ R, e ∈ links τ q ∧ e' ∈ links τ q
  symm := ⟨fun _ _ ⟨hne, q, hq, h1, h2⟩ => ⟨hne.symm, q, hq, h2, h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The distance between links: the number of interaction steps. -/
def linkDist (e e' : δ × ι) : ℕ∞ := (linkGraph τ R).edist e e'

theorem linkDist_triangle (a b c : δ × ι) :
    linkDist τ R a c ≤ linkDist τ R a b + linkDist τ R b c :=
  SimpleGraph.edist_triangle

theorem linkDist_comm (a b : δ × ι) : linkDist τ R a b = linkDist τ R b a :=
  SimpleGraph.edist_comm

theorem linkDist_self (a : δ × ι) : linkDist τ R a a = 0 := SimpleGraph.edist_self

/-- Two different links with no plaquette in common are not neighbours. -/
theorem not_adj_of_no_common {e e' : δ × ι}
    (h : ¬ ∃ q ∈ R, e ∈ links τ q ∧ e' ∈ links τ q) : ¬ (linkGraph τ R).Adj e e' :=
  fun ha => h ha.2

/-! ## 3. Locality of the Wilson potential -/

/-- **The mixed second difference of the potential is zero beyond distance one**: if no plaquette
of `R` contains both `e` and `e'`, changing `e` and changing `e'` do not interact. -/
theorem pot_mixed_diff_zero {e e' : δ × ι}
    (h : ¬ ∃ q ∈ R, e ∈ links τ q ∧ e' ∈ links τ q) (hne : e ≠ e') (k k' : G)
    (U : Conf ι δ G) :
    pot ρ τ R (shift k e.1 e.2 (shift k' e'.1 e'.2 U)) + pot ρ τ R U
      = pot ρ τ R (shift k e.1 e.2 U) + pot ρ τ R (shift k' e'.1 e'.2 U) := by
  simp only [pot_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hcomm : shift k' e'.1 e'.2 (shift k e.1 e.2 U) = shift k e.1 e.2 (shift k' e'.1 e'.2 U) :=
    shift_comm (by simpa using hne.symm) k' k U
  by_cases he : e ∈ links τ q
  · have he' : e' ∉ links τ q := fun he' => h ⟨q, hq, he, he'⟩
    have a1 := dens_shift_eq ρ τ he' k' (shift k e.1 e.2 U)
    have a2 := dens_shift_eq ρ τ he' k' U
    rw [hcomm] at a1
    rw [a1, a2]
  · have a1 := dens_shift_eq ρ τ he k (shift k' e'.1 e'.2 U)
    have a2 := dens_shift_eq ρ τ he k U
    rw [a1, a2]
    ring

/-- A link that is in no plaquette of `R` does not change the potential. -/
theorem pot_shift_eq {e : δ × ι} (h : ∀ q ∈ R, e ∉ links τ q) (k : G) (U : Conf ι δ G) :
    pot ρ τ R (shift k e.1 e.2 U) = pot ρ τ R U := by
  simp only [pot_eq_sum]
  exact Finset.sum_congr rfl fun q hq => dens_shift_eq ρ τ (h q hq) k U

/-- **The projector of a link commutes with the magnetic term** unless the link is in a
plaquette of `R`. -/
theorem elecProj_mag_comm {e : δ × ι} (h : ∀ q ∈ R, e ∉ links τ q) (ψ : State ι δ G) :
    elecProj e.1 e.2 (mag ρ τ R ψ) = mag ρ τ R (elecProj e.1 e.2 ψ) := by
  have := elecProj_mul_comm e (fun U => (pot ρ τ R U : ℂ))
    (fun k U => by rw [pot_shift_eq ρ τ R h k U]) ψ
  exact this

open scoped Classical in
/-- **Bounded degree**: a link has at most `3 Δ` neighbours, if at most `Δ` plaquettes of `R`
pass through any link. -/
theorem adj_card_le {Δ : ℕ} (hΔ : ∀ e : δ × ι, (R.filter fun q => e ∈ links τ q).card ≤ Δ)
    (e : δ × ι) :
    (Finset.univ.filter fun e' => (linkGraph τ R).Adj e e').card ≤ 3 * Δ := by
  classical
  have hsub : (Finset.univ.filter fun e' => (linkGraph τ R).Adj e e')
      ⊆ (R.filter fun q => e ∈ links τ q).biUnion (fun q => (links τ q).erase e) := by
    intro e' he'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
    obtain ⟨hne, q, hq, h1, h2⟩ := he'
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase]
    exact ⟨q, ⟨hq, h1⟩, hne.symm, h2⟩
  calc _ ≤ ((R.filter fun q => e ∈ links τ q).biUnion (fun q => (links τ q).erase e)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ R.filter (fun q => e ∈ links τ q), ((links τ q).erase e).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ R.filter (fun q => e ∈ links τ q), 3 := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hmem : e ∈ links τ q := (Finset.mem_filter.mp hq).2
        have h4 : (links τ q).card ≤ 4 := by
          unfold links
          exact Finset.card_le_four
        rw [Finset.card_erase_of_mem hmem]
        omega
    _ = (R.filter fun q => e ∈ links τ q).card * 3 := by simp
    _ ≤ Δ * 3 := Nat.mul_le_mul_right 3 (hΔ e)
    _ = 3 * Δ := by ring

end KogutSusskindGeometry
