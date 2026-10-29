/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.KogutSusskindTransform

/-!
# Exact structure of the one-link ratio of the ground state

The first step towards the second difference of `log r`. For `r > 0` with `H r = m0 r` write
`S(U) = Σ_e X_e(U)` (the sum over the links of the averages of `r` over one link). The
eigenvalue equation is `λE · S(U) = a(U) · r(U)` with `a(U) = λE · L + λB · V(U) − m0`.

## Main results

- `KogutSusskindSecondDiff.eigen_S` : `λE · S(U) = a(U) · r(U)`.
- `KogutSusskindSecondDiff.ratio_equation` : for the shifted point `U_k = shift k e U`,
  `a(U_k) · r(U_k) = λE · X_e(U) + λE · |G|⁻¹ · Σ_{e'' ≠ e} Σ_h r (shift k e (shift h e'' U))`.
  The one-link ratio `r(U_k) / r(U)` is, up to the factor `a(U) / a(U_k)`, an average of the same
  ratio over the neighbours `shift h e'' U`, weighted by `r`; the term of the link `e` itself
  carries the ratio `1`.
- `KogutSusskindSecondDiff.term_invariant` : the term of the link `e'` in that equation is the same
  at `U` and at `shift k' e' U`. This is the contraction that a bound on the second difference
  uses: changing the link `e'` does not change its own term.

What these lemmas do not do: bound the mixed difference. For that one still needs a metric on the
links, so that the source is of finite range, and a continuity argument in `λB` to select the
small root of the resulting quadratic inequality.
-/

@[expose] public noncomputable section

open Complex Finset KogutSusskind KogutSusskindGap KogutSusskindSpectrum KogutSusskindGround
  KogutSusskindHarnack

namespace KogutSusskindSecondDiff

variable {ι δ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ] [DecidableEq δ]
  [Group G] [Fintype G] [DecidableEq G]
  {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (τ : δ → ι ≃ ι) (R : Finset (ι × δ × δ))

/-- The sum over the links of the averages of `r`. -/
def S (r : Conf ι δ G → ℝ) (U : Conf ι δ G) : ℝ := ∑ e : δ × ι, X r e U

/-- The coefficient `a(U) = λE · L + λB · V(U) − m0`. -/
def aF (lE lB m0 : ℝ) (U : Conf ι δ G) : ℝ :=
  lE * (Fintype.card (δ × ι) : ℝ) + lB * pot ρ τ R U - m0

theorem eigen_S {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ}
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (U : Conf ι δ G) : lE * S r U = aF ρ τ R lE lB m0 U * r U := by
  have h := eigen_real ρ τ R heig U
  have hsum : ∑ e : δ × ι, (r U - X r e U)
      = (Fintype.card (δ × ι) : ℝ) * r U - S r U := by
    simp [S, Finset.sum_sub_distrib]
  rw [hsum] at h
  unfold aF
  linarith

/-- The averages of the other links, at the shifted point. -/
theorem S_shift (r : Conf ι δ G → ℝ) (e : δ × ι) (k : G) (U : Conf ι δ G) :
    S r (shift k e.1 e.2 U)
      = X r e U + (Fintype.card G : ℝ)⁻¹ * ∑ e' ∈ Finset.univ.erase e, ∑ h : G,
          r (shift k e.1 e.2 (shift h e'.1 e'.2 U)) := by
  unfold S
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  have h1 : X r e (shift k e.1 e.2 U) = X r e U := by
    unfold X
    congr 1
    simp only [shift_shift]
    exact Fintype.sum_equiv (Equiv.mulRight k) _ _ fun h => rfl
  rw [h1]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e' he' => ?_
  have hne : (e'.1, e'.2) ≠ (e.1, e.2) := by simpa using (Finset.mem_erase.mp he').1
  unfold X
  congr 1
  exact Finset.sum_congr rfl fun h _ => by rw [shift_comm hne]

/-- **The equation of the one-link ratio.** -/
theorem ratio_equation {lE lB m0 : ℝ} {r : Conf ι δ G → ℝ}
    (heig : ∀ U, ham ρ τ R lE lB (fun U => (r U : ℂ)) U = (m0 : ℂ) * (r U : ℂ))
    (e : δ × ι) (k : G) (U : Conf ι δ G) :
    aF ρ τ R lE lB m0 (shift k e.1 e.2 U) * r (shift k e.1 e.2 U)
      = lE * X r e U + lE * ((Fintype.card G : ℝ)⁻¹ * ∑ e' ∈ Finset.univ.erase e, ∑ h : G,
          r (shift k e.1 e.2 (shift h e'.1 e'.2 U))) := by
  rw [← eigen_S ρ τ R heig, S_shift]
  ring

/-- **The term of the link `e'` does not see a change of `e'`**: its contribution to the equation
of the ratio of another link `e` is the same at `U` and at `shift k' e' U`. -/
theorem term_invariant (r : Conf ι δ G → ℝ) (e e' : δ × ι) (k k' : G) (U : Conf ι δ G) :
    ∑ h : G, r (shift k e.1 e.2 (shift h e'.1 e'.2 (shift k' e'.1 e'.2 U)))
      = ∑ h : G, r (shift k e.1 e.2 (shift h e'.1 e'.2 U)) := by
  simp only [shift_shift]
  exact Fintype.sum_equiv (Equiv.mulRight k') _ _ fun h => rfl

end KogutSusskindSecondDiff
