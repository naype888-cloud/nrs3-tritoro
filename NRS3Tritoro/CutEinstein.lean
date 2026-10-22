/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.FiberBoundary
public import NRS3Tritoro.Gravity.EinsteinEquation

/-!
# The Einstein equation with the entropy per unit area of the cuts

Jacobson's chain (`Gravity`: `Rindler`, `LightSheet`, `Einstein`) takes the area law `δS = η δA`
as its input. Here `η` is the entropy per unit area of a cut, one bit and area `a²` per boundary
step (`ClausiusInput`), and it is `1 / (4 ℓ_P²)` on every cut of the open cube, of `T³` and of the
fibred box. So on every local light sheet the Clausius relation with the Unruh temperature is

  `R_kk = 8π ℓ_P² T_kk`,

and, if it holds on every light sheet through every point, the Ricci form obeys the Einstein
equation with a cosmological constant and the coupling `8π ℓ_P²`, Einstein's `8π G` in units
`ħ = c = 1`. The contracted Bianchi identity and the conservation of `T` enter as in
`Einstein.einstein_equation`.

## Main results

- `CutEinstein.clausius_cut` : with the `η` of a cut, Clausius is `R_kk = 8π ℓ_P² T_kk`.
- `CutEinstein.einstein_cut` : the Einstein equation with coupling `8π ℓ_P²`.
- `CutEinstein.clausius_openCube`, `CutEinstein.clausius_torus`, `CutEinstein.clausius_fiber` :
  the three topologies.
-/

@[expose] public noncomputable section

open ClausiusInput Lorentz Vector
open LinearMap (BilinForm)

namespace CutEinstein

variable {α : Type*} {X : Finset α} {a ℓ κ Rkk Tkk A l₀ : ℝ}

/-- **With the entropy per unit area of a cut, the Clausius relation is `R_kk = 8π ℓ_P² T_kk`.** -/
theorem clausius_cut (hη : entropyPerArea X a = 1 / (4 * ℓ ^ 2)) (hℓ : ℓ ≠ 0) (hκ : κ ≠ 0)
    (hA : A ≠ 0) (hl : l₀ ≠ 0) :
    LightSheet.Clausius (entropyPerArea X a) κ Rkk Tkk A l₀ ↔
      Rkk = 8 * Real.pi * ℓ ^ 2 * Tkk := by
  rw [hη]
  exact LightSheet.eight_pi hℓ hκ hA hl

lemma coupling_eq (hη : entropyPerArea X a = 1 / (4 * ℓ ^ 2)) (hℓ : ℓ ≠ 0) :
    2 * Real.pi / entropyPerArea X a = 8 * Real.pi * ℓ ^ 2 := by
  rw [hη]
  field_simp
  ring

/-- **The Einstein equation from the cuts.** If the Clausius relation with the `η` of a cut holds
on every light sheet through every point, then `Ric − ½ R g + Λ g = 8π ℓ_P² T` for a constant
`Λ`. -/
theorem einstein_cut {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ric T : E → BilinForm ℝ (Lorentz.Vector d)} (hRic : ∀ x, (Ric x).IsSymm)
    (hT : ∀ x, (T x).IsSymm) (hη : entropyPerArea X a = 1 / (4 * ℓ ^ 2)) (hℓ : ℓ ≠ 0)
    (hκ : κ ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0)
    (hC : ∀ x, ∀ k : Lorentz.Vector d, ⟪k, k⟫ₘ = 0 →
      LightSheet.Clausius (entropyPerArea X a) κ (Ric x k k) (T x k k) A l₀)
    (hf : Differentiable ℝ fun x => Einstein.fScalar (8 * Real.pi * ℓ ^ 2) (Ric x) (T x))
    (hR : Differentiable ℝ fun x => Lorentz.Vector.trace (Ric x))
    (hBianchi : ∀ x, fderiv ℝ (fun x => Einstein.fScalar (8 * Real.pi * ℓ ^ 2) (Ric x) (T x)) x =
      (1 / 2 : ℝ) • fderiv ℝ (fun x => Lorentz.Vector.trace (Ric x)) x) :
    ∃ Λ : ℝ, ∀ x, ∀ p q, Ric x p q - Lorentz.Vector.trace (Ric x) / 2 * ⟪p, q⟫ₘ +
      Λ * ⟪p, q⟫ₘ = 8 * Real.pi * ℓ ^ 2 * T x p q := by
  have hη0 : entropyPerArea X a ≠ 0 := by rw [hη]; positivity
  have key := coupling_eq hη hℓ
  obtain ⟨Λ, h⟩ := Einstein.einstein_equation hRic hT hκ hA hl hη0 hC (by rwa [key])
    hR (by rwa [key])
  exact ⟨Λ, fun x p q => by rw [← key]; exact (h x).1 p q⟩

variable {dx dy dz c : ℕ}

/-- On the open cube, `R_kk = 8π ℓ_P² T_kk`. -/
theorem clausius_openCube (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) (hκ : κ ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0) :
    LightSheet.Clausius (entropyPerArea (OpenCubeBoundary.openCrossSteps dx dy dz c) a)
        κ Rkk Tkk A l₀ ↔ Rkk = 8 * Real.pi * ℓ ^ 2 * Tkk :=
  clausius_cut (openCube_eta hy hz hc hℓ ha) hℓ hκ hA hl

/-- On the three-torus, `R_kk = 8π ℓ_P² T_kk`. -/
theorem clausius_torus (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) (hd : 3 ≤ dx)
    (hℓ : ℓ ≠ 0) (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) (hκ : κ ≠ 0) (hA : A ≠ 0)
    (hl : l₀ ≠ 0) :
    LightSheet.Clausius (entropyPerArea (TorusArea.crossSteps dx dy dz c) a) κ Rkk Tkk A l₀ ↔
      Rkk = 8 * Real.pi * ℓ ^ 2 * Tkk :=
  clausius_cut (torus_eta hy hz hc hd hℓ ha) hℓ hκ hA hl

/-- Across the fiber of the fibred box, `R_kk = 8π ℓ_P² T_kk`. -/
theorem clausius_fiber (hx : 0 < dx) (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < 3) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) (hκ : κ ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0) :
    LightSheet.Clausius (entropyPerArea (FiberBoundary.wSteps dx dy dz c) a) κ Rkk Tkk A l₀ ↔
      Rkk = 8 * Real.pi * ℓ ^ 2 * Tkk :=
  clausius_cut (FiberBoundary.eta_w hx hy hz hc hℓ ha) hℓ hκ hA hl

end CutEinstein
