/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.OpenCubeBoundary

/-!
# The input of the Clausius step: one entropy per unit area for every cut

Jacobson's derivation of the Einstein equation takes the area law `δS = η δA` with one constant
`η` for every local horizon, and with `η = 1 / (4 ℓ_P²)` the Clausius relation `δQ = T δS` gives
Einstein's coupling `8π G` (`LightSheet.eight_pi`, PhyslibAlpha). On the open cube and on the
three-torus that input is a theorem: a boundary of `n` steps, each of area `a²` and one bit, has
entropy `n log 2` and area `n a²`, so

  `η = S / A = log 2 / a²`,

the same for every cut: any sizes, any depth, any plane, the open cube and the torus alike. With
the bit of area `a² = 4 ℓ_P² log 2` it is `η = 1 / (4 ℓ_P²)`. The Unruh temperature, the Clausius
relation and the Einstein equation themselves are the steps `G3–G5` on Minkowski in PhyslibAlpha.

## Main results

- `ClausiusInput.entropyPerArea_eq` : `η = log 2 / a²` for any nonempty boundary.
- `ClausiusInput.entropyPerArea_eta` : with the bit of area, `η = 1 / (4 ℓ_P²)`.
- `ClausiusInput.torus_eta`, `ClausiusInput.openCube_eta` : the cuts of `T³` and of the open
  cube.
- `ClausiusInput.eta_universal` : every cut of the torus and of the open cube has the same `η`.
-/

@[expose] public noncomputable section

open TorusArea OpenCubeBoundary
open PathGraph3D (Site3D)

namespace ClausiusInput

variable {α : Type*}

/-- The entropy per unit area of a boundary `X`, one bit and area `a²` per step. -/
def entropyPerArea (X : Finset α) (a : ℝ) : ℝ := (X.card * Real.log 2) / (a ^ 2 * X.card)

/-- **One entropy per unit area**: `η = log 2 / a²`, whatever the boundary. -/
theorem entropyPerArea_eq {X : Finset α} (hX : X.Nonempty) {a : ℝ} (ha : a ≠ 0) :
    entropyPerArea X a = Real.log 2 / a ^ 2 := by
  have hn : (X.card : ℝ) ≠ 0 := by exact_mod_cast hX.card_pos.ne'
  unfold entropyPerArea
  field_simp

/-- With the bit of area `a² = 4 ℓ_P² log 2`, `η = 1 / (4 ℓ_P²)`. -/
theorem entropyPerArea_eta {X : Finset α} (hX : X.Nonempty) {a ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) : entropyPerArea X a = 1 / (4 * ℓ ^ 2) := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : 4 * ℓ ^ 2 * Real.log 2 ≠ 0 := by positivity
    simp_all
  rw [entropyPerArea_eq hX ha0, ha]
  field_simp

variable {dx dy dz c : ℕ} {a ℓ : ℝ}

lemma crossSteps_nonempty (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) (hd : 3 ≤ dx) :
    (crossSteps dx dy dz c).Nonempty := by
  rw [← Finset.card_pos, card_crossSteps hc hd]
  positivity

lemma openCrossSteps_nonempty (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) :
    (openCrossSteps dx dy dz c).Nonempty := by
  rw [← Finset.card_pos, card_openCrossSteps hc]
  positivity

/-- The cut of the three-torus has `η = 1 / (4 ℓ_P²)`. -/
theorem torus_eta (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) (hd : 3 ≤ dx) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    entropyPerArea (crossSteps dx dy dz c) a = 1 / (4 * ℓ ^ 2) :=
  entropyPerArea_eta (crossSteps_nonempty hy hz hc hd) hℓ ha

/-- The cut of the open cube has `η = 1 / (4 ℓ_P²)`. -/
theorem openCube_eta (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = 4 * ℓ ^ 2 * Real.log 2) :
    entropyPerArea (openCrossSteps dx dy dz c) a = 1 / (4 * ℓ ^ 2) :=
  entropyPerArea_eta (openCrossSteps_nonempty hy hz hc) hℓ ha

/-- **The same `η` for every cut**: a cut of the torus and a cut of the open cube, of any sizes,
depths and planes, have the same entropy per unit area. -/
theorem eta_universal {dx' dy' dz' c' : ℕ} (hy : 0 < dy) (hz : 0 < dz) (hc : c + 1 < dx)
    (hd : 3 ≤ dx) (hy' : 0 < dy') (hz' : 0 < dz') (hc' : c' + 1 < dx') (ha : a ≠ 0) :
    entropyPerArea (crossSteps dx dy dz c) a =
      entropyPerArea (openCrossSteps dx' dy' dz' c') a := by
  rw [entropyPerArea_eq (crossSteps_nonempty hy hz hc hd) ha,
    entropyPerArea_eq (openCrossSteps_nonempty hy' hz' hc') ha]

end ClausiusInput
