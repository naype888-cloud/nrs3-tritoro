/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusDirac

/-!
# Dirac's square root on the three-torus

On `T³ = ZMod a × ZMod b × ZMod c` (even sizes) put the three closed transports `T_x`, `T_y`,
`T_z` and the Kogut–Susskind signs

  `A_x = T_x`, `A_y = (−1)^x T_y`, `A_z = (−1)^(x+y) T_z`, `ε = (−1)^(x+y+z)`.

Each sign flips under the shift of an earlier axis, so the four operators anticommute pairwise,
`A_y² = T_y²`, `A_z² = T_z²` and `ε² = 1`. The massive Dirac operator `D_m = A_x + A_y + A_z + m ε`
squares to

  `D_m² = T_x² + T_y² + T_z² + m²`,

the relativistic relation with `c` one position per step on every axis. The eight waves
`u^x v^y w^z`, `u, v, w ∈ {i, −i}` (`4` divides every size), are the corners `(±π/2)³` of the
momentum cube: every transport kills them, so they are the zero modes of `D_0`, the doublers.
`ε` sends each to the opposite corner, and the mass couples them: `D_m e_{uvw} = m e_{−u,−v,−w}`.

## Main results

- `TorusDirac3.Tx_Ay`, `TorusDirac3.Tx_Az`, `TorusDirac3.Ay_Az`, `TorusDirac3.eps_Tx`,
  `TorusDirac3.eps_Ay`, `TorusDirac3.eps_Az` : the four operators anticommute.
- `TorusDirac3.dirac3_sq` : `D_m² = T_x² + T_y² + T_z² + m²`.
- `TorusDirac3.dirac3_wave` : `D_m e_{uvw} = m e_{−u,−v,−w}`; with `m = 0` the eight doublers
  are zero modes.
-/

@[expose] public noncomputable section

open Complex

namespace TorusDirac3

variable {a b c : ℕ}

/-- The states on the three-torus `ZMod a × ZMod b × ZMod c`. -/
abbrev H3 (a b c : ℕ) := EuclideanSpace ℂ (ZMod a × ZMod b × ZMod c)

/-- The sign `(−1)^j` on a closed axis. -/
def sg {n : ℕ} (j : ZMod n) : ℂ := (-1) ^ j.val

theorem sg_add_one {n : ℕ} [NeZero n] (h : 2 ∣ n) (j : ZMod n) : sg (j + 1) = -sg j :=
  TorusUniverse.neg_one_pow_val_add_one h j

theorem sg_sub_one {n : ℕ} [NeZero n] (h : 2 ∣ n) (j : ZMod n) : sg (j - 1) = -sg j :=
  TorusUniverse.neg_one_pow_val_sub_one h j

theorem sg_mul_self {n : ℕ} (j : ZMod n) : sg j * sg j = 1 := by
  rw [sg, ← mul_pow]; norm_num

/-! ## 1. The transports and the signs -/

/-- The transport along `x`. -/
def Tx : H3 a b c →ₗ[ℂ] H3 a b c where
  toFun ψ := WithLp.toLp 2 fun p => (ψ (p.1 + 1, p.2) + ψ (p.1 - 1, p.2)) / 2
  map_add' ψ φ := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' r ψ := by ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The transport along `y`. -/
def Ty : H3 a b c →ₗ[ℂ] H3 a b c where
  toFun ψ := WithLp.toLp 2 fun p =>
    (ψ (p.1, p.2.1 + 1, p.2.2) + ψ (p.1, p.2.1 - 1, p.2.2)) / 2
  map_add' ψ φ := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' r ψ := by ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The transport along `z`. -/
def Tz : H3 a b c →ₗ[ℂ] H3 a b c where
  toFun ψ := WithLp.toLp 2 fun p =>
    (ψ (p.1, p.2.1, p.2.2 + 1) + ψ (p.1, p.2.1, p.2.2 - 1)) / 2
  map_add' ψ φ := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' r ψ := by ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `A_y = (−1)^x T_y`. -/
def Ay : H3 a b c →ₗ[ℂ] H3 a b c where
  toFun ψ := WithLp.toLp 2 fun p =>
    sg p.1 * ((ψ (p.1, p.2.1 + 1, p.2.2) + ψ (p.1, p.2.1 - 1, p.2.2)) / 2)
  map_add' ψ φ := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' r ψ := by ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `A_z = (−1)^(x+y) T_z`. -/
def Az : H3 a b c →ₗ[ℂ] H3 a b c where
  toFun ψ := WithLp.toLp 2 fun p =>
    sg p.1 * sg p.2.1 * ((ψ (p.1, p.2.1, p.2.2 + 1) + ψ (p.1, p.2.1, p.2.2 - 1)) / 2)
  map_add' ψ φ := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' r ψ := by ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The staggered sign `ε = (−1)^(x+y+z)`, Dirac's `β`. -/
def eps : H3 a b c →ₗ[ℂ] H3 a b c where
  toFun ψ := WithLp.toLp 2 fun p => sg p.1 * sg p.2.1 * sg p.2.2 * ψ p
  map_add' ψ φ := by ext p; simp only [PiLp.add_apply]; ring
  map_smul' r ψ := by ext p; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

section Apply

variable (ψ : H3 a b c) (x : ZMod a) (y : ZMod b) (z : ZMod c)

theorem Tx_apply : Tx ψ (x, y, z) = (ψ (x + 1, y, z) + ψ (x - 1, y, z)) / 2 := rfl
theorem Ty_apply : Ty ψ (x, y, z) = (ψ (x, y + 1, z) + ψ (x, y - 1, z)) / 2 := rfl
theorem Tz_apply : Tz ψ (x, y, z) = (ψ (x, y, z + 1) + ψ (x, y, z - 1)) / 2 := rfl
theorem Ay_apply : Ay ψ (x, y, z) = sg x * ((ψ (x, y + 1, z) + ψ (x, y - 1, z)) / 2) := rfl
theorem Az_apply :
    Az ψ (x, y, z) = sg x * sg y * ((ψ (x, y, z + 1) + ψ (x, y, z - 1)) / 2) := rfl
theorem eps_apply : eps ψ (x, y, z) = sg x * sg y * sg z * ψ (x, y, z) := rfl

end Apply

/-! ## 2. The four operators anticommute -/

theorem Tx_Ay [NeZero a] (ha : 2 ∣ a) (ψ : H3 a b c) : Ay (Tx ψ) = -Tx (Ay ψ) := by
  ext ⟨x, y, z⟩
  simp only [PiLp.neg_apply, Tx_apply, Ay_apply, sg_add_one ha, sg_sub_one ha]
  ring

theorem Tx_Az [NeZero a] (ha : 2 ∣ a) (ψ : H3 a b c) : Az (Tx ψ) = -Tx (Az ψ) := by
  ext ⟨x, y, z⟩
  simp only [PiLp.neg_apply, Tx_apply, Az_apply, sg_add_one ha, sg_sub_one ha]
  ring

theorem Ay_Az [NeZero b] (hb : 2 ∣ b) (ψ : H3 a b c) : Az (Ay ψ) = -Ay (Az ψ) := by
  ext ⟨x, y, z⟩
  simp only [PiLp.neg_apply, Ay_apply, Az_apply, sg_add_one hb, sg_sub_one hb]
  ring

theorem eps_Tx [NeZero a] (ha : 2 ∣ a) (ψ : H3 a b c) : eps (Tx ψ) = -Tx (eps ψ) := by
  ext ⟨x, y, z⟩
  simp only [PiLp.neg_apply, Tx_apply, eps_apply, sg_add_one ha, sg_sub_one ha]
  ring

theorem eps_Ay [NeZero b] (hb : 2 ∣ b) (ψ : H3 a b c) : eps (Ay ψ) = -Ay (eps ψ) := by
  ext ⟨x, y, z⟩
  simp only [PiLp.neg_apply, Ay_apply, eps_apply, sg_add_one hb, sg_sub_one hb]
  ring

theorem eps_Az [NeZero c] (hc : 2 ∣ c) (ψ : H3 a b c) : eps (Az ψ) = -Az (eps ψ) := by
  ext ⟨x, y, z⟩
  simp only [PiLp.neg_apply, Az_apply, eps_apply, sg_add_one hc, sg_sub_one hc]
  ring

theorem eps_eps (ψ : H3 a b c) : eps (eps ψ) = ψ := by
  ext ⟨x, y, z⟩
  simp only [eps_apply]
  linear_combination (sg y * sg y * (sg z * sg z) * ψ (x, y, z)) * sg_mul_self x +
    (sg z * sg z * ψ (x, y, z)) * sg_mul_self y + ψ (x, y, z) * sg_mul_self z

theorem Ay_Ay (ψ : H3 a b c) : Ay (Ay ψ) = Ty (Ty ψ) := by
  ext ⟨x, y, z⟩
  simp only [Ay_apply, Ty_apply, add_sub_cancel_right, sub_add_cancel]
  linear_combination ((ψ (x, y + 1 + 1, z) + ψ (x, y, z) + (ψ (x, y, z) +
    ψ (x, y - 1 - 1, z))) / 4) * sg_mul_self x

theorem Az_Az (ψ : H3 a b c) : Az (Az ψ) = Tz (Tz ψ) := by
  ext ⟨x, y, z⟩
  simp only [Az_apply, Tz_apply, add_sub_cancel_right, sub_add_cancel]
  linear_combination ((ψ (x, y, z + 1 + 1) + ψ (x, y, z) + (ψ (x, y, z) +
    ψ (x, y, z - 1 - 1))) / 4) * (sg y * sg y * sg_mul_self x + sg_mul_self y)

/-! ## 3. Dirac's square root -/

/-- The massive Dirac operator `D_m = A_x + A_y + A_z + m ε` on the three-torus. -/
def dirac3 (m : ℝ) : H3 a b c →ₗ[ℂ] H3 a b c := Tx + Ay + Az + (m : ℂ) • eps

variable [NeZero a] [NeZero b] [NeZero c]

/-- **Dirac's square root on `T³`**: `D_m² = T_x² + T_y² + T_z² + m²`. -/
theorem dirac3_sq (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c) (m : ℝ) (ψ : H3 a b c) :
    dirac3 m (dirac3 m ψ) =
      Tx (Tx ψ) + Ty (Ty ψ) + Tz (Tz ψ) + ((m : ℂ) ^ 2) • ψ := by
  simp only [dirac3, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    Tx_Ay ha, Tx_Az ha, Ay_Az hb, eps_Tx ha, eps_Ay hb, eps_Az hc, eps_eps, Ay_Ay, Az_Az]
  module

/-! ## 4. The eight doublers -/

/-- The wave `u^x v^y w^z`. -/
def wave3 (u v w : ℂ) : H3 a b c :=
  WithLp.toLp 2 fun p => u ^ p.1.val * v ^ p.2.1.val * w ^ p.2.2.val

omit [NeZero a] [NeZero b] [NeZero c] in
theorem wave3_apply (u v w : ℂ) (x : ZMod a) (y : ZMod b) (z : ZMod c) :
    wave3 u v w (x, y, z) = u ^ x.val * v ^ y.val * w ^ z.val := rfl

open TorusUniverse in
/-- **The doublers**: with `4` dividing every size and `u, v, w ∈ {i, −i}`,
`D_m e_{uvw} = m e_{−u,−v,−w}`. For `m = 0` the eight waves are zero modes of `D`, and `ε`
sends each to the opposite corner of the momentum cube. -/
theorem dirac3_wave (ha : 4 ∣ a) (hb : 4 ∣ b) (hc : 4 ∣ c) {u v w : ℂ} (hu : u = I ∨ u = -I)
    (hv : v = I ∨ v = -I) (hw : w = I ∨ w = -I) (m : ℝ) :
    dirac3 m (wave3 u v w : H3 a b c) = (m : ℂ) • wave3 (-u) (-v) (-w) := by
  ext ⟨x, y, z⟩
  simp only [dirac3, LinearMap.add_apply, LinearMap.smul_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, Tx_apply, Ay_apply, Az_apply, eps_apply, wave3_apply, pow_val_add_one hu ha,
    pow_val_sub_one hu ha, pow_val_add_one hv hb, pow_val_sub_one hv hb, pow_val_add_one hw hc,
    pow_val_sub_one hw hc, sg, neg_pow u, neg_pow v, neg_pow w]
  linear_combination (u * u ^ x.val * v ^ y.val * w ^ z.val / 2) * sq_of hu +
    ((-1) ^ x.val * u ^ x.val * v * v ^ y.val * w ^ z.val / 2) * sq_of hv +
    ((-1) ^ x.val * (-1) ^ y.val * u ^ x.val * v ^ y.val * w * w ^ z.val / 2) * sq_of hw

end TorusDirac3
