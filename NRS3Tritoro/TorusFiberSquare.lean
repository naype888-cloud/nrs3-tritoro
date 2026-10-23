/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.TorusFiberAxes
public import NRS3Tritoro.SiteEvents

/-!
# `T³` with the closed fiber: Dirac's square and the site events

On `T³ × w` (`ZMod a × ZMod b × ZMod c × ZMod 3`, even sizes) the Dirac operator of
`TorusFiberDirac`, `D₄ = D₃ + ε T°_w`, squares to the sum of the four transports:

  `D₄² = T_x² + T_y² + T_z² + T°_w²`,

so the fiber is a Kaluza–Klein mass: `T°_w` is `1` on the uniform mode and `−1/2` on the two
rotating ones (`FiberDiracAxis`), and the light level `1/2` comes twice, once per sense of turn.

As a lattice, `T³ × w` gives every site eight links, two per axis, the fiber included; the rate of
a site event under `T = T_x + T_y + T_z + T°_w` is the sum of the four hop flows, the rates add up
to `0` and every site obeys Robertson for bits (`SiteEvents`).

## Main results

- `TorusFiberDirac.hop_sq_of_sign` : a hop with a sign weight squares like the plain hop.
- `TorusFiberDirac.dirac_sq` : `D₄² = T_x² + T_y² + T_z² + T°_w²`.
- `TorusFiberDirac.rate_torusFiber` : eight links per site.
- `TorusFiberDirac.sum_rate_torusFiber`, `TorusFiberDirac.rate_torusFiber_sq_le` : conservation
  and Robertson.
-/

@[expose] public noncomputable section

open Complex SiteHop QuantumEvents SiteEvents

namespace TorusFiberDirac

variable {a b c : ℕ}

/-- A hop with a sign weight invariant under the hop squares like the plain hop. -/
theorem hop_sq_of_sign {ι : Type*} (τ : ι ≃ ι) {s : ι → ℝ} (hs : ∀ p, s (τ p) = s p)
    (hs' : ∀ p, s (τ.symm p) = s p) (h1 : ∀ p, s p * s p = 1) (χ : EuclideanSpace ℂ ι) :
    hop τ s (hop τ s χ) = hop τ 1 (hop τ 1 χ) := by
  ext p
  have h1' : ((s p : ℝ) : ℂ) * (s p : ℂ) = 1 := by exact_mod_cast h1 p
  simp only [hop_apply, hs, hs', Pi.one_apply, Complex.ofReal_one, one_mul]
  linear_combination ((χ (τ (τ p)) + χ (τ.symm (τ p)) +
    (χ (τ (τ.symm p)) + χ (τ.symm (τ.symm p)))) / 4) * h1'

/-- The transports along `y` and `z`. -/
def Ty : HT a b c →ₗ[ℂ] HT a b c := hop τy 1
def Tz : HT a b c →ₗ[ℂ] HT a b c := hop τz 1

variable [NeZero a] [NeZero b] [NeZero c] (ha : 2 ∣ a) (hb : 2 ∣ b) (hc : 2 ∣ c)
include ha hb hc

/-- **Dirac's square on `T³ × w`**: `D₄² = T_x² + T_y² + T_z² + T°_w²`. -/
theorem dirac_sq (χ : HT a b c) :
    dirac (dirac χ) = Tx (Tx χ) + Ty (Ty χ) + Tz (Tz χ) + Tw (Tw χ) := by
  have hTy : ∀ χ : HT a b c, Tx (Ay χ) = -Ay (Tx χ) := hop_hop_anticomm (τ := τx) (σ := τy)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (sx_τx ha) (sx_τx_symm ha)
  have hTz : ∀ χ : HT a b c, Tx (Az χ) = -Az (Tx χ) := hop_hop_anticomm (τ := τx) (σ := τz)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (sxy_τx ha) (sxy_τx_symm ha)
  have hTw : ∀ χ : HT a b c, Tx (Mw χ) = -Mw (Tx χ) := hop_hop_anticomm (τ := τx) (σ := τw)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (sxyz_τx ha) (sxyz_τx_symm ha)
  have hyz : ∀ χ : HT a b c, Ay (Az χ) = -Az (Ay χ) := hop_hop_anticomm (τ := τy) (σ := τz)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (sxy_τy hb) (sxy_τy_symm hb)
  have hyw : ∀ χ : HT a b c, Ay (Mw χ) = -Mw (Ay χ) := hop_hop_anticomm (τ := τy) (σ := τw)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (sxyz_τy hb) (sxyz_τy_symm hb)
  have hzw : ∀ χ : HT a b c, Az (Mw χ) = -Mw (Az χ) := hop_hop_anticomm (τ := τz) (σ := τw)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (sxyz_τz hc) (sxyz_τz_symm hc)
  have hAy : ∀ χ : HT a b c, Ay (Ay χ) = Ty (Ty χ) :=
    hop_sq_of_sign τy (fun _ => rfl) (fun _ => rfl) sx_mul_self
  have hAz : ∀ χ : HT a b c, Az (Az χ) = Tz (Tz χ) :=
    hop_sq_of_sign τz (fun _ => rfl) (fun _ => rfl) sxy_mul_self
  simp only [dirac, rest, LinearMap.add_apply, map_add, hTy, hTz, hTw, hyz, hyw, hzw, hAy, hAz,
    Mw_sq]
  abel

omit ha hb hc

/-! ## Site events on `T³ × w` -/

/-- The transport of `T³ × w`: a hop around each of the four closed axes. -/
def transport4 : HT a b c →ₗ[ℂ] HT a b c := Tx + Ty + Tz + Tw

omit [NeZero a] [NeZero b] [NeZero c] in
theorem transport4_isSymmetric [NeZero a] [NeZero b] [NeZero c] :
    (transport4 : HT a b c →ₗ[ℂ] HT a b c).IsSymmetric :=
  (((hop_isSymmetric _ fun _ => rfl).add (hop_isSymmetric _ fun _ => rfl)).add
    (hop_isSymmetric _ fun _ => rfl)).add (hop_isSymmetric _ fun _ => rfl)

omit [NeZero a] [NeZero b] [NeZero c] in
/-- **Eight links per site**: the rate is the sum of the four hop flows, the fiber included. -/
theorem rate_torusFiber [NeZero a] [NeZero b] [NeZero c] (p : Site a b c) (ψ : HT a b c) :
    rate transport4 (siteEvent p) ψ =
      (hopFlow τx ψ (τx.symm p) - hopFlow τx ψ p) + (hopFlow τy ψ (τy.symm p) - hopFlow τy ψ p) +
        (hopFlow τz ψ (τz.symm p) - hopFlow τz ψ p) +
        (hopFlow τw ψ (τw.symm p) - hopFlow τw ψ p) := by
  rw [transport4, rate_add, rate_add, rate_add, Tx, Ty, Tz, Tw, rate_hop, rate_hop, rate_hop,
    rate_hop]

omit [NeZero a] [NeZero b] [NeZero c] in
theorem sum_rate_torusFiber [NeZero a] [NeZero b] [NeZero c] (ψ : HT a b c) :
    ∑ p, rate transport4 (siteEvent p) ψ = 0 :=
  sum_rate_site transport4_isSymmetric ψ

omit [NeZero a] [NeZero b] [NeZero c] in
theorem rate_torusFiber_sq_le [NeZero a] [NeZero b] [NeZero c] (p : Site a b c) {ψ : HT a b c}
    (hψ : ‖ψ‖ = 1) :
    rate transport4 (siteEvent p) ψ ^ 2 ≤
      4 * variance transport4 ψ * (‖ψ p‖ ^ 2 * (1 - ‖ψ p‖ ^ 2)) :=
  rate_site_sq_le transport4_isSymmetric p hψ

end TorusFiberDirac
