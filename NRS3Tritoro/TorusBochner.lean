/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Data.ZMod.ValMinAbs
public import NRS3Hopf.BochnerCurvature

/-!
# Bochner on the three-torus: `T³` is flat

`BochnerCurvature` (in `nrs3-hopf`) reads the Ricci curvature of a graph from Bochner's formula
`½ Δ|∇f|² = |Hess f|² + ⟨∇f, ∇Δf⟩ + Ric(∇f, ∇f)`: with the carré du champ `Γ` and its iterate
`Γ₂ = ½ ΔΓ − Γ(f, Δf)` (Bakry–Émery), the curvature is at least `K` when `Γ₂(f) ≥ K Γ(f, f)`
for every `f`. The carré du champ is the double commutator of the position with transport,
`Γ(f, f) = ½ [f, [f, A]] 1` (`gamma_eq_lie`): the curvature is read from the bracket of NRS.

Here `A` is the transport of `T³ = ZMod a × ZMod b × ZMod c`: one step `±1` along one axis, six
steps from every point. The discrete Bochner identity is exact: `Γ₂(f)` at `(x, y, z)` is the sum
of squares

  `Σ_axes [½ (Δ_i f)² + ¼ (D⁻_i f)² + ¼ (D⁺_i f)²]
    + ½ Σ_{i<j} Σ_{s,t=±1} (f(p + s e_i + t e_j) − f(p + s e_i) − f(p + t e_j) + f(p))²`,

with `Δ_i` the second difference along axis `i` and `D^±_i` the second differences one step
forward and back. So `Γ₂(f) ≥ 0` for every `f` at every point: the torus has curvature `≥ 0`,
whatever its sizes. As soon as one axis has `5` positions the bound is sharp: a function that grows
one step per position along that axis around a point has `Γ₂ = 0` and `Γ = 1` there, so no `K > 0`
holds. The torus is flat, as the path is (`D28`), and unlike the closed fibered space, the 16-cell,
which has `K = 4` (`cell16_curvature`).

## Main results

- `TorusBochner.sum_adj_mul` : `Σ_q A_pq h(q)` is the sum of `h` over the six neighbours.
- `TorusBochner.gam2_eq` : the discrete Bochner identity on `T³`, a sum of squares.
- `TorusBochner.torus_curvature` : `Γ₂(f) ≥ 0`, curvature `≥ 0`.
- `TorusBochner.torus_sharp` : with `5` positions on an axis, `Γ₂ = 0` and `Γ = 1` at a point.
- `TorusBochner.not_curvature_pos` : no `K > 0` bounds the curvature: `T³` is flat.
-/

@[expose] public noncomputable section

open BochnerCurvature

namespace TorusBochner

variable {a b c : ℕ} [NeZero a] [NeZero b] [NeZero c]

/-- The transport of `T³`: one step `±1` along one axis. -/
def adj (a b c : ℕ) : Matrix (ZMod a × ZMod b × ZMod c) (ZMod a × ZMod b × ZMod c) ℝ :=
  fun p q =>
    (if q = (p.1 + 1, p.2) then 1 else 0) + (if q = (p.1 - 1, p.2) then 1 else 0) +
    (if q = (p.1, p.2.1 + 1, p.2.2) then 1 else 0) +
    (if q = (p.1, p.2.1 - 1, p.2.2) then 1 else 0) +
    (if q = (p.1, p.2.1, p.2.2 + 1) then 1 else 0) + (if q = (p.1, p.2.1, p.2.2 - 1) then 1 else 0)

/-- The transport sums over the six neighbours. -/
lemma sum_adj_mul (p : ZMod a × ZMod b × ZMod c) (h : ZMod a × ZMod b × ZMod c → ℝ) :
    ∑ q, adj a b c p q * h q =
      h (p.1 + 1, p.2) + h (p.1 - 1, p.2) + h (p.1, p.2.1 + 1, p.2.2) +
        h (p.1, p.2.1 - 1, p.2.2) + h (p.1, p.2.1, p.2.2 + 1) + h (p.1, p.2.1, p.2.2 - 1) := by
  simp only [adj, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The discrete Bochner identity on `T³`.** `Γ₂(f)` is a sum of squares of second differences:
along each axis, and mixed between each pair of axes. -/
theorem gam2_eq (f : ZMod a × ZMod b × ZMod c → ℝ) (x : ZMod a) (y : ZMod b) (z : ZMod c) :
    gam2 (adj a b c) f (x, y, z) =
      (1 / 2) * (f (x + 1, y, z) + f (x - 1, y, z) - 2 * f (x, y, z)) ^ 2 +
      (1 / 4) * (f (x - 1 - 1, y, z) - 2 * f (x - 1, y, z) + f (x, y, z)) ^ 2 +
      (1 / 4) * (f (x, y, z) - 2 * f (x + 1, y, z) + f (x + 1 + 1, y, z)) ^ 2 +
      (1 / 2) * (f (x, y + 1, z) + f (x, y - 1, z) - 2 * f (x, y, z)) ^ 2 +
      (1 / 4) * (f (x, y - 1 - 1, z) - 2 * f (x, y - 1, z) + f (x, y, z)) ^ 2 +
      (1 / 4) * (f (x, y, z) - 2 * f (x, y + 1, z) + f (x, y + 1 + 1, z)) ^ 2 +
      (1 / 2) * (f (x, y, z + 1) + f (x, y, z - 1) - 2 * f (x, y, z)) ^ 2 +
      (1 / 4) * (f (x, y, z - 1 - 1) - 2 * f (x, y, z - 1) + f (x, y, z)) ^ 2 +
      (1 / 4) * (f (x, y, z) - 2 * f (x, y, z + 1) + f (x, y, z + 1 + 1)) ^ 2 +
      (1 / 2) * (f (x + 1, y + 1, z) - f (x + 1, y, z) - f (x, y + 1, z) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x + 1, y - 1, z) - f (x + 1, y, z) - f (x, y - 1, z) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x - 1, y + 1, z) - f (x - 1, y, z) - f (x, y + 1, z) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x - 1, y - 1, z) - f (x - 1, y, z) - f (x, y - 1, z) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x + 1, y, z + 1) - f (x + 1, y, z) - f (x, y, z + 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x + 1, y, z - 1) - f (x + 1, y, z) - f (x, y, z - 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x - 1, y, z + 1) - f (x - 1, y, z) - f (x, y, z + 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x - 1, y, z - 1) - f (x - 1, y, z) - f (x, y, z - 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x, y + 1, z + 1) - f (x, y + 1, z) - f (x, y, z + 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x, y + 1, z - 1) - f (x, y + 1, z) - f (x, y, z - 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x, y - 1, z + 1) - f (x, y - 1, z) - f (x, y, z + 1) + f (x, y, z)) ^ 2 +
      (1 / 2) * (f (x, y - 1, z - 1) - f (x, y - 1, z) - f (x, y, z - 1) + f (x, y, z)) ^ 2 := by
  simp only [gam2, lap, gam, sum_adj_mul, add_sub_cancel_right, sub_add_cancel]
  ring

/-- **`T³` has curvature `≥ 0`**: `Γ₂(f) ≥ 0` for every `f` at every point. -/
theorem torus_curvature (f : ZMod a × ZMod b × ZMod c → ℝ) (p : ZMod a × ZMod b × ZMod c) :
    0 ≤ gam2 (adj a b c) f p := by
  obtain ⟨x, y, z⟩ := p
  rw [gam2_eq]
  positivity

omit [NeZero a] in
lemma valMinAbs_small (ha : 5 ≤ a) (k : ℤ) (hk : -2 ≤ k ∧ k ≤ 2) :
    haveI : NeZero a := ⟨by omega⟩
    ((k : ZMod a)).valMinAbs = k := by
  have : NeZero a := ⟨by omega⟩
  exact (ZMod.valMinAbs_spec _ _).2 ⟨rfl, by constructor <;> omega⟩

/-- **The bound is sharp.** With `5` positions on the `x` axis, the signed position along `x`
has `Γ = 1` and `Γ₂ = 0` at the origin. -/
theorem torus_sharp (ha : 5 ≤ a) :
    ∃ (f : ZMod a × ZMod b × ZMod c → ℝ) (p : ZMod a × ZMod b × ZMod c),
      gam (adj a b c) f f p = 1 ∧ gam2 (adj a b c) f p = 0 := by
  have v : ∀ (k : ℤ) (u : ZMod a), u = k → -2 ≤ k ∧ k ≤ 2 → (u.valMinAbs : ℝ) = k := by
    rintro k u rfl hk
    exact_mod_cast valMinAbs_small ha k hk
  have e0 := v 0 0 (by simp) (by norm_num)
  have e1 := v 1 (0 + 1) (by simp) (by norm_num)
  have e2 := v 2 (0 + 1 + 1) (by push_cast; ring) (by norm_num)
  have e3 := v (-1) (0 - 1) (by simp) (by norm_num)
  have e4 := v (-2) (0 - 1 - 1) (by push_cast; ring) (by norm_num)
  refine ⟨fun q => (q.1.valMinAbs : ℝ), (0, 0, 0), ?_, ?_⟩
  · simp only [gam, sum_adj_mul]
    rw [e0, e1, e3]
    norm_num
  · rw [gam2_eq]
    simp only [e0, e1, e2, e3, e4]
    norm_num

/-- **`T³` is flat**: once an axis has `5` positions, no `K > 0` bounds its curvature. -/
theorem not_curvature_pos (ha : 5 ≤ a) :
    ¬ ∃ K > 0, ∀ (f : ZMod a × ZMod b × ZMod c → ℝ) p,
      K * gam (adj a b c) f f p ≤ gam2 (adj a b c) f p := by
  rintro ⟨K, hK, h⟩
  obtain ⟨f, p, h1, h2⟩ := torus_sharp (b := b) (c := c) ha
  have := h f p
  rw [h1, h2] at this
  linarith

end TorusBochner
