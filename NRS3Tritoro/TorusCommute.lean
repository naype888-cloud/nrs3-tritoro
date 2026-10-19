/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Tritoro.Torus
public import NRS3Hopf.BoxCommute

/-!
# The axes of the torus commute

Operators on different axes of `ℂ^(Fin k → Fin d)` commute: the product of the lifts of `A` on
axis `i` and `B` on axis `j ≠ i` has entry `A_{p_i q_i} B_{p_j q_j}` when `p` and `q` agree off
`{i, j}`, and `0` otherwise, in either order.

## Main results

- `TorusCommute.liftAlong_split_comm` : lifts to different axes commute.
- `TorusCommute.torusPairs_comm` : the observables of different axes of the torus commute.
-/

@[expose] public noncomputable section

open Matrix PathGraph3DNRS StackedFibers

namespace TorusCommute

variable {k d : ℕ}

theorem liftAlong_split_apply (i : Fin k) (A : Matrix (Fin d) (Fin d) ℂ) (p q : Fin k → Fin d) :
    liftAlong (split i) A p q = if ∀ m, m ≠ i → p m = q m then A (p i) (q i) else 0 := by
  have e : ((fun j : { j // j ≠ i } => p j) = fun j : { j // j ≠ i } => q j) ↔
      ∀ m, m ≠ i → p m = q m :=
    ⟨fun he m hm => congrFun he ⟨m, hm⟩, fun h => funext fun m => h m.1 m.2⟩
  simp only [liftAlong, of_apply, split, Equiv.funSplitAt_apply, e, mul_ite, mul_one, mul_zero]

/-- The entry of the product of lifts to two different axes. -/
theorem mul_apply_split {i j : Fin k} (hij : i ≠ j) (A B : Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin k → Fin d) :
    (liftAlong (split i) A * liftAlong (split j) B) p q =
      if ∀ m, m ≠ i → m ≠ j → p m = q m then A (p i) (q i) * B (p j) (q j) else 0 := by
  rw [mul_apply, Finset.sum_eq_single (Function.update p i (q i))]
  · simp only [liftAlong_split_apply, Function.update_self, Function.update_of_ne hij.symm]
    have h1 : ∀ m, m ≠ i → p m = Function.update p i (q i) m := fun m hm => by
      rw [Function.update_of_ne hm]
    rw [ite_eq_left h1]
    by_cases h : ∀ m, m ≠ i → m ≠ j → p m = q m
    · have h2 : ∀ m, m ≠ j → Function.update p i (q i) m = q m := fun m hm => by
        by_cases hmi : m = i
        · subst hmi; simp
        · rw [Function.update_of_ne hmi]; exact h m hmi hm
      rw [ite_eq_left h2, ite_eq_left h]
    · have h2 : ¬∀ m, m ≠ j → Function.update p i (q i) m = q m := fun c => h fun m hmi hmj => by
        have := c m hmj
        rwa [Function.update_of_ne hmi] at this
      rw [ite_eq_right h2, ite_eq_right h, mul_zero]
  · intro r _ hr
    rw [liftAlong_split_apply, liftAlong_split_apply]
    split_ifs with h1 h2
    · exfalso; refine hr (funext fun m => ?_)
      by_cases hmi : m = i
      · subst hmi; rw [Function.update_self]; exact h2 m hij
      · rw [Function.update_of_ne hmi]; exact (h1 m hmi).symm
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Lifts to different axes commute.** -/
theorem liftAlong_split_comm {i j : Fin k} (hij : i ≠ j) (A B : Matrix (Fin d) (Fin d) ℂ) :
    liftAlong (split i) A * liftAlong (split j) B =
      liftAlong (split j) B * liftAlong (split i) A := by
  ext p q
  rw [mul_apply_split hij, mul_apply_split hij.symm, mul_comm]
  congr 1
  exact propext ⟨fun h m hj hi => h m hi hj, fun h m hi hj => h m hj hi⟩

/-- **The observables of different axes of the torus commute.** -/
theorem torusPairs_comm (s t : Fin 2) (i j : Fin k) (hij : i ≠ j) (ψ : Torus.HT k) :
    Torus.torusPairs k (t, j) (Torus.torusPairs k (s, i) ψ) =
      Torus.torusPairs k (s, i) (Torus.torusPairs k (t, j) ψ) := by
  simp only [Torus.torusPairs, ops]
  exact BoxCommute.apply_comm
    (liftAlong_split_comm (d := 3) hij.symm (CubeInBox.closedPair t) (CubeInBox.closedPair s)) ψ

/-- The observables of the torus are symmetric. -/
theorem torusPairs_isSymmetric (p : Fin 2 × Fin k) : (Torus.torusPairs k p).IsSymmetric := by
  simp only [Torus.torusPairs, ops]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (RobertsonDeterminant3D.liftAlong_isHermitian _ (CubeInBox.closedPair_isHermitian p.1))

end TorusCommute
