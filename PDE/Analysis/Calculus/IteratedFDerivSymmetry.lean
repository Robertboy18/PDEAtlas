/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Moving a direction to the front of an iterated Fréchet derivative

For a smooth map between real normed spaces, a direction placed in any slot of an iterated
Fréchet derivative can be moved to the first slot (`iteratedFDeriv_insertNth_eq_cons_of_smooth`).
In particular the last direction can be moved to the front
(`iteratedFDeriv_snoc_eq_cons_of_smooth`). Invariance under an arbitrary permutation of the
directions is not stated here; Mathlib proves it for analytic maps
(`ContDiffAt.iteratedFDeriv_comp_perm`).
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem iteratedFDeriv_cons_cons_swap
    (n : ℕ) (f : X → Y) (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x a b : X) (r : Fin n → X) :
    iteratedFDeriv ℝ (n + 2) f x (Fin.cons a (Fin.cons b r)) =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons b (Fin.cons a r)) := by
  let g : X → Y := fun z ↦ iteratedFDeriv ℝ n f z r
  have hiter : ContDiff ℝ 2 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (2 + n))
  have hg : ContDiff ℝ 2 g :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ X) Y r).contDiff.comp hiter
  have hsym :=
    ((hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq a b
  have hiter_succ :
      Differentiable ℝ (iteratedFDeriv ℝ (n + 1) f) :=
    (hf.iteratedFDeriv_right
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + (n + 1)))).differentiable
      one_ne_zero
  have hiter_n :
      Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    hiter.differentiable two_ne_zero
  have hinner (c : X) :
      (fun z ↦ iteratedFDeriv ℝ (n + 1) f z (Fin.cons c r)) =
        fun z ↦ fderiv ℝ g z c := by
    funext z
    rw [iteratedFDeriv_succ_apply_left]
    exact
      (fderiv_continuousMultilinear_apply_const_apply (hiter_n z) r c).symm
  have hfull (c d : X) :
      iteratedFDeriv ℝ (n + 2) f x (Fin.cons c (Fin.cons d r)) =
        fderiv ℝ (fderiv ℝ g) x c d := by
    rw [iteratedFDeriv_succ_apply_left]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [← fderiv_continuousMultilinear_apply_const_apply
      (hiter_succ x) (Fin.cons d r) c]
    rw [hinner d]
    rw [fderiv_clm_apply]
    · simp
    · exact (hg.fderiv_right (by norm_num)).differentiable one_ne_zero x
    · exact differentiableAt_const d
  rw [hfull a b, hfull b a]
  exact hsym

/-- For a smooth map, a direction inserted in any slot of an iterated derivative
can be moved to the first slot. -/
theorem iteratedFDeriv_insertNth_eq_cons_of_smooth
    (n : ℕ) (f : X → Y) (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x : X) (i : Fin (n + 1)) (r : Fin n → X) (l : X) :
    iteratedFDeriv ℝ (n + 1) f x (i.insertNth l r) =
      iteratedFDeriv ℝ (n + 1) f x (Fin.cons l r) := by
  induction n generalizing x with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      simp [hi, Fin.insertNth_zero']
  | succ n ih =>
      cases i using Fin.cases with
      | zero => simp [Fin.insertNth_zero']
      | succ i =>
          have hiter : Differentiable ℝ (iteratedFDeriv ℝ (n + 1) f) :=
            (hf.iteratedFDeriv_right
              (ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + (n + 1)))).differentiable
              one_ne_zero
          have heq :
              (fun z ↦ iteratedFDeriv ℝ (n + 1) f z (i.insertNth l (Fin.tail r))) =
                fun z ↦ iteratedFDeriv ℝ (n + 1) f z (Fin.cons l (Fin.tail r)) :=
            funext fun z ↦ ih z i (Fin.tail r)
          have hr : r = Fin.cons (r 0) (Fin.tail r) := (Fin.cons_self_tail r).symm
          rw [hr, Fin.insertNth_succ_cons]
          calc
            _ = fderiv ℝ
                (fun z ↦ iteratedFDeriv ℝ (n + 1) f z
                  (i.insertNth l (Fin.tail r))) x (r 0) :=
              (hiter x).iteratedFDeriv_succ_apply_left'
            _ = fderiv ℝ
                (fun z ↦ iteratedFDeriv ℝ (n + 1) f z
                  (Fin.cons l (Fin.tail r))) x (r 0) := by rw [heq]
            _ = iteratedFDeriv ℝ (n + 2) f x
                (Fin.cons (r 0) (Fin.cons l (Fin.tail r))) :=
              ((hiter x).iteratedFDeriv_succ_apply_left'
                (m := Fin.cons (r 0) (Fin.cons l (Fin.tail r)))).symm
            _ = _ := iteratedFDeriv_cons_cons_swap n f hf x (r 0) l (Fin.tail r)

/-- For a smooth map, moving the final direction of an iterated derivative to
the front does not change its value. -/
theorem iteratedFDeriv_snoc_eq_cons_of_smooth
    (n : ℕ) (f : X → Y) (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x : X) (r : Fin n → X) (l : X) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.snoc r l) =
      iteratedFDeriv ℝ (n + 1) f x (Fin.cons l r) := by
  simpa only [Fin.insertNth_last'] using
    iteratedFDeriv_insertNth_eq_cons_of_smooth n f hf x (Fin.last n) r l

end PDE.Analysis
