/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.PartialDeriv

/-!
# Coordinate words of a function that is `C^k` near a point

Near a point at which `f` is `C^k`, the coordinate word `iteratedPartialDeriv w f` of length `k`
is the `k`-th Fréchet derivative evaluated on the coordinate directions of `w`, the head of the
word first. A Lipschitz `k`-th derivative on an open set therefore makes every coordinate word of
length `k` Lipschitz there, with the same constant.

## Main results

* `iteratedFDeriv_single_eq_iteratedPartialDeriv`: the word as an evaluation of the Fréchet
  derivative, under `C^k` regularity at the point only.
* `LipschitzOnWith.iteratedPartialDeriv`: Lipschitz words from a Lipschitz `k`-th derivative.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open Filter
open scoped Topology NNReal

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- At a point near which `f` is `C^j`, the `j`-th Fréchet derivative on the coordinate directions
`e_{v 0}, …, e_{v (j-1)}` is the coordinate word `∂_{v 0} ⋯ ∂_{v (j-1)} f`. -/
theorem iteratedFDeriv_single_eq_iteratedPartialDeriv {j : ℕ} {f : ℝ^n → F} {x : ℝ^n}
    (hf : ContDiffAt ℝ j f x) (v : Fin j → Fin n) :
    iteratedFDeriv ℝ j f x (fun i ↦ EuclideanSpace.single (v i) (1 : ℝ)) =
      iteratedPartialDeriv (List.ofFn v) f x := by
  induction j generalizing x with
  | zero => simp [iteratedPartialDeriv]
  | succ j ih =>
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
      hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
    have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ j f y :=
      (hf.of_le (by exact_mod_cast Nat.le_succ j)).eventually (by simp)
    have heq : (fun y ↦ iteratedFDeriv ℝ j f y
        (Fin.tail fun i ↦ EuclideanSpace.single (v i) (1 : ℝ))) =ᶠ[𝓝 x]
        iteratedPartialDeriv (List.ofFn fun i ↦ v i.succ) f :=
      hev.mono fun y hy ↦ ih hy fun i ↦ v i.succ
    rw [hd.iteratedFDeriv_succ_apply_left', List.ofFn_succ, iteratedPartialDeriv, heq.fderiv_eq]
    rfl

end PDE

/-- **Lipschitz coordinate words.** If `f` is `C^k` on an open set `U` and its `k`-th Fréchet
derivative is `K`-Lipschitz on `U`, then every coordinate word of length `k` is `K`-Lipschitz on
`U`. -/
theorem LipschitzOnWith.iteratedPartialDeriv {k : ℕ} {f : ℝ^n → F} {U : Set (ℝ^n)} {K : ℝ≥0}
    (hK : LipschitzOnWith K (iteratedFDeriv ℝ k f) U) (hU : IsOpen U)
    (hf : ContDiffOn ℝ k f U) (w : List (Fin n)) (hw : w.length = k) :
    LipschitzOnWith K (iteratedPartialDeriv w f) U := by
  subst hw
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
  have ey :=
    PDE.iteratedFDeriv_single_eq_iteratedPartialDeriv (hf.contDiffAt (hU.mem_nhds hy)) w.get
  have ez :=
    PDE.iteratedFDeriv_single_eq_iteratedPartialDeriv (hf.contDiffAt (hU.mem_nhds hz)) w.get
  rw [List.ofFn_get] at ey ez
  rw [← ey, ← ez, dist_eq_norm, ← sub_apply]
  calc ‖(iteratedFDeriv ℝ w.length f y - iteratedFDeriv ℝ w.length f z)
          (fun i ↦ EuclideanSpace.single (w.get i) (1 : ℝ))‖
      ≤ ‖iteratedFDeriv ℝ w.length f y - iteratedFDeriv ℝ w.length f z‖ *
          ∏ i, ‖EuclideanSpace.single (w.get i) (1 : ℝ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = dist (iteratedFDeriv ℝ w.length f y) (iteratedFDeriv ℝ w.length f z) := by
        simp [dist_eq_norm]
    _ ≤ K * dist y z := hK.dist_le_mul y hy z hz
