/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Picard iteration for small-Lipschitz semilinear equations

Banach's fixed-point theorem applied to a coercive variational operator perturbed
by a sufficiently small globally Lipschitz nonlinear load: the Picard map, its
fixed-point equation, convergence from every initial guess, and the standard
a priori and a posteriori error bounds.

No separate problem structure is needed: the bilinear form, nonlinear load,
and forcing remain ordinary arguments throughout. The Picard step inverts `B`
with the Lax–Milgram solution operator `solveCLM`. The fixed point, the
convergence of the iterates and both error bounds then come from Mathlib's
`ContractingWith.fixedPoint`, `ContractingWith.tendsto_iterate_fixedPoint`,
`ContractingWith.apriori_dist_iterate_fixedPoint_le` and
`ContractingWith.aposteriori_dist_iterate_fixedPoint_le`.

## Main results

* `semilinearPicardMap`, `semilinearPicardMap_contractingWith`: the Picard
  step `u ↦ solveCLM B hB (ell - N u)` and its contraction property when
  `‖solveCLM B hB‖ · K < 1`.
* `existsUnique_semilinear_of_small_lipschitz`,
  `existsUnique_semilinear_of_lipschitz_lt_coercivity`: existence and
  uniqueness for the semilinear equation `B(u, v) + N(u)(v) = ell(v)`.
* `tendsto_iterate_semilinearPicardMap`,
  `apriori_dist_iterate_semilinearPicardMap_le`,
  `aposteriori_dist_iterate_semilinearPicardMap_le`: convergence of the
  iteration and the geometric error bounds.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.1, Theorem 1 (Banach's Fixed Point Theorem).
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 5 (Hilbert Spaces), pp. 131-156.
  <https://doi.org/10.1007/978-0-387-70914-7_5>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Weak

open PDE.Analysis.Variational
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- One Picard step for the semilinear weak equation

`B(u, v) + N(u)(v) = ell(v)`.

The step freezes the nonlinear load at `u` and solves the resulting coercive
linear equation by Lax–Milgram. -/
noncomputable def semilinearPicardMap
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V) :
    V → V :=
  fun u ↦ solveCLM (V := V) B hB (ell - N u)

/-- The product of the Lax–Milgram solution-operator norm and the nonlinear
Lipschitz constant is a Lipschitz bound for the Picard map. -/
theorem semilinearPicardMap_lipschitzWith
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N) (ell : StrongDual ℝ V) :
    LipschitzWith (‖solveCLM (V := V) B hB‖₊ * K)
      (semilinearPicardMap B hB N ell) := by
  have hload : LipschitzWith K (fun u ↦ ell - N u) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_sub_left]
    exact hN.dist_le_mul x y
  change LipschitzWith (‖solveCLM (V := V) B hB‖₊ * K)
    (fun u ↦ solveCLM (V := V) B hB (ell - N u))
  simpa only [Function.comp_def] using
    (solveCLM (V := V) B hB).lipschitzWith.comp hload

/-- The Picard map is contracting when the product of the linear inverse norm
and the nonlinear Lipschitz constant is strictly less than one. -/
theorem semilinearPicardMap_contractingWith
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) :
    ContractingWith (‖solveCLM (V := V) B hB‖₊ * K)
      (semilinearPicardMap B hB N ell) :=
  ⟨hsmall, semilinearPicardMap_lipschitzWith B hB N hN ell⟩

/-- A fixed point of the Picard map is exactly a solution of the semilinear
weak equation. -/
theorem isFixedPt_semilinearPicardMap_iff
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V) (u : V) :
    Function.IsFixedPt (semilinearPicardMap B hB N ell) u ↔
      ∀ v, B u v + N u v = ell v := by
  constructor
  · intro hfixed
    have husolve :
        solve (V := V) B hB (ell - N u) = u := by
      simpa only [semilinearPicardMap, solveCLM_apply] using hfixed.eq
    have huweak : IsWeakSolution (V := V) B (ell - N u) u := by
      intro v
      calc
        B u v = B (solve (V := V) B hB (ell - N u)) v :=
          congrArg (fun z ↦ B z v) husolve.symm
        _ = (ell - N u) v :=
          solve.isWeakSolution (V := V) B hB (ell - N u) v
    intro v
    calc
      B u v + N u v = (ell - N u) v + N u v :=
        congrArg (fun r : ℝ ↦ r + N u v) (huweak v)
      _ = ell v := by simp
  · intro hu
    have huweak : IsWeakSolution (V := V) B (ell - N u) u := by
      intro v
      simpa only [sub_apply] using (eq_sub_iff_add_eq.mpr (hu v))
    have husolve := huweak.eq_solve (V := V) B hB (ell - N u)
    change semilinearPicardMap B hB N ell u = u
    simpa only [semilinearPicardMap, solveCLM_apply] using husolve.symm

/-- The canonical semilinear solution selected by Banach's fixed-point
theorem. -/
noncomputable def semilinearPicardSolution
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) : V :=
  ContractingWith.fixedPoint
    (semilinearPicardMap B hB N ell)
    (semilinearPicardMap_contractingWith B hB N hN hsmall ell)

/-- The canonical Picard solution is a fixed point of one Picard step. -/
theorem semilinearPicardSolution_isFixedPt
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) :
    Function.IsFixedPt (semilinearPicardMap B hB N ell)
      (semilinearPicardSolution B hB N hN hsmall ell) := by
  exact
    (semilinearPicardMap_contractingWith B hB N hN hsmall ell).fixedPoint_isFixedPt

/-- The canonical Picard solution satisfies the semilinear weak equation. -/
theorem semilinearPicardSolution_spec
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) :
    ∀ v,
      B (semilinearPicardSolution B hB N hN hsmall ell) v +
          N (semilinearPicardSolution B hB N hN hsmall ell) v =
        ell v :=
  (isFixedPt_semilinearPicardMap_iff B hB N ell _).mp
    (semilinearPicardSolution_isFixedPt B hB N hN hsmall ell)

/-- A coercive variational equation with a sufficiently small globally
Lipschitz nonlinear load has a unique solution.

The smallness condition makes `u ↦ solveCLM B hB (ell - N u)` contracting
by bounding its Lipschitz constant by `‖solveCLM B hB‖₊ * K`. It is a
sufficient condition; the composed map may have a smaller Lipschitz bound. -/
theorem existsUnique_semilinear_of_small_lipschitz
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) :
    ∃! u, ∀ v, B u v + N u v = ell v := by
  have hT :
      ContractingWith (‖solveCLM (V := V) B hB‖₊ * K)
        (semilinearPicardMap B hB N ell) :=
    semilinearPicardMap_contractingWith B hB N hN hsmall ell
  refine
    ⟨semilinearPicardSolution B hB N hN hsmall ell,
      semilinearPicardSolution_spec B hB N hN hsmall ell, ?_⟩
  intro u hu
  apply hT.fixedPoint_unique'
  · exact (isFixedPt_semilinearPicardMap_iff B hB N ell u).mpr hu
  · exact semilinearPicardSolution_isFixedPt B hB N hN hsmall ell

/-- Picard iteration converges to the semilinear solution from every initial
guess. -/
theorem tendsto_iterate_semilinearPicardMap
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) (u₀ : V) :
    Filter.Tendsto
      (fun m ↦ (semilinearPicardMap B hB N ell)^[m] u₀)
      Filter.atTop
      (𝓝 (semilinearPicardSolution B hB N hN hsmall ell)) := by
  exact
    (semilinearPicardMap_contractingWith B hB N hN hsmall ell)
      |>.tendsto_iterate_fixedPoint u₀

/-- A priori geometric error estimate for Picard iteration. -/
theorem apriori_dist_iterate_semilinearPicardMap_le
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) (u₀ : V) (m : ℕ) :
    dist ((semilinearPicardMap B hB N ell)^[m] u₀)
        (semilinearPicardSolution B hB N hN hsmall ell) ≤
      dist u₀ (semilinearPicardMap B hB N ell u₀) *
          ((‖solveCLM (V := V) B hB‖₊ * K : NNReal) : ℝ) ^ m /
        (1 - ((‖solveCLM (V := V) B hB‖₊ * K : NNReal) : ℝ)) := by
  exact
    (semilinearPicardMap_contractingWith B hB N hN hsmall ell)
      |>.apriori_dist_iterate_fixedPoint_le u₀ m

/-- A posteriori error estimate in terms of two consecutive Picard
iterates. -/
theorem aposteriori_dist_iterate_semilinearPicardMap_le
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N)
    (hsmall : ‖solveCLM (V := V) B hB‖₊ * K < 1)
    (ell : StrongDual ℝ V) (u₀ : V) (m : ℕ) :
    dist ((semilinearPicardMap B hB N ell)^[m] u₀)
        (semilinearPicardSolution B hB N hN hsmall ell) ≤
      dist ((semilinearPicardMap B hB N ell)^[m] u₀)
          ((semilinearPicardMap B hB N ell)^[m + 1] u₀) /
        (1 - ((‖solveCLM (V := V) B hB‖₊ * K : NNReal) : ℝ)) := by
  exact
    (semilinearPicardMap_contractingWith B hB N hN hsmall ell)
      |>.aposteriori_dist_iterate_fixedPoint_le u₀ m

/-- Explicit coercivity-modulus form of the small-Lipschitz theorem.

If `c ‖v‖² ≤ B(v,v)` and the nonlinear Lipschitz constant is strictly less
than `c`, then the Lax–Milgram solution map composed with the nonlinear load
is contracting. -/
theorem existsUnique_semilinear_of_lipschitz_lt_coercivity
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ * ‖v‖ ≤ B v v)
    (N : V → StrongDual ℝ V) {K : NNReal}
    (hN : LipschitzWith K N) (hsmall : (K : ℝ) < c)
    (ell : StrongDual ℝ V) :
    ∃! u, ∀ v, B u v + N u v = ell v := by
  have hB : IsCoercive B := ⟨c, hc, hcoercive⟩
  let S := solveCLM (V := V) B hB
  have hSnorm : ‖S‖ ≤ c⁻¹ := by
    simpa only [S] using
      solveCLM.norm_le (V := V) B hB c hc hcoercive
  have hcontract : ‖S‖₊ * K < 1 := by
    apply NNReal.coe_lt_coe.mp
    have hlt : c⁻¹ * (K : ℝ) < 1 := by
      rw [inv_mul_eq_div]
      exact (div_lt_one hc).2 hsmall
    exact
      (mul_le_mul_of_nonneg_right hSnorm (NNReal.coe_nonneg K)).trans_lt
        hlt
  exact existsUnique_semilinear_of_small_lipschitz B hB N hN (by
    simpa only [S] using hcontract) ell

end SobolevSpace.Weak
