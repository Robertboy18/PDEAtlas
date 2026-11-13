/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.Coercivity
public import PDE.Elliptic.Semilinear.Resolvent.SemilinearEnergy
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity.Finset

/-!
# Proximal iteration for semilinear energies

We study repeated application of the resolvent of

`u ↦ B u + D Phi u`

when the quadratic form `B` has a positive coercivity modulus. At every
positive resolvent parameter, the coercivity estimate gives a contraction
factor

`q = 1 / (1 + lambda * c) < 1`.

Consequently, proximal iteration converges from every initial point to the
unique zero of the semilinear energy gradient. The results are propositions about
the resolvent map `semilinearEnergyResolvent`; no iteration or solution structure is
introduced. Since the resolvent is a contraction, the zero, the convergence of the iterates and
the a posteriori bound come from Mathlib's `ContractingWith.fixedPoint`,
`ContractingWith.tendsto_iterate_fixedPoint` and
`ContractingWith.aposteriori_dist_iterate_fixedPoint_le`.

## Main results

* `semilinearEnergyResolvent_contractingWith`: the resolvent is a strict
  contraction with factor `1/(1 + lambda c)`.
* `isFixedPt_semilinearEnergyResolvent_iff`,
  `existsUnique_semilinearEnergyGradient_zero`: fixed points are zeros of
  `u ↦ B u + D Phi u`, and there is exactly one.
* `tendsto_iterate_semilinearEnergyResolvent_of_eq_zero`,
  `dist_iterate_semilinearEnergyResolvent_le`,
  `aposteriori_dist_iterate_semilinearEnergyResolvent_le`: convergence of
  the iterates with a priori and a posteriori geometric error bounds.

## References

* R. T. Rockafellar, "Monotone operators and the proximal point algorithm", *SIAM J. Control
  Optim.* 14 (1976), 877-898.
  <https://doi.org/10.1137/0314056>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, the definition of the nonlinear resolvent, p. 563.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Positive coercivity and a positive step size make the semilinear-energy
resolvent a strict contraction with factor
`1 / (1 + lambda * c)`. -/
theorem semilinearEnergyResolvent_contractingWith
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ContractingWith (Real.toNNReal (1 / (1 + lambda * c)))
      (semilinearEnergyResolvent
        B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
          Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda.le) := by
  refine ⟨?_, semilinearEnergyResolvent_lipschitzWith
    B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
      c hc.le hBcoercive
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le⟩
  rw [Real.toNNReal_lt_one, div_lt_one]
  · nlinarith [mul_pos hlambda hc]
  · positivity

/-- Fixed points of a positive-parameter semilinear-energy resolvent are
exactly zeros of the energy gradient `u ↦ B u + D Phi u`. -/
theorem isFixedPt_semilinearEnergyResolvent_iff
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (u : H) :
    Function.IsFixedPt
        (semilinearEnergyResolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda.le)
        u ↔
      B u + DPhi u = 0 := by
  constructor
  · intro hfixed
    have hequation :=
      semilinearEnergyResolvent_equation
        B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda.le u
    rw [hfixed.eq] at hequation
    have hscaled : lambda • (B u + DPhi u) = 0 := by
      apply add_left_cancel
      simpa only [add_zero] using hequation
    exact (smul_eq_zero.mp hscaled).resolve_left hlambda.ne'
  · intro hzero
    apply (semilinearEnergyResolvent_eq_iff
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        lambda hlambda.le u u).2
    intro v
    have hzeroAt : B u v + DPhi u v = 0 := by
      simpa only [add_apply, zero_apply] using
        congrArg (fun L : StrongDual ℝ H ↦ L v) hzero
    simp only [hzeroAt, mul_zero, add_zero]

/-- Positive coercivity gives a unique zero of the derivative of the
semilinear energy. The proof applies the Banach fixed-point theorem to the
resolvent at parameter one. -/
theorem existsUnique_semilinearEnergyGradient_zero
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u) :
    ∃! u, B u + DPhi u = 0 := by
  let hBnonneg : ∀ u, 0 ≤ B u u :=
    IsCoercive.self_nonneg_of_bound hc hBcoercive
  let J :=
    semilinearEnergyResolvent
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff 1 zero_le_one
  let hJ :=
    semilinearEnergyResolvent_contractingWith
      B hBsymm c hc hBcoercive
        Phi hPhiConvex DPhi hPhiDiff 1 one_pos
  refine ⟨ContractingWith.fixedPoint J hJ, ?_, ?_⟩
  · apply (isFixedPt_semilinearEnergyResolvent_iff
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        1 one_pos _).1
    simpa only [J] using hJ.fixedPoint_isFixedPt
  · intro u hu
    apply hJ.fixedPoint_unique'
    · simpa only [J] using
        (isFixedPt_semilinearEnergyResolvent_iff
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            1 one_pos u).2 hu
    · exact hJ.fixedPoint_isFixedPt

/-- The distance from a proximal iterate to any zero of the semilinear
energy gradient decays geometrically with the coercivity-improved resolvent
factor. -/
theorem dist_iterate_semilinearEnergyResolvent_le
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (u : H) (hu : B u + DPhi u = 0) (x : H) (n : ℕ) :
    dist
        ((semilinearEnergyResolvent
          B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
            Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda.le)^[n] x)
        u ≤
      (1 / (1 + lambda * c)) ^ n * dist x u := by
  let hBnonneg : ∀ u, 0 ≤ B u u :=
    IsCoercive.self_nonneg_of_bound hc hBcoercive
  let J :=
    semilinearEnergyResolvent
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        lambda hlambda.le
  let q := Real.toNNReal (1 / (1 + lambda * c))
  have hJ : ContractingWith q J := by
    simpa only [J, q] using
      semilinearEnergyResolvent_contractingWith
        B hBsymm c hc hBcoercive
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  have huFixed : Function.IsFixedPt J u := by
    simpa only [J] using
      (isFixedPt_semilinearEnergyResolvent_iff
        B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda u).2 hu
  have hdist := (hJ.toLipschitzWith.iterate n).dist_le_mul x u
  rw [huFixed.iterate n] at hdist
  have hfactorNonneg : 0 ≤ 1 / (1 + lambda * c) := by positivity
  simpa only [J, hBnonneg, q, NNReal.coe_pow,
    Real.coe_toNNReal _ hfactorNonneg] using hdist

/-- Proximal iteration converges from every initial point to any given zero
of the semilinear energy gradient. Strong coercivity makes that zero unique. -/
theorem tendsto_iterate_semilinearEnergyResolvent_of_eq_zero
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (u : H) (hu : B u + DPhi u = 0) (x : H) :
    Filter.Tendsto
      (fun n ↦
        (semilinearEnergyResolvent
          B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
            Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda.le)^[n] x)
      Filter.atTop
      (𝓝 u) := by
  let hBnonneg : ∀ u, 0 ≤ B u u :=
    IsCoercive.self_nonneg_of_bound hc hBcoercive
  let J :=
    semilinearEnergyResolvent
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        lambda hlambda.le
  let hJ :=
    semilinearEnergyResolvent_contractingWith
      B hBsymm c hc hBcoercive
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  have huFixed : Function.IsFixedPt J u := by
    simpa only [J] using
      (isFixedPt_semilinearEnergyResolvent_iff
        B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda u).2 hu
  have huUnique : u = ContractingWith.fixedPoint J hJ :=
    hJ.fixedPoint_unique huFixed
  simpa only [J, hBnonneg, huUnique] using hJ.tendsto_iterate_fixedPoint x

/-- For every positive step size and every initial point, proximal iteration
converges to a zero of the semilinear-energy derivative. That zero is unique
by `existsUnique_semilinearEnergyGradient_zero`. -/
theorem exists_zero_and_tendsto_iterate_semilinearEnergyResolvent
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    ∃ u, B u + DPhi u = 0 ∧
      Filter.Tendsto
        (fun n ↦
          (semilinearEnergyResolvent
            B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
              Phi hPhiConvex DPhi hPhiDiff
              lambda hlambda.le)^[n] x)
        Filter.atTop
        (𝓝 u) := by
  obtain ⟨u, hu, -⟩ :=
    existsUnique_semilinearEnergyGradient_zero
      B hBsymm c hc hBcoercive
        Phi hPhiConvex DPhi hPhiDiff
  exact ⟨u, hu,
    tendsto_iterate_semilinearEnergyResolvent_of_eq_zero
      B hBsymm c hc hBcoercive
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda u hu x⟩

/-- An a posteriori proximal-iteration error bound in terms of two consecutive
iterates. This gives a certified stopping criterion without knowing the
initial distance to the solution. -/
theorem aposteriori_dist_iterate_semilinearEnergyResolvent_le
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (u : H) (hu : B u + DPhi u = 0) (x : H) (n : ℕ) :
    dist
        ((semilinearEnergyResolvent
          B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
            Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda.le)^[n] x)
        u ≤
      dist
          ((semilinearEnergyResolvent
            B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
              Phi hPhiConvex DPhi hPhiDiff
              lambda hlambda.le)^[n] x)
          ((semilinearEnergyResolvent
            B hBsymm (IsCoercive.self_nonneg_of_bound hc hBcoercive)
              Phi hPhiConvex DPhi hPhiDiff
              lambda hlambda.le)^[n + 1] x) /
        (1 - 1 / (1 + lambda * c)) := by
  let hBnonneg : ∀ u, 0 ≤ B u u :=
    IsCoercive.self_nonneg_of_bound hc hBcoercive
  let J :=
    semilinearEnergyResolvent
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        lambda hlambda.le
  let hJ :=
    semilinearEnergyResolvent_contractingWith
      B hBsymm c hc hBcoercive
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  have huFixed : Function.IsFixedPt J u := by
    simpa only [J] using
      (isFixedPt_semilinearEnergyResolvent_iff
        B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda u).2 hu
  have huUnique : u = ContractingWith.fixedPoint J hJ :=
    hJ.fixedPoint_unique huFixed
  have hfactorNonneg : 0 ≤ 1 / (1 + lambda * c) := by positivity
  simpa only [J, hBnonneg, huUnique,
    Real.coe_toNNReal _ hfactorNonneg] using
    hJ.aposteriori_dist_iterate_fixedPoint_le x n

end PDE.Elliptic.Semilinear
