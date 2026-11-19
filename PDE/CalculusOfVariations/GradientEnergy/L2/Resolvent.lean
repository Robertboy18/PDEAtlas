/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.Operator
public import PDE.CalculusOfVariations.GradientEnergy.L2.Equilibrium
public import PDE.Analysis.Convex.Proximal.Resolvent

/-!
# H² regularity of the gradient-energy resolvent

The general proper convex Hilbert resolvent constructs a solution for
every L² load. The domain theorem places it in H²∩H¹₀.
Zero is an equilibrium even with an affine part in the density, so
nonexpansiveness bounds the solution by the data. Global nonlinear
regularity then gives the homogeneous H² estimate.

These are the solution of (31) and the estimate (32) in the proof of
Evans, §9.6.3, Theorem 4. Evans minimizes the functional `J` directly;
we obtain the solution from the abstract resolvent instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.3, proof of Theorem 4, (31)-(32).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

/-- The unit resolvent exists for every L² load, is unique in the entire
ambient subdifferential domain, and has an H² bound depending only on the data.
By the operator formula, the residual is the negative nonlinear divergence,
including for densities with a nonzero affine part. -/
theorem exists_H2_resolvent_l2DirichletGradientEnergy
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : DerivLp n 2 Ω, ∃ W : W^{2,2}(Ω),
      lowerOrderCLM (by omega : 1 ≤ 2) W ∈ (h10SubmoduleOn (n := n) (Ω := Ω)) ∧
      (f - wkpBaseCoordinateCLM W) ∈
        subdifferential (l2DirichletGradientEnergy L) (wkpBaseCoordinateCLM W) ∧
      ‖W‖ ≤ M * ‖f‖ ∧
      ∀ z : DerivLp n 2 Ω,
        f - z ∈ subdifferential (l2DirichletGradientEnergy L) z →
          z = wkpBaseCoordinateCLM W := by
  let I : DerivLp n 2 Ω → EReal := l2DirichletGradientEnergy L
  have hp : IsProper I := isProper_l2DirichletGradientEnergy L
  have hc : Convex ℝ (realEpigraph I) :=
    convex_realEpigraph_l2DirichletGradientEnergy hΩ
      ((Analysis.strongConvexOn_of_hessian_bound hL hlower).strictConvexOn hθ).convexOn
      (integrable_gradientDensity_of_hessian_bounds hbounded hL hθ C.coe_nonneg hlower hupper)
  have hl : LowerSemicontinuous I :=
    lowerSemicontinuous_l2DirichletGradientEnergy_of_hessian_bounds (Fact.out : 0 < n)
      hΩ hbounded hL hθ C.coe_nonneg hlower hupper
  have hz : (0 : DerivLp n 2 Ω) ∈ subdifferential I 0 :=
    zero_mem_subdifferential_l2DirichletGradientEnergy hΩ hbounded hL hθ hlower hupper
  have hRzero : resolvent I hp hc hl 1 zero_lt_one 0 = 0 :=
    resolvent_eq_of_mem_subdifferential hp hc hl zero_lt_one hz (by simp)
  obtain ⟨M, hM, hregularity⟩ := exists_H2_of_mem_subdifferential_l2DirichletGradientEnergy
    hΩ hbounded hgraph hL hθ hlower hupper
  refine ⟨2 * M, mul_nonneg (by norm_num) hM, ?_⟩
  intro f
  let x := resolvent I hp hc hl 1 zero_lt_one f
  have hx : f - x ∈ subdifferential I x := by
    simpa only [inv_one, one_smul] using
      resolvent_residual_mem_subdifferential hp hc hl zero_lt_one f
  have hxnorm : ‖x‖ ≤ ‖f‖ := by
    simpa only [hRzero, sub_zero] using norm_resolvent_sub_le hp hc hl zero_lt_one f 0
  obtain ⟨u, hu⟩ := (l2DirichletGradientEnergy_ne_top_iff hΩ L x).mp
    (ne_top_of_mem_subdifferential hp hx)
  have hux : f - baseCoordCLM u ∈ subdifferential I (baseCoordCLM u) := by
    rwa [hu]
  obtain ⟨W, hW, hWnorm⟩ := hregularity u (f - baseCoordCLM u) hux
  have hbase : wkpBaseCoordinateCLM W = baseCoordCLM u := by
    have hb := congrArg wkpBaseCoordinateCLM hW
    simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex, baseCoordCLM_apply] using hb
  refine ⟨W, by rw [hW]; exact u.property, ?_, ?_, ?_⟩
  · simpa only [hbase] using hux
  · calc
      ‖W‖ ≤ M * ‖f - baseCoordCLM u‖ := hWnorm
      _ ≤ M * (‖f‖ + ‖x‖) := by
        rw [hu]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hM
      _ ≤ M * (‖f‖ + ‖f‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hxnorm) hM
      _ = (2 * M) * ‖f‖ := by ring
  · intro z hz
    rw [hbase, hu]
    exact eq_of_subdifferential_resolvent_eq hp (w := f) (show (0 : ℝ) ≤ 1 by norm_num)
      hz hx (by simp) (by simp)

end PDE.CalculusOfVariations
