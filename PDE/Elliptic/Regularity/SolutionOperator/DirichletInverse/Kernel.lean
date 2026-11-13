/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.ClassicalEquation
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Comparison

/-!
# Triviality of the smooth Dirichlet kernel

The maximum principle rules out a nonzero weak solution with zero load
when the principal matrix is uniformly elliptic (not necessarily symmetric) and the
potential is nonnegative. Smooth closure regularity and the geometric trace kernel provide
the classical equation and boundary values used in the comparison.

There is no coercivity assumption on the full form, nor any restriction on the
size, sign, or divergence of the drift. Connectedness is unnecessary.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A zero-load Dirichlet weak solution is zero. All classical and boundary
identifications are derived from the weak equation and smooth data. -/
theorem eq_zero_of_form_eq_zero
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (u : H¹₀(Ω)) (hu : ∀ v : H¹₀(Ω), P.form hopen hbounded u v = 0) :
    u = 0 := by
  let hzero (k : ℕ) : ContDiffUpToBoundary k (fun _ : ℝ^n ↦ (0 : ℝ)) Ω :=
    ContDiffUpToBoundary.const 0
  have hzeroLp : (hzero 0).toLp hopen hbounded 2 = 0 :=
    Lp.ext (((hzero 0).toLp_coeFn hopen hbounded 2).trans
      (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)).symm)
  obtain ⟨z, hz, hzraw, hzae, hboundary, heq⟩ :=
    P.exists_smoothRepresentative_of_form_eq hopen hbounded hgraph halpha hell
      (fun _ ↦ 0) hzero 0 u (fun v ↦ by
        simpa only [zero_mul, add_zero, hzeroLp, inner_zero_left] using hu v)
  have hreg (x : ℝ^n) (hx : x ∈ Ω) : ContDiffAt ℝ 2 z x :=
    (hzraw 2).contDiffOn.contDiffAt (hopen.mem_nhds hx)
  have hload (x : ℝ^n) (hx : x ∈ Ω) : P.classicalLoad z x = 0 := by
    simpa only [zero_mul, add_zero] using heq x hx
  have hloadzero (x : ℝ^n) (hx : x ∈ Ω) :
      P.classicalLoad (fun _ ↦ 0) x = 0 := by
    exact (P.classicalLoad_eq_matrixOperator hopen hx contDiffAt_const).trans
      ((EllipticMaximum.matrixOperator_const
        (fun y ↦ Matrix.of (P.principal y)) P.nondivergenceDrift P.potential 0 x).trans
        (mul_zero _))
  have hupper := P.le_on_closure_of_classicalLoad_le hopen hbounded halpha hell hc
    hz.continuousOn continuousOn_const hreg (fun _ _ ↦ contDiffAt_const)
    (fun x hx ↦ (hload x hx).le.trans (hloadzero x hx).symm.le)
    (fun x hx ↦ (hboundary x hx).le)
  have hlower := P.le_on_closure_of_classicalLoad_le hopen hbounded halpha hell hc
    continuousOn_const hz.continuousOn (fun _ _ ↦ contDiffAt_const) hreg
    (fun x hx ↦ (hloadzero x hx).le.trans (hload x hx).symm.le)
    (fun x hx ↦ (hboundary x hx).symm.le)
  apply baseCoordCLM_injective hopen
  rw [map_zero]
  apply Lp.ext
  filter_upwards [hzae, ae_restrict_mem hopen.measurableSet,
    Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hxz hx hxzero
  exact hxz.symm.trans
    ((le_antisymm (hupper x (subset_closure hx)) (hlower x (subset_closure hx))).trans
      hxzero.symm)

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
