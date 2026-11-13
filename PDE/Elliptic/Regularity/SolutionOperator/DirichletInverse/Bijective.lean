/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Kernel
import PDE.Elliptic.Variational.FredholmAlternative

/-!
# Invertibility of the smooth Dirichlet operator

The weak operator is bijective when the potential is nonnegative.
Gårding's mass shift and bounded-domain Rellich compactness give the Fredholm
alternative; the classical maximum principle eliminates its kernel alternative.
No coercivity of the unshifted full form is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open PDE.Analysis.Variational
open scoped ENNReal

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Bijectivity of the full weak Dirichlet operator, including arbitrary
smooth drift. The data imply shifted coercivity and a trivial unshifted kernel. -/
theorem bijective_form
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    Function.Bijective (P.form hopen hbounded) := by
  let a := fun i j ↦ (P.principal_smooth 0 i j).toLp hopen hbounded ∞
  let b := fun i ↦ (P.drift_smooth 0 i).toLp hopen hbounded ∞
  let c := (P.potential_smooth 0).toLp hopen hbounded ∞
  let aSob := fun i j ↦ (P.principal_smooth 1 i j).toWkpSpaceOn hopen hbounded ∞
  have ha : coefficientBase aSob = a := by
    funext i j
    exact Lp.ext (((P.principal_smooth 1 i j).toWkpSpaceOn_base_ae
      hopen hbounded ∞).trans
      ((P.principal_smooth 0 i j).toLp_coeFn hopen hbounded ∞).symm)
  have hellAE := coefficientBase_aeUniformlyElliptic hopen.measurableSet aSob P.principal
    (fun i j ↦ (P.principal_smooth 1 i j).toWkpSpaceOn_base_ae hopen hbounded ∞)
    alpha halpha hell
  rw [ha] at hellAE
  have hcoercive := shiftedDivergenceForm_isCoercive
    (multiplicationCoefficientOperator a) (multiplicationFirstOrderOperator b)
    (multiplicationZeroOrderOperator c)
    (integratedElliptic_multiplication_of_ae a hellAE)
    (lowerOrderBounds_multiplication b c (norm_nonneg b) (norm_nonneg c)
      (norm_le_pi_norm b) le_rfl)
  have hFredholm := fullDivergenceForm.fredholmAlternative_of_bounded
    hopen.measurableSet hbounded (multiplicationCoefficientOperator a)
    (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
    (coerciveShift (n := n) alpha ‖b‖ ‖c‖) hcoercive
  have hkernel (u : H¹₀(Ω))
      (hu : IsWeakSolution (P.form hopen hbounded) 0 u) : u = 0 :=
    P.eq_zero_of_form_eq_zero hopen hbounded hgraph halpha hell hc u hu
  rcases hFredholm with ⟨⟨u, hu, hzero⟩, _⟩ | ⟨hsolv, _⟩
  · exact (hu (hkernel u hzero)).elim
  · have hsolv' : ∀ ell : StrongDual ℝ (H¹₀(Ω)),
        ∃! u, P.form hopen hbounded u = ell := by
      intro ell
      obtain ⟨u, hu, huniq⟩ := hsolv ell
      refine ⟨u, ContinuousLinearMap.ext hu, ?_⟩
      intro v hv
      apply huniq v
      intro z
      exact congrArg (fun L : StrongDual ℝ (H¹₀(Ω)) ↦ L z) hv
    refine ⟨?_, fun ell ↦ (hsolv' ell).exists⟩
    intro u v huv
    exact (hsolv' (P.form hopen hbounded v)).unique huv rfl

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
