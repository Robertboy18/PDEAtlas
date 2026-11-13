/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Parameters
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedZeroTrace
import PDE.Elliptic.Regularity.Boundary.ChartWeakEquation

/-!
# The gradient and nonlinear flux in boundary coordinates

The Sobolev chain rule gives `Dw = D(E⁻¹)† Du`. The derivative identity for
the inverse chart then gives `DE† Dw = Du`. Consequently the
transformed nonlinear flux is the Piola transform `J DE A(Du)`.

These are identities for the stored weak derivatives of the localized
pullback on the region where its cutoff is locally one. No differentiability
of the Sobolev solution or assumed cancellation identity is used.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open SobolevSpace.WeakChangeOfVariables PDE.Analysis.Operator
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The inverse-chart chain rule cancels the chart derivative. -/
theorem chartGradientMap_of_inverse_chainRule
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {y : ℝ^n} (hy : y ∈ E.target) (v w : ℝ^n)
    (hw : ∀ k, w k = ∑ j : Fin n, v j *
      (∂[k] (fun z ↦ E.symm z)) y j) :
    chartGradientMap E y w = v := by
  ext i
  change (fderiv ℝ (fun x ↦ E x) (E.symm y)).adjoint w i = v i
  rw [← mulVec_chartDerivativeMatrix_eq_adjoint E hE (E.symm y) w i]
  have hcancel :
      Matrix.mulVec (chartDerivativeMatrix E (E.symm y))
        (fun k ↦ ∑ j : Fin n, v j * (∂[k] (fun z ↦ E.symm z)) y j) i = v i :=
    congrFun (mulVec_chartInverseDerivative E hE hSymm y hy v) i
  simpa only [Matrix.mulVec, dotProduct, hw] using hcancel

/-- The transformed flux is exactly the determinant-weighted chart derivative
applied to the physical flux. -/
theorem chartFlux_of_inverse_chainRule
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (A : ℝ^n → ℝ^n) {y : ℝ^n} (hy : y ∈ E.target) (v w : ℝ^n)
    (hw : ∀ k, w k = ∑ j : Fin n, v j *
      (∂[k] (fun z ↦ E.symm z)) y j) :
    chartFlux E A y w =
      |(fderiv ℝ (fun z ↦ E.symm z) y).det| •
        fderiv ℝ (fun x ↦ E x) (E.symm y) (A v) := by
  unfold chartFlux pullbackFlux
  rw [chartGradientMap_of_inverse_chainRule E hE hSymm hy v w hw]
  simp only [chartGradientMap, ContinuousLinearMap.adjoint_adjoint,
    inverseChartJacobianWeight]

variable [Fact (0 < n)]

/-- On the core of the solution cutoff, the localized pullback carries
the physical gradient and flux through the chart derivative. -/
theorem chartFlux_localizedHalfSpacePullback_ae_on_core
    (hΩ : MeasurableSet Ω) (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ E.target)
    (u : H¹₀(Ω)) (A : ℝ^n → ℝ^n) {K : Set (ℝ^n)}
    (hcore : ∀ y ∈ K, κ.toFun =ᶠ[nhds y] 1) :
    ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ K →
      chartFlux E A y
        (Lp.euclideanTuple (fun i ↦ derivCoordCLM i
          (localizedHalfSpacePullbackCLM hΩ hE hSymm hTarget hflat κ hκ u)) y) =
      |(fderiv ℝ (fun z ↦ E.symm z) y).det| •
        fderiv ℝ (fun x ↦ E x) (E.symm y)
          (A (WithLp.toLp 2 (fun j ↦ derivCoordCLM j u (E.symm y)))) := by
  let U := localizedHalfSpacePullbackCLM hΩ hE hSymm hTarget hflat κ hκ u
  have hderiv := ae_all_iff.mpr (fun i ↦
    localizedHalfSpacePullbackCLM_derivative_ae_on_core
      hΩ hE hSymm hTarget hflat κ hκ u i hcore)
  filter_upwards [hderiv, Lp.euclideanTuple_apply_ae (fun i ↦ derivCoordCLM i U)]
    with y hy ht hyK
  have hyt : y ∈ E.target := hκ (subset_tsupport κ.toFun (by
    change κ.toFun y ≠ 0
    rw [(hcore y hyK).eq_of_nhds]; norm_num))
  apply chartFlux_of_inverse_chainRule E hE hSymm A hyt
  intro k
  rw [ht]
  exact hy k hyK

end PDE.Elliptic.Regularity.Quasilinear
