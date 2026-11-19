/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartCoefficients
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Agreement
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Sobolev transport of a boundary-chart weak equation

`smoothWeakEquation_flattened` (in `PDE.Elliptic.Regularity.Boundary.ChartCoefficients`)
transports a divergence-form weak identity through a boundary chart when the solution is
differentiable. In the boundary `H²` argument, step 8 of Evans's proof of §6.3.2,
Theorem 4, the solution is only an `H¹` function, so we prove the nonsmooth
counterpart. The transport lemmas take coordinate functions `du` and `dv` related by
the almost-everywhere chain-rule identity

`dv_k(y) = ∑ⱼ du_j(E⁻¹ y) · ∂(E⁻¹)ⱼ/∂y_k` almost everywhere on the chart target.

The derivatives in these lemmas are those of the `C¹` chart `E` and its inverse.
The test vector field `eta` is arbitrary; when `eta = ∇psi`, its transformed
coordinates give `∇(psi ∘ E)`. The principal pairing over the chart source equals
the flattened pairing with coefficient `J · Dᵀ A D` over the chart target.
Together with the forcing change of variables, this transports the given
physical integral identity to the target.

The final section specialises this to the Sobolev coordinates produced by the `C¹` domain
extension machinery: the localized boundary piece `ψᵢ U` and its image under the bounded flattening
operator `flattenCLM`. There the chain-rule relation between the two gradient representatives
comes from the extension library, so only the physical weak identity is needed.

## Main results

* `chartDerivativeMatrix_eq_fderiv_apply`, `mulVec_chartInverseDerivative`: the chart matrix as
  the Fréchet derivative on basis vectors, and cancellation of the chart derivative against the
  derivative of its inverse.
* `integral_source_principalPairing_weak_eq_integral_flattened`: change of variables for the
  principal pairing with weak-gradient representatives.
* `weakEquation_flattened_of_weakGradientRepresentatives`: transport of a divergence-form weak
  identity through a `C¹` chart without differentiating the solution.
* `localizedChartGradient`, `flattenedChartGradient`, `flattenCLM_weakEquation_on_chartTarget`:
  the specialisation to the library's localized and flattened Sobolev coordinates.

## Implementation notes

The representative-level lemmas assume the a.e. chain-rule identity, without separate
measurability or integrability hypotheses on `du`, `dv`, or `eta`. They assert equalities
of Bochner integrals, not integrability of the pairings. Applying them to a weak
equation requires choosing `eta` as the test gradient and supplying the physical
integral identity. The final specialization obtains the gradient representatives
and their chain-rule relation from the Sobolev extension operators.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 8 of the proof of Theorem 4, (61)-(68),
  pp. 338-339.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set Function ENNReal
open scoped BigOperators Topology Sobolev

variable {n : ℕ}

/-- A chart-matrix entry is the corresponding coordinate of the Fréchet
derivative applied to a standard basis vector. -/
theorem chartDerivativeMatrix_eq_fderiv_apply
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (x : ℝ^n) (i k : Fin n) :
    chartDerivativeMatrix (n := n) E x i k =
      ((fderiv ℝ (fun z ↦ E z) x)
        (EuclideanSpace.single i (1 : ℝ))) k := by
  have hchart : HasFDerivAt (fun z ↦ E z)
      (fderiv ℝ (fun z ↦ E z) x) x :=
    (hE.differentiable (by norm_num) x).hasFDerivAt
  have hcoordDeriv :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) (E x) k).comp x hchart
  have happlyCoord := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦
      L (EuclideanSpace.single i (1 : ℝ))) hcoordDeriv.fderiv
  change
    (fderiv ℝ (fun z ↦ (E z).ofLp k) x)
        (EuclideanSpace.single i (1 : ℝ)) =
      ((fderiv ℝ (fun z ↦ E z) x)
        (EuclideanSpace.single i (1 : ℝ))).ofLp k at happlyCoord
  simpa [chartDerivativeMatrix, partialDeriv,
    ContinuousLinearMap.comp_apply] using happlyCoord

/-- The derivative of a C1 chart cancels the derivative of its inverse in
the row/column convention used by `Matrix.mulVec`.

If `D i k = ∂y_k/∂x_i` and
`z_k = ∑_j xi_j ∂x_j/∂y_k`, then `D z = xi`. -/
theorem mulVec_chartInverseDerivative
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (y : ℝ^n) (hy : y ∈ E.target) (xi : Fin n → ℝ) :
    Matrix.mulVec
      (chartDerivativeMatrix (n := n) E (E.symm y))
      (fun k ↦ ∑ j : Fin n, xi j *
        ((∂[k] (fun z ↦ E.symm z)) y) j) = xi := by
  classical
  let x := E.symm y
  have hx : x ∈ E.source := E.map_target hy
  have hchart : HasFDerivAt (fun z ↦ E z)
      (fderiv ℝ (fun z ↦ E z) x) x :=
    (hE.differentiable (by norm_num) x).hasFDerivAt
  have hinverse : HasFDerivAt (fun z ↦ E.symm z)
      (fderiv ℝ (fun z ↦ E.symm z) y) y :=
    (hEsymm.differentiable (by norm_num) y).hasFDerivAt
  have hEx : E x = y := by
    simpa [x] using E.right_inv hy
  have hinverseAt : HasFDerivAt (fun z ↦ E.symm z)
      (fderiv ℝ (fun z ↦ E.symm z) y) (E x) := by
    simpa [hEx] using hinverse
  have hcomp := hinverseAt.comp x hchart
  have hroundtrip :
      Filter.EventuallyEq (nhds x) (fun z ↦ E.symm (E z)) id := by
    filter_upwards [E.open_source.mem_nhds hx] with z hz
    exact E.left_inv hz
  have hcompId :
      (fderiv ℝ (fun z ↦ E.symm z) y).comp
          (fderiv ℝ (fun z ↦ E z) x) =
        ContinuousLinearMap.id ℝ (ℝ^n) :=
    (hcomp.congr_of_eventuallyEq hroundtrip.symm).unique (hasFDerivAt_id x)
  funext i
  have hcoord (j : Fin n) :
      (∑ k : Fin n,
          chartDerivativeMatrix (n := n) E x i k *
            ((fderiv ℝ (fun z ↦ E.symm z) y)
              (EuclideanSpace.single k (1 : ℝ))) j) =
        if j = i then 1 else 0 := by
    have happly := congrArg
      (fun L : (ℝ^n →L[ℝ] ℝ^n) ↦
        L (EuclideanSpace.single i (1 : ℝ))) hcompId
    have hcomponent := congrArg (fun v : ℝ^n ↦ v j) happly
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcomponent
    have hdecomp (v : ℝ^n) :
        v = ∑ k : Fin n, v k • EuclideanSpace.single k (1 : ℝ) := by
      ext k
      simp [Pi.single_apply]
    have hDE (k : Fin n) :
        ((fderiv ℝ (fun z ↦ E z) x)
          (EuclideanSpace.single i (1 : ℝ))) k =
          chartDerivativeMatrix (n := n) E x i k := by
      exact (chartDerivativeMatrix_eq_fderiv_apply
        (n := n) E hE x i k).symm
    rw [hdecomp ((fderiv ℝ (fun z ↦ E z) x)
      (EuclideanSpace.single i (1 : ℝ)))] at hcomponent
    simp only [map_sum, map_smul] at hcomponent
    simp_rw [hDE] at hcomponent
    simpa [PiLp.single_apply, mul_comm] using hcomponent
  simp only [Matrix.mulVec]
  calc
    (∑ k : Fin n, chartDerivativeMatrix (n := n) E (E.symm y) i k *
        ∑ j : Fin n, xi j *
          ((fderiv ℝ (fun z ↦ E.symm z) y)
            (EuclideanSpace.single k (1 : ℝ))) j) =
        ∑ j : Fin n, xi j *
          ∑ k : Fin n, chartDerivativeMatrix (n := n) E x i k *
            ((fderiv ℝ (fun z ↦ E.symm z) y)
              (EuclideanSpace.single k (1 : ℝ))) j := by
          simp only [x]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ = ∑ j : Fin n, xi j * (if j = i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcoord j]
    _ = xi i := by simp

/-- Principal-part change of variables for weak derivative representatives.

`du` is a physical-coordinate gradient representative and `dv` is a
flattened-coordinate representative satisfying the Sobolev chain rule with
the inverse chart almost everywhere on the target. The test vector field
`eta` is arbitrary. The change of variables uses the derivatives of the
chart and inverse chart; no differentiability of `du` or `dv` is required. -/
theorem integral_source_principalPairing_weak_eq_integral_flattened
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (du dv eta : Fin n → ℝ^n → ℝ)
    (hdv : ∀ k : Fin n,
      dv k =ᵐ[domainMeasure n E.target] fun y ↦
        ∑ j : Fin n, du j (E.symm y) *
          ((∂[k] (fun z ↦ E.symm z)) y) j) :
    (∫ x in E.source,
        principalPairing (A x) (fun j ↦ du j x)
          (fun i ↦ ∑ k : Fin n,
            chartDerivativeMatrix (n := n) E x i k * eta k (E x))
        ∂(volume : Measure (ℝ^n))) =
      ∫ y in E.target,
        principalPairing
          (flattenedPrincipalCoefficientAt (n := n) E A y)
          (fun l ↦ dv l y) (fun k ↦ eta k y)
        ∂(volume : Measure (ℝ^n)) := by
  classical
  have hderiv : ∀ y ∈ E.target,
      HasFDerivAt (fun z ↦ E.symm z)
        (fderiv ℝ (fun z ↦ E.symm z) y) y := by
    intro y _
    exact (hEsymm.differentiable (by norm_num) y).hasFDerivAt
  have hchange :=
    SobolevSpace.WeakChangeOfVariables.integral_source_eq_integral_abs_det_fderiv_mul
      (n := n) (E := E)
      (E' := fun y ↦ fderiv ℝ (fun z ↦ E.symm z) y)
      hderiv
      (fun x ↦ principalPairing (A x) (fun j ↦ du j x)
        (fun i ↦ ∑ k : Fin n,
          chartDerivativeMatrix (n := n) E x i k * eta k (E x)))
  rw [hchange]
  apply integral_congr_ae
  have hdvAll : ∀ᵐ y ∂domainMeasure n E.target, ∀ k : Fin n,
      dv k y = ∑ j : Fin n, du j (E.symm y) *
        ((fderiv ℝ (fun z ↦ E.symm z) y)
          (EuclideanSpace.single k (1 : ℝ))) j :=
    MeasureTheory.ae_all_iff.2 hdv
  filter_upwards [ae_restrict_mem E.open_target.measurableSet, hdvAll] with
      y hy hdvy
  have hcancel := mulVec_chartInverseDerivative
    (n := n) E hE hEsymm y hy (fun j ↦ du j (E.symm y))
  have hright := principalPairing_flattenedPrincipalCoefficientAt
    (n := n) E A y (fun l ↦ dv l y) (fun k ↦ eta k y)
  rw [hright]
  rw [show Matrix.mulVec
      (chartDerivativeMatrix (n := n) E (E.symm y))
      (fun l ↦ dv l y) = fun j ↦ du j (E.symm y) by
    simpa only [hdvy, partialDeriv] using hcancel]
  rw [E.right_inv hy]
  simp only [inverseChartJacobianWeight]
  congr 1

/-- Transport a divergence-form weak identity through a C1 chart when the
physical and flattened weak-gradient representatives are related by the
Sobolev chain rule.

The a.e. relation `hdv` connects the coordinate functions `du` and `dv`,
and `hweak` supplies the physical integral identity for the fixed `psi`
and `eta`. Only the chart and inverse chart are differentiated. Taking
`du` and `dv` to be weak-gradient representatives and `eta` to be a test
gradient gives the transport identity for an `H¹` solution. -/
theorem weakEquation_flattened_of_weakGradientRepresentatives
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (f psi : ℝ^n → ℝ)
    (du dv eta : Fin n → ℝ^n → ℝ)
    (hdv : ∀ k : Fin n,
      dv k =ᵐ[domainMeasure n E.target] fun y ↦
        ∑ j : Fin n, du j (E.symm y) *
          ((∂[k] (fun z ↦ E.symm z)) y) j)
    (hweak :
      (∫ x in E.source,
          principalPairing (A x) (fun j ↦ du j x)
            (fun i ↦ ∑ k : Fin n,
              chartDerivativeMatrix (n := n) E x i k * eta k (E x))
          ∂(volume : Measure (ℝ^n))) =
        ∫ x in E.source, f x * psi (E x)
          ∂(volume : Measure (ℝ^n))) :
    (∫ y in E.target,
        principalPairing
          (flattenedPrincipalCoefficientAt (n := n) E A y)
          (fun l ↦ dv l y) (fun k ↦ eta k y)
        ∂(volume : Measure (ℝ^n))) =
      ∫ y in E.target,
        flattenedForcing (n := n) E f y * psi y
        ∂(volume : Measure (ℝ^n)) := by
  calc
    _ = ∫ x in E.source,
          principalPairing (A x) (fun j ↦ du j x)
            (fun i ↦ ∑ k : Fin n,
              chartDerivativeMatrix (n := n) E x i k * eta k (E x))
          ∂(volume : Measure (ℝ^n)) :=
      (integral_source_principalPairing_weak_eq_integral_flattened
        (n := n) hE hEsymm A du dv eta hdv).symm
    _ = ∫ x in E.source, f x * psi (E x)
          ∂(volume : Measure (ℝ^n)) := hweak
    _ = ∫ y in E.target,
          flattenedForcing (n := n) E f y * psi y
          ∂(volume : Measure (ℝ^n)) :=
      integral_source_forcing_eq_integral_flattenedForcing
        (n := n) hEsymm f psi

section BoundaryChart

variable [Fact (0 < n)] {Omega : Set (ℝ^n)}

/-- Physical weak-gradient representative of the localized boundary piece
`psi_i * U`, obtained by taking its `j`-th derivative coordinate in the
Sobolev space on `Omega`. -/
def localizedChartGradient
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N) (U : W^{1,2}(Omega))
    (j : Fin n) : ℝ^n → ℝ :=
  ((((cutoffCLM (n := n) (p := (2 : ENNReal)) (Ω := Omega)
      (hOmega.boundaryCutoff i) U : WkpAmbientOn n 1 2 Omega)
      (singleDerivIndex n j) : DerivLp n 2 Omega) : ℝ^n → ℝ))

/-- Flattened weak-gradient representative produced by the bounded chart
operator. -/
def flattenedChartGradient
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N) (U : W^{1,2}(Omega))
    (k : Fin n) : ℝ^n → ℝ :=
  (((SobolevSpace.Extension.C1.BoundaryPiece.flattenCLM
      (n := n) (p := (2 : ENNReal)) (Ω := Omega) i U :
        WkpAmbientOn n 1 2 (HalfSpace.upper n))
      (singleDerivIndex n k) : DerivLp n 2 (HalfSpace.upper n)) :
        ℝ^n → ℝ)

/-- The representative-level transport theorem specialized to the
localized and flattened Sobolev coordinates constructed by the C1-domain
extension machinery.

The hypothesis is the physical weak identity restricted to the chart source;
the conclusion is its transformed identity on the chart target.
`flattenCLM_deriv_agree_ae` supplies the Sobolev chain-rule relation between
the two gradient representatives. -/
theorem flattenCLM_weakEquation_on_chartTarget
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N) (U : W^{1,2}(Omega))
    (A : ℝ^n → Fin n → Fin n → ℝ)
    (f psi : ℝ^n → ℝ) (eta : Fin n → ℝ^n → ℝ)
    (hweak :
      let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
        (n := n) (Ω := Omega) i
      (∫ x in E.source,
          principalPairing (A x)
            (fun j ↦ localizedChartGradient hOmega i U j x)
            (fun r ↦ ∑ k : Fin n,
              chartDerivativeMatrix (n := n) E x r k * eta k (E x))
          ∂(volume : Measure (ℝ^n))) =
        ∫ x in E.source, f x * psi (E x)
          ∂(volume : Measure (ℝ^n))) :
    let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
      (n := n) (Ω := Omega) i
    (∫ y in E.target,
        principalPairing
          (flattenedPrincipalCoefficientAt (n := n) E A y)
          (fun k ↦ flattenedChartGradient hOmega i U k y)
          (fun k ↦ eta k y)
        ∂(volume : Measure (ℝ^n))) =
      ∫ y in E.target,
        flattenedForcing (n := n) E f y * psi y
        ∂(volume : Measure (ℝ^n)) := by
  classical
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
    (n := n) (Ω := Omega) i
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := by
    simpa [E, SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
      hOmega.chart_contDiff i
  have hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y) := by
    simpa [E, SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
      hOmega.chart_symm_contDiff i
  have hdv : ∀ k : Fin n,
      flattenedChartGradient hOmega i U k =ᵐ[domainMeasure n E.target]
        fun y ↦ ∑ j : Fin n, localizedChartGradient hOmega i U j (E.symm y) *
          ((fderiv ℝ (fun z ↦ E.symm z) y)
            (EuclideanSpace.single k (1 : ℝ))) j := by
    intro k
    filter_upwards [
      SobolevSpace.Extension.C1.BoundaryPiece.flattenCLM_deriv_agree_ae
        (n := n) (p := (2 : ENNReal)) (Ω := Omega) i U k] with y hy
    simpa [E, localizedChartGradient, flattenedChartGradient,
      SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hy
  exact weakEquation_flattened_of_weakGradientRepresentatives
    (n := n) hE hEsymm A f psi
      (localizedChartGradient hOmega i U)
      (flattenedChartGradient hOmega i U) eta hdv hweak

end BoundaryChart

end SobolevSpace.GraphSpace.BoundaryRegularity
