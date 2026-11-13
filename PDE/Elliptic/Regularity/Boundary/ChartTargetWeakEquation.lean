/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartWeakEquation
public import PDE.Elliptic.Regularity.Boundary.TestFunctionPullback
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Localization.CutoffEquation.WeakEquation
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Weak equations on flattened boundary-chart targets

We transport a localized divergence-form weak equation from the physical domain to the target of a
boundary chart. We localize upper-half-space tests, identify the pulled-back variational equation,
and state the chart-target forcing identity. The solution is differentiated only through its Sobolev
coordinates. For the localized solution this is the weak equation (61) of step 8 of Evans's proof of
§6.3.2, Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 8 of the proof of Theorem 4, (61)-(68),
  pp. 338-339.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set Function ENNReal
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs
open scoped BigOperators Topology

variable {n : ℕ}

section BoundaryChart

variable [Fact (0 < n)]

/-- Localize an arbitrary upper-half-space test function by the canonical
target cutoff for a boundary chart.  Its support lies in the chart target, so
it is a legitimate test in the chart-local transformed weak equation. -/
noncomputable def localizeUpperTestToChartTarget
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (phi : TestFunctionOn n (SobolevSpace.HalfSpace.upper n)) :
    TestFunctionOn n
      (SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
        (n := n) (Ω := Omega) i).target := by
  let eta := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
    (n := n) (Ω := Omega) i
  let product := TestFunction.mul eta phi.1
  refine ⟨product, ?_⟩
  intro y hy
  have hproductToFun :
      product.toFun = fun x ↦ eta.toFun x * phi.1.toFun x := by
    funext x
    simp [product, TestFunction.mul_apply]
  have hyProduct :
      y ∈ tsupport (fun x ↦ eta.toFun x * phi.1.toFun x) := by
    rw [← hproductToFun]
    exact hy
  have hyEta : y ∈ tsupport eta.toFun := by
    exact (tsupport_mul_subset_left
      (f := eta.toFun) (g := phi.1.toFun)) hyProduct
  have hyPhi : y ∈ tsupport phi.1.toFun := by
    exact (tsupport_mul_subset_right
      (f := eta.toFun) (g := phi.1.toFun)) hyProduct
  rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
  exact ⟨Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_targetSupportCutoff_subset_target
      (n := n) (Ω := Omega) i hyEta,
    phi.2 hyPhi⟩

/-- On the compact support of the flattened solution, target localization
does not change an upper-half-space test function. -/
theorem localizeUpperTestToChartTarget_eq_on_KTarget
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (phi : TestFunctionOn n (SobolevSpace.HalfSpace.upper n)) :
    ∀ y ∈ Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget
        (n := n) (Ω := Omega) i,
      (localizeUpperTestToChartTarget hOmega i phi).1.toFun y = phi.1.toFun y := by
  intro y hy
  change (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := n) (Ω := Omega) i).toFun y * phi.1.toFun y = phi.1.toFun y
  rw [Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff_eq_one_on_boundarySupportInTarget
    (n := n) (Ω := Omega) i y hy]
  simp

/-- On `KTarget`, target localization also leaves every coordinate
derivative of the test function unchanged.  The neighborhood form of the
cutoff identity is essential here. -/
theorem partialDeriv_localizeUpperTestToChartTarget_eq_on_KTarget
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (phi : TestFunctionOn n (SobolevSpace.HalfSpace.upper n))
    (k : Fin n) :
    ∀ y ∈ Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget
        (n := n) (Ω := Omega) i,
      (∂[k]
          (localizeUpperTestToChartTarget hOmega i phi).1.toFun) y =
        (∂[k] phi.1.toFun) y := by
  intro y hy
  have h : (fun z ↦ (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := n) (Ω := Omega) i).toFun z * phi.1.toFun z) =ᶠ[𝓝 y] phi.1.toFun := by
    filter_upwards [targetSupportCutoff_eq_one_nhds_on_boundarySupportInTarget
      (n := n) (Ω := Omega) i y hy] with z hz
    simp [hz]
  exact PDE.partialDeriv_congr_nhds k h


end BoundaryChart

/-- An operator-valued weak equation evaluated at an arbitrary `H1_0` test,
with the finite coefficient sum assembled into `principalPairing`. -/
theorem weakSolution_eq_principalPairing_integral
    {Omega : Set (ℝ^n)}
    (a : Fin n → Fin n → DerivLp n ∞ Omega)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Omega)
        (multiplicationCoefficientOperator (n := n) (Ω := Omega) a))
      (loadFunctional (n := n) (Ω := Omega) f) u)
    (v : H¹₀(Omega)) :
    (∫ x,
        principalPairing
          (fun i j ↦ (a i j : ℝ^n → ℝ) x)
          (fun j ↦
            (derivCoordCLM (n := n) (Ω := Omega) j u :
              ℝ^n → ℝ) x)
          (fun i ↦
            (derivCoordCLM (n := n) (Ω := Omega) i v :
              ℝ^n → ℝ) x)
      ∂domainMeasure n Omega) =
      ∫ x, (f : ℝ^n → ℝ) x *
          (baseCoordCLM (n := n) (Ω := Omega) v : ℝ^n → ℝ) x
        ∂domainMeasure n Omega := by
  classical
  have hterm (i j : Fin n) : Integrable (fun x ↦ (a i j : ℝ^n → ℝ) x *
      (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ) x *
      (derivCoordCLM (n := n) (Ω := Omega) i v : ℝ^n → ℝ) x) (domainMeasure n Omega) := by
    refine (L2.integrable_inner (𝕜 := ℝ) (multiplicationCoefficientOperator a i j
      (derivCoordCLM j u)) (derivCoordCLM i v)).congr ?_
    filter_upwards [multiplicationCoefficientOperator_apply_ae a i j (derivCoordCLM j u)] with x hx
    rw [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [← weakSolution_eq_integral a f u hu v]
  simp only [principalPairing]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j]
  exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hterm i j


/-- Integrating a zero extension from `S` inside `Omega` is the same as
integrating the original function over `S` against volume. -/
theorem integral_domainMeasure_indicator_eq_setIntegral
    {Omega S : Set (ℝ^n)} (hS : MeasurableSet S) (hSOmega : S ⊆ Omega)
    (F : ℝ^n → ℝ) :
    (∫ x, S.indicator F x ∂domainMeasure n Omega) =
      ∫ x in S, F x ∂(volume : Measure (ℝ^n)) := by
  rw [MeasureTheory.integral_indicator hS]
  rw [show (domainMeasure n Omega).restrict S = domainMeasure n S by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (volume : Measure (ℝ^n))) hSOmega)]

section BoundaryChart

variable [Fact (0 < n)]

/-- Evaluating a physical weak solution at the `H1_0` pullback of
a target test yields the weak identity restricted to the chart source.

This is the missing nonsmooth test-function step: `phi` is smooth in
flattened coordinates, but its physical pullback is used only through the
Sobolev element produced by `exists_chartTest_pullback`. -/
theorem weakSolution_chartPullback_source_identity
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (a : Fin n → Fin n → DerivLp n ∞ Omega)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Omega)
        (multiplicationCoefficientOperator (n := n) (Ω := Omega) a))
      (loadFunctional (n := n) (Ω := Omega)
        f) u)
    (phi : TestFunctionOn n
      (SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
        (n := n) (Ω := Omega) i).target) :
    let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
      (n := n) (Ω := Omega) i
    (∫ x in E.source,
        principalPairing (fun r s ↦ (a r s : ℝ^n → ℝ) x)
          (fun s ↦
            (derivCoordCLM (n := n) (Ω := Omega) s u : ℝ^n → ℝ) x)
          (fun r ↦ ∑ k : Fin n,
            chartDerivativeMatrix (n := n) E x r k *
              (∂[k] phi.1.toFun) (E x))
        ∂(volume : Measure (ℝ^n))) =
      ∫ x in E.source, (f : ℝ^n → ℝ) x * phi.1.toFun (E x)
        ∂(volume : Measure (ℝ^n)) := by
  classical
  intro E
  obtain ⟨Phi, hPhiBase, hPhiDeriv⟩ :=
    PDE.Elliptic.Regularity.Boundary.TestFunctionPullback.exists_chartTest_pullback hOmega i phi
  have hS := E.open_source.measurableSet
  have hSub : E.source ⊆ Omega := fun x hx ↦ by
    simpa [E, SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx.2
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := hOmega.chart_contDiff i
  have hprincipal : (fun x ↦ principalPairing (fun r s ↦ (a r s : ℝ^n → ℝ) x)
      (fun s ↦ (derivCoordCLM (n := n) (Ω := Omega) s u : ℝ^n → ℝ) x)
      (fun r ↦ (derivCoordCLM (n := n) (Ω := Omega) r Phi : ℝ^n → ℝ) x))
      =ᵐ[domainMeasure n Omega] E.source.indicator fun x ↦
        principalPairing (fun r s ↦ (a r s : ℝ^n → ℝ) x)
          (fun s ↦ (derivCoordCLM (n := n) (Ω := Omega) s u : ℝ^n → ℝ) x)
          (fun r ↦ ∑ k : Fin n, chartDerivativeMatrix (n := n) E x r k *
            (∂[k] phi.1.toFun) (E x)) := by
    filter_upwards [ae_all_iff.2 hPhiDeriv] with x
      (hx : ∀ r, (derivCoordCLM (n := n) (Ω := Omega) r Phi : ℝ^n → ℝ) x = _)
    simp only [hx, PDE.Elliptic.Regularity.Boundary.TestFunctionPullback.pullbackDerivative]
    by_cases hxE : x ∈ E.source
    · simp only [E, Set.indicator_of_mem hxE, chartDerivativeMatrix_eq_fderiv_apply E hE, mul_comm]
    · simp only [E, Set.indicator_of_notMem hxE, principalPairing, mul_zero,
        Finset.sum_const_zero]
  have hbase : (fun x ↦ (f : ℝ^n → ℝ) x *
      (baseCoordCLM (n := n) (Ω := Omega) Phi : ℝ^n → ℝ) x)
      =ᵐ[domainMeasure n Omega] E.source.indicator fun x ↦ (f : ℝ^n → ℝ) x * phi.1.toFun (E x) := by
    filter_upwards [hPhiBase] with x hx
    rw [Set.indicator_mul_right]
    exact congrArg ((f : ℝ^n → ℝ) x * ·) hx
  have hglobal := weakSolution_eq_principalPairing_integral a f u hu Phi
  rwa [integral_congr_ae hprincipal, integral_congr_ae hbase,
    integral_domainMeasure_indicator_eq_setIntegral hS hSub,
    integral_domainMeasure_indicator_eq_setIntegral hS hSub] at hglobal


/--
The support and variational identities obtained by transporting one localized
physical weak equation to a boundary-chart target.

This is the common chart-level handoff used by both the `L²` and higher-order
forcing arguments.
-/
structure LocalizedChartEquationData
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (u : H¹(Omega))
    (physicalForcing : DerivLp n 2 Omega) where
  /-- The physical forcing is supported in the selected boundary patch. -/
  physicalForcing_support :
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport
        (n := n) (Ω := Omega) i).indicator
          (physicalForcing : ℝ^n → ℝ) =ᵐ[domainMeasure n Omega]
        (physicalForcing : ℝ^n → ℝ)
  /-- The flattened forcing is supported in the compact chart-target core. -/
  flattenedForcing_support :
      (let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
        (n := n) (Ω := Omega) i
       (Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget
          (n := n) (Ω := Omega) i).indicator
            (flattenedForcing (n := n) E (physicalForcing : ℝ^n → ℝ)) =ᵐ[
              domainMeasure n E.target]
          flattenedForcing (n := n) E (physicalForcing : ℝ^n → ℝ))
  /-- The localized solution satisfies the flattened equation on the chart target. -/
  weakEquation :
      ∀ phi : TestFunctionOn n
        (SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
          (n := n) (Ω := Omega) i).target,
        let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
          (n := n) (Ω := Omega) i
        (∫ y in E.target,
            principalPairing
              (flattenedPrincipalCoefficientAt (n := n) E a y)
              (fun k ↦ flattenedChartGradient hOmega i u k y)
              (fun k ↦ (∂[k] phi.1.toFun) y)
            ∂(volume : Measure (ℝ^n))) =
          ∫ y in E.target,
            flattenedForcing (n := n) E (physicalForcing : ℝ^n → ℝ) y *
              phi.1.toFun y
            ∂(volume : Measure (ℝ^n))

/-- Transport an already-localized physical weak equation to one boundary chart. -/
theorem LocalizedChartEquationData.of_localized_weak_divergence_solution
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (aLp : Fin n → Fin n → DerivLp n ∞ Omega)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s, (aLp r s : ℝ^n → ℝ) =ᵐ[domainMeasure n
      Omega] fun x ↦ a x r s)
    (u : H¹(Omega))
    (w : H¹₀(Omega))
    (g : DerivLp n 2 Omega)
    (hw :
      (w : H¹(Omega)) =
        cutoffCLM (n := n) (p := 2) (Ω := Omega) (hOmega.boundaryCutoff i) u)
    (hgSupport :
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport
        (n := n) (Ω := Omega) i).indicator (g : ℝ^n → ℝ) =ᵐ[domainMeasure n
          Omega] (g : ℝ^n → ℝ))
    (hgw : IsWeakDivergenceSolution
      (n := n) (Ω := Omega) aLp g w) :
    LocalizedChartEquationData hOmega i a u g := by
  classical
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Omega) i
  let K := Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport (n := n) (Ω := Omega) i
  let KT :=
    Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget (n := n) (Ω := Omega) i
  have hsourceSub : E.source ⊆ Omega := fun x hx ↦ by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx.2
  have hle := ae_mono (domainMeasure_le hsourceSub)
  have hqmp : QuasiMeasurePreserving (fun y ↦ E.symm y)
      (domainMeasure n E.target) (domainMeasure n E.source) :=
    SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph (E := E.symm)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hOmega.chart_symm_contDiff i)
      (by simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hOmega.chart_contDiff i)
  have hforcingSupport : KT.indicator (flattenedForcing (n := n) E (g : ℝ^n → ℝ))
      =ᵐ[domainMeasure n E.target] flattenedForcing (n := n) E (g : ℝ^n → ℝ) := by
    filter_upwards [hqmp.ae_eq_comp (hgSupport.filter_mono hle),
      ae_restrict_mem E.open_target.measurableSet] with y hy hyTarget
    by_cases hyKT : y ∈ KT
    · exact Set.indicator_of_mem hyKT _
    rw [Set.indicator_of_notMem hyKT]
    have hxNotK : E.symm y ∉ K := fun hxK ↦ hyKT ⟨E.symm y, hxK, by
      simpa [E, KT, K, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using E.right_inv hyTarget⟩
    have hgZero : (g : ℝ^n → ℝ) (E.symm y) = 0 :=
      ((Set.indicator_of_notMem hxNotK _).symm.trans hy).symm
    simp [flattenedForcing, hgZero]
  refine
    { physicalForcing_support := hgSupport
      flattenedForcing_support := hforcingSupport
      weakEquation := fun phi ↦ ?_ }
  have hwDeriv (r : Fin n) :
      (derivCoordCLM (n := n) (Ω := Omega) r w : ℝ^n → ℝ) =
        localizedChartGradient hOmega i u r := by
    change (((((w : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
      (singleDerivIndex n r) : DerivLp n 2 Omega) : ℝ^n → ℝ)) = _
    rw [hw]
    rfl
  have hsource := weakSolution_chartPullback_source_identity hOmega i aLp g w
    ((isWeakSolution_iff_isWeakDivergenceSolution hOmega.isOpen aLp g w).2 hgw) phi
  simp only [hwDeriv] at hsource
  have haSource : ∀ᵐ x ∂domainMeasure n E.source, ∀ r s : Fin n,
      (aLp r s : ℝ^n → ℝ) x = a x r s :=
    ae_all_iff.2 fun r ↦ ae_all_iff.2 fun s ↦ (haRep r s).filter_mono hle
  refine flattenCLM_weakEquation_on_chartTarget hOmega i u a g phi.1.toFun
    (fun k ↦ ∂[k] phi.1.toFun) ((integral_congr_ae ?_).trans hsource)
  filter_upwards [haSource] with x hx
  simp only [principalPairing, hx]


/-- The complete weak-equation handoff for one boundary chart.

Starting from the physical divergence-form equation with `W^{1,∞}`
coefficients, this theorem localizes by the boundary partition function,
constructs the resulting `L²` commutator forcing, and transports the weak
equation to the chart target.  The flattened solution is the bounded
Sobolev chart transform `flattenCLM`; no classical derivative of `u` is used.
-/
theorem exists_flattenedLocalized_l2_equation_on_chart_target
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ((((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n
          Omega] fun x ↦ a x r s)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u) :
    ∃ physicalForcing : DerivLp n 2 Omega,
      LocalizedChartEquationData hOmega i a
        (u : H¹(Omega)) physicalForcing := by
  classical
  obtain ⟨w, hwBase, g, -, hgSupport, hgw⟩ :=
    exists_localized_weakDivergenceSolution hOmega.isOpen A u f hu (hOmega.boundaryCutoff i)
  refine ⟨g, .of_localized_weak_divergence_solution hOmega i _ a haRep u w g ?_
    (by simpa [Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport] using hgSupport) hgw⟩
  exact WkpSpaceOn.ext_of_base_ae hOmega.isOpen _ _
    (hwBase.trans (cutoffCLM_base_apply_ae (hOmega.boundaryCutoff i) (u : H¹(Omega))).symm)


end BoundaryChart

end SobolevSpace.GraphSpace.BoundaryRegularity
