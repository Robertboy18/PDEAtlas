/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartTargetWeakEquation
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.Coordinates
import PDE.Spaces.Sobolev.Extension.C1.LocalPieces.BoundaryFlattening
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.EssentialBound

/-!
# Promotion of chart-target weak equations to the upper half-space

After a Dirichlet solution `u ∈ H¹₀(Ω)` has been localized by a boundary
cutoff and flattened through a boundary chart, the resulting weak equation
holds on the chart target, a bounded open subset of the upper half-space
`Ω⁺`. The difference-quotient argument, however, runs on all of `Ω⁺`. We
promote the equation: the transformed commutator forcing is extended by
zero from the chart target, and the flattened principal coefficient is joined
outside the compact chart core to the constant matrix `β I` by a smooth
cutoff. Because the localized solution, its weak gradient, and the forcing
are all supported in the chart core, neither extension changes the
variational identity, and the result is a weak equation on `Ω⁺` against every
test function in `C_c^∞(Ω⁺)`.

## Main results

* `LocalizedChartEquationData.zeroExtension_memLp`: the zero-extended
  transformed forcing of any `L²(Ω)` forcing is in `L²(Ω⁺)`.
* `LocalizedChartEquationData.weakEquation_on_upper`: the chart-target
  equation holds on `Ω⁺` with the extended coefficient.
* `exists_flattenedLocalized_l2_equation_on_upper`: existence of an `L²(Ω⁺)`
  forcing for which the flattened localized field satisfies the weak
  divergence-form equation on the whole half-space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 6-8 of the proof of Theorem 4 (straightening
  the boundary and the transformed equation), (57)-(68), pp. 337-339.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set Function ENNReal
open scoped BigOperators Topology

variable {n : ℕ}

section BoundaryChart

variable [Fact (0 < n)]

/-- The transformed forcing of an `L²(Ω)` forcing, extended by zero from the chart target,
belongs to `L²` on the upper half-space: the inverse chart is a `C¹` change of variables onto
part of the bounded domain, and the Jacobian weight is bounded on the bounded chart target. -/
theorem LocalizedChartEquationData.zeroExtension_memLp
    {Omega : Set (ℝ^n)}
    {hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega}
    {i : Fin hOmega.N}
    {g : DerivLp n 2 Omega} :
    let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ
      (n := n) (Ω := Omega) i
    MemLp (E.target.indicator
        (flattenedForcing (n := n) E (g : ℝ^n → ℝ))) 2
      (domainMeasure n (SobolevSpace.HalfSpace.upper n)) := by
  classical
  intro E
  have hsourceSub : E.source ⊆ Omega := fun x hx ↦ by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx.2
  have htargetSub : E.target ⊆ (hOmega.chart i).target := by
    rw [show E.target = (hOmega.chart i).target ∩ SobolevSpace.HalfSpace.upper n by
      simpa [E] using Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper
        (n := n) (Ω := Omega) i]
    exact inter_subset_left
  have hEC1 : ContDiff ℝ 1 (fun x ↦ E x) := by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hOmega.chart_contDiff i
  have hSymmC1 : ContDiff ℝ 1 (fun y ↦ E.symm y) := by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hOmega.chart_symm_contDiff i
  -- `g ∘ E.symm` is square integrable on the bounded chart target, by the change of variables
  -- of the bounded chart `E.symm` (its target `E.source` lies in the bounded domain).
  have hcomp : MemLp (fun y ↦ (g : ℝ^n → ℝ) (E.symm y)) 2 (domainMeasure n E.target) := by
    have h := SobolevSpace.WeakChangeOfVariables.memLp_comp_partialHomeomorph_on_bounded_chart
      (E := E.symm) (p := 2) hSymmC1 (by simpa using hEC1)
      (by simpa using hOmega.bounded.subset hsourceSub)
      (f := (g : ℝ^n → ℝ)) (by simpa using (Lp.memLp g).mono_measure (domainMeasure_le hsourceSub))
    simpa using h
  -- The Jacobian weight is continuous and the chart target is bounded.
  have hJcont : Continuous (inverseChartJacobianWeight (n := n) E) :=
    (ContinuousLinearMap.continuous_det.comp (by
      simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
        (hOmega.chart_symm_contDiff i).continuous_fderiv (by norm_num))).abs
  have hJ : MemLp (inverseChartJacobianWeight (n := n) E) ∞ (domainMeasure n E.target) :=
    (SobolevSpace.WeakChangeOfVariables.memLp_on_compact_of_continuous (p := (∞ : ENNReal))
      ((hOmega.chart_target_bounded i).subset htargetSub).isCompact_closure hJcont).mono_measure
      (domainMeasure_le subset_closure)
  have hforcing : MemLp (flattenedForcing (n := n) E (g : ℝ^n → ℝ)) 2
      (domainMeasure n E.target) :=
    hJ.fun_mul (r := (2 : ENNReal)) hcomp
  rw [memLp_indicator_iff_restrict E.open_target.measurableSet.nullMeasurableSet]
  simpa [show (domainMeasure n (SobolevSpace.HalfSpace.upper n)).restrict E.target =
      domainMeasure n E.target by
    simpa [domainMeasure, E] using Measure.restrict_restrict_of_subset (μ := volume)
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Omega) i)]
    using hforcing

/-- Promote a chart-target weak equation to the whole upper half-space. -/
theorem LocalizedChartEquationData.weakEquation_on_upper
    {Omega : Set (ℝ^n)}
    {hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega}
    {i : Fin hOmega.N}
    {a : ℝ^n → Fin n → Fin n → ℝ}
    {u : H¹(Omega)}
    {g : DerivLp n 2 Omega}
    (data : LocalizedChartEquationData hOmega i a u g)
    (beta : ℝ)
    (phi : TestFunctionOn n (SobolevSpace.HalfSpace.upper n)) :
    let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ
      (n := n) (Ω := Omega) i
    (∫ y,
        principalPairing
          (extendedFlattenedPrincipalCoefficientAt (n := n)
            hOmega i beta a y)
          (fun k ↦ flattenedChartGradient hOmega i u k y)
          (fun k ↦ (∂[k] phi.1.toFun) y)
      ∂domainMeasure n (SobolevSpace.HalfSpace.upper n)) =
      ∫ y, E.target.indicator (flattenedForcing (n := n) E (g : ℝ^n → ℝ)) y *
        phi.1.toFun y
        ∂domainMeasure n (SobolevSpace.HalfSpace.upper n) := by
  classical
  intro E
  let KT := Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget (n := n) (Ω := Omega) i
  let localized := localizeUpperTestToChartTarget hOmega i phi
  have hsub := Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Omega) i
  have hgrad : ∀ᵐ y ∂domainMeasure n (SobolevSpace.HalfSpace.upper n), ∀ k : Fin n,
      KT.indicator (flattenedChartGradient hOmega i u k) y =
        flattenedChartGradient hOmega i u k y :=
    ae_all_iff.2 fun k ↦
      Extension.C1.BoundaryPiece.flattenCLM_deriv_boundarySupportInTarget_indicator_ae
        (p := (2 : ENNReal)) i u k
  have hlhs : (fun y ↦
      principalPairing (extendedFlattenedPrincipalCoefficientAt hOmega i beta a y)
        (fun k ↦ flattenedChartGradient hOmega i u k y) (fun k ↦ (∂[k] phi.1.toFun) y))
        =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)] E.target.indicator fun y ↦
          principalPairing (flattenedPrincipalCoefficientAt (n := n) E a y)
            (fun k ↦ flattenedChartGradient hOmega i u k y)
            (fun k ↦ (∂[k] localized.1.toFun) y) := by
    filter_upwards [hgrad,
      ae_restrict_mem (SobolevSpace.HalfSpace.isOpen_upper (n := n)).measurableSet]
      with y hy hyUpper
    by_cases hyKT : y ∈ KT
    · have hyE : y ∈ E.target := by
        rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
        exact ⟨Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget_subset_target
          (n := n) (Ω := Omega) i hyKT, hyUpper⟩
      rw [Set.indicator_of_mem hyE,
        extendedFlattenedPrincipalCoefficientAt_eq_on_KTarget (n := n) hOmega i beta a hyKT]
      exact congrArg _ (funext fun k ↦
        (partialDeriv_localizeUpperTestToChartTarget_eq_on_KTarget hOmega i phi k y hyKT).symm)
    · have hzero (k : Fin n) : flattenedChartGradient hOmega i u k y = 0 := by
        simpa [Set.indicator_of_notMem hyKT] using (hy k).symm
      simp [Set.indicator_apply, principalPairing, hzero]
  have hforce : (∫ y in E.target, flattenedForcing (n := n) E g y * localized.1.toFun y) =
      ∫ y in E.target, flattenedForcing (n := n) E g y * phi.1.toFun y := by
    refine integral_congr_ae ?_
    filter_upwards [data.flattenedForcing_support] with y hy
    by_cases hyKT : y ∈ KT
    · rw [localizeUpperTestToChartTarget_eq_on_KTarget hOmega i phi y hyKT]
    · rw [Set.indicator_of_notMem hyKT] at hy
      rw [← hy, zero_mul, zero_mul]
  rw [integral_congr_ae hlhs,
    integral_domainMeasure_indicator_eq_setIntegral E.open_target.measurableSet hsub]
  refine (data.weakEquation localized).trans (hforce.trans ?_)
  rw [← integral_domainMeasure_indicator_eq_setIntegral E.open_target.measurableSet hsub]
  simp_rw [Set.indicator_mul_left]

/-- The chart-local identity promoted to the whole upper half-space.

The coefficient is extended by the uniformly elliptic background matrix
outside the chart core, while the forcing is extended by zero outside the
chart target.  Since the localized solution, its weak gradient, and the
commutator forcing are all supported in `KTarget`, these extensions do not
alter the variational equation. -/
theorem exists_flattenedLocalized_l2_equation_on_upper
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
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (beta : ℝ) :
    ∃ upperForcing : DerivLp n 2 (SobolevSpace.HalfSpace.upper n),
      ∀ phi : TestFunctionOn n (SobolevSpace.HalfSpace.upper n),
        (∫ y,
            principalPairing
              (extendedFlattenedPrincipalCoefficientAt (n := n)
                hOmega i beta a y)
              (fun k ↦ flattenedChartGradient hOmega i
                (u : H¹(Omega)) k y)
              (fun k ↦ (∂[k] phi.1.toFun) y)
          ∂domainMeasure n (SobolevSpace.HalfSpace.upper n)) =
          ∫ y, (upperForcing : ℝ^n → ℝ) y * phi.1.toFun y
            ∂domainMeasure n (SobolevSpace.HalfSpace.upper n) := by
  classical
  obtain ⟨physicalForcing, chartEquation⟩ :=
    exists_flattenedLocalized_l2_equation_on_chart_target hOmega i A a haRep f u hu
  have hmem := LocalizedChartEquationData.zeroExtension_memLp (hOmega := hOmega) (i := i)
    (g := physicalForcing)
  refine ⟨hmem.toLp _, fun phi ↦
    (chartEquation.weakEquation_on_upper beta phi).trans (integral_congr_ae ?_)⟩
  filter_upwards [hmem.coeFn_toLp] with y hy
  rw [hy]

end BoundaryChart

end SobolevSpace.GraphSpace.BoundaryRegularity
