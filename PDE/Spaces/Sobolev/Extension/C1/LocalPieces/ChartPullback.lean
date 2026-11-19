/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension
public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability -- shake: keep
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Chart pullback for C¹ extension

The boundary construction in the extension theorem (Evans §5.4, Theorem 1) ends by transporting the
reflected function on the flattened picture back to the original coordinates: `x ↦ v(Φᵢ x)` for the
`C¹` chart `Φᵢ`. We build the coordinate maps of that pullback as bounded operators on `L^p`,
localized to the compact set `targetCutoffSupport i` (the support of the target cutoff `η`) in the
chart target and extended by zero outside the compact set
`pullbackSupport i = Φᵢ⁻¹(targetCutoffSupport i)` in the chart source. Localization to a compact set
is what makes the pullback bounded: on a compact subset of the chart target the Jacobian of `Φᵢ` is
bounded above and below, so the change of variables changes `L^p` norms by at most a constant
factor.

The first derivatives transform by the chain rule,

  `∂ₖ(v ∘ Φᵢ)(x) = ∑ⱼ (∂ⱼ v)(Φᵢ x) · ∂ₖ(Φᵢ)ⱼ(x)`,

and the Jacobian entries `∂ₖ(Φᵢ)ⱼ` are continuous, hence `L^∞` multipliers on
the compact pullback support.

## Main definitions and results

* `localizedChartPullbackLp i : L^p(Φᵢ.target) →L L^p(ℝ^n)`: the localized
  pullback `u ↦ 𝟙_L · (𝟙_K u) ∘ Φᵢ`, with `localizedChartPullbackLp_apply_ae`.
* `chartJacobianCoefficient i k j = ∂ₖ(Φᵢ)ⱼ`.
* `localizedChartDerivativeLp i k`: the bounded map sending the family of
  derivative coordinates `(∂ⱼ v)ⱼ` to the chain-rule sum above, extended by
  zero, with `localizedChartDerivativeLp_apply_ae`.

These coordinate maps are assembled into an operator on the full `W^{1,p}`
bundle in `LocalPieces.ChartOperator`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the return to the original
  variables is in step 5, p. 270.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Pull a chart-target `L^p` field back through the chart after localization
to the compact reflected target support. -/
noncomputable def localizedChartPullbackCompactLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i) :=
  SobolevSpace.WeakChangeOfVariables.localizedPullbackCLM
      (n := n) (p := p) (E := hΩ.chart i)
      (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_targetCutoffSupport
        (n := n) (Ω := Ω) i)
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport_subset_target
        (n := n) (Ω := Ω) i)

/-- Pull a chart-target `L^p` field back through the chart after compact
localization, then extend it by zero to `ℝ^n`. -/
noncomputable def localizedChartPullbackLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n)) :=
  (SobolevSpace.Extension.Lp.zeroExtendLp
      (n := n) (p := p)
      (Ω := Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_pullbackSupport
        (n := n) (Ω := Ω) i).measurableSet).comp
    (localizedChartPullbackCompactLp (n := n) (p := p) (Ω := Ω) i)

/-- The compact localized chart pullback is represented by the pulled-back localized field. -/
private theorem localizedChartPullbackCompactLp_apply_ae (i : Fin hΩ.N)
    (u : SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) :
    ((localizedChartPullbackCompactLp (n := n) (p := p) (Ω := Ω) i u :
        SobolevSpace.GraphSpace.DerivLp n p
          (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)]
        fun x ↦ (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport
          (n := n) (Ω := Ω) i).indicator (fun y ↦ u y) (hΩ.chart i x) :=
  SobolevSpace.WeakChangeOfVariables.localizedPullbackLp_apply_ae (n := n) (p := p)
    (E := hΩ.chart i) (hΩ.chart_contDiff i) (hΩ.chart_symm_contDiff i)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_targetCutoffSupport (n := n) (Ω := Ω) i)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport_subset_target
      (n := n) (Ω := Ω) i) u

omit [Fact (0 < n)] in
/-- The zero extension of a field represented by `g` on `L` is represented by `𝟙_L g`. -/
private theorem zeroExtendLp_ae_eq_indicator {L : Set (ℝ^n)} (hL : MeasurableSet L)
    (v : SobolevSpace.GraphSpace.DerivLp n p L) {g : ℝ^n → ℝ}
    (hv : (v : ℝ^n → ℝ) =ᵐ[domainMeasure n L] g) :
    ((SobolevSpace.Extension.Lp.zeroExtendLp (n := n) (p := p) (Ω := L) hL v :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))] L.indicator g := by
  have hImp : ∀ᵐ x ∂ domainMeasure n (Set.univ : Set (ℝ^n)), x ∈ L →
      (v : ℝ^n → ℝ) x = g x := by
    refine (ae_restrict_iff' hL).1 ?_
    rw [show (domainMeasure n (Set.univ : Set (ℝ^n))).restrict L = domainMeasure n L by
      simp [domainMeasure]]
    exact hv
  filter_upwards [SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae (n := n) (p := p) hL v, hImp]
    with x hx hxv
  rw [hx]
  by_cases hxL : x ∈ L <;> simp [SobolevSpace.Extension.Lp.extensionByZero, hxL, hxv]

/-- Almost-everywhere formula for the global localized chart pullback. -/
theorem localizedChartPullbackLp_apply_ae (i : Fin hΩ.N)
    (u : SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) :
    ((localizedChartPullbackLp (n := n) (p := p) (Ω := Ω) i u :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i).indicator
          (fun x ↦
            (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport
              (n := n) (Ω := Ω) i).indicator (fun y ↦ u y) (hΩ.chart i x)) := by
  rw [localizedChartPullbackLp, ContinuousLinearMap.comp_apply]
  exact zeroExtendLp_ae_eq_indicator _ _ (localizedChartPullbackCompactLp_apply_ae i u)

/-- The `(k,j)` chain-rule coefficient `∂ₖ Φᵢʲ` for pullback by the `i`-th
chart. -/
def chartJacobianCoefficient (i : Fin hΩ.N) (k j : Fin n) : ℝ^n → ℝ :=
  fun x ↦ ((fderiv ℝ (fun z ↦ hΩ.chart i z) x)
    (EuclideanSpace.single k (1 : ℝ))) j

/-- Each chart Jacobian coefficient is continuous, since the chart is `C¹`. -/
theorem continuous_chartJacobianCoefficient
    (i : Fin hΩ.N) (k j : Fin n) :
    Continuous (chartJacobianCoefficient (n := n) (Ω := Ω) i k j) := by
  have hcoord : Continuous fun v : ℝ^n ↦ v j := by
    simpa [EuclideanSpace.proj] using (EuclideanSpace.proj j).continuous
  exact hcoord.comp
    (((hΩ.chart_contDiff i).continuous_fderiv (hn := by simp)).clm_apply continuous_const)

/-- A chart Jacobian coefficient as an `L^∞` function on the compact pulled
back support. -/
noncomputable def chartJacobianCoefficientLpTop
    (i : Fin hΩ.N) (k j : Fin n) :
    SobolevSpace.GraphSpace.DerivLp n ∞
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i) :=
  let hmem := SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous
    (n := n)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_pullbackSupport
      (n := n) (Ω := Ω) i).isBounded
    (continuous_chartJacobianCoefficient (n := n) (Ω := Ω) i k j)
  hmem.toLp (chartJacobianCoefficient (n := n) (Ω := Ω) i k j)

/-- The `L^∞` Jacobian coefficient represents the analytic chart derivative
almost everywhere. -/
private theorem chartJacobianCoefficientLpTop_apply_ae
    (i : Fin hΩ.N) (k j : Fin n) :
    ((chartJacobianCoefficientLpTop (n := n) (Ω := Ω) i k j :
        SobolevSpace.GraphSpace.DerivLp n ∞
          (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)]
        chartJacobianCoefficient (n := n) (Ω := Ω) i k j := by
  let hmem := SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous
    (n := n)
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_pullbackSupport
      (n := n) (Ω := Ω) i).isBounded
    (continuous_chartJacobianCoefficient (n := n) (Ω := Ω) i k j)
  simpa [chartJacobianCoefficientLpTop, hmem] using hmem.coeFn_toLp

/-- One Jacobian-weighted derivative term, pulled back from the chart target
and extended globally. -/
noncomputable def localizedChartDerivativeTermLp
    (i : Fin hΩ.N) (k j : Fin n) :
    SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n)) :=
  (SobolevSpace.Extension.Lp.zeroExtendLp
      (n := n) (p := p)
      (Ω := Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_pullbackSupport
        (n := n) (Ω := Ω) i).measurableSet).comp
    ((SobolevSpace.GraphSpace.mulLpLeft
        (n := n) (p := p)
        (Ω := Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i)
        (chartJacobianCoefficientLpTop (n := n) (Ω := Ω) i k j)).comp
      (localizedChartPullbackCompactLp (n := n) (p := p) (Ω := Ω) i))

/-- Almost-everywhere formula for one global Jacobian-weighted chart derivative
term. -/
private theorem localizedChartDerivativeTermLp_apply_ae
    (i : Fin hΩ.N) (k j : Fin n)
    (u : SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) :
    ((localizedChartDerivativeTermLp (n := n) (p := p) (Ω := Ω) i k j u :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i).indicator
          (fun x ↦
            chartJacobianCoefficient (n := n) (Ω := Ω) i k j x *
              (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport
                (n := n) (Ω := Ω) i).indicator (fun y ↦ u y) (hΩ.chart i x)) := by
  rw [localizedChartDerivativeTermLp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  refine zeroExtendLp_ae_eq_indicator _ _ ?_
  filter_upwards [SobolevSpace.GraphSpace.mulLpLeft_apply_ae (n := n) (p := p)
      (chartJacobianCoefficientLpTop (n := n) (Ω := Ω) i k j)
      (localizedChartPullbackCompactLp (n := n) (p := p) (Ω := Ω) i u),
    chartJacobianCoefficientLpTop_apply_ae (n := n) (Ω := Ω) i k j,
    localizedChartPullbackCompactLp_apply_ae i u] with x hmul hcoeff hpull
  simpa [hcoeff, hpull] using hmul

/-- The full `k`-th derivative coordinate of a localized chart pullback,
implementing `∑ j, (∂ⱼu ∘ Φᵢ) ∂ₖΦᵢʲ`. -/
noncomputable def localizedChartDerivativeLp
    (i : Fin hΩ.N) (k : Fin n) :
    (Fin n → SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n)) := by
  classical
  exact ∑ j : Fin n,
    (localizedChartDerivativeTermLp (n := n) (p := p) (Ω := Ω) i k j).comp
      (ContinuousLinearMap.proj j)

private theorem localizedChartDerivativeLp_apply
    (i : Fin hΩ.N) (k : Fin n)
    (du : Fin n → SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) :
    localizedChartDerivativeLp (n := n) (p := p) (Ω := Ω) i k du =
      ∑ j : Fin n,
        localizedChartDerivativeTermLp (n := n) (p := p) (Ω := Ω) i k j (du j) := by
  classical
  simp [localizedChartDerivativeLp]

/-- Almost-everywhere formula for the complete global chart derivative
coordinate. -/
theorem localizedChartDerivativeLp_apply_ae
    (i : Fin hΩ.N) (k : Fin n)
    (du : Fin n → SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).target) :
    ((localizedChartDerivativeLp (n := n) (p := p) (Ω := Ω) i k du :
        SobolevSpace.GraphSpace.DerivLp n p (Set.univ : Set (ℝ^n))) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (Set.univ : Set (ℝ^n))]
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i).indicator
          (fun x ↦ ∑ j : Fin n,
            chartJacobianCoefficient (n := n) (Ω := Ω) i k j x *
              (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport
                (n := n) (Ω := Ω) i).indicator (fun y ↦ du j y) (hΩ.chart i x)) := by
  classical
  rw [localizedChartDerivativeLp_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun j ↦
      localizedChartDerivativeTermLp (n := n) (p := p) (Ω := Ω) i k j (du j),
    ae_all_iff.2 fun j ↦ localizedChartDerivativeTermLp_apply_ae i k j (du j)]
    with x hxsum hxterms
  rw [hxsum, Finset.sum_congr rfl fun j _ ↦ hxterms j]
  by_cases hxL :
    x ∈ Boundary.C1ExtensionAtlas.DerivedCutoffs.pullbackSupport (n := n) (Ω := Ω) i <;> simp [hxL]

end BoundaryPiece

end C1

end Extension

end SobolevSpace
