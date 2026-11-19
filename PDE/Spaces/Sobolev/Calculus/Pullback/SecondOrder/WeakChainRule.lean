/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.SecondOrder.Rows
public import PDE.Spaces.Sobolev.Calculus.Pullback.SecondOrder.Classical
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.PullbackBounds
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge

/-!
# Weak second-order chain rule

The chain rule for second weak derivatives under a `C²` change of variables. Let `E` be a `C²`
chart with `C¹` inverse and `U ∈ W^{2,2}(E.target)` with base representative `u`. On any open
set `E.symm '' V`, where `V ⊆ K` is open and `K ⊆ E.target` is compact, the composition
`u ∘ E` has the weak derivatives

`∂ᵢ(u ∘ E) = Σ_j (∂ⱼu ∘ E) ∂ᵢEⱼ`,

`∂ᵢ∂ₖ(u ∘ E) = Σ_{j,l} (∂ₗ∂ⱼu ∘ E) ∂ᵢEₗ ∂ₖEⱼ + Σ_j (∂ⱼu ∘ E) ∂ᵢ∂ₖEⱼ`,

where the right-hand sides are the bounded `L²` rows of `Pullback.SecondOrder.Rows`. This is
the computation behind flattening the boundary in `H²` boundary regularity (Evans §6.3.2,
proof of Theorem 4, steps 7-10).

The proof follows the usual pattern. Smooth approximants of `U` converging in `W^{2,2}` on `K` are
obtained by mollification (`interiorApproximation_Wkp`, Evans §5.3.1, Theorem 1); the classical
second-order chain rule of `Pullback.SecondOrder.Classical` gives the identity for each approximant;
the rows are continuous in `U`, so the transformed derivatives converge in `L²(E.symm '' K)`; and
closedness of weak derivatives (`hasWeakDerivativeOn_of_tendsto_eLpNorm`) passes the identity to the
limit.

## Main results

* `firstSobolevPullbackRow_apply_ae`, `secondSobolevPullbackRow_apply_ae`: the abstract `L²`
  rows have the classical chain-rule formulas as almost-everywhere representatives.
* `hasWeakDerivativeOn_secondSobolevPullbackRow_of_tendsto`: closedness of the second-order
  formula under `L²` convergence of smooth approximants.
* `hasWeakDerivativeOn_firstSobolevPullbackRow_compactCarrier`,
  `hasWeakDerivativeOn_secondSobolevPullbackRow_compactCarrier`: the weak-derivative relations
  on the compact carrier `E.symm '' K`, which justify the construction `localizedH2Pullback`.
* `hasWeakDerivativeOn_firstSobolevPullbackRow`,
  `hasWeakDerivativeOn_secondSobolevPullbackRow`: the chain rules on the open set
  `E.symm '' V`.

## Implementation notes

The compact-carrier statements are weak-derivative identities on a measurable set that may
have empty interior; they justify the `W^{2,2}` element but are not by themselves the
analytic chain rule. The open-patch theorems restrict them to `E.symm '' V`, which is open
because `E` is a partial homeomorphism.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.1, Theorem 1, pp. 264-265, for local approximation by
  mollification; and §6.3.2, Theorem 4, pp. 334-340, whose proof straightens the boundary in steps
  7-9, pp. 338-339, and returns to the original coordinates in step 10, p. 340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set Function ENNReal
open scoped Sobolev
open SobolevSpace.GraphSpace
open SecondOrderPullback

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Base coordinate of the compactly localized Sobolev pullback. -/
noncomputable def localizedSobolevPullbackBase
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) :
    DerivLp n 2 (compactPullbackSource (n := n) E K) :=
  localizedPullbackCLM (n := n) (p := (2 : ENNReal))
    hE hEsymm hK hKsub
    ((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2))

/-- Every localized target `L²` row is represented on the compact source
patch by ordinary composition with the chart.  This row-level statement is
the common semantic bridge used for both first and second weak derivatives. -/
theorem localizedPullbackCLM_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (v : DerivLp n 2 E.target) :
    ((localizedPullbackCLM (n := n) (p := (2 : ENNReal))
        hE hEsymm hK hKsub v :
        DerivLp n 2 (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        fun x ↦ (v : ℝ^n → ℝ) (E x) := by
  refine (localizedPullbackLp_apply_ae (n := n) (p := (2 : ENNReal)) hE hEsymm hK hKsub v).trans
    (ae_restrict_of_forall_mem
      (isCompact_compactPullbackSource (n := n) hEsymm.continuous hK).measurableSet ?_)
  rintro _ ⟨y, hyK, rfl⟩
  simp [localizedPullbackFun, hyK, E.right_inv (hKsub hyK)]

/-- On the compact source patch, the localized base coordinate agrees almost
everywhere with ordinary composition by the chart. -/
theorem localizedSobolevPullbackBase_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) :
    ((localizedSobolevPullbackBase (n := n) hE hEsymm hK hKsub U :
        DerivLp n 2 (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
      fun x ↦ ((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2) : ℝ^n → ℝ) (E x) :=
  localizedPullbackCLM_apply_ae hE hEsymm hK hKsub _

/-- Almost-everywhere representative of a Hessian chart coefficient. -/
theorem hessianChartCoefficient_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i k j l : Fin n) :
    ((hessianChartCoefficient (n := n) hE hEsymm hK i k j l :
        DerivLp n ∞ (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        fun x ↦
          (∂[i] (fun y ↦ E y l)) x *
            (∂[k] (fun y ↦ E y j)) x := by
  simpa [hessianChartCoefficient] using compactCoefficientLp_apply_ae (n := n)
    (isCompact_compactPullbackSource (n := n) hEsymm.continuous hK)
    (fun x ↦ (∂[i] (fun y ↦ E y l)) x * (∂[k] (fun y ↦ E y j)) x)
    ((continuous_chart_first (n := n) hE i l).mul (continuous_chart_first (n := n) hE k j))

/-- Almost-everywhere representative of a second-chart-derivative coefficient. -/
theorem gradientChartCoefficient_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i k j : Fin n) :
    ((gradientChartCoefficient (n := n) hE hEsymm hK i k j :
        DerivLp n ∞ (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        fun x ↦ (∂[i]
          (fun y ↦ (∂[k] (fun z ↦ E z j)) y)) x := by
  simpa [gradientChartCoefficient] using compactCoefficientLp_apply_ae (n := n)
    (isCompact_compactPullbackSource (n := n) hEsymm.continuous hK) _
    (continuous_chart_second (n := n) hE i k j)

/-- Almost-everywhere representative of a first-chart-derivative coefficient. -/
theorem firstChartCoefficient_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i j : Fin n) :
    ((firstChartCoefficient (n := n) hE hEsymm hK i j :
        DerivLp n ∞ (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        fun x ↦ (∂[i] (fun y ↦ E y j)) x := by
  simpa [firstChartCoefficient] using compactCoefficientLp_apply_ae (n := n)
    (isCompact_compactPullbackSource (n := n) hEsymm.continuous hK) _
    (continuous_chart_first (n := n) hE i j)

/-- A finite sum of `L²` classes is represented by the sum of the representatives of its
terms. -/
private theorem coeFn_finsetSum_ae {L : Set (ℝ^n)} {ι : Type*} (s : Finset ι)
    (T : ι → DerivLp n 2 L) {g : ι → ℝ^n → ℝ}
    (h : ∀ j, (T j : ℝ^n → ℝ) =ᵐ[domainMeasure n L] g j) :
    ((∑ j ∈ s, T j : DerivLp n 2 L) : ℝ^n → ℝ) =ᵐ[domainMeasure n L]
      fun x ↦ ∑ j ∈ s, g j x := by
  filter_upwards [Lp.coeFn_fun_finsetSum s T, eventuallyEq_sum (s := s) fun j _ ↦ h j]
    with x hx hg
  rw [hx]
  simpa only [Finset.sum_apply] using hg

/-- A chart coefficient times a localized pullback is represented by the pointwise product. -/
private theorem mulLpLeft_localizedPullbackCLM_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    {c : DerivLp n ∞ (compactPullbackSource (n := n) E K)} {a : ℝ^n → ℝ}
    (hc : (c : ℝ^n → ℝ) =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)] a)
    (v : DerivLp n 2 E.target) :
    ((mulLpLeft (n := n) (p := (2 : ENNReal)) c
        (localizedPullbackCLM (n := n) (p := (2 : ENNReal)) hE hEsymm hK hKsub v) :
        DerivLp n 2 (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        fun x ↦ (v : ℝ^n → ℝ) (E x) * a x := by
  filter_upwards [mulLpLeft_apply_ae (n := n) (p := (2 : ENNReal)) c
      (localizedPullbackCLM (n := n) (p := (2 : ENNReal)) hE hEsymm hK hKsub v), hc,
    localizedPullbackCLM_apply_ae (n := n) hE hEsymm hK hKsub v] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_comm]

/-- The bounded first-order row has the classical coordinate chain-rule
representative almost everywhere. -/
theorem firstSobolevPullbackRow_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i : Fin n) :
    ((firstSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i :
        DerivLp n 2 (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        fun x ↦ ∑ j : Fin n,
          ((U : WkpAmbientOn n 2 2 E.target)
            (firstDerivIndex n 2 (by norm_num) j) : ℝ^n → ℝ) (E x) *
          (∂[i] (fun y ↦ E y j)) x :=
  coeFn_finsetSum_ae Finset.univ _ fun j ↦ mulLpLeft_localizedPullbackCLM_apply_ae
    (hE.of_le (by norm_num)) hEsymm hK hKsub (firstChartCoefficient_apply_ae hE hEsymm hK i j) _

/-- Pointwise formula represented by the bounded second-order Sobolev
pullback row.  The target derivatives are the canonical `L²`
representatives stored in `U`; all chart derivatives are classical. -/
def secondSobolevPullbackRepresentative
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (U : W^{2,2}(E.target)) (i k : Fin n) (x : ℝ^n) : ℝ :=
  (∑ j : Fin n, ∑ l : Fin n,
    ((U : WkpAmbientOn n 2 2 E.target)
      (pairDerivIndex n l j) : ℝ^n → ℝ) (E x) *
      (∂[i] (fun y ↦ E y l)) x *
      (∂[k] (fun y ↦ E y j)) x) +
  ∑ j : Fin n,
    ((U : WkpAmbientOn n 2 2 E.target)
      (firstDerivIndex n 2 (by norm_num) j) : ℝ^n → ℝ) (E x) *
      (∂[i]
        (fun y ↦ (∂[k] (fun z ↦ E z j)) y)) x

/-- The abstract bounded `L²` row has exactly the second-order chain-rule
representative almost everywhere on the compact source patch. -/
theorem secondSobolevPullbackRow_apply_ae
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    ((secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k :
        DerivLp n 2 (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        secondSobolevPullbackRepresentative (n := n) U i k := by
  refine (Lp.coeFn_add _ _).trans ?_
  filter_upwards [coeFn_finsetSum_ae Finset.univ _ fun j ↦ coeFn_finsetSum_ae Finset.univ _
      fun l ↦ mulLpLeft_localizedPullbackCLM_apply_ae (hE.of_le (by norm_num)) hEsymm hK hKsub
        (hessianChartCoefficient_apply_ae hE hEsymm hK i k j l)
        ((U : WkpAmbientOn n 2 2 E.target) (pairDerivIndex n l j)),
    coeFn_finsetSum_ae Finset.univ _ fun j ↦ mulLpLeft_localizedPullbackCLM_apply_ae
      (hE.of_le (by norm_num)) hEsymm hK hKsub
      (gradientChartCoefficient_apply_ae hE hEsymm hK i k j)
      ((U : WkpAmbientOn n 2 2 E.target) (firstDerivIndex n 2 (by norm_num) j))] with x hh hg
  simp only [Pi.add_apply, hh, hg, secondSobolevPullbackRepresentative, mul_assoc]

/-- Transport of local `L²` convergence on `K` through the chart to `E.symm '' K`. -/
private theorem tendsto_eLpNorm_comp_chart
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (h : Filter.Tendsto (fun m ↦ eLpNorm (fun y ↦ f m y - g y) 2 (domainMeasure n K))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m ↦ eLpNorm (fun x ↦ f m (E x) - g (E x)) 2
      (domainMeasure n (compactPullbackSource (n := n) E K))) Filter.atTop (nhds 0) :=
  tendsto_eLpNorm_comp_partialHomeomorph_of_compact (n := n) (p := 2) (by norm_num) hEsymm
    (isCompact_compactPullbackSource (n := n) hEsymm.continuous hK)
    ((image_mono hKsub).trans E.symm_image_target_eq_source.subset)
    (by rwa [show E '' compactPullbackSource (n := n) E K = K from
      E.toPartialEquiv.image_symm_image_of_subset_target hKsub])

/-- Local `L²` convergence on the compact target patch transports to
convergence toward the canonical localized Sobolev pullback on the compact
source patch. -/
theorem tendsto_localizedSobolevPullbackBase_of_tendsto
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (u_m : ℕ → ℝ^n → ℝ)
    (hU : Filter.Tendsto
      (fun m ↦ eLpNorm (fun y ↦ u_m m y -
        ((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2) : ℝ^n → ℝ) y)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ u_m m (E x) -
        (localizedSobolevPullbackBase (n := n)
          hE hEsymm hK hKsub U : ℝ^n → ℝ) x)
        (2 : ENNReal) (domainMeasure n (compactPullbackSource (n := n) E K)))
      Filter.atTop (nhds 0) :=
  (tendsto_eLpNorm_comp_chart hEsymm hK hKsub hU).congr' <| .of_forall fun _ ↦
    eLpNorm_congr_ae <| .sub .rfl (localizedSobolevPullbackBase_apply_ae hE hEsymm hK hKsub U).symm

private theorem tendsto_eLpNorm_mul_continuous_on_compact
    {K : Set (ℝ^n)} (hK : IsCompact K)
    {f_m : ℕ → ℝ^n → ℝ} {a : ℝ^n → ℝ}
    (ha : Continuous a)
    (hf : Filter.Tendsto
      (fun m ↦ eLpNorm (f_m m) (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ f_m m x * a x)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0) := by
  have haLp : MemLp a ∞ (domainMeasure n K) :=
    memLp_on_compact_of_continuous (n := n) (p := ∞) hK ha
  -- The `L∞ × L²` estimate applies even when an individual `f_m m` has infinite norm.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.const_mul hf (Or.inr haLp.eLpNorm_ne_top))
    (fun _ ↦ zero_le) fun m ↦ ?_
  simpa only [mul_comm] using (show eLpNorm (fun x ↦ a x * f_m m x) 2 _ ≤ _ from
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 haLp.aestronglyMeasurable)

private theorem tendsto_eLpNorm_finset_sum
    {ι : Type*} [Fintype ι]
    {K : Set (ℝ^n)}
    {f : ℕ → ι → ℝ^n → ℝ}
    (hf : ∀ i, Filter.Tendsto
      (fun m ↦ eLpNorm (f m i) (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ ∑ i : ι, f m i x)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_finsetSum Finset.univ fun i _ ↦ hf i) (fun _ ↦ zero_le)
    fun m ↦ ?_
  simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := domainMeasure n K) (p := 2)
    (f := f m) (s := Finset.univ) (by norm_num)

private theorem tendsto_eLpNorm_add
    {K : Set (ℝ^n)} {f g : ℕ → ℝ^n → ℝ}
    (hf : Filter.Tendsto
      (fun m ↦ eLpNorm (f m) (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0))
    (hg : Filter.Tendsto
      (fun m ↦ eLpNorm (g m) (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ f m x + g m x)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hf.add hg)
    (fun _ ↦ zero_le) fun _ ↦ eLpNorm_add_le (by norm_num)

/-- Coordinatewise local convergence of the first and second derivatives of
smooth approximants implies convergence of the complete transformed Hessian
row.  The proof is a finite-dimensional `L²` estimate: pull each derivative
error through the chart, multiply by its fixed continuous coefficient, and
sum the resulting errors. -/
theorem tendsto_secondPullbackRow_of_target_derivatives
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n)
    (u_m : ℕ → ℝ^n → ℝ)
    (hfirst : ∀ j : Fin n, Filter.Tendsto
      (fun m ↦ eLpNorm (fun y ↦
        iteratedPartialDeriv (n := n) [j] (u_m m) y -
          ((U : WkpAmbientOn n 2 2 E.target)
            (firstDerivIndex n 2 (by norm_num) j) : ℝ^n → ℝ) y)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0))
    (hsecond : ∀ j l : Fin n, Filter.Tendsto
      (fun m ↦ eLpNorm (fun y ↦
        iteratedPartialDeriv (n := n) [l, j] (u_m m) y -
          ((U : WkpAmbientOn n 2 2 E.target)
            (pairDerivIndex n l j) : ℝ^n → ℝ) y)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ secondPullbackRow (n := n) i k (u_m m) E x -
        (secondSobolevPullbackRow (n := n)
          hE hEsymm hK hKsub U i k : ℝ^n → ℝ) x)
        (2 : ENNReal) (domainMeasure n (compactPullbackSource (n := n) E K)))
      Filter.atTop (nhds 0) := by
  classical
  have hL := isCompact_compactPullbackSource (n := n) hEsymm.continuous hK
  have hH (j l : Fin n) := tendsto_eLpNorm_mul_continuous_on_compact (n := n) hL
    ((continuous_chart_first (n := n) hE i l).mul (continuous_chart_first (n := n) hE k j))
    (tendsto_eLpNorm_comp_chart hEsymm hK hKsub (hsecond j l))
  have hG (j : Fin n) := tendsto_eLpNorm_mul_continuous_on_compact (n := n) hL
    (continuous_chart_second (n := n) hE i k j)
    (tendsto_eLpNorm_comp_chart hEsymm hK hKsub (hfirst j))
  refine (tendsto_eLpNorm_add (tendsto_eLpNorm_finset_sum fun j ↦
    tendsto_eLpNorm_finset_sum (hH j)) (tendsto_eLpNorm_finset_sum hG)).congr' <|
      .of_forall fun m ↦ eLpNorm_congr_ae ?_
  filter_upwards [secondSobolevPullbackRow_apply_ae (n := n) hE hEsymm hK hKsub U i k] with x hx
  rw [hx]
  simp only [secondPullbackRow, secondSobolevPullbackRepresentative, iteratedPartialDeriv,
    Pi.mul_apply, sub_mul, Finset.sum_sub_distrib, mul_assoc]
  ring

/-- Closedness of the classical second-order pullback formula in `L²`.

This theorem has no smoothness assumption on `U`.  The sequence `u_m` is only
the local smooth approximation used to identify the already-defined bounded
Sobolev operator with the distributional second derivative. -/
theorem hasWeakDerivativeOn_secondSobolevPullbackRow_of_tendsto
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n)
    (u_m : ℕ → ℝ^n → ℝ) (hu_m : ∀ m, ContDiff ℝ 2 (u_m m))
    (hbase : Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ u_m m (E x) -
        (localizedSobolevPullbackBase (n := n)
          (hE.of_le (by norm_num)) hEsymm hK hKsub U : ℝ^n → ℝ) x)
        (2 : ENNReal) (domainMeasure n (compactPullbackSource (n := n) E K)))
      Filter.atTop (nhds 0))
    (hsecond : Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ secondPullbackRow (n := n) i k (u_m m) E x -
        (secondSobolevPullbackRow (n := n)
          hE hEsymm hK hKsub U i k : ℝ^n → ℝ) x)
        (2 : ENNReal) (domainMeasure n (compactPullbackSource (n := n) E K)))
      Filter.atTop (nhds 0)) :
    HasWeakDerivativeOn (n := n) (compactPullbackSource (n := n) E K) [i, k]
      (localizedSobolevPullbackBase (n := n)
        (hE.of_le (by norm_num)) hEsymm hK hKsub U)
      (secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k) := by
  have hL := isCompact_compactPullbackSource (n := n) hEsymm.continuous hK
  exact hasWeakDerivativeOn_of_tendsto_eLpNorm (n := n) (p := (2 : ENNReal)) (α := [i, k])
    (fSeq := fun m x ↦ u_m m (E x)) (gSeq := fun m ↦ secondPullbackRow (n := n) i k (u_m m) E)
    (fun m ↦ memLp_on_compact_of_continuous (n := n) (p := (2 : ENNReal)) hL
      ((hu_m m).continuous.comp hE.continuous))
    (fun m ↦ memLp_secondPullbackRow_on_compact (n := n) hL i k (u_m m) E
      ((hu_m m).of_le (by norm_num)) hE) (Lp.memLp _) (Lp.memLp _)
    (fun m ↦ hasWeakDerivativeOn_secondPullbackRow (n := n) i k (u_m m) E
      ((hu_m m).of_le (by norm_num)) hE) hbase hsecond

/-- First-order weak-derivative data on the compact carrier used by
`localizedH2Pullback`.

This gives the closed-graph construction on a measurable compact
set. It is not the open-domain chain rule, because compact carriers may have
empty interior. -/
theorem hasWeakDerivativeOn_firstSobolevPullbackRow_compactCarrier
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i : Fin n) :
    HasWeakDerivativeOn (n := n) (compactPullbackSource (n := n) E K) [i]
      (localizedSobolevPullbackBase (n := n)
        (hE.of_le (by norm_num)) hEsymm hK hKsub U)
      (firstSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i) := by
  let du : Fin n → ℝ^n → ℝ := fun j ↦
    ((U : WkpAmbientOn n 2 2 E.target)
      (firstDerivIndex n 2 (by norm_num) j) : ℝ^n → ℝ)
  have hraw := (hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
    (n := n) (p := (2 : ENNReal)) μ (by norm_num) (hE.of_le (by norm_num)) hEsymm (Lp.memLp _)
    (fun _ ↦ Lp.memLp _) (fun j ↦ by simpa [du] using
      U.property.hasWeakDerivativeOn_first (by norm_num) j) i).mono (n := n)
    (isCompact_compactPullbackSource (n := n) hEsymm.continuous hK).measurableSet
    ((image_mono hKsub).trans E.symm_image_target_eq_source.subset)
  simp only [fderiv_chart_single_apply (n := n) (hE.of_le (by norm_num))] at hraw
  exact (hasWeakDerivativeOn_congr_ae (n := n) (α := [i])
    (localizedSobolevPullbackBase_apply_ae (n := n) (hE.of_le (by norm_num)) hEsymm hK hKsub U).symm
    (firstSobolevPullbackRow_apply_ae (n := n) hE hEsymm hK hKsub U i).symm).1 hraw

/-- Second-order weak chain-rule data on a compact carrier.

For arbitrary `U ∈ H²(E.target)`, the compactly localized pullback has the
expected `(i,k)` weak Hessian row.  No smoothness of `U` is assumed.  The
proof constructs a mollified approximating sequence, identifies every weak
derivative limit with the canonical row stored in `U`, transports the
coordinatewise convergence through the chart, and closes the weak derivative
identity in `L²`.

This intermediate statement is used to build the closed-graph object on the
compact carrier. The open-patch theorem below is the analytic chain rule: it
restricts this identity to an open set compactly contained in the chart. -/
theorem hasWeakDerivativeOn_secondSobolevPullbackRow_compactCarrier
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    HasWeakDerivativeOn (n := n) (compactPullbackSource (n := n) E K) [i, k]
      (localizedSobolevPullbackBase (n := n)
        (hE.of_le (by norm_num)) hEsymm hK hKsub U)
      (secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k) := by
  classical
  let u : SobolevSpaceOn n 2 2 E.target :=
    toRepresentative (n := n) (k := 2) (p := (2 : ENNReal))
      (Ω := E.target) U
  rcases SobolevSpace.Approximation.interiorApproximation_Wkp
      (n := n) μ (2 : ENNReal) (by norm_num) 2 E.target
      u E.open_target K hK hKsub with
    ⟨u_m, hu_m, hbaseTarget, hderiv⟩
  have hcanonical (α : List (Fin n)) (hα : α.length ≤ 2) :
      Filter.Tendsto
        (fun m ↦ eLpNorm (fun x ↦
          iteratedPartialDeriv (n := n) α (u_m m) x -
            ((U : WkpAmbientOn n 2 2 E.target)
              (derivIndexOfList (n := n) (k := 2) α hα) : ℝ^n → ℝ) x)
          (2 : ENNReal) (domainMeasure n K))
        Filter.atTop (nhds 0) := by
    rcases hderiv α hα with ⟨g, _, hgWeak, hgConv⟩
    let aα : DerivIndex n 2 :=
      derivIndexOfList (n := n) (k := 2) α hα
    have hUWeak : HasWeakDerivativeOn (n := n) E.target α u.toFun
        ((U : WkpAmbientOn n 2 2 E.target) aα) := by
      simpa [aα, u, baseRepresentative] using
        U.property.hasWeakDerivativeOn_list α hα
    have hgAE : g =ᵐ[domainMeasure n E.target]
        ((U : WkpAmbientOn n 2 2 E.target) aα : ℝ^n → ℝ) :=
      hgWeak.unique_ae E.open_target hUWeak
    refine hgConv.congr' (Filter.Eventually.of_forall fun m ↦ ?_)
    apply eLpNorm_congr_ae
    have hμ : domainMeasure n K ≤ domainMeasure n E.target := by
      simpa [domainMeasure] using
        (Measure.restrict_mono_set (volume : Measure (ℝ^n)) hKsub)
    exact Filter.EventuallyEq.rfl.sub
      (hgAE.filter_mono (MeasureTheory.ae_mono hμ))
  have hbaseCanonical : Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ u_m m x -
        ((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2) : ℝ^n → ℝ) x)
        (2 : ENNReal) (domainMeasure n K))
      Filter.atTop (nhds 0) := by
    simpa [u, toRepresentative] using hbaseTarget
  have hbase := tendsto_localizedSobolevPullbackBase_of_tendsto
    (n := n) (hE.of_le (by norm_num)) hEsymm hK hKsub U u_m hbaseCanonical
  exact hasWeakDerivativeOn_secondSobolevPullbackRow_of_tendsto
    (n := n) hE hEsymm hK hKsub U i k u_m
    (fun m ↦ (hu_m m).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hbase
    (tendsto_secondPullbackRow_of_target_derivatives (n := n) hE hEsymm hK hKsub U i k u_m
      (fun j ↦ hcanonical [j] (by simp)) fun j l ↦ hcanonical [l, j] (by simp))

/-- The first-order weak chain rule on an open patch. Let `E` be a chart whose coercion is `C²`
and whose inverse is `C¹`, let `V ⊆ K` with `V` open and `K ⊆ E.target` compact, and let
`U ∈ H²(E.target)`. Then on `E.symm '' V` the localized pullback of `U` has the row
`firstSobolevPullbackRow` as its `i`-th weak derivative. The compact set `K` controls the
localized representatives and estimates. -/
theorem hasWeakDerivativeOn_firstSobolevPullbackRow
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {V K : Set (ℝ^n)} (hV : IsOpen V) (hVK : V ⊆ K)
    (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i : Fin n) :
    HasWeakDerivativeOn (n := n) (E.symm '' V) [i]
      (localizedSobolevPullbackBase (n := n)
        (hE.of_le (by norm_num)) hEsymm hK hKsub U)
      (firstSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i) :=
  (hasWeakDerivativeOn_firstSobolevPullbackRow_compactCarrier (n := n) μ hE hEsymm hK hKsub
    U i).mono (E.isOpen_image_symm_of_subset_target hV (hVK.trans hKsub)).measurableSet
      (image_mono hVK)

/-- The second-order weak chain rule on an open patch, as used when straightening the
boundary (Evans §6.3.2, proof of Theorem 4). Let `E` be a chart whose coercion is `C²` and
whose inverse is `C¹`, let `V ⊆ K` with `V` open and `K ⊆ E.target` compact, and let
`U ∈ H²(E.target)`. Then on `E.symm '' V` the localized pullback of `U` has the classical
Hessian chain-rule row `secondSobolevPullbackRow` as its `(i,k)` weak derivative. The compact
set `K` is used only for localization and `L²` estimates. -/
theorem hasWeakDerivativeOn_secondSobolevPullbackRow
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {V K : Set (ℝ^n)} (hV : IsOpen V) (hVK : V ⊆ K)
    (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    HasWeakDerivativeOn (n := n) (E.symm '' V) [i, k]
      (localizedSobolevPullbackBase (n := n)
        (hE.of_le (by norm_num)) hEsymm hK hKsub U)
      (secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k) :=
  (hasWeakDerivativeOn_secondSobolevPullbackRow_compactCarrier (n := n) μ hE hEsymm hK hKsub
    U i k).mono (E.isOpen_image_symm_of_subset_target hV (hVK.trans hKsub)).measurableSet
      (image_mono hVK)

end SobolevSpace.WeakChangeOfVariables
