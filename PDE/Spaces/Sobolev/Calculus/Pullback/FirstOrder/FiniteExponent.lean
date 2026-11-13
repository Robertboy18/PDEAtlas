/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Algebra.Order.Ring.Star
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.PullbackBounds

/-!
# The finite-exponent Sobolev chain rule

The weak chain rule under a `C¹` change of variables. Let `E` be a `C¹` partial homeomorphism
of `ℝ^n` with `C¹` inverse, and let `u ∈ W^{1,p}(E.target)` with weak partial derivatives
`du j`, where `p < ∞`. Then `u ∘ E` has weak partial derivatives on `E.source` given by

`∂ᵢ(u ∘ E)(x) = Σ_j (∂ⱼu)(E x) · ∂ᵢEⱼ(x)`.

This change of variables is in Chapter 9 of Brezis, *Functional Analysis, Sobolev Spaces and PDE*.
Evans straightens the boundary with the map of Appendix C.1 in the proof of boundary `H²`
regularity, and states there that `u ∘ Ψ ∈ H¹` is straightforward to check (PDE, §6.3.2, Theorem 4,
(58)-(59)). This theorem is the technical input for every boundary-flattening argument in this
library.

The proof mollifies `u`, applies the classical chain rule to the smooth approximants, and
passes to the limit on the compact support of each test function using
`hasWeakDerivativeOn_of_tendsto_eLpNorm` from `Closure`. Mollification converges in `L^p` only
for `p < ∞`, which is what `hp : p ≠ ∞` is for, and `LocalizedPullback` removes it on
finite-measure targets by lowering the exponent. Most of the proof handles two localisations:
from `E.target` to the compact `E '' K` on which the mollified derivatives converge, and back
through `E` to `K = tsupport φ`.

## Main results

* `hasWeakDerivativeOn_comp_partialHomeomorph_W1p`: the chain rule above, for globally
  measurable representatives `u` and `du j`.

## Implementation notes

The `C¹` hypotheses are placed on the coercions `fun x => E x` and `fun x => E.symm x` as
functions on all of `ℝ^n`, not only on `E.source` and `E.target`; the boundary charts in this
library satisfy them.

Measurability of the representatives is assumed so that the indicator extension
`E.target.indicator u` can be mollified on all of `ℝ^n` as a function, not an a.e. class.
`LocalizedPullback` removes this assumption by passing to `AEMeasurable.mk` representatives
and transporting the identity back through `E`, which preserves null sets.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for change of variables in `W^{1,p}`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4, pp. 334-339, whose proof straightens the
  boundary and states in step 7, (58)-(59), p. 338, that `u'(y) = u(Ψ(y))` lies in `H¹(U')`; and
  Appendix C.1, p. 711, for the flattening map `Φ(x) = (x', xₙ - γ(x'))`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section
namespace SobolevSpace

open MeasureTheory Set Function ENNReal Approximation
open scoped Topology

namespace WeakChangeOfVariables

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-!
## Weak chain rule under a `C¹` diffeomorphism (Sobolev `W^{1,p}`)

This is the core technical lemma needed to move between boundary charts and the half-space, as
in the boundary-straightening arguments of Evans, PDE, §6.3.2 and Appendix C.1.

The hypothesis `p < ∞` is what makes mollification converge in `L^p`. The chain rule is proved
by:
1. mollifying `u` (and using commutation with weak derivatives on interior compacts),
2. applying the classical chain rule to the smooth approximants,
3. passing to the limit in the weak-derivative identity on the compact support of the test
   function.
-/

/-- For a compact `K` inside an open set `Ω`, the classical partial derivatives
`∂ⱼ (mollify μ (ε m) (Ω.indicator u))` converge in `L^p(K)` to a weak derivative
`g ∈ L^p(Ω)` of `u` as `ε m → 0`. -/
private theorem tendsto_eLpNorm_partialDeriv_mollify_indicator_sub
    (μ : SobolevSpace.Approximation.Mollifier n) (hp : p ≠ ∞)
    {Ω K : Set (ℝ^n)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u g : ℝ^n → ℝ} {j : Fin n} (hu : MemLp u p (domainMeasure n Ω))
    (hg : MemLp g p (domainMeasure n Ω)) (hweak : HasWeakDerivativeOn (n := n) Ω [j] u g)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m) (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun m ↦ eLpNorm (fun x ↦ (∂[j] (mollify μ (ε m) (Ω.indicator u))) x - g x) p
        (domainMeasure n K))
      Filter.atTop (𝓝 0) := by
  have huΩLoc : LocallyIntegrable (Ω.indicator u) volume :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet.nullMeasurableSet).2 hu).locallyIntegrable
      Fact.out
  obtain ⟨R, hR⟩ := μ.compactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
  obtain ⟨δ, hδpos, hδK⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hεR : Filter.Tendsto (fun m ↦ ε m * R) Filter.atTop (𝓝 0) := by
    simpa using hε0.mul_const R
  -- Once `ε m * R < δ`, the derivative of the mollified `u` is the mollified `g` on `K`.
  refine (mollify_indicator_converges_Lp_on_subset μ hp hΩ.measurableSet hK.measurableSet hKΩ
    hg ε hεpos hε0).congr' ?_
  filter_upwards [hεR.eventually (Iio_mem_nhds hδpos)] with m hm
  refine eLpNorm_congr_ae (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
  have hball : Metric.closedBall x (ε m * R) ⊆ Ω :=
    (Metric.closedBall_subset_cthickening hx _).trans
      ((Metric.cthickening_mono hm.le K).trans hδK)
  have hcomm :=
    iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn
      μ (hεpos m) hR (by simp) huΩLoc hweak x hball
  simp only [iteratedPartialDeriv] at hcomm
  simp only [hcomm]

/-- If `f m j → 0` in `L^p(ν)` for each `j` and every coefficient `a j` lies in `L^∞(ν)`, then
`Σ_j f m j · a j → 0` in `L^p(ν)`. -/
private theorem tendsto_eLpNorm_sum_mul_of_tendsto {ν : Measure (ℝ^n)} {ι : Type*} [Fintype ι]
    {f : ℕ → ι → ℝ^n → ℝ} {a : ι → ℝ^n → ℝ} (ha : ∀ j, MemLp (a j) ∞ ν)
    (hf : ∀ j, Filter.Tendsto (fun m ↦ eLpNorm (f m j) p ν) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m ↦ eLpNorm (fun x ↦ ∑ j, f m j x * a j x) p ν) Filter.atTop
      (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans_le Fact.out
  have hterm (j : ι) :
      Filter.Tendsto (fun m ↦ eLpNorm (fun x ↦ f m j x * a j x) p ν) Filter.atTop (𝓝 0) := by
    have hlim : Filter.Tendsto (fun m ↦ eLpNorm (f m j) p ν * eLpNorm (a j) ∞ ν)
        Filter.atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const (hf j) (Or.inr (ha j).eLpNorm_lt_top.ne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ bot_le) fun m ↦ ?_
    exact eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top_of_pos (μ := ν) (φ := f m j) (f := a j) p hp0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_finsetSum Finset.univ fun j _ ↦ hterm j) (fun _ ↦ bot_le)
    fun m ↦ ?_
  simpa [Finset.sum_fn] using
    eLpNorm_sum_le (μ := ν) (s := Finset.univ) (f := fun j x ↦ f m j x * a j x) Fact.out

/-- An integrand `f · ψ` with `support ψ ⊆ K ⊆ Ω` has the same integral over `Ω` as over `K`. -/
private theorem integral_domainMeasure_mul_eq_of_support_subset {Ω K : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hKΩ : K ⊆ Ω) (f : ℝ^n → ℝ) {ψ : ℝ^n → ℝ}
    (hψ : Function.support ψ ⊆ K) :
    ∫ x, f x * ψ x ∂ domainMeasure n Ω = ∫ x, f x * ψ x ∂ domainMeasure n K :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ hKΩ fun x hx ↦ by
    by_contra h
    exact hx.2 (hψ (Function.support_mul_subset_right f ψ h))

/-- The weak chain rule for `W^{1,p}`, `p < ∞`, under a `C¹` partial homeomorphism `E` with
`C¹` inverse. If `u` has weak partial derivatives `du j` on `E.target`, all in `L^p`, then
`u ∘ E` has weak partial derivatives on `E.source`, namely
`∂ᵢ(u ∘ E)(x) = Σ_j du j (E x) · (DE(x) eᵢ)_j`. The mollifier `μ` only builds the smooth
approximants; the conclusion does not depend on it. Measurability of `u` and the `du j` is
assumed so the argument can work with functions rather than a.e. classes; see
`hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp` for the version without it. -/
theorem hasWeakDerivativeOn_comp_partialHomeomorph_W1p
    (μ : SobolevSpace.Approximation.Mollifier n) (hp : p ≠ ∞)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {u : ℝ^n → ℝ} (hu_meas : Measurable u)
    (huLp : MeasureTheory.MemLp u p (domainMeasure n E.target))
    {du : Fin n → ℝ^n → ℝ}
    (hdu_meas : ∀ j, Measurable (du j))
    (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n E.target))
    (hweak : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u (du j)) :
    ∀ i,
      HasWeakDerivativeOn (n := n) E.source [i] (fun x ↦ u (E x))
        (fun x ↦ ∑ j : Fin n, du j (E x) *
          (∂[i] (fun z ↦ E z)) x j) := by
  classical
  intro i
  let a : Fin n → ℝ^n → ℝ := fun j x ↦ (∂[i] (fun z ↦ E z)) x j
  have ha_cont (j : Fin n) : Continuous (a j) :=
    (EuclideanSpace.proj j).continuous.comp (hE.partialDeriv i).continuous
  -- Both sides of the chain rule lie in `L^p` on every compact subset of `E.source`.
  have hbaseLoc : LocallyIntegrableOn (fun x ↦ u (E x)) E.source volume := by
    refine (locallyIntegrableOn_iff E.open_source.isLocallyClosed).2 fun K hKsub hK ↦ ?_
    have := isFiniteMeasure_domainMeasure_of_isBounded hK.isBounded
    exact (memLp_comp_partialHomeomorph_of_compact hp hE hEsymm hK hKsub hu_meas
      huLp).integrable Fact.out
  have hderivLoc :
      LocallyIntegrableOn (fun x ↦ ∑ j : Fin n, du j (E x) * a j x) E.source volume := by
    refine (locallyIntegrableOn_iff E.open_source.isLocallyClosed).2 fun K hKsub hK ↦ ?_
    have := isFiniteMeasure_domainMeasure_of_isBounded hK.isBounded
    have hterm (j : Fin n) : MemLp (fun x ↦ du j (E x) * a j x) p (domainMeasure n K) := by
      have hduComp := memLp_comp_partialHomeomorph_of_compact hp hE hEsymm hK hKsub
        (hdu_meas j) (hduLp j)
      have haTop : MemLp (a j) ∞ (domainMeasure n K) :=
        memLp_on_compact_of_continuous hK (ha_cont j)
      simpa [Pi.mul_def, mul_comm] using hduComp.fun_mul haTop
    exact (memLp_finsetSum Finset.univ fun j _ ↦ hterm j).integrable Fact.out
  refine ⟨hbaseLoc, hderivLoc, fun φ hφsupp ↦ ?_⟩
  -- Fix a test function; `K = tsupport φ` is a compact subset of `E.source`.
  let K : Set (ℝ^n) := tsupport φ.toFun
  have hKc : IsCompact K := φ.hasCompactSupport
  have hEK : IsCompact (E '' K) := hKc.image_of_continuousOn (E.continuousOn.mono hφsupp)
  have hEK_sub : E '' K ⊆ E.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact E.map_source (hφsupp hx)
  -- Mollify the zero extension of `u` along the scales `ε m = 1 / (m + 1)`.
  let ε : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hεpos : ∀ m, 0 < ε m := fun m ↦ by positivity
  have hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have huΩLoc : LocallyIntegrable (E.target.indicator u) volume :=
    ((memLp_indicator_iff_restrict E.open_target.measurableSet.nullMeasurableSet).2
      huLp).locallyIntegrable Fact.out
  let u_m : ℕ → ℝ^n → ℝ := fun m ↦ mollify μ (ε m) (E.target.indicator u)
  have hu_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (u_m m) := fun m ↦
    mollify_contDiff_of_pos μ (hεpos m) _ huΩLoc
  -- `u_m → u` and `∂ⱼ u_m → du j` in `L^p(E '' K)`, pulled back through `E` to `L^p(K)`.
  have hconv_u :
      Filter.Tendsto (fun m ↦ eLpNorm (fun x ↦ u_m m (E x) - u (E x)) p (domainMeasure n K))
        Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_comp_partialHomeomorph_of_compact hp hEsymm hKc hφsupp
      (mollify_indicator_converges_Lp_on_subset μ hp E.open_target.measurableSet
        hEK.measurableSet hEK_sub huLp ε hεpos hε0)
  have hconv_du (j : Fin n) :
      Filter.Tendsto
        (fun m ↦ eLpNorm (fun x ↦ (∂[j] (u_m m)) (E x) - du j (E x)) p (domainMeasure n K))
        Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_comp_partialHomeomorph_of_compact hp hEsymm hKc hφsupp
      (tendsto_eLpNorm_partialDeriv_mollify_indicator_sub μ hp E.open_target hEK hEK_sub huLp
        (hduLp j) (hweak j) ε hεpos hε0)
  -- The classical chain rule for `u_m ∘ E`, and convergence of its right-hand side.
  let g_m : ℕ → ℝ^n → ℝ := fun m x ↦ ∑ j : Fin n, (∂[j] (u_m m)) (E x) * a j x
  have hweak_m (m : ℕ) :
      HasWeakDerivativeOn (n := n) K [i] (fun x ↦ u_m m (E x)) (g_m m) := by
    simpa only [PDE.fderiv_apply_eq_sum_partialDeriv_mul] using
      hasWeakDerivativeOn_comp_of_contDiff_one (Ω := K) (i := i) ((hu_m m).of_le (by simp)) hE
  have hconv_g :
      Filter.Tendsto
        (fun m ↦ eLpNorm (fun x ↦ g_m m x - ∑ j : Fin n, du j (E x) * a j x) p
          (domainMeasure n K))
        Filter.atTop (𝓝 0) := by
    simpa [g_m, ← Finset.sum_sub_distrib, ← sub_mul] using
      tendsto_eLpNorm_sum_mul_of_tendsto
        (fun j ↦ memLp_on_compact_of_continuous hKc (ha_cont j)) hconv_du
  -- Pass to the limit on `K` by closedness of weak derivatives under `L^p` convergence.
  have hu_mLp (m : ℕ) : MemLp (fun x ↦ u_m m (E x)) p (domainMeasure n K) :=
    memLp_on_compact_of_continuous hKc ((hu_m m).continuous.comp hE.continuous)
  have hg_mLp (m : ℕ) : MemLp (g_m m) p (domainMeasure n K) :=
    memLp_on_compact_of_continuous hKc <| continuous_finsetSum _ fun j _ ↦
      (((hu_m m).partialDeriv j).continuous.comp hE.continuous).mul (ha_cont j)
  have hweakK : HasWeakDerivativeOn (n := n) K [i] (fun x ↦ u (E x))
      (fun x ↦ ∑ j : Fin n, du j (E x) * a j x) :=
    hasWeakDerivativeOn_of_tendsto_eLpNorm hu_mLp hg_mLp
      (Lp.memLp_of_cauchy_tendsto Fact.out hu_mLp _ hconv_u)
      (Lp.memLp_of_cauchy_tendsto Fact.out hg_mLp _ hconv_g) hweak_m hconv_u hconv_g
  -- Both pairings only see `K`, so the identity on `K` is the identity on `E.source`.
  have hsrc : MeasurableSet E.source := E.open_source.measurableSet
  rw [integral_domainMeasure_mul_eq_of_support_subset hsrc hφsupp _
      ((subset_tsupport _).trans (tsupport_iteratedPartialDeriv_subset_tsupport [i] φ.toFun)),
    integral_domainMeasure_mul_eq_of_support_subset hsrc hφsupp _ (subset_tsupport _)]
  exact hweakK φ subset_rfl

end WeakChangeOfVariables

end SobolevSpace
