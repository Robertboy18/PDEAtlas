/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Strong translation derivatives and weak spatial derivatives

A strong L² limit of coordinate difference quotients satisfies the distributional derivative
identity by discrete integration by parts against test functions. A norm derivative of the
translation orbit gives this limit along the nonzero steps 1/(m+1).

Identity pullback transfers the result between the whole-space Sobolev domain measure
and ordinary Lebesgue L². Conversely, an H¹ field has a strongly differentiable coordinate
translation orbit, whose derivative is its weak derivative row.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped Convolution ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open PDE.Analysis SobolevSpace.GraphSpace.Rellich
open scoped Topology Distributions

variable {n : ℕ}

/-- A strong `L²` limit of coordinate difference quotients is the corresponding weak
derivative. Discrete integration by parts identifies the limit against every test function. -/
theorem hasWeakDerivativeOn_of_tendsto_differenceQuotients
    (i : Fin n) (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0) (u g : DerivLp n 2 Set.univ)
    (hstrong : Filter.Tendsto (fun m ↦ differenceQuotientLp 2 i (h m) u)
      Filter.atTop (nhds g)) :
    HasWeakDerivativeOn Set.univ [i] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp u) (by norm_num),
    memLp_locallyIntegrableOn_domain (Lp.memLp g) (by norm_num), ?_⟩
  intro φ _
  have htest := tendsto_differenceQuotientL2_testFunction
    i φ (fun m ↦ -(h m)) (by simpa using hzero.neg)
      (fun m ↦ neg_ne_zero.mpr (hne m))
  have hpair := inner_limit_of_differenceQuotients i h hne
    u (testFunctionL2 φ) g (partialTestFunctionL2 i φ) hstrong htest
  have hgtest : inner ℝ g (testFunctionL2 φ) =
      ∫ x, g x * φ.toFun x ∂(domainMeasure n Set.univ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have hφ : (testFunctionL2 φ : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ] φ.toFun := by
      simpa only [domainMeasure, Measure.restrict_univ] using testFunctionL2_apply_ae φ
    filter_upwards [hφ] with x hx
    rw [hx]
    simp [RCLike.inner_apply, mul_comm]
  have hutest : inner ℝ u (partialTestFunctionL2 i φ) =
      ∫ x, u x * (∂[i] φ.toFun) x ∂(domainMeasure n Set.univ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    have hφ : (partialTestFunctionL2 i φ : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
        fun x ↦ (∂[i] φ.toFun) x := by
      simpa only [domainMeasure, Measure.restrict_univ] using
        partialTestFunctionL2_apply_ae i φ
    filter_upwards [hφ] with x hx
    rw [hx]
    simp [RCLike.inner_apply, mul_comm]
  rw [hgtest, hutest] at hpair
  simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
    Nat.zero_add, pow_one, neg_mul, one_mul] using (neg_eq_iff_eq_neg.mp hpair.symm)

/-- Differentiability of positive spatial translation in `L²` gives the spatial weak
derivative. The nonzero steps `1/(m+1)` turn the norm derivative into difference quotients. -/
theorem hasWeakDerivativeOn_of_hasDerivAt_translateLp (i : Fin n)
    (u g : DerivLp n 2 Set.univ)
    (hderiv : HasDerivAt
      (fun t : ℝ ↦ translateLp 2 (t • EuclideanSpace.single i 1) u) g 0) :
    HasWeakDerivativeOn Set.univ [i] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  let h : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hzero : Filter.Tendsto h Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hne : ∀ m, h m ≠ 0 := fun m ↦ ne_of_gt (by dsimp [h]; positivity)
  have hpunctured : Filter.Tendsto h Filter.atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Filter.Eventually.of_forall hne⟩
  apply hasWeakDerivativeOn_of_tendsto_differenceQuotients i h hzero hne u g
  simpa only [Function.comp_def, slope_def_module, sub_zero, zero_smul, translateLp_zero,
    differenceQuotientLp_apply, coordinateStep] using
    hderiv.tendsto_slope.comp hpunctured

end SobolevSpace.GraphSpace.DifferenceQuotient

namespace PDE.Analysis

variable {n : ℕ}

open SobolevSpace.GraphSpace.Rellich in
/-- The `L²` norm derivative of positive translation satisfies the usual weak-derivative
identity on Euclidean space. -/
theorem hasWeakDerivativeOn_of_hasDerivAt_translateL2 (j : Fin n)
    (u g : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (hderiv : HasDerivAt
      (fun t : ℝ ↦ translateL2 ℝ (-(t • EuclideanSpace.single j 1)) u) g 0) :
    SobolevSpace.HasWeakDerivativeOn Set.univ [j] (u : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  have hid : MeasurePreserving (id : ℝ^n → ℝ^n)
      (SobolevSpace.domainMeasure n Set.univ) volume := by
    simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ] using
      MeasurePreserving.id (volume : Measure (ℝ^n))
  -- Pullback by the identity retains the canonical instances of both L2 models.
  let e : Lp ℝ 2 (volume : Measure (ℝ^n)) →ₗᵢ[ℝ]
      SobolevSpace.GraphSpace.DerivLp n 2 Set.univ :=
    Lp.compMeasurePreservingₗᵢ ℝ id hid
  have he (v : Lp ℝ 2 (volume : Measure (ℝ^n))) :
      (e v : ℝ^n → ℝ) =ᵐ[SobolevSpace.domainMeasure n Set.univ] (v : ℝ^n → ℝ) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving v hid] with x hx
    exact hx
  have hcomm (t : ℝ) :
      translateLp 2 (t • EuclideanSpace.single j 1) (e u) =
        e (translateL2 ℝ (-(t • EuclideanSpace.single j 1)) u) := by
    have hshift :
        (fun x ↦ e u (x + t • EuclideanSpace.single j 1))
          =ᵐ[SobolevSpace.domainMeasure n Set.univ]
            fun x ↦ u (x + t • EuclideanSpace.single j 1) := by
      have hpres : QuasiMeasurePreserving
          (translationContinuousMap (t • EuclideanSpace.single j 1))
          (SobolevSpace.domainMeasure n Set.univ) (SobolevSpace.domainMeasure n Set.univ) :=
        (translationMeasurePreserving (n := n)
          (t • EuclideanSpace.single j 1)).quasiMeasurePreserving
      simpa only [Function.comp_def, translationContinuousMap_apply] using
        hpres.ae_eq_comp (he u)
    have htranslate :
        (translateL2 ℝ (-(t • EuclideanSpace.single j 1)) u : ℝ^n → ℝ)
          =ᵐ[SobolevSpace.domainMeasure n Set.univ]
            fun x ↦ u (x + t • EuclideanSpace.single j 1) := by
      simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ, sub_neg_eq_add] using
        translateL2_ae_eq ℝ (-(t • EuclideanSpace.single j 1)) u
    apply Lp.ext
    filter_upwards [translateLp_apply_ae 2 (t • EuclideanSpace.single j 1) (e u),
      he (translateL2 ℝ (-(t • EuclideanSpace.single j 1)) u), hshift, htranslate]
      with x hleft hright hshift htranslate
    exact hleft.trans (hshift.trans (htranslate.symm.trans hright.symm))
  have hderiv' : HasDerivAt
      (fun t : ℝ ↦ translateLp 2 (t • EuclideanSpace.single j 1) (e u)) (e g) 0 := by
    have h := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hderiv
    change HasDerivAt
      (fun t : ℝ ↦ e (translateL2 ℝ (-(t • EuclideanSpace.single j 1)) u)) (e g) 0 at h
    simpa only [← hcomm] using h
  have hweak :=
    SobolevSpace.GraphSpace.DifferenceQuotient.hasWeakDerivativeOn_of_hasDerivAt_translateLp
      j (e u) (e g) hderiv'
  exact (SobolevSpace.hasWeakDerivativeOn_congr_ae (he u) (he g)).mp hweak

end PDE.Analysis

open Filter

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}

/-- Positive coordinate translation of an H1 field is differentiable in L2, with derivative
its weak derivative. Sequential difference-quotient convergence determines the norm limit. -/
theorem hasDerivAt_translateLp_base (i : Fin n) (U : H¹(ℝ^n)) :
    HasDerivAt
      (fun t : ℝ ↦ translateLp 2 (t • EuclideanSpace.single i 1)
        ((U : WkpAmbientOn n 1 2 univ) (baseIndex n 1)))
      ((U : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i)) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro h hh
  have hne : ∀ᶠ k in atTop, h k ≠ 0 :=
    hh.eventually self_mem_nhdsWithin
  let h' : ℕ → ℝ := fun k ↦ if h k = 0 then 1 / ((k : ℝ) + 1) else h k
  have heq : h' =ᶠ[atTop] h := by
    filter_upwards [hne] with k hk
    simp only [h', ite_eq_right hk]
  have hzero : Tendsto h' atTop (𝓝 0) :=
    (hh.mono_right nhdsWithin_le_nhds).congr' heq.symm
  have hne' (k : ℕ) : h' k ≠ 0 := by
    dsimp only [h']
    split_ifs with hk
    · positivity
    · exact hk
  have hlimit := tendsto_differenceQuotientL2_base i U h' hzero hne'
  have hlimit' := hlimit.congr' (heq.mono fun k hk ↦
    congrArg (fun t ↦ differenceQuotientLp 2 i t
      ((U : WkpAmbientOn n 1 2 univ) (baseIndex n 1))) hk)
  simpa only [Function.comp_def, slope_def_module, sub_zero, zero_smul,
    translateLp_zero, differenceQuotientLp_apply, coordinateStep] using hlimit'

end SobolevSpace.GraphSpace.DifferenceQuotient

namespace PDE.Analysis

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}

/-- An H1 representative identifies the strong derivative of the corresponding ordinary
Lebesgue L2 translation orbit. The identity pullback respects both canonical L2 models. -/
theorem hasDerivAt_translateL2_of_H1 (i : Fin n) (U : H¹(ℝ^n))
    (u g : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (hu : ((U : WkpAmbientOn n 1 2 univ) (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[volume] u)
    (hg : ((U : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[volume] g) :
    HasDerivAt (fun t : ℝ ↦ translateL2 ℝ (-(t • EuclideanSpace.single i 1)) u) g 0 := by
  have hid : MeasurePreserving (id : ℝ^n → ℝ^n)
      volume (domainMeasure n univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      MeasurePreserving.id (volume : Measure (ℝ^n))
  let e : DerivLp n 2 univ →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) :=
    Lp.compMeasurePreservingₗᵢ ℝ id hid
  have he (v : DerivLp n 2 univ) : (e v : ℝ^n → ℝ) =ᵐ[volume] v := by
    filter_upwards [Lp.coeFn_compMeasurePreserving v hid] with x hx
    exact hx
  have hcomm (z : ℝ^n) (v : DerivLp n 2 univ) :
      e (translateLp 2 z v) = translateL2 ℝ (-z) (e v) := by
    have hshift : (fun x ↦ e v (x + z)) =ᵐ[volume] fun x ↦ v (x + z) := by
      have hpres : QuasiMeasurePreserving (fun x : ℝ^n ↦ x + z)
          volume volume := (measurePreserving_add_right volume z).quasiMeasurePreserving
      exact hpres.ae_eq_comp (he v)
    have htranslate : (translateLp 2 z v : ℝ^n → ℝ) =ᵐ[volume]
        fun x ↦ v (x + z) := by
      simpa only [domainMeasure, Measure.restrict_univ] using translateLp_apply_ae 2 z v
    apply Lp.ext
    filter_upwards [he (translateLp 2 z v), htranslate,
      translateL2_ae_eq ℝ (-z) (e v), hshift] with x hleft hv hright hshift
    rw [hleft, hv, hright, sub_neg_eq_add, hshift]
  have heU : e ((U : WkpAmbientOn n 1 2 univ) (baseIndex n 1)) = u :=
    Lp.ext ((he _).trans hu)
  have heD : e ((U : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i)) = g :=
    Lp.ext ((he _).trans hg)
  have h := e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (DifferenceQuotient.hasDerivAt_translateLp_base i U)
  change HasDerivAt
    (fun t : ℝ ↦ e (translateLp 2 (t • EuclideanSpace.single i 1)
      ((U : WkpAmbientOn n 1 2 univ) (baseIndex n 1))))
    (e ((U : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i))) 0 at h
  simpa only [hcomm, heU, heD] using h

end PDE.Analysis
