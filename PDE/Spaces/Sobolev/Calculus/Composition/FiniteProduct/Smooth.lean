/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Integrands
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The chain rule for finite families of Sobolev fields

A zero-preserving `C¹` function with bounded derivative acts on every finite family of
scalar `W¹ᵖ` fields on Euclidean space. Its weak derivative is the Fréchet
derivative applied to the column of weak derivatives. Smooth approximation takes place
simultaneously in the finite family. The continuous superposition theorem then passes
both sides of the classical chain rule to the limit.

Neither the target dimension nor the spatial dimension is required to be positive.
The zero-preserving condition is needed because the underlying measure can be infinite.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : ℝ^m → ℝ} {C : ℝ≥0}

/-- The classical chain rule, with the derivative column expressed in Euclidean coordinates. -/
theorem partialDeriv_comp_finite (hF : ContDiff ℝ 1 F)
    (f : Fin m → ℝ^n → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y ↦ F (WithLp.toLp 2 (fun j ↦ f j y)))) x =
      fderiv ℝ F (WithLp.toLp 2 (fun j ↦ f j x))
        (WithLp.toLp 2 (fun j ↦ (∂[i] (f j)) x)) := by
  let v : ℝ^n → ℝ^m := fun y ↦ WithLp.toLp 2 (fun j ↦ f j y)
  let D : ℝ^n →L[ℝ] ℝ^m :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j ↦ fderiv ℝ (f j) x)
  have hv : HasFDerivAt v D x :=
    (PiLp.hasFDerivAt_toLp 2 (fun j ↦ f j x)).comp x
      (hasFDerivAt_pi.mpr fun j ↦ ((hf j).differentiable (by simp)).differentiableAt.hasFDerivAt)
  have hcomp := ((hF.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp x hv
  have hcol : D (EuclideanSpace.single i 1) =
      WithLp.toLp 2 (fun j ↦ (∂[i] (f j)) x) := by
    ext j
    rfl
  change fderiv ℝ (F ∘ v) x (EuclideanSpace.single i 1) = _
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, hcol]

/-- Smooth representatives of a finite family identify both jet projections simultaneously. -/
theorem smooth_firstJet_ae (f : Fin m → ℝ^n → ℝ)
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) (i : Fin n) :
    let U : Fin m → W^{1,p}(ℝ^n) := fun j ↦
      mkWkpSpaceOnOfContDiff (f j) (hf j) (hcs j)
    ∀ᵐ x ∂domainMeasure n univ,
      valuesCLM (vectorWkpFirstJetCLM U x) = WithLp.toLp 2 (fun j ↦ f j x) ∧
        derivativeCLM i (vectorWkpFirstJetCLM U x) =
          WithLp.toLp 2 (fun j ↦ (∂[i] (f j)) x) := by
  dsimp only
  let U : Fin m → W^{1,p}(ℝ^n) := fun j ↦
    mkWkpSpaceOnOfContDiff (f j) (hf j) (hcs j)
  have hbase : ∀ᵐ x ∂domainMeasure n univ, ∀ j,
      wkpBaseCoordinateCLM (U j) x = f j x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := p) (Ω := univ)
      (f j) (hf j) (hcs j) (baseIndex n 1)] with x hx
    simpa only [wkpBaseCoordinateCLM_apply, U, baseIndex_toList, iteratedPartialDeriv] using hx
  have hderiv : ∀ᵐ x ∂domainMeasure n univ, ∀ j,
      wkpCoordinateCLM (singleDerivIndex n i) (U j) x = (∂[i] (f j)) x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := p) (Ω := univ)
      (f j) (hf j) (hcs j) (singleDerivIndex n i)] with x hx
    simpa only [wkpCoordinateCLM_apply, U, singleDerivIndex_toList,
      iteratedPartialDeriv, Function.comp_def] using hx
  filter_upwards [valuesCLM_firstJet_ae U, derivativeCLM_firstJet_ae U i, hbase, hderiv]
    with x hx hy hb hd
  constructor
  · rw [hx]
    ext j
    exact hb j
  · rw [hy]
    ext j
    exact hd j

/-- The weak chain rule for a finite family of Sobolev fields on the whole space. -/
theorem hasWeakDerivativeOn_comp (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(ℝ^n)) (i : Fin n) :
    HasWeakDerivativeOn univ [i] (fun x ↦ F (values U x))
      (fun x ↦ fderiv ℝ F (values U x) (derivatives U i x)) := by
  choose f hf hcs hnorm using fun j ↦
    globalApproximation_WkpSpace (Approximation.standardMollifier n) hp 1 (U j)
  let Us : ℕ → Fin m → W^{1,p}(ℝ^n) := fun k j ↦
    mkWkpSpaceOnOfContDiff (f j k) (hf j k) (hcs j k)
  have hUs : Tendsto Us atTop (𝓝 U) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (hnorm j)
  let J : (Fin m → W^{1,p}(ℝ^n)) →L[ℝ]
      Lp (Fin m → ℝ × ℝ^n) p (domainMeasure n univ) := vectorWkpFirstJetCLM
  have hJ : Tendsto (fun k ↦ J (Us k)) atTop (𝓝 (J U)) :=
    (J.continuous.tendsto U).comp hUs
  have hvmem := memLp_valueIntegrand (n := n) (p := p) (Ω := univ) hF hzero hbound
  have hdmem := memLp_derivativeIntegrand (p := p) (Ω := univ) hF hbound i
  have hvconv :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k ↦ hvmem (J (Us k))) _
      (hvmem (J U))).mp
        ((continuous_valueSuperposition hp hF hzero hbound).continuousAt.tendsto.comp hJ)
  have hdconv :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun k ↦ hdmem (J (Us k))) _
      (hdmem (J U))).mp
        ((continuous_derivativeSuperposition hp hF hbound i).continuousAt.tendsto.comp hJ)
  have hweak (k : ℕ) :
      HasWeakDerivativeOn univ [i]
        (fun x ↦ valueIntegrand F (J (Us k) x))
        (fun x ↦ derivativeIntegrand F i (J (Us k) x)) := by
    have hv : ContDiff ℝ 1 (fun x ↦ WithLp.toLp 2 (fun j ↦ f j k x)) :=
      (contDiff_piLp 2).mpr fun j ↦ (hf j k).of_le (by simp)
    have hw := WeakChangeOfVariables.hasWeakDerivativeOn_of_contDiff_one
      (Ω := univ) (i := i) (hF.comp hv)
    have hraw : HasWeakDerivativeOn univ [i]
        (fun x ↦ F (WithLp.toLp 2 (fun j ↦ f j k x)))
        (fun x ↦ fderiv ℝ F (WithLp.toLp 2 (fun j ↦ f j k x))
          (WithLp.toLp 2 (fun j ↦ (∂[i] (f j k)) x))) := by
      simpa only [Function.comp_def,
        partialDeriv_comp_finite hF (fun j ↦ f j k) (fun j ↦ hf j k) i] using hw
    have hjet := smooth_firstJet_ae (p := p) (fun j ↦ f j k)
      (fun j ↦ hf j k) (fun j ↦ hcs j k) i
    apply (hasWeakDerivativeOn_congr_ae _ _).mpr hraw
    · filter_upwards [hjet] with x hx
      exact congrArg F hx.1
    · filter_upwards [hjet] with x hx
      exact congrArg₂ (fun z v ↦ fderiv ℝ F z v) hx.1 hx.2
  have hclosed := WeakChangeOfVariables.hasWeakDerivativeOn_of_tendsto_eLpNorm
    (fun k ↦ hvmem (J (Us k))) (fun k ↦ hdmem (J (Us k)))
    (hvmem (J U)) (hdmem (J U)) hweak hvconv hdconv
  apply (hasWeakDerivativeOn_congr_ae _ _).mp hclosed
  · filter_upwards [valuesCLM_firstJet_ae U] with x hx
    exact congrArg F hx
  · filter_upwards [valuesCLM_firstJet_ae U, derivativeCLM_firstJet_ae U i] with x hx hy
    exact congrArg₂ (fun z v ↦ fderiv ℝ F z v) hx hy

end SobolevSpace.GraphSpace.FiniteProductComposition
