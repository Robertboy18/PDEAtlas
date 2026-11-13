/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Compactness.Rellich.SmoothTranslation
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.L1.CellAverages
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Global W^{1,1} translation estimate

For `U ∈ W^{1,1}(ℝ^n)` with base coordinate `u`, translation by `h` satisfies

  `‖τ_h u - u‖_{L¹} ≤ |h| ‖U‖_{W^{1,1}}`.

This is the `p = 1` case of the difference-quotient estimate of Evans §5.8.2, Theorem 3(i), for
arbitrary translation vectors on `ℝ^n` (compare the `L¹` bound in step 4 of the proof of Evans §5.7,
Theorem 1; see also Brezis, Chapter 9). It is first proved for a test function `φ` with the
coordinate gradient density `∑ᵢ |∂ᵢφ|` in place of the Sobolev norm: write
`φ(x + h) - φ(x) = ∫₀¹ Dφ(x + th) · h dt`, bound `|Dφ · h| ≤ |h| ∑ᵢ |∂ᵢφ|`, and integrate in `x`
using Fubini and translation invariance. The `W^{1,1}` graph norm dominates `∫ ∑ᵢ |∂ᵢφ|`, and the
general case follows by density of test functions in `W^{1,1}(ℝ^n)`, since both sides of the
inequality depend continuously on `U`.

The `L²` analogue, with the squared gradient in place of the coordinate `ℓ¹`
density, is `Rellich.SmoothTranslation`.

## Main results

* `testFunctionGradientL1 φ x = ∑ᵢ |∂ᵢφ x|` and its continuity, compact
  support, integrability, and translation invariance.
* `testFunction_directional_abs_le_norm_mul_gradientL1`,
  `testFunction_translation_abs_le_intervalIntegral_gradientL1`: the pointwise
  segment estimates.
* `integral_testFunction_translation_abs_le`: the smooth `L¹` translation
  estimate.
* `globalTranslationDefectL1 h`: the operator `U ↦ τ_h u - u` on
  `W^{1,1}(ℝ^n)`.
* `globalTranslationDefectL1.norm_le_of_testFunction`,
  `globalTranslationDefectL1.norm_le`: the estimate for test functions and,
  by density, for all of `W^{1,1}(ℝ^n)`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for translation estimates of Sobolev functions.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 3(i), pp. 291-292; and §5.7, Theorem 1, step
  4 of the proof, p. 287, for `∫_V |u^ε - u| ≤ ε ∫_V |Du|`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace
namespace GraphSpace
namespace RellichKondrachov

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

section EndpointL1

/-- The coordinate `ℓ¹` density of the first derivatives of a test
function. -/
noncomputable def testFunctionGradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, |(∂[i] φ.toFun) x|

/-- The coordinate gradient density is a sum of absolute values, hence
nonnegative. -/
@[simp]
theorem testFunctionGradientL1_nonneg
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    0 ≤ testFunctionGradientL1 φ x :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The coordinate gradient density of a test function is continuous, since
each partial derivative of a smooth function is. -/
theorem continuous_testFunctionGradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Continuous (testFunctionGradientL1 φ) := by
  unfold testFunctionGradientL1
  apply continuous_finsetSum
  intro i _
  have happ : Continuous fun p : ℝ^n × ℝ^n ↦
      (fderiv ℝ φ.toFun p.1 : ℝ^n →L[ℝ] ℝ) p.2 :=
    φ.contDiff.continuous_fderiv_apply (by simp)
  have hpair : Continuous fun y : ℝ^n ↦
      (y, EuclideanSpace.single i (1 : ℝ)) :=
    continuous_id.prodMk continuous_const
  have hpartial : Continuous fun y : ℝ^n ↦
      (∂[i] φ.toFun) y := by
    have hcomp := happ.comp hpair
    change Continuous fun y : ℝ^n ↦
      (fderiv ℝ φ.toFun y : ℝ^n →L[ℝ] ℝ)
        (EuclideanSpace.single i (1 : ℝ)) at hcomp
    simpa [partialDeriv] using hcomp
  exact hpartial.abs

/-- The coordinate gradient density of a test function has compact support,
contained in the support of `φ`. -/
theorem testFunctionGradientL1_hasCompactSupport
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    HasCompactSupport (testFunctionGradientL1 φ) := by
  classical
  unfold testFunctionGradientL1
  have habs (i : Fin n) :
      HasCompactSupport (fun x : ℝ^n ↦
        |(∂[i] φ.toFun) x|) := by
    have hpartial : HasCompactSupport fun x : ℝ^n ↦
        (∂[i] φ.toFun) x := by
      simpa [partialDeriv] using
        φ.hasCompactSupport.fderiv_apply
          (𝕜 := ℝ) (v := EuclideanSpace.single i (1 : ℝ))
    exact hpartial.comp_left abs_zero
  have hsum :
      HasCompactSupport
        (∑ i : Fin n, fun x : ℝ^n ↦
          |(∂[i] φ.toFun) x|) :=
    HasCompactSupport.finset_sum fun i _ ↦ habs i
  have hfun :
      (∑ i : Fin n, fun x : ℝ^n ↦
        |(∂[i] φ.toFun) x|) =
        fun x : ℝ^n ↦ ∑ i : Fin n,
          |(∂[i] φ.toFun) x| := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- The coordinate gradient density of a test function is integrable on `ℝ^n`,
being continuous with compact support. -/
theorem integrable_testFunctionGradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Integrable (testFunctionGradientL1 φ) MeasureTheory.volume :=
  (continuous_testFunctionGradientL1 φ).integrable_of_hasCompactSupport
    (testFunctionGradientL1_hasCompactSupport φ)

/-- Translation invariance of Lebesgue measure: the integral of the gradient
density is unchanged by shifting the argument. -/
theorem integral_testFunctionGradientL1_add_right
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (a : ℝ^n) :
    (∫ x : ℝ^n, testFunctionGradientL1 φ (x + a)) =
      ∫ x : ℝ^n, testFunctionGradientL1 φ x :=
  integral_add_right_eq_self (testFunctionGradientL1 φ) a

/-- The gradient density evaluated along the segment `x + t h`, `t ∈ (0, 1]`, is
integrable on the product of the parameter interval with `ℝ^n`.  This is the
Fubini hypothesis for exchanging the segment and space integrals. -/
theorem integrable_segment_testFunctionGradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    Integrable
      (Function.uncurry fun t : ℝ ↦ fun x : ℝ^n ↦
        testFunctionGradientL1 φ (x + t • h))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        MeasureTheory.volume) := by
  let F : ℝ × ℝ^n → ℝ := fun p ↦
    testFunctionGradientL1 φ (p.2 + p.1 • h)
  have hFcont : Continuous F :=
    (continuous_testFunctionGradientL1 φ).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))
  apply (MeasureTheory.integrable_prod_iff hFcont.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t ↦ by
      have hpres : MeasurePreserving
          (Rellich.translationContinuousMap (t • h))
          (MeasureTheory.volume : Measure (ℝ^n)) MeasureTheory.volume := by
        simpa [domainMeasure] using
          Rellich.translationMeasurePreserving (n := n) (t • h)
      simpa [F, Function.comp_def, Rellich.translationContinuousMap] using
        hpres.integrable_comp_of_integrable
          (integrable_testFunctionGradientL1 φ)
  · have heq :
        (fun t : ℝ ↦ ∫ x : ℝ^n,
          ‖F (t, x)‖ ∂MeasureTheory.volume) =
          fun _ : ℝ ↦ ∫ x : ℝ^n,
            testFunctionGradientL1 φ x ∂MeasureTheory.volume := by
      funext t
      simp only [F, Real.norm_eq_abs,
        abs_of_nonneg (testFunctionGradientL1_nonneg φ _)]
      exact integral_testFunctionGradientL1_add_right φ (t • h)
    rw [heq]
    exact MeasureTheory.integrableOn_const
      (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.uIoc (0 : ℝ) 1) (by simp)

/-- Averaging the translated gradient density over the unit segment does not
change its total integral: swap the integrals and use translation invariance
for each fixed `t`. -/
theorem integral_intervalIntegral_testFunctionGradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    (∫ x : ℝ^n, ∫ t in (0 : ℝ)..1,
      testFunctionGradientL1 φ (x + t • h)) =
      ∫ x : ℝ^n, testFunctionGradientL1 φ x := by
  rw [← MeasureTheory.intervalIntegral_integral_swap
    (integrable_segment_testFunctionGradientL1 φ h)]
  simp_rw [integral_testFunctionGradientL1_add_right φ]
  simp

/-- Coordinatewise bound for a directional derivative. -/
theorem testFunction_directional_abs_le_norm_mul_gradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x h : ℝ^n) :
    |(fderiv ℝ φ.toFun x) h| ≤
      ‖h‖ * testFunctionGradientL1 φ x := by
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  calc
    |∑ i : Fin n,
        (∂[i] φ.toFun) x * h i|
        ≤ ∑ i : Fin n,
          |(∂[i] φ.toFun) x * h i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,
          ‖h‖ * |(∂[i] φ.toFun) x| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (by simpa using PiLp.norm_apply_le h i) (abs_nonneg _)
    _ = ‖h‖ * testFunctionGradientL1 φ x := by
      simp [testFunctionGradientL1, partialDeriv,
        Finset.mul_sum]

/-- Pointwise fundamental-theorem estimate along the segment from `x` to
`x+h`. -/
theorem testFunction_translation_abs_le_intervalIntegral_gradientL1
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x h : ℝ^n) :
    |φ.toFun (x + h) - φ.toFun x| ≤
      ‖h‖ * ∫ t in (0 : ℝ)..1,
        testFunctionGradientL1 φ (x + t • h) := by
  rw [Rellich.testFunction_translation_sub_eq_intervalIntegral
    (n := n) φ x h]
  calc
    |∫ t in (0 : ℝ)..1,
        (fderiv ℝ φ.toFun (x + t • h)) h|
        ≤ ∫ t in (0 : ℝ)..1,
          |(fderiv ℝ φ.toFun (x + t • h)) h| := by
      simpa [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm
          (f := fun t : ℝ ↦
            (fderiv ℝ φ.toFun (x + t • h)) h)
          (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ ∫ t in (0 : ℝ)..1,
          ‖h‖ * testFunctionGradientL1 φ (x + t • h) := by
      apply intervalIntegral.integral_mono (by norm_num)
      · exact
          (((φ.contDiff.continuous_fderiv (by simp)).comp
            (continuous_const.add
              (continuous_id.smul continuous_const))).clm_apply
                continuous_const).abs.intervalIntegrable 0 1
      · exact
          (continuous_const.mul
            ((continuous_testFunctionGradientL1 φ).comp
              (continuous_const.add
                (continuous_id.smul continuous_const)))).intervalIntegrable 0 1
      · intro t
        exact testFunction_directional_abs_le_norm_mul_gradientL1
          (n := n) φ (x + t • h) h
    _ = ‖h‖ * ∫ t in (0 : ℝ)..1,
          testFunctionGradientL1 φ (x + t • h) := by
      rw [intervalIntegral.integral_const_mul]

/-- The smooth global `W^{1,1}` translation estimate. -/
theorem integral_testFunction_translation_abs_le
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    (∫ x : ℝ^n, |φ.toFun (x + h) - φ.toFun x|) ≤
      ‖h‖ * ∫ x : ℝ^n, testFunctionGradientL1 φ x := by
  let segment : ℝ^n → ℝ := fun x ↦
    ∫ t in (0 : ℝ)..1,
      testFunctionGradientL1 φ (x + t • h)
  have hsegInt : Integrable segment MeasureTheory.volume := by
    have hprod := integrable_segment_testFunctionGradientL1 φ h
    have houter := hprod.integral_prod_right
    simpa [segment,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using houter
  have hlhs : Integrable
      (fun x : ℝ^n ↦ |φ.toFun (x + h) - φ.toFun x|)
      MeasureTheory.volume := by
    have hdiff : HasCompactSupport
        (fun x : ℝ^n ↦ φ.toFun (x + h) - φ.toFun x) := by
      exact
        (φ.hasCompactSupport.comp_homeomorph
          (Homeomorph.addRight h)).sub φ.hasCompactSupport
    exact
      (((φ.contDiff.continuous.comp
        (continuous_id.add continuous_const)).sub
          φ.contDiff.continuous).abs).integrable_of_hasCompactSupport
            (hdiff.comp_left abs_zero)
  calc
    (∫ x : ℝ^n, |φ.toFun (x + h) - φ.toFun x|)
        ≤ ∫ x : ℝ^n, ‖h‖ * segment x := by
      exact MeasureTheory.integral_mono hlhs
        (hsegInt.const_mul _) fun x ↦
          testFunction_translation_abs_le_intervalIntegral_gradientL1
            (n := n) φ x h
    _ = ‖h‖ * ∫ x : ℝ^n, segment x := by
      rw [MeasureTheory.integral_const_mul]
    _ = ‖h‖ * ∫ x : ℝ^n, testFunctionGradientL1 φ x := by
      rw [integral_intervalIntegral_testFunctionGradientL1 φ h]

/-- Translation defect of the global base coordinate. -/
noncomputable def globalTranslationDefectL1 (h : ℝ^n) :
    W^{1,(1 : ℝ≥0∞)}(ℝ^n) →L[ℝ] DerivLp n 1 Set.univ :=
  (Rellich.translateLp 1 h).toContinuousLinearMap.comp
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := 1) (Ω := Set.univ)) -
    wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 1) (Ω := Set.univ)

/-- The translation defect of `U` is `τ_h u - u`, where `u` is the base
coordinate of `U`. -/
@[simp]
theorem globalTranslationDefectL1_apply
    (h : ℝ^n) (U : W^{1,(1 : ℝ≥0∞)}(ℝ^n)) :
    globalTranslationDefectL1 (n := n) h U =
      Rellich.translateLp 1 h
          (wkpBaseCoordinateCLM
            (n := n) (m := 1) (p := 1) (Ω := Set.univ) U) -
        wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := 1) (Ω := Set.univ) U :=
  rfl

/-- The integral coordinate-gradient density of a test function is bounded
by its complete global `W^{1,1}` norm. -/
theorem integral_testFunctionGradientL1_le_globalW11_norm
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    let U : W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
      mkWkpSpaceOnOfContDiff
        (n := n) (k := 1) (p := (1 : ℝ≥0∞))
        (Ω := (Set.univ : Set (ℝ^n)))
        (f := φ.toFun) φ.contDiff φ.hasCompactSupport
    (∫ x : ℝ^n, testFunctionGradientL1 φ x) ≤ ‖U‖ := by
  dsimp only
  let U : W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff
      (n := n) (k := 1) (p := (1 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n)))
      (f := φ.toFun) φ.contDiff φ.hasCompactSupport
  have hpartialInt (i : Fin n) :
      Integrable (fun x : ℝ^n ↦
        |(∂[i] φ.toFun) x|) MeasureTheory.volume := by
    have hcont : Continuous fun x : ℝ^n ↦
        (∂[i] φ.toFun) x := by
      have happ : Continuous fun p : ℝ^n × ℝ^n ↦
          (fderiv ℝ φ.toFun p.1 : ℝ^n →L[ℝ] ℝ) p.2 :=
        φ.contDiff.continuous_fderiv_apply (by simp)
      have hcomp := happ.comp
        (continuous_id.prodMk
          (continuous_const : Continuous fun _ : ℝ^n ↦
            EuclideanSpace.single i (1 : ℝ)))
      change Continuous fun x : ℝ^n ↦
        (fderiv ℝ φ.toFun x : ℝ^n →L[ℝ] ℝ)
          (EuclideanSpace.single i (1 : ℝ)) at hcomp
      simpa [partialDeriv] using hcomp
    have hcs : HasCompactSupport fun x : ℝ^n ↦
        (∂[i] φ.toFun) x := by
      simpa [partialDeriv] using
        φ.hasCompactSupport.fderiv_apply
          (𝕜 := ℝ) (v := EuclideanSpace.single i (1 : ℝ))
    exact hcont.abs.integrable_of_hasCompactSupport
      (hcs.comp_left abs_zero)
  have hcoord (i : Fin n) :
      ‖((U : WkpAmbientOn n 1 1 Set.univ)
        (singleDerivIndex (n := n) i))‖ =
        ∫ x : ℝ^n, |(∂[i] φ.toFun) x| := by
    rw [MeasureTheory.L1.norm_eq_integral_norm]
    have hrep := mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := (1 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n)))
      (f := φ.toFun) φ.contDiff φ.hasCompactSupport
      (singleDerivIndex (n := n) i)
    have hrep' :
        ((((U : WkpAmbientOn n 1 1 Set.univ)
          (singleDerivIndex (n := n) i) :
            DerivLp n 1 Set.univ) : ℝ^n → ℝ))
          =ᵐ[MeasureTheory.volume]
            fun x ↦ (∂[i] φ.toFun) x := by
      simpa [U, domainMeasure, iteratedPartialDeriv] using hrep
    simpa [domainMeasure, Real.norm_eq_abs, Function.comp_def] using
      MeasureTheory.integral_congr_ae
        (hrep'.fun_comp fun z ↦ ‖z‖)
  have hinj : Function.Injective (singleDerivIndex (n := n)) := by
    intro i j hij
    have hlist := congrArg DerivIndex.toList hij
    simpa using hlist
  calc
    (∫ x : ℝ^n, testFunctionGradientL1 φ x) =
        ∑ i : Fin n, ∫ x : ℝ^n,
          |(∂[i] φ.toFun) x| := by
      simp only [testFunctionGradientL1]
      exact MeasureTheory.integral_finsetSum _ fun i _ ↦ hpartialInt i
    _ = ∑ i : Fin n,
        ‖((U : WkpAmbientOn n 1 1 Set.univ)
          (singleDerivIndex (n := n) i))‖ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hcoord i).symm
    _ = ∑ a ∈ Finset.univ.image (singleDerivIndex (n := n)),
        ‖((U : WkpAmbientOn n 1 1 Set.univ) a)‖ := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij ↦ hinj hij
    _ ≤ ∑ a : DerivIndex n 1,
        ‖((U : WkpAmbientOn n 1 1 Set.univ) a)‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) fun _ _ _ ↦ norm_nonneg _
    _ = ‖U‖ := by
      change (∑ a : DerivIndex n 1,
        ‖((U : WkpAmbientOn n 1 1 Set.univ) a)‖) =
          ‖(U : WkpAmbientOn n 1 1 Set.univ)‖
      rw [PiLp.norm_eq_sum (by norm_num)]
      norm_num

/-- Norm form of the global `W^{1,1}` translation estimate for a test
function. -/
theorem globalTranslationDefectL1.norm_le_of_testFunction
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    let U : W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
      mkWkpSpaceOnOfContDiff
        (n := n) (k := 1) (p := (1 : ℝ≥0∞))
        (Ω := (Set.univ : Set (ℝ^n)))
        (f := φ.toFun) φ.contDiff φ.hasCompactSupport
    ‖globalTranslationDefectL1 (n := n) h U‖ ≤ ‖h‖ * ‖U‖ := by
  dsimp only
  let U : W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff
      (n := n) (k := 1) (p := (1 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n)))
      (f := φ.toFun) φ.contDiff φ.hasCompactSupport
  let u0 : DerivLp n 1 Set.univ :=
    wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 1) (Ω := Set.univ) U
  have hrep : (u0 : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume] φ.toFun := by
    have hbase := mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := (1 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n)))
      (f := φ.toFun) φ.contDiff φ.hasCompactSupport
      (baseIndex n 1)
    simpa [u0, U, wkpBaseCoordinateCLM, wkpCoordinateCLM,
      domainMeasure, iteratedPartialDeriv] using hbase
  have hpres : MeasurePreserving
      (Rellich.translationContinuousMap h)
      (MeasureTheory.volume : Measure (ℝ^n)) MeasureTheory.volume := by
    simpa [domainMeasure] using
      Rellich.translationMeasurePreserving (n := n) h
  have hrepTrans :
      (fun x ↦ u0 (x + h)) =ᵐ[MeasureTheory.volume]
        fun x ↦ φ.toFun (x + h) := by
    simpa [Function.comp_def, Rellich.translationContinuousMap] using
      hpres.quasiMeasurePreserving.ae_eq_comp hrep
  calc
    ‖globalTranslationDefectL1 (n := n) h U‖ =
        ∫ x : ℝ^n, |φ.toFun (x + h) - φ.toFun x| := by
      rw [globalTranslationDefectL1_apply,
        norm_translateL1_sub_eq_integral]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hrep, hrepTrans] with x hx hxtrans
      rw [hx, hxtrans]
    _ ≤ ‖h‖ * ∫ x : ℝ^n, testFunctionGradientL1 φ x :=
      integral_testFunction_translation_abs_le φ h
    _ ≤ ‖h‖ * ‖U‖ := by
      exact mul_le_mul_of_nonneg_left
        (integral_testFunctionGradientL1_le_globalW11_norm φ)
        (norm_nonneg _)

/-- Evans's global endpoint translation estimate, obtained from the smooth
case by density in the complete `W^{1,1}` graph norm. -/
theorem globalTranslationDefectL1.norm_le
    (h : ℝ^n) (U : W^{1,(1 : ℝ≥0∞)}(ℝ^n)) :
    ‖globalTranslationDefectL1 (n := n) h U‖ ≤ ‖h‖ * ‖U‖ := by
  let S : Set (W^{1,(1 : ℝ≥0∞)}(ℝ^n)) :=
    {V | ‖globalTranslationDefectL1 (n := n) h V‖ ≤ ‖h‖ * ‖V‖}
  have hSclosed : IsClosed S := by
    exact isClosed_le (by fun_prop) (by fun_prop)
  obtain ⟨f_m, hf_m, hcs_m, htend⟩ :=
    globalApproximation_WkpSpace
      (Approximation.standardMollifier n)
      (by norm_num : (1 : ℝ≥0∞) ≠ ∞) 1 U
  let U_m : ℕ → W^{1,(1 : ℝ≥0∞)}(ℝ^n) := fun m ↦
    mkWkpSpaceOnOfContDiff
      (n := n) (k := 1) (p := (1 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n)))
      (f := f_m m) (hf_m m) (hcs_m m)
  have hUm : Filter.Tendsto U_m Filter.atTop (𝓝 U) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hnorm := htend
    rw [Metric.tendsto_atTop] at hnorm
    obtain ⟨N, hN⟩ := hnorm ε hε
    refine ⟨N, fun m hm ↦ ?_⟩
    simpa [dist_eq_norm, U_m] using hN m hm
  have hmem : ∀ m, U_m m ∈ S := by
    intro m
    let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      ⟨f_m m, hf_m m, hcs_m m, subset_univ _⟩
    simpa [S, U_m, φ] using
      globalTranslationDefectL1.norm_le_of_testFunction (n := n) φ h
  exact hSclosed.mem_of_tendsto hUm (Filter.Eventually.of_forall hmem)

end EndpointL1

end RellichKondrachov
end GraphSpace
end SobolevSpace
