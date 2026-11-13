/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import PDE.FDeriv.Operators
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Smooth translation bounds for Rellich compactness

For a smooth compactly supported `φ : ℝ^n → ℝ` and a translation vector `h`,

  `∫ |φ(x + h) - φ(x)|² dx ≤ |h|² ∫ |Dφ(x)|² dx`.

The proof is the classical one: write `φ(x + h) - φ(x) = ∫₀¹ Dφ(x + th) · h dt` by the fundamental
theorem of calculus along the segment, apply Cauchy–Schwarz in `t`, bound the directional derivative
by `|h| |Dφ|`, and integrate in `x` using Fubini and translation invariance of Lebesgue measure.
This is the `L²` form of the translation estimate that Evans derives from the same identity along a
segment, in `L¹` in step 4 of the proof of §5.7, Theorem 1, and in `L^p` for coordinate difference
quotients in §5.8.2, Theorem 3(i) (see also Brezis, Chapter 9). It is the quantitative input to our
proof of the Rellich–Kondrachov theorem: translation errors of a bounded set in `H¹` are uniformly
small, so the cell-averaging errors of `Rellich.CellAverages` are too.

The estimate is proved here for test functions only and then restated for the `H¹` element
`testFunctionToH1 φ`, with the gradient energy bounded by the full `H¹` norm. The extension to `H¹₀`
functions by density is `translationDefectCLM.norm_le` in `Rellich.ZeroExtension`.

## Main results

* `testFunction_translation_sub_eq_intervalIntegral`: the segment identity.
* `testFunctionGradientEnergy φ x = ∑ᵢ (∂ᵢφ x)²`, with its continuity, compact
  support, integrability and translation invariance.
* `integral_testFunction_translation_sq_le`: the translation estimate for `φ`.
* `integral_testFunctionGradientEnergy_le_globalH1_norm_sq`: `∫ |Dφ|²` is at
  most `‖testFunctionToH1 φ‖²`.
* `norm_translateL2_sub_globalTestFunction_le`: the norm form
  `‖τ_h φ - φ‖_{L²} ≤ |h| ‖φ‖_{H¹}` for the bundled test function.
* `tendsto_translateLp_zero`: strong continuity of translations at `h = 0` in
  `L^p`, `p < ∞`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for translation estimates of Sobolev functions.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1, step 4 of the proof, p. 287, for
  `∫_V |u^ε - u| ≤ ε ∫_V |Du|` from the identity along a segment; and §5.8.2, Theorem 3(i),
  pp. 291-292, for difference quotients.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev Gradient

namespace SobolevSpace
namespace GraphSpace
namespace Rellich

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

variable {n : ℕ}

/-- Strong continuity at the zero translation for every finite exponent. -/
theorem tendsto_translateLp_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (u : DerivLp n p Set.univ) :
    Filter.Tendsto (fun h : ℝ^n ↦ translateLp p h u)
      (𝓝 0) (𝓝 u) := by
  have h :
      Filter.Tendsto (fun z : ℝ^n ↦ translateLp p z u)
        (𝓝 0) (𝓝 (translateLp p (0 : ℝ^n) u)) :=
    (continuous_translateLp (n := n) p hp u).continuousAt
  simpa using h

/-- Fundamental-theorem-of-calculus identity along the segment from `x` to
`x + h`. This is the pointwise starting point for the translation estimate
`integral_testFunction_translation_sq_le`. -/
theorem testFunction_translation_sub_eq_intervalIntegral
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x h : ℝ^n) :
    φ.toFun (x + h) - φ.toFun x =
      ∫ t in (0 : ℝ)..1, (fderiv ℝ φ.toFun (x + t • h)) h := by
  let γ : ℝ → ℝ^n := fun t ↦ x + t • h
  have hγ (t : ℝ) : HasDerivAt γ h t := by
    have hsmul : HasDerivAt (fun s : ℝ ↦ s • h) ((1 : ℝ) • h) t :=
      (hasDerivAt_id t).smul_const h
    simpa [γ, one_smul] using hsmul.const_add x
  have hcomp (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ φ.toFun (γ s))
        ((fderiv ℝ φ.toFun (γ t)) h) t := by
    have hφ : HasFDerivAt φ.toFun (fderiv ℝ φ.toFun (γ t)) (γ t) :=
      (φ.contDiff.differentiable (by simp) (γ t)).hasFDerivAt
    simpa [Function.comp_def] using hφ.comp_hasDerivAt t (hγ t)
  have hcont : Continuous fun t : ℝ ↦ (fderiv ℝ φ.toFun (γ t)) h :=
    ((φ.contDiff.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (fderiv ℝ φ.toFun (γ t)) h)
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ ↦ φ.toFun (γ t))
    (f' := fun t : ℝ ↦ (fderiv ℝ φ.toFun (γ t)) h)
    (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hcomp t) hint
  simpa [γ] using hFTC.symm

/-- Cauchy-Schwarz/Jensen on the unit interval, normalized here by the fact
that its Lebesgue measure is one. -/
theorem sq_intervalIntegral_le_intervalIntegral_sq
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤
      ∫ t in (0 : ℝ)..1, (g t) ^ 2 := by
  have hgInt : IntegrableOn g (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hgSq : Continuous fun t : ℝ ↦ (g t) ^ 2 := hg.pow 2
  have hgSqInt : IntegrableOn (fun t : ℝ ↦ (g t) ^ 2)
      (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume :=
    (hgSq.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hJ :=
    (show Even 2 by norm_num).convexOn_pow.map_set_average_le
      (μ := (MeasureTheory.volume : Measure ℝ))
      (s := (Set.univ : Set ℝ)) (t := Set.Ioc (0 : ℝ) 1)
      (f := g) (continuous_pow 2).continuousOn isClosed_univ
      (by simp [Real.volume_Ioc]) (by simp)
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _)
      hgInt (by simpa [Function.comp_def] using hgSqInt)
  rw [setAverage_eq, setAverage_eq,
    Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hJ
  simpa [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Function.comp_def] using hJ

/-- Pointwise squared translation estimate for a test function, after applying
Cauchy-Schwarz in the segment parameter. -/
theorem testFunction_translation_sq_le_intervalIntegral_directional_sq
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x h : ℝ^n) :
    (φ.toFun (x + h) - φ.toFun x) ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ.toFun (x + t • h)) h) ^ 2 := by
  rw [testFunction_translation_sub_eq_intervalIntegral (n := n) φ x h]
  apply sq_intervalIntegral_le_intervalIntegral_sq
  exact ((φ.contDiff.continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

/-- The directional derivative is controlled by the Euclidean gradient.  The
right-hand side is written in coordinates because this is the form that
integrates directly to the first-order Sobolev seminorm. -/
theorem testFunction_directional_sq_le_norm_sq_mul_sum_partial_sq
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x h : ℝ^n) :
    ((fderiv ℝ φ.toFun x) h) ^ 2 ≤
      ‖h‖ ^ 2 * ∑ i : Fin n, ((∂[i] φ.toFun) x) ^ 2 := by
  have hinner :
      (fderiv ℝ φ.toFun x) h = ⟪∇ φ.toFun x, h⟫_ℝ :=
    inner_gradient_left.symm
  have habs :
      |(fderiv ℝ φ.toFun x) h| ≤ ‖∇ φ.toFun x‖ * ‖h‖ := by
    rw [hinner]
    exact abs_real_inner_le_norm _ _
  have hsquare :
      ((fderiv ℝ φ.toFun x) h) ^ 2 ≤
        (‖∇ φ.toFun x‖ * ‖h‖) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 habs
  calc
    ((fderiv ℝ φ.toFun x) h) ^ 2
        ≤ (‖∇ φ.toFun x‖ * ‖h‖) ^ 2 := hsquare
    _ = ‖h‖ ^ 2 * ‖∇ φ.toFun x‖ ^ 2 := by ring
    _ = ‖h‖ ^ 2 * ∑ i : Fin n, (∇ φ.toFun x i) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq (∇ φ.toFun x)]
    _ = ‖h‖ ^ 2 * ∑ i : Fin n, ((∂[i] φ.toFun) x) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [PDE.gradient_apply_eq_partialDeriv]

/-- The squared first-derivative energy density of a test function. -/
noncomputable def testFunctionGradientEnergy
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) : ℝ :=
  ∑ i : Fin n, ((∂[i] φ.toFun) x) ^ 2

/-- The gradient energy density is a sum of squares, hence nonnegative. -/
@[simp]
theorem testFunctionGradientEnergy_nonneg
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    0 ≤ testFunctionGradientEnergy φ x :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The square of a coordinate derivative of a test function is continuous with compact
support. -/
private theorem partialDeriv_sq_testFunction (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
    Continuous (fun x : ℝ^n ↦ ((∂[i] φ.toFun) x) ^ 2) ∧
      HasCompactSupport (fun x : ℝ^n ↦ ((∂[i] φ.toFun) x) ^ 2) :=
  ⟨((φ.contDiff.of_le (by simp)).continuous_partialDeriv i).pow 2,
    (φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))).comp_left
      (g := fun y : ℝ ↦ y ^ 2) (by norm_num)⟩

/-- The gradient energy density of a test function is continuous. -/
theorem continuous_testFunctionGradientEnergy
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Continuous (testFunctionGradientEnergy φ) :=
  continuous_finsetSum _ fun i _ ↦ (partialDeriv_sq_testFunction φ i).1

/-- The gradient energy density of a test function has compact support. -/
theorem testFunctionGradientEnergy_hasCompactSupport
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    HasCompactSupport (testFunctionGradientEnergy φ) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) fun i _ ↦
    (partialDeriv_sq_testFunction φ i).2
  rw [Finset.sum_fn] at h
  exact h

/-- The gradient energy density of a test function is globally integrable. -/
theorem integrable_testFunctionGradientEnergy
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Integrable (testFunctionGradientEnergy φ) MeasureTheory.volume :=
  (continuous_testFunctionGradientEnergy φ).integrable_of_hasCompactSupport
    (testFunctionGradientEnergy_hasCompactSupport φ)

/-- Translation invariance of the global gradient-energy integral. -/
theorem integral_testFunctionGradientEnergy_add_right
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (a : ℝ^n) :
    (∫ x : ℝ^n, testFunctionGradientEnergy φ (x + a)) =
      ∫ x : ℝ^n, testFunctionGradientEnergy φ x := by
  exact integral_add_right_eq_self (testFunctionGradientEnergy φ) a

/-- The translated gradient energy is integrable on the product of a bounded
segment-parameter interval and Euclidean space.  This is the precise Fubini
hypothesis used in the global translation estimate. -/
theorem integrable_segment_testFunctionGradientEnergy
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    Integrable
      (Function.uncurry fun t : ℝ ↦ fun x : ℝ^n ↦
        testFunctionGradientEnergy φ (x + t • h))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        MeasureTheory.volume) := by
  let F : ℝ × ℝ^n → ℝ := fun p ↦ testFunctionGradientEnergy φ (p.2 + p.1 • h)
  have hFcont : Continuous F := (continuous_testFunctionGradientEnergy φ).comp
    (continuous_snd.add (continuous_fst.smul continuous_const))
  refine (MeasureTheory.integrable_prod_iff hFcont.aestronglyMeasurable).2
    ⟨.of_forall fun t ↦ ?_, ?_⟩
  · have hpres : MeasurePreserving (translationContinuousMap (t • h))
        (MeasureTheory.volume : Measure (ℝ^n)) MeasureTheory.volume := by
      simpa [domainMeasure] using translationMeasurePreserving (n := n) (t • h)
    simpa [F, Function.comp_def, translationContinuousMap] using
      hpres.integrable_comp_of_integrable (integrable_testFunctionGradientEnergy φ)
  · simp only [F, Real.norm_eq_abs, abs_of_nonneg (testFunctionGradientEnergy_nonneg φ _),
      integral_testFunctionGradientEnergy_add_right φ]
    exact MeasureTheory.integrableOn_const (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.uIoc (0 : ℝ) 1) (by simp)

/-- Averaging translated gradient energy along the unit segment leaves its
global integral unchanged. -/
theorem integral_intervalIntegral_testFunctionGradientEnergy
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    (∫ x : ℝ^n, ∫ t in (0 : ℝ)..1,
      testFunctionGradientEnergy φ (x + t • h)) =
      ∫ x : ℝ^n, testFunctionGradientEnergy φ x := by
  rw [← MeasureTheory.intervalIntegral_integral_swap
    (integrable_segment_testFunctionGradientEnergy φ h)]
  simp_rw [integral_testFunctionGradientEnergy_add_right φ]
  simp

/-- The pointwise segment estimate with the directional derivative replaced
by the full first-order Sobolev energy density. -/
theorem testFunction_translation_sq_le_norm_sq_mul_intervalIntegral_gradient_sq
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x h : ℝ^n) :
    (φ.toFun (x + h) - φ.toFun x) ^ 2 ≤
      ‖h‖ ^ 2 * ∫ t in (0 : ℝ)..1,
        testFunctionGradientEnergy φ (x + t • h) := by
  let γ : ℝ → ℝ^n := fun t ↦ x + t • h
  have hγ : Continuous γ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdir : Continuous fun t : ℝ ↦ ((fderiv ℝ φ.toFun (γ t)) h) ^ 2 :=
    (((φ.contDiff.continuous_fderiv (by simp)).comp hγ).clm_apply continuous_const).pow 2
  have henergy : Continuous fun t : ℝ ↦
      ‖h‖ ^ 2 * testFunctionGradientEnergy φ (γ t) :=
    continuous_const.mul ((continuous_testFunctionGradientEnergy φ).comp hγ)
  calc
    (φ.toFun (x + h) - φ.toFun x) ^ 2
        ≤ ∫ t in (0 : ℝ)..1, ((fderiv ℝ φ.toFun (γ t)) h) ^ 2 := by
          simpa [γ] using
            testFunction_translation_sq_le_intervalIntegral_directional_sq
              (n := n) φ x h
    _ ≤ ∫ t in (0 : ℝ)..1,
          ‖h‖ ^ 2 * testFunctionGradientEnergy φ (γ t) := by
      exact intervalIntegral.integral_mono (by norm_num)
        (hdir.intervalIntegrable 0 1) (henergy.intervalIntegrable 0 1) fun t ↦
          by simpa [testFunctionGradientEnergy] using
            testFunction_directional_sq_le_norm_sq_mul_sum_partial_sq
              (n := n) φ (γ t) h
    _ = ‖h‖ ^ 2 * ∫ t in (0 : ℝ)..1,
          testFunctionGradientEnergy φ (x + t • h) := by
      rw [intervalIntegral.integral_const_mul]

/-- The translation estimate for a smooth compactly supported function:
`∫ |φ(x+h)-φ(x)|² ≤ |h|² ∫ |Dφ(x)|²`. Compare step 4 of the proof of Evans §5.7, Theorem 1,
and §5.8.2, Theorem 3(i). -/
theorem integral_testFunction_translation_sq_le
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    (∫ x : ℝ^n, (φ.toFun (x + h) - φ.toFun x) ^ 2) ≤
      ‖h‖ ^ 2 * ∫ x : ℝ^n, testFunctionGradientEnergy φ x := by
  let segmentEnergy : ℝ^n → ℝ := fun x ↦
    ∫ t in (0 : ℝ)..1, testFunctionGradientEnergy φ (x + t • h)
  have hsegment : Integrable segmentEnergy MeasureTheory.volume := by
    simpa [segmentEnergy, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (integrable_segment_testFunctionGradientEnergy φ h).integral_prod_right
  have hrhs : Integrable (fun x : ℝ^n ↦ ‖h‖ ^ 2 * segmentEnergy x) MeasureTheory.volume :=
    hsegment.const_mul _
  have hlhs : Integrable (fun x : ℝ^n ↦ (φ.toFun (x + h) - φ.toFun x) ^ 2)
      MeasureTheory.volume := by
    refine hrhs.mono (((φ.contDiff.continuous.comp (continuous_id.add continuous_const)).sub
      φ.contDiff.continuous).pow 2).aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg_of_forall
        (by norm_num) fun _ ↦ testFunctionGradientEnergy_nonneg φ _))]
    exact testFunction_translation_sq_le_norm_sq_mul_intervalIntegral_gradient_sq (n := n) φ x h
  calc
    (∫ x : ℝ^n, (φ.toFun (x + h) - φ.toFun x) ^ 2)
        ≤ ∫ x : ℝ^n, ‖h‖ ^ 2 * segmentEnergy x := MeasureTheory.integral_mono hlhs hrhs fun x ↦
          testFunction_translation_sq_le_norm_sq_mul_intervalIntegral_gradient_sq (n := n) φ x h
    _ = ‖h‖ ^ 2 * ∫ x : ℝ^n, testFunctionGradientEnergy φ x := by
      rw [MeasureTheory.integral_const_mul,
        integral_intervalIntegral_testFunctionGradientEnergy φ h]

/-- The base coordinate of a globally bundled test function is represented
by the original smooth function. -/
theorem globalTestFunction_base_apply_ae
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (((testFunctionToH1 (n := n) (Ω := Set.univ)
        (⟨φ, subset_univ _⟩ : TestFunctionOn n Set.univ) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
      φ.toFun := by
  have hrep := mkWkpSpaceOnOfContDiff_apply_ae
    (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := (Set.univ : Set (ℝ^n)))
    (f := φ.toFun) φ.contDiff φ.hasCompactSupport (baseIndex n 1)
  simpa [testFunctionToH1, domainMeasure, iteratedPartialDeriv] using hrep

/-- The integral of the first-derivative energy is bounded by the complete
global `H¹` norm square. -/
theorem integral_testFunctionGradientEnergy_le_globalH1_norm_sq
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x : ℝ^n, testFunctionGradientEnergy φ x) ≤
      ‖testFunctionToH1 (n := n) (Ω := Set.univ)
        (⟨φ, subset_univ _⟩ : TestFunctionOn n Set.univ)‖ ^ 2 := by
  let U : W^{1,2}(ℝ^n) :=
    testFunctionToH1 (n := n) (Ω := Set.univ) (⟨φ, subset_univ _⟩ : TestFunctionOn n Set.univ)
  have hcoord (i : Fin n) :
      ‖((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex (n := n) i))‖ ^ 2 =
        ∫ x : ℝ^n, ((∂[i] φ.toFun) x) ^ 2 := by
    rw [show ‖((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex (n := n) i))‖ ^ 2 =
        ∫ x : ℝ^n, (((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex (n := n) i) :
          DerivLp n 2 Set.univ) x) ^ 2 by
      simpa [domainMeasure] using MeasureTheory.Lp.norm_sq_eq_integral_sq
        ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex (n := n) i))]
    have hrep := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := (2 : ℝ≥0∞))
      (Ω := (Set.univ : Set (ℝ^n))) (f := φ.toFun) φ.contDiff φ.hasCompactSupport
      (singleDerivIndex (n := n) i)
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [show (((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex (n := n) i) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
          fun x ↦ (∂[i] φ.toFun) x by
        simpa [U, testFunctionToH1, domainMeasure, iteratedPartialDeriv] using hrep] with x hx
    rw [hx]
  calc
    (∫ x : ℝ^n, testFunctionGradientEnergy φ x)
        = ∑ i : Fin n, ‖((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex (n := n) i))‖ ^ 2 := by
      simp only [testFunctionGradientEnergy, hcoord]
      exact MeasureTheory.integral_finsetSum _ fun i _ ↦
        (partialDeriv_sq_testFunction φ i).1.integrable_of_hasCompactSupport
          (partialDeriv_sq_testFunction φ i).2
    _ = ∑ a ∈ (Finset.univ.image (singleDerivIndex (n := n))),
          ‖((U : WkpAmbientOn n 1 2 Set.univ) a)‖ ^ 2 := by
      rw [Finset.sum_image fun i _ j _ hij ↦ by simpa using congrArg DerivIndex.toList hij]
    _ ≤ ∑ a : DerivIndex n 1, ‖((U : WkpAmbientOn n 1 2 Set.univ) a)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ sq_nonneg _
    _ = ‖U‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ (U : WkpAmbientOn n 1 2 Set.univ)).symm

/-- Norm form of the smooth translation estimate for the bundled base
coordinate of a global test function. -/
theorem norm_translateL2_sub_globalTestFunction_le
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    let U := testFunctionToH1 (n := n) (Ω := Set.univ)
      (⟨φ, subset_univ _⟩ : TestFunctionOn n Set.univ)
    ‖translateLp 2 h ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) -
        ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖ ≤
      ‖h‖ * ‖U‖ := by
  dsimp only
  let U : W^{1,2}(ℝ^n) :=
    testFunctionToH1 (n := n) (Ω := Set.univ) (⟨φ, subset_univ _⟩ : TestFunctionOn n Set.univ)
  let u0 : DerivLp n 2 Set.univ := (U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)
  have hrep : (u0 : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume] φ.toFun := by
    simpa [u0, U] using globalTestFunction_base_apply_ae φ
  have hpres : MeasurePreserving (translationContinuousMap h)
      (MeasureTheory.volume : Measure (ℝ^n)) MeasureTheory.volume := by
    simpa [domainMeasure] using translationMeasurePreserving (n := n) h
  have hrepTrans : (fun x ↦ u0 (x + h)) =ᵐ[MeasureTheory.volume] fun x ↦ φ.toFun (x + h) := by
    simpa [Function.comp_def, translationContinuousMap] using
      hpres.quasiMeasurePreserving.ae_eq_comp hrep
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  calc
    ‖translateLp 2 h u0 - u0‖ ^ 2 = ∫ x : ℝ^n, (φ.toFun (x + h) - φ.toFun x) ^ 2 := by
      rw [norm_translateL2_sub_sq_eq_integral]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hrep, hrepTrans] with x hx hxtrans
      rw [hx, hxtrans]
    _ ≤ ‖h‖ ^ 2 * ‖U‖ ^ 2 := (integral_testFunction_translation_sq_le φ h).trans
      (by gcongr; exact integral_testFunctionGradientEnergy_le_globalH1_norm_sq φ)
    _ = (‖h‖ * ‖U‖) ^ 2 := by ring


end Rellich
end GraphSpace
end SobolevSpace
