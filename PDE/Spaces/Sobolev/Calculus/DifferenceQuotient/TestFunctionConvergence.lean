/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Operators
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.MeasureTheory.DominatedLp
import PDE.Spaces.Sobolev.Compactness.Rellich.SmoothTranslation
import PDE.Spaces.Sobolev.Calculus.Translation.Energy

/-!
# Test-function convergence of difference quotients

For a smooth compactly supported `φ` on `ℝ^n`, the coordinate difference quotient is an
average of the partial derivative along the step,

`Dᵢʰ φ (x) = ∫₀¹ ∂ᵢφ (x + t h eᵢ) dt`,

and Jensen's (or Hölder's) inequality together with translation invariance of Lebesgue measure
gives the sharp bound `‖Dᵢʰ φ‖_{Lᵖ} ≤ ‖∂ᵢφ‖_{Lᵖ}` for every finite `p`, uniformly in
`h ≠ 0`. This is the smooth case of the difference-quotient estimate in Evans, PDE, §5.8.2; the
extension to Sobolev functions by density is carried out in
`DifferenceQuotient.WeakDerivative`. The same averaging formula, with dominated convergence on
the compact `1`-thickening of the support, gives strong `Lᵖ` convergence `Dᵢʰ φ → ∂ᵢφ` as
`h → 0`.

## Main results

* `testFunctionLp`, `partialTestFunctionLp` (and their `L²` specializations): a test function
  and its coordinate derivative as global `Lᵖ` vectors, with a.e. representatives.
* `forwardDifference_testFunction_eq_intervalIntegral_partial`: the averaging formula.
* `norm_differenceQuotientLp_testFunction_le`,
  `norm_differenceQuotientLp_testFunction_le_of_ne_top`: the sharp estimate
  `‖Dᵢʰ φ‖_p ≤ ‖∂ᵢφ‖_p`, stated for a real exponent `r ≥ 1` and for `p ≠ ∞`.
* `tendsto_differenceQuotientLp_testFunction`, `tendsto_differenceQuotientL2_testFunction`:
  strong convergence along any sequence of nonzero steps tending to zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2, Theorem 3(i), estimate (8), p. 292, and step 1 of its
  proof, pp. 292-293, which proves (8) for smooth `u` from
  `u(x + h eᵢ) - u(x) = h ∫₀¹ u_{x_i}(x + t h eᵢ) dt`. Evans's constant is unspecified; for test
  functions on `ℝ^n` the same step gives the constant one.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace
open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}

/-- A compactly supported smooth test function as a global `Lᵖ` vector. -/
noncomputable def testFunctionLp (p : ℝ≥0∞)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    DerivLp n p Set.univ := by
  have hm : MemLp φ.toFun p (domainMeasure n Set.univ) := by
    simpa [domainMeasure] using
      (φ.contDiff.continuous.memLp_of_hasCompactSupport
        (p := p) (μ := MeasureTheory.volume) φ.hasCompactSupport)
  exact hm.toLp φ.toFun

/-- The coordinate derivative of a test function as a global `Lᵖ` vector. -/
noncomputable def partialTestFunctionLp (p : ℝ≥0∞)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : DerivLp n p Set.univ :=
  testFunctionLp p
    (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ)

/-- The canonical `Lᵖ` representative of a test function agrees almost
everywhere with the original smooth function. -/
theorem testFunctionLp_apply_ae (p : ℝ≥0∞)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ((testFunctionLp p φ : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume] φ.toFun := by
  have hm : MemLp φ.toFun p (domainMeasure n Set.univ) := by
    simpa [domainMeasure] using
      (φ.contDiff.continuous.memLp_of_hasCompactSupport
        (p := p) (μ := MeasureTheory.volume) φ.hasCompactSupport)
  simpa [testFunctionLp, domainMeasure] using hm.coeFn_toLp

/-- The bundled coordinate derivative of a test function agrees almost
everywhere with its classical partial derivative. -/
theorem partialTestFunctionLp_apply_ae (p : ℝ≥0∞)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ((partialTestFunctionLp p i φ : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume]
        fun x ↦ (∂[i] φ.toFun) x := by
  change
    ((testFunctionLp p
        (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) φ) :
      DerivLp n p Set.univ) : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
      fun x ↦ (∂[i] φ.toFun) x
  filter_upwards
    [testFunctionLp_apply_ae p
      (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i (1 : ℝ)) φ)]
    with x hx
  refine hx.trans ?_
  change (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
    (∂[i] φ.toFun) x
  rw [testFunction_lineDerivCLM_apply]
  rfl

/-- A compactly supported smooth test function as a global `L²` vector. -/
noncomputable def testFunctionL2 (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    DerivLp n 2 Set.univ :=
  testFunctionLp 2 φ

/-- The coordinate derivative of a test function as a global `L²` vector. -/
noncomputable def partialTestFunctionL2
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : DerivLp n 2 Set.univ :=
  partialTestFunctionLp 2 i φ

/-- The `L²` representative of a test function agrees almost everywhere
with the original smooth function. -/
theorem testFunctionL2_apply_ae (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ((testFunctionL2 φ : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume] φ.toFun :=
  testFunctionLp_apply_ae 2 φ

/-- The `L²` representative of a test function's coordinate derivative
agrees almost everywhere with its classical partial derivative. -/
theorem partialTestFunctionL2_apply_ae
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ((partialTestFunctionL2 i φ : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume]
        fun x ↦ (∂[i] φ.toFun) x :=
  partialTestFunctionLp_apply_ae 2 i φ

/-- A smooth coordinate difference quotient is the average of the
corresponding partial derivative along the coordinate segment. -/
theorem forwardDifference_testFunction_eq_intervalIntegral_partial
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    forwardDifference i h φ.toFun x =
      ∫ t in (0 : ℝ)..1,
        (∂[i] φ.toFun)
          (x + t • coordinateStep i h) := by
  rw [forwardDifference,
    SobolevSpace.GraphSpace.Rellich.testFunction_translation_sub_eq_intervalIntegral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [coordinateStep]
  simp only [map_smul, smul_eq_mul]
  change h⁻¹ * (h * (∂[i] φ.toFun)
    (x + t • (h • EuclideanSpace.single i (1 : ℝ)))) =
      (∂[i] φ.toFun)
        (x + t • (h • EuclideanSpace.single i (1 : ℝ)))
  field_simp

private noncomputable abbrev partialDerivRpow
    (r : ℝ) (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (x : ℝ^n) : ℝ :=
  |(∂[i] φ.toFun) x| ^ r

private theorem continuous_partialDeriv_testFunction (i : Fin n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Continuous fun x : ℝ^n ↦ (∂[i] φ.toFun) x :=
  (PDE.contDiff_top_partialDeriv φ.contDiff).continuous

private theorem continuous_forwardDifference_testFunction (i : Fin n) (h : ℝ)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Continuous fun x : ℝ^n ↦ forwardDifference i h φ.toFun x :=
  ((φ.contDiff.continuous.comp (continuous_id.add continuous_const)).sub
    φ.contDiff.continuous).const_mul _

/-- The `Lᵖ` difference quotient of a test function is its classical forward difference. -/
private theorem differenceQuotientLp_testFunctionLp_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin n)
    (h : ℝ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (differenceQuotientLp p i h (testFunctionLp p φ) : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ forwardDifference i h φ.toFun x := by
  have hφ := testFunctionLp_apply_ae p φ
  have hpres : MeasurePreserving (translationContinuousMap (coordinateStep i h)) volume volume := by
    simpa [domainMeasure] using translationMeasurePreserving (n := n) (coordinateStep i h)
  have hφshift : (fun x ↦ (testFunctionLp p φ : ℝ^n → ℝ) (x + coordinateStep i h)) =ᵐ[volume]
      fun x ↦ φ.toFun (x + coordinateStep i h) := by
    simpa [Function.comp_def, translationContinuousMap] using
      hpres.quasiMeasurePreserving.ae_eq_comp hφ
  filter_upwards [differenceQuotientLp_apply_ae (n := n) p i h (testFunctionLp p φ), hφ, hφshift]
    with x hdqx hφx hφshiftx
  rw [hdqx, hφx, hφshiftx]
  rfl

private theorem continuous_partialDerivRpow
    {r : ℝ} (hr : 0 < r) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Continuous (partialDerivRpow r i φ) :=
  (continuous_partialDeriv_testFunction i φ).abs.rpow_const fun _ ↦ Or.inr hr.le

private theorem partialDerivRpow_hasCompactSupport
    {r : ℝ} (hr : 0 < r) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    HasCompactSupport (partialDerivRpow r i φ) := by
  have hp : HasCompactSupport fun x : ℝ^n ↦
      (∂[i] φ.toFun) x := by
    simpa [partialDeriv] using
      φ.hasCompactSupport.fderiv_apply
        (𝕜 := ℝ) (v := EuclideanSpace.single i (1 : ℝ))
  have hcomp := hp.comp_left
    (g := fun y : ℝ ↦ |y| ^ r)
    (by simp [Real.zero_rpow hr.ne'])
  change HasCompactSupport
    (fun x : ℝ^n ↦ |(∂[i] φ.toFun) x| ^ r)
  exact hcomp

private theorem integrable_partialDerivRpow
    {r : ℝ} (hr : 0 < r) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Integrable (partialDerivRpow r i φ) MeasureTheory.volume :=
  (continuous_partialDerivRpow hr i φ).integrable_of_hasCompactSupport
    (partialDerivRpow_hasCompactSupport hr i φ)

private theorem integral_partialDerivRpow_add_right
    {r : ℝ} (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (a : ℝ^n) :
    (∫ x : ℝ^n, partialDerivRpow r i φ (x + a)) =
      ∫ x : ℝ^n, partialDerivRpow r i φ x :=
  integral_add_right_eq_self (partialDerivRpow r i φ) a

private theorem integrable_segment_partialDerivRpow
    {r : ℝ} (hr : 0 < r) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    Integrable
      (Function.uncurry fun t : ℝ ↦ fun x : ℝ^n ↦
        partialDerivRpow r i φ (x + t • h))
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        MeasureTheory.volume) := by
  have hFcont : Continuous fun z : ℝ × ℝ^n ↦ partialDerivRpow r i φ (z.2 + z.1 • h) :=
    (continuous_partialDerivRpow hr i φ).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))
  refine (integrable_prod_iff hFcont.aestronglyMeasurable).2
    ⟨.of_forall fun t ↦ (integrable_partialDerivRpow hr i φ).comp_add_right (t • h), ?_⟩
  have heq : (fun t : ℝ ↦ ∫ x : ℝ^n, ‖partialDerivRpow r i φ (x + t • h)‖) =
      fun _ ↦ ∫ x : ℝ^n, partialDerivRpow r i φ x := funext fun t ↦
    (integral_congr_ae (.of_forall fun x ↦ Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _))
      ).trans (integral_partialDerivRpow_add_right i φ (t • h))
  rw [heq]
  exact integrableOn_const (by simp)

private theorem integral_intervalIntegral_partialDerivRpow
    {r : ℝ} (hr : 0 < r) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (h : ℝ^n) :
    (∫ x : ℝ^n, ∫ t in (0 : ℝ)..1,
      partialDerivRpow r i φ (x + t • h)) =
      ∫ x : ℝ^n, partialDerivRpow r i φ x := by
  rw [← MeasureTheory.intervalIntegral_integral_swap
    (integrable_segment_partialDerivRpow hr i φ h)]
  simp_rw [integral_partialDerivRpow_add_right i φ]
  simp

private theorem forwardDifference_testFunction_abs_rpow_le
    {r : ℝ} (hr : 1 ≤ r) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (x : ℝ^n) :
    |forwardDifference i h φ.toFun x| ^ r ≤
      ∫ t in (0 : ℝ)..1,
        partialDerivRpow r i φ (x + t • coordinateStep i h) := by
  rw [forwardDifference_testFunction_eq_intervalIntegral_partial i hh φ x]
  exact SobolevSpace.Translation.norm_intervalIntegral_rpow_le
    ((continuous_partialDeriv_testFunction i φ).comp
      (continuous_const.add (continuous_id.smul continuous_const))) hr

private theorem integral_forwardDifference_abs_rpow_le
    {r : ℝ} (hr : 1 ≤ r) (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x : ℝ^n, |forwardDifference i h φ.toFun x| ^ r) ≤
      ∫ x : ℝ^n, partialDerivRpow r i φ x := by
  let segment : ℝ^n → ℝ := fun x ↦
    ∫ t in (0 : ℝ)..1,
      partialDerivRpow r i φ (x + t • coordinateStep i h)
  have hprod :=
    integrable_segment_partialDerivRpow (zero_lt_one.trans_le hr) i φ
      (coordinateStep i h)
  have hsegment : Integrable segment MeasureTheory.volume := by
    have houter := hprod.integral_prod_right
    simpa [segment, intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using houter
  have hlhs : Integrable (fun x : ℝ^n ↦ |forwardDifference i h φ.toFun x| ^ r) :=
    hsegment.mono' ((continuous_forwardDifference_testFunction i h φ).abs.rpow_const
      fun _ ↦ Or.inr (zero_lt_one.trans_le hr).le).aestronglyMeasurable (.of_forall fun x ↦
        (Real.norm_of_nonneg (by positivity)).trans_le
          (forwardDifference_testFunction_abs_rpow_le hr i hh φ x))
  exact (integral_mono hlhs hsegment fun x ↦
    forwardDifference_testFunction_abs_rpow_le hr i hh φ x).trans_eq
      (integral_intervalIntegral_partialDerivRpow (zero_lt_one.trans_le hr) i φ _)

/-- For a test function `φ` on `ℝ^n`, a real exponent `r ≥ 1`, a coordinate `i` and a step
`h ≠ 0`, `‖D_i^h φ‖_{L^r} ≤ ‖∂_i φ‖_{L^r}`. This is the smooth case of Evans's estimate
(§5.8.2, Theorem 3(i)), with constant one. -/
theorem norm_differenceQuotientLp_testFunction_le
    {r : ℝ} (hr : 1 ≤ r) [Fact (1 ≤ ENNReal.ofReal r)]
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ‖differenceQuotientLp (ENNReal.ofReal r) i h
        (testFunctionLp (ENNReal.ofReal r) φ)‖ ≤
      ‖partialTestFunctionLp (ENNReal.ofReal r) i φ‖ := by
  have hr_pos : 0 < r := zero_lt_one.trans_le hr
  let q :=
    differenceQuotientLp (ENNReal.ofReal r) i h
      (testFunctionLp (ENNReal.ofReal r) φ)
  let d := partialTestFunctionLp (ENNReal.ofReal r) i φ
  have hqPow :=
    MeasureTheory.norm_toLp_rpow_eq_integral_abs hr_pos
      (MeasureTheory.Lp.memLp q)
  have hdPow :=
    MeasureTheory.norm_toLp_rpow_eq_integral_abs hr_pos
      (MeasureTheory.Lp.memLp d)
  rw [MeasureTheory.Lp.toLp_coeFn] at hqPow hdPow
  simp only [domainMeasure, Measure.restrict_univ] at hqPow hdPow
  have hqRep : (q : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ forwardDifference i h φ.toFun x :=
    differenceQuotientLp_testFunctionLp_ae _ i h φ
  have hdRep : (d : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ (∂[i] φ.toFun) x :=
    partialTestFunctionLp_apply_ae (ENNReal.ofReal r) i φ
  have hqIntegral : (∫ x : ℝ^n, |q x| ^ r) = ∫ x : ℝ^n, |forwardDifference i h φ.toFun x| ^ r :=
    integral_congr_ae (hqRep.fun_comp fun y : ℝ ↦ |y| ^ r)
  have hdIntegral : (∫ x : ℝ^n, |d x| ^ r) = ∫ x : ℝ^n, partialDerivRpow r i φ x :=
    integral_congr_ae (hdRep.fun_comp fun y : ℝ ↦ |y| ^ r)
  apply (Real.rpow_le_rpow_iff (norm_nonneg q) (norm_nonneg d) hr_pos).mp
  rw [hqPow, hdPow, hqIntegral, hdIntegral]
  exact integral_forwardDifference_abs_rpow_le hr i hh φ

/-- Exponent-native form of the sharp smooth difference-quotient estimate.
The hypothesis `p ≠ ∞` is the exact finiteness assumption; no chosen real
presentation of `p` is exposed to callers. -/
theorem norm_differenceQuotientLp_testFunction_le_of_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ‖differenceQuotientLp p i h (testFunctionLp p φ)‖ ≤
      ‖partialTestFunctionLp p i φ‖ := by
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 1 ≤ r ∧ ENNReal.ofReal r = p := by
    refine ⟨p.toReal, ?_, ENNReal.ofReal_toReal hp_top⟩
    simpa using
      ENNReal.toReal_mono hp_top (show (1 : ℝ≥0∞) ≤ p from Fact.out)
  exact norm_differenceQuotientLp_testFunction_le
    (n := n) (r := r) hr i hh φ

/-- Strong `Lᵖ` convergence of smooth test-function difference quotients
to the corresponding partial derivative for every finite exponent. -/
theorem tendsto_differenceQuotientLp_testFunction
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0) :
    Filter.Tendsto
      (fun m ↦ differenceQuotientLp p i (h m) (testFunctionLp p φ))
      Filter.atTop (nhds (partialTestFunctionLp p i φ)) := by
  obtain ⟨C, hφlip⟩ := exists_lipschitzWith_testFunction φ
  let K : Set (ℝ^n) := Metric.cthickening 1 (tsupport φ.toFun)
  have hK : IsCompact K := φ.hasCompactSupport.cthickening
  let F : ℕ → ℝ^n → ℝ := fun m x ↦ forwardDifference i (h m) φ.toFun x - (∂[i] φ.toFun) x
  let bound : ℝ^n → ℝ := K.indicator fun _ ↦ 2 * (C : ℝ)
  -- once `|h m| ≤ 1`, the error `F m` vanishes off `K` and is bounded by `2 C` on it
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
    hzero.eventually (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)
  have hdom (m : ℕ) (hm : |h m| ≤ 1) : ∀ᵐ x ∂volume, ‖F m x‖ ≤ ‖bound x‖ := .of_forall fun x ↦ by
    by_cases hx : x ∈ K
    · rw [show bound x = 2 * (C : ℝ) by simp [bound, hx],
        Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 * C by positivity)]
      calc ‖F m x‖ ≤ ‖forwardDifference i (h m) φ.toFun x‖ + ‖(∂[i] φ.toFun) x‖ :=
            norm_sub_le _ _
        _ ≤ C + C := add_le_add (norm_forwardDifference_testFunction_le i φ hφlip (hne m) x)
            (norm_partialDeriv_testFunction_le i φ hφlip x)
        _ = 2 * (C : ℝ) := by ring
    · simpa [F, bound, hx] using
        forwardDifference_sub_partial_eq_zero_of_not_mem_cthickening i φ hm hx
  have hFmeas (m : ℕ) : AEStronglyMeasurable (F m) volume :=
    ((continuous_forwardDifference_testFunction i (h m) φ).sub
      (continuous_partialDeriv_testFunction i φ)).aestronglyMeasurable
  have hFeLp : Filter.Tendsto (fun m ↦ eLpNorm (F m) p volume) Filter.atTop (𝓝 0) := by
    refine (Filter.tendsto_add_atTop_iff_nat N).1 ?_
    simpa only [sub_zero] using tendsto_Lp_of_tendsto_ae_of_ae_norm_le Fact.out hp_top
      (fun m ↦ hFmeas (m + N)) MemLp.zero
      (memLp_indicator_const p hK.measurableSet.nullMeasurableSet (2 * (C : ℝ))
        (Or.inr hK.measure_lt_top.ne))
      (fun m ↦ hdom (m + N) (by simpa [Real.dist_eq] using hN (m + N) (Nat.le_add_left N m)))
      (.of_forall fun x ↦ by
        simpa [F, Function.comp_def] using ((tendsto_forwardDifference_testFunction_sequence
          i φ x h hzero hne).sub_const ((∂[i] φ.toFun) x)).comp (Filter.tendsto_add_atTop_nat N))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  simp only [domainMeasure, Measure.restrict_univ]
  refine hFeLp.congr fun m ↦ eLpNorm_congr_ae ?_
  filter_upwards [differenceQuotientLp_testFunctionLp_ae p i (h m) φ,
    partialTestFunctionLp_apply_ae p i φ] with x h₁ h₂
  simp only [F, Pi.sub_apply, h₁, h₂]

/-- Strong `L²` convergence of smooth test-function difference quotients
to the corresponding partial derivative. -/
theorem tendsto_differenceQuotientL2_testFunction
    (i : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (h : ℕ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0) :
    Filter.Tendsto
      (fun m ↦ differenceQuotientLp 2 i (h m) (testFunctionL2 φ))
      Filter.atTop (nhds (partialTestFunctionL2 i φ)) := by
  simpa [testFunctionL2, partialTestFunctionL2] using
    tendsto_differenceQuotientLp_testFunction
      (n := n) 2 (by norm_num) i φ h hzero hne
end SobolevSpace.GraphSpace.DifferenceQuotient
