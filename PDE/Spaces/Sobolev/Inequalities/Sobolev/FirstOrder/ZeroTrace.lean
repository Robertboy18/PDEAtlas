/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.FDeriv.Operators
import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.OneDimensionalCritical
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global

/-!
# Finite-exponent Sobolev embeddings for zero-trace functions

The general `W^{1,p}_0` gradient bound for `1 ≤ p < n` is proved in
`ZeroTrace.FiniteExponent`, including `p = 1`. We also treat `H¹₀`
in the critical and supercritical dimensions.

On a measurable domain of finite measure, zero extension puts `H¹₀` functions
in the global Sobolev space. Here `H¹₀` is the closure of compactly supported
smooth test functions in the Sobolev graph space; this definition also makes
sense when the domain is not open. Every finite `q ≥ 2` is allowed in dimensions
one and two; in dimensions above two the range ends at `q = 2n/(n-2)`, inclusively.
No boundedness, openness or boundary charts are required by these embeddings.

Finite measure permits lowering the derivative exponent of the zero extension.
In dimension one this reaches the global `W¹,¹` bounded-representative theorem;
in dimension two it reaches a subcritical exponent with the requested target q.
The closed graph theorem then makes the inclusion a bounded linear map.
In dimension one, the fundamental theorem of calculus also gives the explicit
bound `‖u‖q ≤ |Ω|^(1/2 + 1/q) ‖u'‖₂`, and hence an operator-norm bound for
the same inclusion. A supplied estimate on supported test functions transfers to the
completed inclusion with the same constant. In dimensions above two, the coordinate
endpoint inequality gives the explicit critical bound `2n(n-1)/(n-2)`; in dimension
three this is `12` for the inclusion into `L⁶`. Lowering the target exponent
introduces the finite-volume Hölder factor `|Ω|^(1/q-1/r)`. These quantitative
versions are useful for validated PDE solutions.
-/

open PDE (iteratedPartialDeriv)
open scoped Sobolev

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace SobolevSpace.GraphSpace

open ZeroTrace

variable {n : ℕ} {Ω : Set (ℝ^n)}


/-- All coordinates of the zero extension vanish outside the domain. -/
theorem hasCoordinateSupportIn_zeroExtendH10 (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) :
    HasCoordinateSupportIn Ω (zeroExtendH10 hΩ u) := by
  intro a
  have hzero := zeroExtendH10_coordinate_apply_ae hΩ u a
  change Ω.indicator _ =ᵐ[domainMeasure n Set.univ] _
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hzero] with x hx
  by_cases hxΩ : x ∈ Ω
  · simp [hxΩ]
  · simpa [hxΩ] using hx.symm

/-- Restricting the base representative of the zero extension recovers
the canonical `L²(Ω)` displacement coordinate. -/
theorem zeroExtendH10_base_ae (hΩ : MeasurableSet Ω) (u : H¹₀(Ω)) :
    (baseRepresentative (zeroExtendH10 hΩ u)) =ᵐ[domainMeasure n Ω]
      (baseCoordCLM u : ℝ^n → ℝ) := by
  have hzero := ae_restrict_of_ae (s := Ω)
    (zeroExtendH10_coordinate_apply_ae hΩ u (baseIndex n 1))
  filter_upwards [hzero, ae_restrict_mem hΩ] with x hx hxΩ
  simpa only [baseRepresentative, baseCoordCLM_apply, indicator_of_mem hxΩ] using hx

/-- On a measurable domain of finite measure, every finite exponent `q ≥ 2`
in the H¹₀ Sobolev range is attained. The endpoint `q = 2n/(n-2)` is included
when `n ≥ 3`; in dimensions one and two there is no finite upper bound on `q`. -/
theorem memLp_baseCoord_of_sobolevExponent
    (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)]
    {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2))
    (u : H¹₀(Ω)) :
    MemLp (baseCoordCLM u : ℝ^n → ℝ) (ENNReal.ofReal q) (domainMeasure n Ω) := by
  let U := zeroExtendH10 hΩ u
  have hUbase := zeroExtendH10_base_ae hΩ u
  have hsupport : HasCoordinateSupportIn Ω U :=
    hasCoordinateSupportIn_zeroExtendH10 hΩ u
  have hfinite : domainMeasure n Set.univ Ω ≠ ∞ := by
    simpa only [domainMeasure, Measure.restrict_univ, Measure.restrict_apply_univ] using
      (measure_lt_top (domainMeasure n Ω) Set.univ).ne
  have hmeasure : domainMeasure n Ω ≤ (volume : Measure (ℝ^n)) :=
    Measure.restrict_le_self
  by_cases hq2 : q = 2
  · simpa only [hq2, ENNReal.ofReal_ofNat] using Lp.memLp (baseCoordCLM u)
  have hq2' : 2 < q := lt_of_le_of_ne hq (Ne.symm hq2)
  by_cases hn2 : 2 < n
  · have hnR : (2 : ℝ) < n := by exact_mod_cast hn2
    have : Fact (1 ≤ ((2 : NNReal) : ℝ≥0∞)) := ⟨by norm_num⟩
    have hglobal := Inequalities.memLp_higherOrderExponent
      (p := (2 : NNReal))
      (by norm_num) hn (by simpa using hnR) U
    have hdom := MemLp.ae_eq hUbase (hglobal.mono_measure hmeasure)
    apply hdom.mono_exponent
    apply ENNReal.ofReal_le_coe.mpr
    rw [Inequalities.higherOrderExponent_coe (by simpa using hnR)]
    simpa only [NNReal.coe_ofNat, Nat.cast_one, one_mul] using hnq hn2
  · have hn12 : n = 1 ∨ n = 2 := by omega
    rcases hn12 with rfl | rfl
    · let V : W^{1,1}(ℝ^1) :=
        lowerExponentOfFiniteMeasureSupport (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          Ω hfinite U hsupport
      have hVbase : baseRepresentative V =ᵐ[volume] baseRepresentative U := by
        simpa only [V, domainMeasure, Measure.restrict_univ, baseRepresentative] using
          lowerExponentOfFiniteMeasureSupport_apply_ae
            (by norm_num : (1 : ℝ≥0∞) ≤ 2) Ω hfinite U hsupport (baseIndex 1 1)
      obtain ⟨F, hF, _⟩ := CriticalOneDimensional.exists_boundedContinuousRepresentative V
      have hFdomBase : (fun x ↦ F x) =ᵐ[domainMeasure 1 Ω]
          baseRepresentative U :=
        MeasureTheory.ae_restrict_of_ae (s := Ω) (hF.trans hVbase)
      have hFdom : (fun x ↦ F x) =ᵐ[domainMeasure 1 Ω]
          (baseCoordCLM u : ℝ^1 → ℝ) :=
        hFdomBase.trans hUbase
      have hFmem : MemLp (fun x ↦ F x) (ENNReal.ofReal q) (domainMeasure 1 Ω) := by
        refine (memLp_const (‖F‖ : ℝ)).mono' F.continuous.aestronglyMeasurable ?_
        exact Eventually.of_forall fun x ↦ F.norm_coe_le_norm x
      exact MemLp.ae_eq hFdom hFmem
    · let qn : NNReal := ⟨q, by linarith⟩
      have hqn : 0 < (qn : ℝ) := by
        change 0 < q
        exact lt_trans (by norm_num) hq2'
      let s : NNReal := Inequalities.pStarPreimage 2 qn
      have hs1 : (1 : NNReal) ≤ s :=
        Inequalities.one_le_pStarPreimage (by norm_num) hq2'
      have hs2 : (s : ℝ) < 2 :=
        Inequalities.pStarPreimage_lt_dimension (by norm_num) hqn
      have hsE2 : (s : ℝ≥0∞) ≤ 2 := by exact_mod_cast hs2.le
      have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
      let V : W^{1,(s : ℝ≥0∞)}(ℝ^2) :=
        lowerExponentOfFiniteMeasureSupport hsE2 Ω hfinite U hsupport
      have hVbase : baseRepresentative V =ᵐ[volume] baseRepresentative U := by
        simpa only [V, domainMeasure, Measure.restrict_univ, baseRepresentative] using
          lowerExponentOfFiniteMeasureSupport_apply_ae
            hsE2 Ω hfinite U hsupport (baseIndex 2 1)
      have hexponent : Inequalities.higherOrderExponent 2 1 s = qn := by
        have he : Inequalities.higherOrderExponent 2 1 s = Inequalities.pStar 2 s := by
          simp only [Inequalities.higherOrderExponent, Inequalities.pStar,
            Nat.cast_one, one_mul]
        rw [he]
        exact Inequalities.pStar_pStarPreimage (by norm_num) hqn
      have hglobal := Inequalities.memLp_higherOrderExponent
         hs1 (by norm_num) (by simpa using hs2) V
      rw [hexponent] at hglobal
      have heq : (qn : ℝ≥0∞) = ENNReal.ofReal q :=
        ENNReal.coe_nnreal_eq qn
      rw [heq] at hglobal
      have hVdom : baseRepresentative V =ᵐ[domainMeasure 2 Ω]
          baseRepresentative U :=
        MeasureTheory.ae_restrict_of_ae (s := Ω) hVbase
      exact MemLp.ae_eq (hVdom.trans hUbase) (hglobal.mono_measure hmeasure)

/-- The bounded inclusion `H¹₀(Ω) → Lᑫ(Ω)` for finite `q ≥ 2` in the Sobolev
range on a measurable domain of finite measure. Zero extension supplies the
`Lᑫ` integrability. The closed graph theorem then lifts the canonical `L²(Ω)`
displacement map to `Lᑫ(Ω)`, with a finite but unspecified operator norm. -/
def h10LpEmbedding
    (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)]
    {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    H¹₀(Ω) →L[ℝ] DerivLp n (ENNReal.ofReal q) Ω := by
  letI : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let J : H¹₀(Ω) →L[ℝ] Lp ℝ 2 (domainMeasure n Ω) := baseCoordCLM
  exact J.liftLpExponent (𝕜 := ℝ) (q := ENNReal.ofReal q)
    (memLp_baseCoord_of_sobolevExponent hn hΩ hq hnq)

/-- The new exponent changes the normed space, not the displacement
represented by the function. -/
theorem h10LpEmbedding_ae
    (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)]
    {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2))
    (u : H¹₀(Ω)) :
    (h10LpEmbedding hn hΩ hq hnq u : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  exact (baseCoordCLM (n := n) (Ω := Ω)).coeFn_liftLpExponent (𝕜 := ℝ)
    (q := ENNReal.ofReal q) (memLp_baseCoord_of_sobolevExponent hn hΩ hq hnq) u

/-- A supplied estimate on supported test functions gives the same gradient bound
for the completed zero-boundary inclusion. -/
theorem norm_h10LpEmbedding_apply_le_of_testFunction_bound
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) (C : ℝ≥0)
    (hbound : ∀ φ : TestFunctionOn n Ω,
      eLpNorm φ.1.toFun (ENNReal.ofReal q) volume ≤
        C * eLpNorm (fderiv ℝ φ.1.toFun) 2 volume)
    (u : H¹₀(Ω)) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding hn hΩ hq hnq u‖ ≤ C * ‖gradientCLM u‖ := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  apply isClosed_property denseRange_testFunctionToH10Linear
    (isClosed_le (by fun_prop) (by fun_prop)) ?_ u
  intro φ
  let U := testFunctionToH10 φ
  change ‖h10LpEmbedding hn hΩ hq hnq U‖ ≤ C * ‖gradientCLM U‖
  have hJ := (h10LpEmbedding_ae hn hΩ hq hnq U).trans
    (baseCoordCLM_testFunction_apply_ae φ)
  have hJnorm : eLpNorm φ.1.toFun (ENNReal.ofReal q) volume =
      eLpNorm (h10LpEmbedding hn hΩ hq hnq U) (ENNReal.ofReal q)
        (domainMeasure n Ω) := by
    calc
      _ = eLpNorm φ.1.toFun (ENNReal.ofReal q) (domainMeasure n Ω) :=
        (eLpNorm_restrict_eq_of_support_subset φ.1.contDiff.continuous.aestronglyMeasurable
          ((subset_tsupport _).trans φ.2)).symm
      _ = _ := (eLpNorm_congr_ae hJ).symm
  have hd : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      derivCoordCLM i U x = (∂[i] φ.1.toFun) x :=
    ae_all_iff.mpr fun i ↦ derivCoordCLM_testFunction_apply_ae i φ
  have hg : (gradientCLM U : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω]
      gradient φ.1.toFun := by
    filter_upwards [gradientCLM_apply_ae U, hd] with x hx hy
    ext i
    exact (hx i).trans ((hy i).trans (PDE.gradient_apply_eq_partialDeriv _ _ _).symm)
  have hderivnorm : eLpNorm (fderiv ℝ φ.1.toFun) 2 volume =
      eLpNorm (gradientCLM U) 2 (domainMeasure n Ω) := by
    calc
      _ = eLpNorm (fderiv ℝ φ.1.toFun) 2 (domainMeasure n Ω) := by
        apply (eLpNorm_restrict_eq_of_support_subset
          (φ.1.contDiff.continuous_fderiv (by simp)).aestronglyMeasurable ?_).symm
        intro x hx
        by_contra hout
        exact hx (fderiv_of_notMem_tsupport ℝ (fun h ↦ hout (φ.2 h)))
      _ = _ := by
        apply eLpNorm_congr_norm_ae
          (φ.1.contDiff.continuous_fderiv (by simp)).aestronglyMeasurable
          (Lp.memLp _).aestronglyMeasurable
        filter_upwards [hg] with x hx
        rw [hx]
        exact ((InnerProductSpace.toDual ℝ (ℝ^n)).symm.norm_map _).symm
  have h := hbound φ
  rw [hJnorm, hderivnorm] at h
  have hfinite : (C : ℝ≥0∞) * eLpNorm (gradientCLM U) 2 (domainMeasure n Ω) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top _)
  have hreal := ENNReal.toReal_mono hfinite h
  simpa only [Lp.norm_def, ENNReal.toReal_mul, ENNReal.coe_toReal] using hreal

/-- A supplied estimate on supported test functions bounds the operator norm
of the completed inclusion by the same constant. -/
theorem norm_h10LpEmbedding_le_of_testFunction_bound
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {q : ℝ} (hq : 2 ≤ q)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) (C : ℝ≥0)
    (hbound : ∀ φ : TestFunctionOn n Ω,
      eLpNorm φ.1.toFun (ENNReal.ofReal q) volume ≤
        C * eLpNorm (fderiv ℝ φ.1.toFun) 2 volume) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding hn hΩ hq hnq‖ ≤ C := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  apply (h10LpEmbedding hn hΩ hq hnq).opNorm_le_bound C.property
  intro u
  exact (norm_h10LpEmbedding_apply_le_of_testFunction_bound hn hΩ hq hnq C hbound u).trans
    (mul_le_mul_of_nonneg_left (gradientCLM_norm_le u) C.property)

/-- The critical zero-boundary inclusion has an explicit dimension-dependent
constant, obtained from the coordinate endpoint inequality. -/
theorem norm_h10LpEmbedding_le_critical
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 2 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] :
    have : Fact (1 ≤ ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 2))) := by
      constructor
      apply ENNReal.one_le_ofReal.mpr
      have hnR : (2 : ℝ) < n := by exact_mod_cast hn
      apply (le_div_iff₀ (sub_pos.mpr hnR)).mpr
      linarith
    ‖h10LpEmbedding (by omega) hΩ
      (q := 2 * (n : ℝ) / ((n : ℝ) - 2))
      (by
        have hnR : (2 : ℝ) < n := by exact_mod_cast hn
        apply (le_div_iff₀ (sub_pos.mpr hnR)).mpr
        linarith)
      (fun _ ↦ le_rfl)‖ ≤
      2 * (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 2) := by
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  have hq : 2 ≤ 2 * (n : ℝ) / ((n : ℝ) - 2) := by
    apply (le_div_iff₀ (sub_pos.mpr hnR)).mpr
    linarith
  have : Fact (1 ≤ ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 2))) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hC : 0 ≤ 2 * (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 2) :=
    div_nonneg (mul_nonneg (by positivity) hn1) (by linarith)
  have h := norm_h10LpEmbedding_le_of_testFunction_bound (by omega) hΩ hq
    (fun _ ↦ le_rfl)
    (Real.toNNReal (2 * (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 2))) ?_
  · simpa only [Real.coe_toNNReal _ hC] using h
  intro φ
  have hφ := Inequalities.eLpNorm_le_explicit_mul_eLpNorm_fderiv_pStar
    (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport
    (p := 2) (by norm_num) (by omega) (by simpa using hnR)
  have hpStar : (Inequalities.pStar n 2 : ℝ≥0∞) =
      ENNReal.ofReal (2 * (n : ℝ) / ((n : ℝ) - 2)) := by
    simp only [Inequalities.pStar, NNReal.coe_ofNat, ENNReal.ofReal, mul_comm]
  have hcoeff : (n : ℝ≥0) *
      (2 * ((n : ℝ) - 1) / ((n : ℝ) - 2)).toNNReal =
      (2 * (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 2)).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_natCast,
      Real.coe_toNNReal _ (div_nonneg (mul_nonneg (by norm_num) hn1) (by linarith)),
      Real.coe_toNNReal _ hC]
    ring
  simpa [hpStar, hcoeff] using hφ

/-- Lowering the target exponent costs exactly the finite-measure Hölder factor. -/
theorem norm_h10LpEmbedding_apply_le_of_le
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {q r : ℝ} (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2))
    (hnr : 2 < n → r ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) (hqr : q ≤ r)
    (u : H¹₀(Ω)) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    have : Fact (1 ≤ ENNReal.ofReal r) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding hn hΩ hq hnq u‖ ≤
      (volume Ω).toReal ^ (1 / q - 1 / r) * ‖h10LpEmbedding hn hΩ hr hnr u‖ := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have : Fact (1 ≤ ENNReal.ofReal r) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let Uq := h10LpEmbedding hn hΩ hq hnq u
  let Ur := h10LpEmbedding hn hΩ hr hnr u
  change ‖Uq‖ ≤ (volume Ω).toReal ^ (1 / q - 1 / r) * ‖Ur‖
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  have hexp : 0 ≤ 1 / q - 1 / r := sub_nonneg.mpr
    (one_div_le_one_div_of_le hq0 hqr)
  have heq : (Uq : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (Ur : ℝ^n → ℝ) :=
    (h10LpEmbedding_ae hn hΩ hq hnq u).trans
      (h10LpEmbedding_ae hn hΩ hr hnr u).symm
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := domainMeasure n Ω) (f := (Ur : ℝ^n → ℝ))
    (p := ENNReal.ofReal q) (q := ENNReal.ofReal r)
    (ENNReal.ofReal_le_ofReal hqr) (Lp.memLp Ur).aestronglyMeasurable
  rw [← eLpNorm_congr_ae (p := ENNReal.ofReal q) heq] at h
  simp only [ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal hr0.le] at h
  have hfinite : eLpNorm (Ur : ℝ^n → ℝ) (ENNReal.ofReal r)
      (domainMeasure n Ω) *
      (domainMeasure n Ω) Set.univ ^ (1 / q - 1 / r) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top Ur)
      (ENNReal.rpow_ne_top_of_nonneg hexp (measure_lt_top _ Set.univ).ne)
  have hreal := ENNReal.toReal_mono hfinite h
  change (eLpNorm (Uq : ℝ^n → ℝ) (ENNReal.ofReal q)
    (domainMeasure n Ω)).toReal ≤
      (volume Ω).toReal ^ (1 / q - 1 / r) *
        (eLpNorm (Ur : ℝ^n → ℝ) (ENNReal.ofReal r)
          (domainMeasure n Ω)).toReal
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  have hmeasure : (domainMeasure n Ω) Set.univ = volume Ω := by
    simp only [domainMeasure, Measure.restrict_apply_univ]
  rw [hmeasure] at hreal
  exact hreal.trans_eq (mul_comm _ _)

/-- Lowering the target exponent of the zero-boundary inclusion costs the
finite-volume Hölder factor in its operator norm. -/
theorem norm_h10LpEmbedding_le_of_le
    {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n) (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {q r : ℝ} (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hnq : 2 < n → q ≤ 2 * (n : ℝ) / ((n : ℝ) - 2))
    (hnr : 2 < n → r ≤ 2 * (n : ℝ) / ((n : ℝ) - 2)) (hqr : q ≤ r) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    have : Fact (1 ≤ ENNReal.ofReal r) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding hn hΩ hq hnq‖ ≤
      (volume Ω).toReal ^ (1 / q - 1 / r) * ‖h10LpEmbedding hn hΩ hr hnr‖ := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have : Fact (1 ≤ ENNReal.ofReal r) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  refine (h10LpEmbedding hn hΩ hq hnq).opNorm_le_bound (by positivity) ?_
  intro u
  calc
    _ ≤ (volume Ω).toReal ^ (1 / q - 1 / r) *
        ‖h10LpEmbedding hn hΩ hr hnr u‖ :=
      norm_h10LpEmbedding_apply_le_of_le hn hΩ hq hr hnq hnr hqr u
    _ ≤ (volume Ω).toReal ^ (1 / q - 1 / r) *
        (‖h10LpEmbedding hn hΩ hr hnr‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        ((h10LpEmbedding hn hΩ hr hnr).le_opNorm u) (by positivity)
    _ = _ := by rw [mul_assoc]

private theorem norm_h10LpEmbedding_testFunction_le_one
    {Ω : Set (ℝ^1)} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure 1 Ω)] {q : ℝ} (hq : 2 ≤ q)
    (φ : TestFunctionOn 1 Ω) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding (by omega) hΩ hq (by omega) (testFunctionToH10 φ)‖ ≤
      (volume Ω).toReal ^ (1 / 2 + 1 / q : ℝ) *
        ‖derivCoordCLM 0 (testFunctionToH10 φ)‖ := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let μ := domainMeasure 1 Ω
  let d : ℝ^1 → ℝ := ∂[0] φ.1.toFun
  have hdcont : Continuous d := by
    simpa [d, iteratedPartialDeriv] using
      (PDE.contDiff_top_iteratedPartialDeriv φ.1.contDiff [0]).continuous
  have hdsupp : Function.support d ⊆ Ω :=
    (subset_tsupport d).trans <|
      (tsupport_fderiv_apply_subset ℝ
        (f := φ.1.toFun) (EuclideanSpace.single 0 (1 : ℝ))).trans φ.2
  have hdRestrict : eLpNorm d 1 volume = eLpNorm d 1 μ := by
    exact (eLpNorm_restrict_eq_of_support_subset
      hdcont.aestronglyMeasurable hdsupp).symm
  have hd2 : eLpNorm d 2 μ =
      eLpNorm (derivCoordCLM 0 (testFunctionToH10 φ)) 2 μ :=
    (eLpNorm_congr_ae (derivCoordCLM_testFunction_apply_ae 0 φ)).symm
  have hdCompare : (eLpNorm d 1 volume).toReal ≤
      ‖derivCoordCLM 0 (testFunctionToH10 φ)‖ * (volume Ω).toReal ^ (1 / 2 : ℝ) := by
    rw [hdRestrict]
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := μ) (f := d) (p := 1) (q := 2) (by norm_num)
      hdcont.aestronglyMeasurable
    rw [hd2] at h
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
      show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] at h
    have hfinite : eLpNorm (derivCoordCLM 0 (testFunctionToH10 φ)) 2 μ *
        μ Set.univ ^ (1 / 2 : ℝ) ≠ ∞ :=
      ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_lt_top μ Set.univ).ne)
    have hreal := ENNReal.toReal_mono hfinite h
    simpa only [Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_rpow,
      μ, domainMeasure, Measure.restrict_apply_univ] using hreal
  have hpoint (x : ℝ^1) : ‖φ.1.toFun x‖ ≤
      ‖derivCoordCLM 0 (testFunctionToH10 φ)‖ * (volume Ω).toReal ^ (1 / 2 : ℝ) :=
    (CriticalOneDimensional.norm_apply_le_eLpNorm_partialDeriv_one_toReal
      φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport x).trans hdCompare
  have hJ := (h10LpEmbedding_ae (by omega) hΩ hq (by omega)
    (testFunctionToH10 φ)).trans (baseCoordCLM_testFunction_apply_ae φ)
  have hbound := Lp.norm_le_of_ae_bound (by positivity)
    (hJ.mono fun x hx ↦ hx ▸ hpoint x)
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ (volume Ω).toReal ^ (1 / q : ℝ) *
        (‖derivCoordCLM 0 (testFunctionToH10 φ)‖ *
          (volume Ω).toReal ^ (1 / 2 : ℝ)) := by
      simpa only [measureUnivNNReal, μ, domainMeasure, Measure.restrict_apply_univ,
        ENNReal.coe_toNNReal_eq_toReal, NNReal.coe_rpow, ENNReal.toReal_ofReal hq0.le,
        one_div] using hbound
    _ = _ := by
      rw [Real.rpow_add_of_nonneg ENNReal.toReal_nonneg (by positivity) (by positivity)]
      ring

/-- In one dimension, the zero-boundary inclusion has the explicit estimate
`‖u‖q ≤ |Ω|^(1/2 + 1/q) ‖u'‖₂`. The fundamental theorem of calculus controls
the uniform norm, and Hölder supplies the two powers of the domain's measure.
No boundary regularity or boundedness assumption is needed. -/
theorem norm_h10LpEmbedding_apply_le_one
    {Ω : Set (ℝ^1)} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure 1 Ω)] {q : ℝ} (hq : 2 ≤ q)
    (u : H¹₀(Ω)) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding (by omega) hΩ hq (by omega) u‖ ≤
      (volume Ω).toReal ^ (1 / 2 + 1 / q : ℝ) * ‖derivCoordCLM 0 u‖ := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  apply isClosed_property denseRange_testFunctionToH10Linear
    (isClosed_le (by fun_prop) (by fun_prop)) ?_ u
  exact fun φ ↦ norm_h10LpEmbedding_testFunction_le_one hΩ hq φ

/-- Operator-norm bound for the one-dimensional zero-boundary inclusion.
In particular, a unit-measure domain gives an inclusion of norm at most one
for every finite target exponent `q ≥ 2`. -/
theorem norm_h10LpEmbedding_le_one
    {Ω : Set (ℝ^1)} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure 1 Ω)] {q : ℝ} (hq : 2 ≤ q) :
    have : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ‖h10LpEmbedding (by omega) hΩ hq (by omega)‖ ≤
      (volume Ω).toReal ^ (1 / 2 + 1 / q : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  refine (h10LpEmbedding (by omega) hΩ hq (by omega)).opNorm_le_bound
    (by positivity) ?_
  intro u
  exact (norm_h10LpEmbedding_apply_le_one hΩ hq u).trans
    (mul_le_mul_of_nonneg_left (derivCoordCLM_norm_le 0 u) (by positivity))

end SobolevSpace.GraphSpace
