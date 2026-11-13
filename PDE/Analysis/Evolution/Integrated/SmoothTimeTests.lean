/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
public import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.ReflectedExtension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Extending smooth initial-value tests to endpoint time tests

Smooth tests supported in `(-∞, b)` may be nonzero at `a`. Their weak identity therefore
retains the initial term. For scalar L² states and loads, this identity extends to every
`TimeTest a b`.

The proof constructs the integral primitive of the load. To identify the state with this
primitive, it tests with a cutoff backward primitive of each function in `C_c^∞((a,b))`
and applies Mathlib's distributional fundamental lemma. This is a density argument;
neither the desired time-test identity nor an absolutely continuous state is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace PDE.Analysis.Evolution

/-- An interior smooth test has a smooth antiderivative supported before the terminal
endpoint. On the entire closed interval its derivative is the negative of the test.
The antiderivative may be nonzero at the initial endpoint. -/
theorem exists_smooth_initial_test_antiderivative
    {a b : ℝ} (hab : a < b) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ Ioo a b) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Iio b ∧
      ∀ t ∈ Icc a b, HasDerivAt ζ (-ψ t) t := by
  classical
  let K : Set ℝ := insert a (tsupport ψ)
  obtain ⟨c, hcK, hcmax⟩ := (hcs.isCompact.insert a).exists_isGreatest
    (show K.Nonempty from ⟨a, mem_insert _ _⟩)
  have hcb : c < b := by
    rcases hcK with rfl | hc
    exacts [hab, (hsupp hc).2]
  have hψzero (t : ℝ) (ht : c < t) : ψ t = 0 := image_eq_zero_of_notMem_tsupport fun hmem ↦
    (not_le_of_gt ht) (hcmax (mem_insert_of_mem _ hmem))
  let q : ℝ → ℝ := fun t ↦ ∫ r in t..b, ψ r
  have hqd (t : ℝ) : HasDerivAt q (-ψ t) t :=
    intervalIntegral.integral_hasDerivAt_left (hψ.continuous.intervalIntegrable t b)
      hψ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuous.continuousAt
  have hqs : ContDiff ℝ (⊤ : ℕ∞) q := contDiff_infty_iff_deriv.mpr
    ⟨fun t ↦ (hqd t).differentiableAt, by rw [funext fun t ↦ (hqd t).deriv]; exact hψ.neg⟩
  have hqzero (t : ℝ) (ht : c < t) : q t = 0 :=
    intervalIntegral.integral_zero_ae <| ae_of_all _ fun r hr ↦ hψzero r <|
      (mem_uIoc.mp hr).elim (fun h ↦ ht.trans h.1) fun h ↦ hcb.trans h.1
  obtain ⟨χ, hχsupp, _hχone, hχnear, _hχrange⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_Iio isCompact_Icc (show Icc a c ⊆ Iio b from fun t ht ↦ ht.2.trans_lt hcb)
  let ζ : ℝ → ℝ := fun t ↦ χ t * q t
  refine ⟨ζ, χ.contDiff.mul hqs, χ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans hχsupp, fun t ht ↦ (hqd t).congr_of_eventuallyEq ?_⟩
  rcases le_or_gt t c with htc | hct
  · filter_upwards [hχnear t ⟨ht.1, htc⟩] with r hr
    change χ r * q r = q r
    rw [show χ r = 1 from hr, one_mul]
  · filter_upwards [isOpen_Ioi.mem_nhds hct] with r hr
    change χ r * q r = q r
    rw [hqzero r hr, mul_zero]

/-- The primitive of the zero-extended L² load is absolutely continuous on `[a,b]`
and has derivative equal to the original load almost everywhere in `(a,b]`. -/
private theorem primitive_regularity
    {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) (x : ℝ) :
    let w : ℝ → ℝ := fun t ↦ x + ∫ r in a..t, intervalZeroExtension a b g r
    AbsolutelyContinuousOnInterval w a b ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt w (g t) t := by
  let ν := volume.restrict (Ioc a b)
  let g₀ := intervalZeroExtension a b g
  let w : ℝ → ℝ := fun t ↦ x + ∫ r in a..t, g₀ r
  have hg₀ : Integrable g₀ volume :=
    integrable_intervalZeroExtension (hg.integrable (by norm_num))
  have hwAC : AbsolutelyContinuousOnInterval w a b := by
    exact ((LipschitzWith.const x).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (absolutelyContinuousOnInterval_intervalIntegral_any_base hg₀ a a b)
  have hwd : ∀ᵐ t ∂ν, HasDerivAt w (g t) t := by
    have hd := ae_hasDerivAt_intervalIntegral_any_base hg₀ a a b
    have hdr : ∀ᵐ t ∂ν, t ∈ uIcc a b →
        HasDerivAt (fun s ↦ ∫ r in a..s, g₀ r) (g₀ t) t :=
      hd.filter_mono (ae_mono (show ν ≤ volume from Measure.restrict_le_self))
    filter_upwards [hdr, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    have ht' : t ∈ uIcc a b := by
      simpa only [uIcc_of_le hab.le] using Ioc_subset_Icc_self hmem
    have h := (hasDerivAt_const t x).add (ht ht')
    apply HasDerivAt.of_isLittleO
    simpa only [w, g₀, intervalZeroExtension, indicator_of_mem hmem,
      Pi.add_apply, zero_add, smul_eq_mul] using h.isLittleO
  exact ⟨hwAC, hwd⟩

/-- The smooth compactly supported initial-value identity determines the scalar
primitive of the load almost everywhere. Tests are supported before `b`, not strictly
inside `(a,b)`, so the initial value is determined rather than lost. -/
theorem ae_eq_primitive_of_smooth_initial_tests
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) (x : ℝ)
    (hweak : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Iio b →
      -(∫ t, u t * deriv ζ t ∂volume.restrict (Ioc a b)) =
        (∫ t, g t * ζ t ∂volume.restrict (Ioc a b)) + x * ζ a) :
    u =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ x + ∫ r in a..t, intervalZeroExtension a b g r := by
  let ν := volume.restrict (Ioc a b)
  let g₀ := intervalZeroExtension a b g
  let w : ℝ → ℝ := fun t ↦ x + ∫ r in a..t, g₀ r
  obtain ⟨hwAC, hwd⟩ := primitive_regularity hab hg x
  have hwa : w a = x := by simp [w]
  have hwLp : MemLp w 2 ν :=
    memLp_restrict_Ioc_of_continuousOn
      (by simpa only [uIcc_of_le hab.le] using hwAC.continuousOn)
  have hwtest : ∀ τ : TimeTest a b,
      -(∫ t, w t * τ.derivFun t ∂ν) =
        (∫ t, g t * τ.toFun t ∂ν) + x * τ.toFun a := by
    intro τ
    have h := τ.integrationByParts_inner (u := w) (du := g) hab.le (1 : ℝ) hwAC hwd
    simpa only [Real.inner_apply, mul_one, intervalIntegral.integral_of_le hab.le,
      hwa] using h
  have huw : IntegrableOn (fun t ↦ u t - w t) (Ioo a b) volume :=
    ((hu.integrable (by norm_num)).sub (hwLp.integrable (by norm_num))).mono_measure
      (volume.restrict_mono_set Ioo_subset_Ioc_self)
  have hzero : ∀ᵐ t ∂volume, t ∈ Ioo a b → u t - w t = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero huw.locallyIntegrableOn
      fun ψ hψ hcs hsupp ↦ ?_
    obtain ⟨ζ, hζ, hζcs, hζsupp, hζd⟩ :=
      exists_smooth_initial_test_antiderivative hab ψ hψ hcs hsupp
    let τ : TimeTest a b := {
      toFun := ζ
      derivFun := deriv ζ
      hasDerivAt := fun t _ ↦ (hζ.differentiable (by simp)).differentiableAt.hasDerivAt
      memLp := memLp_restrict_Ioc_of_continuousOn hζ.continuous.continuousOn
      derivMemLp := memLp_restrict_Ioc_of_continuousOn
        (hζ.continuous_deriv (by simp)).continuousOn
      final_zero := image_eq_zero_of_notMem_tsupport fun ht ↦ lt_irrefl b (hζsupp ht) }
    have hder (f : ℝ → ℝ) : (∫ t, f t * deriv ζ t ∂ν) = -(∫ t, f t * ψ t ∂ν) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [(hζd t (Ioc_subset_Icc_self ht)).deriv, mul_neg]
    have h₁ := hweak ζ hζ hζcs hζsupp
    have h₂ : -(∫ t, w t * deriv ζ t ∂ν) = (∫ t, g t * ζ t ∂ν) + x * ζ a := hwtest τ
    rw [hder, neg_neg] at h₁ h₂
    have hψLp : MemLp ψ 2 ν := memLp_restrict_Ioc_of_continuousOn hψ.continuous.continuousOn
    have hout (t : ℝ) (ht : t ∉ Ioc a b) : ψ t • (u t - w t) = 0 := by
      rw [image_eq_zero_of_notMem_tsupport fun hs ↦ ht (Ioo_subset_Ioc_self (hsupp hs)),
        zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    calc (∫ t in Ioc a b, ψ t • (u t - w t)) = (∫ t, u t * ψ t ∂ν) - ∫ t, w t * ψ t ∂ν := by
          rw [← integral_sub (f := fun t ↦ u t * ψ t) (g := fun t ↦ w t * ψ t)
            (hu.integrable_mul hψLp) (hwLp.integrable_mul hψLp)]
          exact integral_congr_ae (ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; ring)
      _ = 0 := sub_eq_zero.mpr (h₁.trans h₂.symm)
  change u =ᵐ[ν] w
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume b)] with t ht hmem hne
  exact sub_eq_zero.mp (ht ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩)

/-- Extend the standard smooth initial-value identity to all endpoint time tests.
The state and load are merely L²; no representative continuity or time derivative is
assumed. The conclusion retains exactly the prescribed initial boundary term. -/
theorem timeTest_identity_of_smooth_initial_tests
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) (x : ℝ)
    (hweak : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Iio b →
      -(∫ t, u t * deriv ζ t ∂volume.restrict (Ioc a b)) =
        (∫ t, g t * ζ t ∂volume.restrict (Ioc a b)) + x * ζ a)
    (τ : TimeTest a b) :
    -(∫ t, u t * τ.derivFun t ∂volume.restrict (Ioc a b)) =
      (∫ t, g t * τ.toFun t ∂volume.restrict (Ioc a b)) + x * τ.toFun a := by
  let ν := volume.restrict (Ioc a b)
  let g₀ := intervalZeroExtension a b g
  let w : ℝ → ℝ := fun t ↦ x + ∫ r in a..t, g₀ r
  obtain ⟨hwAC, hwd⟩ := primitive_regularity hab hg x
  have h := τ.integrationByParts_inner (u := w) (du := g) hab.le (1 : ℝ) hwAC hwd
  have hwa : w a = x := by simp [w]
  have hae := ae_eq_primitive_of_smooth_initial_tests hab hu hg x hweak
  have heq : (∫ t, u t * τ.derivFun t ∂ν) = ∫ t, w t * τ.derivFun t ∂ν := by
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    rw [show u t = w t from ht]
  rw [heq]
  simpa only [Real.inner_apply, mul_one, intervalIntegral.integral_of_le hab.le, hwa] using h

end PDE.Analysis.Evolution
