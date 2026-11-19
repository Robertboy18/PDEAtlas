/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Distributional limits of local difference quotients

For a test function compactly supported in an open set, sufficiently small translations
remain in that set. Its quotient pairings can therefore be computed using the zero
extension of the local Lp function, even when the original function has no Lp control
outside that set. Discrete integration by parts then gives the distributional limit.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set Rellich TopologicalSpace
open SobolevSpace.Extension.Lp
open scoped Distributions ENNReal Topology

variable {n : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [ENNReal.HolderConjugate p q]

/-- A supported test sees the same quotient pairing after extending the local input by
zero, provided its support and its translate stay inside the domain. -/
theorem integral_local_quotient_eq_pairing {V : Set (ℝ^n)} (hV : MeasurableSet V)
    {u : ℝ^n → ℝ} (hu : MemLp u p (domainMeasure n V))
    (i : Fin n) (h : ℝ) (s : DerivLp n p V)
    (hs : (s : ℝ^n → ℝ) =ᵐ[domainMeasure n V] forwardDifference i h u)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ V)
    (hshift : MapsTo (fun x ↦ x + coordinateStep i h) (tsupport φ.toFun) V) :
    (∫ x, s x * φ.toFun x ∂domainMeasure n V) =
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n univ) p q
        (differenceQuotientLp p i h (zeroExtendLp hV (hu.toLp u)))
        (testFunctionLp q φ) := by
  let f := zeroExtendLp hV (hu.toLp u)
  have hf : ∀ᵐ x ∂volume, x ∈ V → f x = u x :=
    (ae_restrict_iff' hV).mp
      ((zeroExtendLp_agree_ae hV (hu.toLp u)).trans hu.coeFn_toLp)
  have hft := (measurePreserving_add_right (volume : Measure (ℝ^n))
    (coordinateStep i h)).quasiMeasurePreserving.ae hf
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  have htest :
      (∫ x, (ContinuousLinearMap.mul ℝ ℝ)
          (differenceQuotientLp p i h f x) (testFunctionLp q φ x)
          ∂domainMeasure n univ) =
        ∫ x, differenceQuotientLp p i h f x * φ.toFun x ∂domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    filter_upwards [testFunctionLp_apply_ae q φ] with x hx
    simp only [ContinuousLinearMap.mul_apply', hx]
  rw [htest]
  have hrestrict :
      (∫ x, differenceQuotientLp p i h f x * φ.toFun x ∂domainMeasure n univ) =
        ∫ x, differenceQuotientLp p i h f x * φ.toFun x ∂domainMeasure n V := by
    simp only [domainMeasure, Measure.restrict_univ]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hzero : φ.toFun x = 0 := by
      by_contra hne
      exact hx (hφ (subset_tsupport _ hne))
    simp only [hzero, mul_zero]
  rw [hrestrict]
  apply integral_congr_ae
  filter_upwards [hs, hf.filter_mono (ae_mono Measure.restrict_le_self),
    hft.filter_mono (ae_mono Measure.restrict_le_self),
    (differenceQuotientLp_apply_ae p i h f).filter_mono
      (ae_mono Measure.restrict_le_self)] with x hsx hfx hftx hdq
  by_cases hx : φ.toFun x = 0
  · simp only [hx, mul_zero]
  · have hxs := subset_tsupport φ.toFun hx
    rw [hsx, hdq]
    simp only [forwardDifference, hfx (hφ hxs), hftx (hshift hxs)]

/-- Quotients represented in the local Lp space converge distributionally to the derivative
of the local input. Only Lp integrability on the open test domain is required. -/
theorem tendsto_integral_local_quotient {V : Set (ℝ^n)} (hV : IsOpen V)
    (hq : q ≠ ∞) {u : ℝ^n → ℝ} (hu : MemLp u p (domainMeasure n V))
    (i : Fin n) (h : ℕ → ℝ) (hzero : Tendsto h atTop (𝓝 0)) (hne : ∀ m, h m ≠ 0)
    (s : ℕ → DerivLp n p V)
    (hs : ∀ m, (s m : ℝ^n → ℝ) =ᵐ[domainMeasure n V] forwardDifference i (h m) u)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ V) :
    Tendsto (fun m ↦ ∫ x, s m x * φ.toFun x ∂domainMeasure n V) atTop
      (𝓝 (-(∫ x, u x * (∂[i] φ.toFun) x ∂domainMeasure n V))) := by
  let f := zeroExtendLp hV.measurableSet (hu.toLp u)
  have htest := tendsto_differenceQuotientLp_testFunction q hq i φ
    (fun m ↦ -(h m)) (by simpa using hzero.neg) (fun m ↦ neg_ne_zero.mpr (hne m))
  have ht := (((ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (domainMeasure n univ) p q f).continuous.tendsto (partialTestFunctionLp q i φ)
    ).comp htest
  have hlimit :
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n univ) p q
          f (partialTestFunctionLp q i φ) =
        ∫ x, u x * (∂[i] φ.toFun) x ∂domainMeasure n V := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    calc
      (∫ x, (ContinuousLinearMap.mul ℝ ℝ) (f x)
          (partialTestFunctionLp q i φ x) ∂domainMeasure n univ) =
          ∫ x, f x * (∂[i] φ.toFun) x ∂domainMeasure n univ := by
        simp only [domainMeasure, Measure.restrict_univ]
        apply integral_congr_ae
        filter_upwards [partialTestFunctionLp_apply_ae q i φ] with x hx
        simp only [ContinuousLinearMap.mul_apply', hx]
      _ = ∫ x, hu.toLp u x * (∂[i] φ.toFun) x ∂domainMeasure n V := by
        simpa only [domainMeasure, Measure.restrict_univ] using
          integral_zeroExtendLp_mul hV.measurableSet _ _
      _ = _ := integral_congr_ae (hu.coeFn_toLp.mono fun _ hx ↦
        congrArg (fun a ↦ a * _) hx)
  have hpair : Tendsto (fun m ↦ (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (domainMeasure n univ) p q (differenceQuotientLp p i (h m) f)
        (testFunctionLp q φ)) atTop
      (𝓝 (-(∫ x, u x * (∂[i] φ.toFun) x ∂domainMeasure n V))) := by
    simpa only [Function.comp_def, lpPairing_differenceQuotientLp_left, hlimit] using ht.neg
  obtain ⟨δ, hδ, hδV⟩ :=
    φ.hasCompactSupport.exists_thickening_subset_open hV hφ
  apply hpair.congr'
  have hhδ : ∀ᶠ m in atTop, |h m| < δ :=
    (hzero.abs).eventually (by simpa using gt_mem_nhds hδ)
  filter_upwards [hhδ] with m hm
  symm
  apply integral_local_quotient_eq_pairing hV.measurableSet hu i (h m) (s m) (hs m) φ hφ
  intro x hx
  apply hδV
  apply Metric.mem_thickening_iff.mpr
  exact ⟨x, hx, by simpa only [dist_eq_norm, add_sub_cancel_left, norm_coordinateStep] using hm⟩

end SobolevSpace.GraphSpace.DifferenceQuotient

namespace SobolevSpace.GraphSpace

open MeasureTheory Set DifferenceQuotient
open scoped InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Discrete Green's formula across a domain boundary: extend the local
factor by zero, then move the signed backward quotient onto it as a forward
whole-space quotient.  No boundary term appears because the extension is
literally zero off `Ω`. -/
theorem inner_neg_restrict_backwardDifference_eq
    (hΩmeas : MeasurableSet Ω)
    (k : Fin n) {h : ℝ} (hh : h ≠ 0)
    (q : DerivLp n 2 Ω) (w : DerivLp n 2 Set.univ) :
    inner ℝ q
        (-restrictDerivLp (n := n) (p := 2)
          (subset_univ Ω) (differenceQuotientLp 2 k (-h) w)) =
      inner ℝ
        (differenceQuotientLp 2 k h
          (Extension.Lp.zeroExtendLp
            (n := n) (p := 2) (Ω := Ω) hΩmeas q)) w := by
  rw [inner_neg_right]
  rw [← Extension.Lp.inner_zeroExtendLp_eq_inner_restrict]
  exact (inner_differenceQuotientL2_left k hh
    (Extension.Lp.zeroExtendLp
      (n := n) (p := 2) (Ω := Ω) hΩmeas q) w).symm

end SobolevSpace.GraphSpace
