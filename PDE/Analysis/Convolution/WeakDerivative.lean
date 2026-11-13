/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Transferring a weak kernel derivative through convolution

A compact source needs no classical derivative when differentiating its potential.
Fubini transfers one weak derivative from a locally integrable kernel to its
convolution. Compact support of the source and test function limits the kernel
to a compact set, so local kernel integrability is sufficient.

## Main results

* `integral_convolution_mul_eq`: pairing a convolution with a compact test function equals
  pairing the kernel with the translated test.
* `hasWeakDerivativeOn_convolution`: a weak coordinate derivative of a kernel gives the
  corresponding weak derivative of its convolution with an integrable compact source.
* `integral_convolution_mul_eq_add`: the pairing written with the kernel variable outside the
  translated source pairing.
* `hasWeakDerivativeOn_convolution_right`: a weak coordinate derivative of a compact source
  passes through convolution with any locally integrable kernel.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Filter Topology Set
open scoped Convolution Distributions

/-- For `K` locally integrable, `F` integrable with compact support and `φ` continuous with compact
support, `(x, y) ↦ K (x - y) F y φ x` is integrable on `ℝ^n × ℝ^n`. -/
private theorem integrable_convolution_pairing
    {n : ℕ} {K F φ : ℝ^n → ℝ} (hK : LocallyIntegrable K volume)
    (hF : Integrable F volume) (hFc : HasCompactSupport F)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : ℝ^n × ℝ^n ↦ K (p.1 - p.2) * F p.2 * φ p.1)
      (volume.prod volume) := by
  obtain ⟨R, _, hR⟩ := hFc.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨S, _, hS⟩ := hφc.isCompact.isBounded.exists_pos_norm_le
  let B := Metric.closedBall (0 : ℝ^n) (R + S)
  have hKi : Integrable (B.indicator K) volume := by
    exact (integrable_indicator_iff measurableSet_closedBall).2
      (hK.integrableOn_isCompact (isCompact_closedBall _ _))
  have hprod := hF.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hKi
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hi := hprod.mul_bdd hφ.aestronglyMeasurable.comp_fst
    (Eventually.of_forall fun p ↦ hM p.1)
  apply hi.congr
  filter_upwards with p
  by_cases hFzero : F p.2 = 0
  · simp [hFzero]
  by_cases hφzero : φ p.1 = 0
  · simp [hφzero]
  have hFp : p.2 ∈ tsupport F := subset_tsupport F hFzero
  have hφp : p.1 ∈ tsupport φ := subset_tsupport φ hφzero
  have hp : p.1 - p.2 ∈ B := by
    change dist (p.1 - p.2) 0 ≤ R + S
    rw [dist_zero_right]
    exact (norm_sub_le _ _).trans (by linarith [hR _ hFp, hS _ hφp])
  simp only [ContinuousLinearMap.mul_apply', indicator_of_mem hp]
  ring

/-- Fubini pairs a convolution with a compact test function by translating that test
against the kernel. Only local integrability of the kernel is needed. -/
theorem integral_convolution_mul_eq
    {n : ℕ} {K F φ : ℝ^n → ℝ} (hK : LocallyIntegrable K volume)
    (hF : Integrable F volume) (hFc : HasCompactSupport F)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    (∫ x, (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F) x * φ x) =
      ∫ y, F y * (∫ x, K (x - y) * φ x) := by
  have hi := integrable_convolution_pairing hK hF hFc hφ hφc
  calc
    (∫ x, (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F) x * φ x) =
        ∫ x, ∫ y, K (x - y) * F y * φ x := by
      congr 1
      funext x
      rw [convolution_mul_swap]
      exact (integral_mul_const (φ x) (fun y ↦ K (x - y) * F y)).symm
    _ = ∫ y, ∫ x, K (x - y) * F y * φ x := integral_integral_swap hi
    _ = ∫ y, F y * (∫ x, K (x - y) * φ x) := by
      congr 1
      funext y
      rw [← integral_const_mul]
      congr 1
      funext x
      ring

/-- A weak coordinate derivative of a kernel gives the corresponding weak derivative
of its convolution with an integrable compact source. Continuity of the two convolutions
is enough to supply their local integrability. -/
theorem hasWeakDerivativeOn_convolution
    {n : ℕ} {K G F : ℝ^n → ℝ} (i : Fin n)
    (hweak : SobolevSpace.HasWeakDerivativeOn univ [i] K G)
    (hF : Integrable F volume) (hFc : HasCompactSupport F)
    (hP : Continuous (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F))
    (hD : Continuous (G ⋆[ContinuousLinearMap.mul ℝ ℝ] F)) :
    SobolevSpace.HasWeakDerivativeOn univ [i]
      (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F)
      (G ⋆[ContinuousLinearMap.mul ℝ ℝ] F) := by
  have hK := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  have hG := locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  refine ⟨hP.locallyIntegrable.locallyIntegrableOn univ,
    hD.locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro φ _
  have hdφ : Continuous (∂[i] φ.toFun) := by
    change Continuous (fun x ↦ fderiv ℝ φ.toFun x (EuclideanSpace.single i (1 : ℝ)))
    exact (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport (∂[i] φ.toFun) :=
    φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hidentity (y : ℝ^n) :
      (∫ x, K (x - y) * (∂[i] φ.toFun) x) =
        -(∫ x, G (x - y) * φ x) := by
    let ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ) :=
      { toFun := fun z ↦ φ (y + z)
        contDiff' := φ.contDiff.comp (contDiff_const.add contDiff_id)
        hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft y)
        tsupport_subset' := subset_univ _ }
    have hψderiv (z : ℝ^n) : (∂[i] ψ.toFun) z = (∂[i] φ.toFun) (y + z) :=
      congrFun (partialDeriv_comp_add_left i φ.toFun y) z
    have hw := hweak.integral_identity ψ (subset_univ _)
    simp only [SobolevSpace.domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
      List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul,
      hψderiv] at hw
    rw [← integral_add_left_eq_self (fun x ↦ K (x - y) * (∂[i] φ.toFun) x) y,
      ← integral_add_left_eq_self (fun x ↦ G (x - y) * φ x) y]
    simpa only [add_sub_cancel_left, ψ] using hw
  simp only [SobolevSpace.domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
    List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul]
  rw [integral_convolution_mul_eq hK hF hFc hdφ hdφc,
    integral_convolution_mul_eq (φ := φ.toFun) hG hF hFc
      φ.contDiff.continuous φ.hasCompactSupport]
  simp_rw [hidentity, mul_neg]
  rw [integral_neg]
  rfl

/-- For `K` locally integrable, `F` integrable with compact support and `φ` continuous with compact
support, `(x, y) ↦ F x K y φ (x + y)` is integrable on `ℝ^n × ℝ^n`. -/
private theorem integrable_convolution_add_pairing
    {n : ℕ} {K F φ : ℝ^n → ℝ} (hK : LocallyIntegrable K volume)
    (hF : Integrable F volume) (hFc : HasCompactSupport F)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun p : ℝ^n × ℝ^n ↦ F p.1 * K p.2 * φ (p.1 + p.2))
      (volume.prod volume) := by
  obtain ⟨R, _, hR⟩ := hFc.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨S, _, hS⟩ := hφc.isCompact.isBounded.exists_pos_norm_le
  let B := Metric.closedBall (0 : ℝ^n) (R + S)
  have hKi : Integrable (B.indicator K) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (hK.integrableOn_isCompact (isCompact_closedBall _ _))
  obtain ⟨M, hM⟩ := hφ.bounded_above_of_compact_support hφc
  have hi := (hF.mul_prod hKi).mul_bdd
    (hφ.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
    (Eventually.of_forall fun p ↦ hM (p.1 + p.2))
  apply hi.congr
  filter_upwards with p
  by_cases hFzero : F p.1 = 0
  · simp [hFzero]
  by_cases hφzero : φ (p.1 + p.2) = 0
  · simp [hφzero]
  have hFp : p.1 ∈ tsupport F := subset_tsupport F hFzero
  have hφp : p.1 + p.2 ∈ tsupport φ := subset_tsupport φ hφzero
  have hp : p.2 ∈ B := by
    change dist p.2 0 ≤ R + S
    rw [dist_zero_right]
    have ht : ‖p.2‖ ≤ ‖p.1 + p.2‖ + ‖p.1‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (p.1 + p.2) p.1
    linarith [hR _ hFp, hS _ hφp]
  simp only [indicator_of_mem hp]
  rfl

/-- Fubini can instead leave the kernel variable outside the translated source pairing.
This form transfers a weak source derivative without requiring kernel smoothness. -/
theorem integral_convolution_mul_eq_add
    {n : ℕ} {K F φ : ℝ^n → ℝ} (hK : LocallyIntegrable K volume)
    (hF : Integrable F volume) (hFc : HasCompactSupport F)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    (∫ x, (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F) x * φ x) =
      ∫ z, K z * (∫ y, F y * φ (y + z)) := by
  rw [integral_convolution_mul_eq hK hF hFc hφ hφc]
  calc
    (∫ y, F y * (∫ x, K (x - y) * φ x)) =
        ∫ y, ∫ z, F y * K z * φ (y + z) := by
      congr 1
      funext y
      rw [← integral_add_left_eq_self (fun x ↦ K (x - y) * φ x) y,
        ← integral_const_mul]
      congr 1
      funext z
      rw [add_sub_cancel_left]
      ring
    _ = ∫ z, ∫ y, F y * K z * φ (y + z) :=
      integral_integral_swap (integrable_convolution_add_pairing hK hF hFc hφ hφc)
    _ = ∫ z, K z * (∫ y, F y * φ (y + z)) := by
      congr 1
      funext z
      rw [← integral_const_mul]
      congr 1
      funext y
      ring

/-- A compact source's weak coordinate derivative passes through convolution with
any locally integrable kernel. Source and derivative are integrable and compact;
no classical source derivative or smooth extension across a jump is assumed. -/
theorem hasWeakDerivativeOn_convolution_right
    {n : ℕ} {K F G : ℝ^n → ℝ} (i : Fin n)
    (hK : LocallyIntegrable K volume)
    (hweak : SobolevSpace.HasWeakDerivativeOn univ [i] F G)
    (hF : Integrable F volume) (hFc : HasCompactSupport F)
    (hG : Integrable G volume) (hGc : HasCompactSupport G)
    (hP : Continuous (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F))
    (hD : Continuous (K ⋆[ContinuousLinearMap.mul ℝ ℝ] G)) :
    SobolevSpace.HasWeakDerivativeOn univ [i]
      (K ⋆[ContinuousLinearMap.mul ℝ ℝ] F)
      (K ⋆[ContinuousLinearMap.mul ℝ ℝ] G) := by
  refine ⟨hP.locallyIntegrable.locallyIntegrableOn univ,
    hD.locallyIntegrable.locallyIntegrableOn univ, ?_⟩
  intro φ _
  have hdφ : Continuous (∂[i] φ.toFun) := by
    change Continuous (fun x ↦ fderiv ℝ φ.toFun x (EuclideanSpace.single i (1 : ℝ)))
    exact (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport (∂[i] φ.toFun) :=
    φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hidentity (z : ℝ^n) :
      (∫ y, F y * (∂[i] φ.toFun) (y + z)) =
        -(∫ y, G y * φ.toFun (y + z)) := by
    let ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ) :=
      { toFun := fun y ↦ φ.toFun (y + z)
        contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
        hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight z)
        tsupport_subset' := subset_univ _ }
    have hψderiv (y : ℝ^n) : (∂[i] ψ.toFun) y = (∂[i] φ.toFun) (y + z) :=
      congrFun (partialDeriv_comp_add_right i φ.toFun z) y
    simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
      List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul, hψderiv, ψ] using
      hweak.integral_identity ψ (subset_univ _)
  simp only [SobolevSpace.domainMeasure, Measure.restrict_univ, iteratedPartialDeriv,
    List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul]
  rw [integral_convolution_mul_eq_add hK hF hFc hdφ hdφc,
    integral_convolution_mul_eq_add (φ := φ.toFun) hK hG hGc
      φ.contDiff.continuous φ.hasCompactSupport]
  simp_rw [hidentity, mul_neg]
  rw [integral_neg]

end PDE.Analysis
