/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm
public import PDE.Analysis.Integration.PositiveTime.Cutoff
import PDE.DistributionTheory.TestFunction
import PDE.FDeriv.Calculus

/-!
# Interior cutoffs and Fubini for initial-boundary weak forms

Scalar and Banach-valued weak equations share the same time cutoff and
measure-preserving identification of positive spacetime with a product.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw

/-- Multiplication by the initial transition gives an interior test. -/
def interiorCutoffTest (φ : InitialValueTestFunction)
    {ε : ℝ} (hε : 0 < ε) : 𝓓^{1}(forwardHalfSpace, ℝ) where
  toFun p := initialTimeCutoff ε (p 0) * φ p
  contDiff' := by
    have hproj : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 0) :=
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).contDiff
    exact ((contDiff_initialTimeCutoff ε).of_le (by norm_num) |>.comp hproj).mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' := by
    have hs : tsupport (fun p : ℝ^2 ↦ initialTimeCutoff ε (p 0) * φ p) ⊆
        {p : ℝ^2 | ε ≤ p 0} := by
      apply closure_minimal _ (isClosed_le continuous_const
        (EuclideanSpace.proj (0 : Fin 2)).continuous)
      intro p hp
      by_contra hn
      change ¬ ε ≤ p 0 at hn
      exact hp (mul_eq_zero_of_left (initialTimeCutoff_zero hε (not_le.mp hn).le) _)
    exact fun p hp ↦ hε.trans_le (hs hp)

/-- The same cutoff preserves smooth tests. Its support proof is the C¹ support proof. -/
def smoothInteriorCutoffTest (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ^2), ℝ))
    {ε : ℝ} (hε : 0 < ε) : 𝓓(forwardHalfSpace, ℝ) where
  toFun p := initialTimeCutoff ε (p 0) * φ p
  contDiff' := by
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (initialTimeCutoff ε) :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.div_const ε).sub contDiff_const)
    exact (hχ.comp (EuclideanSpace.proj 0).contDiff).mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' :=
    (interiorCutoffTest
      (.mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset) hε).tsupport_subset

/-- A time cutoff has no spatial derivative, so spatial differentiation commutes
with multiplication by it. -/
theorem partialDeriv_spatial_initialTimeCutoff_mul
    {f : ℝ^2 → ℝ} {p : ℝ^2} (hf : DifferentiableAt ℝ f p) (ε : ℝ) :
    (∂[1] (fun q ↦ initialTimeCutoff ε (q 0) * f q)) p =
      initialTimeCutoff ε (p 0) * (∂[1] f) p := by
  have hχ : DifferentiableAt ℝ (fun p : ℝ^2 ↦ initialTimeCutoff ε (p 0)) p :=
    ((contDiff_initialTimeCutoff ε).differentiable (by norm_num) _).comp p
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).differentiableAt
  rw [partialDeriv_mul hχ hf, partialDeriv_comp_real (u := fun q : ℝ^2 ↦ q 0) (x := p) 1
      ((contDiff_initialTimeCutoff ε).differentiable (by norm_num) _)
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).differentiableAt, partialDeriv_coord]
  simp

/-- Both spatial derivatives of a cut off test remain on its spatial factor. -/
theorem secondPartialDeriv_smoothInteriorCutoffTest
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ^2), ℝ)) {ε : ℝ} (hε : 0 < ε) (p : ℝ^2) :
    (∂[1] (∂[1] (smoothInteriorCutoffTest φ hε : ℝ^2 → ℝ))) p =
      initialTimeCutoff ε (p 0) * (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p := by
  have heq : (∂[1] (smoothInteriorCutoffTest φ hε : ℝ^2 → ℝ)) =
      fun q ↦ initialTimeCutoff ε (q 0) * (∂[1] (φ : ℝ^2 → ℝ)) q :=
    funext fun q ↦ partialDeriv_spatial_initialTimeCutoff_mul
      (φ.contDiff.differentiable (by simp) q) ε
  rw [heq]
  exact partialDeriv_spatial_initialTimeCutoff_mul
    ((contDiff_top_partialDeriv φ.contDiff).differentiable (by simp) p) ε

/-- The measure equivalence between time-space pairs and Euclidean spacetime. -/
def spaceTimePair : (ℝ × ℝ) ≃ᵐ ℝ^2 :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- The time-space equivalence preserves the coordinate order. -/
theorem spaceTimePair_apply (p : ℝ × ℝ) :
    spaceTimePair p = !₂[p.1, p.2] := by
  ext i
  fin_cases i <;> simp [spaceTimePair]

/-- The time-space equivalence preserves Lebesgue measure. -/
theorem measurePreserving_spaceTimePair :
    MeasurePreserving spaceTimePair volume volume := by
  have hp : MeasurePreserving ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume :=
    PiLp.volume_preserving_ofLp (Fin 2)
  exact hp.symm.comp (volume_preserving_finTwoArrow ℝ).symm

/-- Positive time is the product of the positive half-line and space. -/
theorem preimage_forwardHalfSpace :
    spaceTimePair ⁻¹' (forwardHalfSpace : Set ℝ^2) = Ioi 0 ×ˢ (univ : Set ℝ) := by
  ext p
  simp [spaceTimePair_apply, forwardHalfSpace]

/-- Integrating an integrable spacetime function over space gives an integrable time function. -/
theorem integrableOn_sliceIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^2 → E} (hf : IntegrableOn f forwardHalfSpace) :
    IntegrableOn (fun t : ℝ ↦ ∫ x : ℝ, f !₂[t, x]) (Ioi 0) := by
  have hp := (measurePreserving_spaceTimePair.integrableOn_comp_preimage
    spaceTimePair.measurableEmbedding).2 hf
  rw [preimage_forwardHalfSpace] at hp
  simp only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ,
    Measure.volume_eq_prod] at hp
  simpa [IntegrableOn, Function.comp_def, spaceTimePair_apply] using hp.integral_prod_left

/-- Fubini writes the integral over positive spacetime as an iterated time-space integral. -/
theorem integral_forwardHalfSpace_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^2 → E} (hf : IntegrableOn f forwardHalfSpace) :
    (∫ p : ℝ^2 in forwardHalfSpace, f p) = ∫ t : ℝ in Ioi 0, ∫ x : ℝ, f !₂[t, x] := by
  have hp := (measurePreserving_spaceTimePair.integrableOn_comp_preimage
    spaceTimePair.measurableEmbedding).2 hf
  have heq := measurePreserving_spaceTimePair.setIntegral_preimage_emb
    spaceTimePair.measurableEmbedding (g := f) (s := (forwardHalfSpace : Set ℝ^2))
  rw [preimage_forwardHalfSpace] at hp heq
  rw [← heq, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  simp only [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ] at hp
  simpa only [Function.comp_def, spaceTimePair_apply] using integral_prod (f ∘ spaceTimePair) hp


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuity up to the initial boundary gives the right limit of every
compact test pairing. Compactness controls the spatial support uniformly in time. -/
theorem InitialValueTestFunction.tendsto_integral_smul_of_continuousOn
    (φ : InitialValueTestFunction) {u : ℝ^2 → E} (hu : ContinuousOn u {p : ℝ^2 | 0 ≤ p 0}) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] • u !₂[t, x]) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, φ !₂[0, x] • u !₂[0, x])) := by
  obtain ⟨R, hR⟩ := φ.exists_spatial_support_interval
  have hc : ContinuousOn (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] • u !₂[t, x]) (Ici 0) := by
    apply continuousOn_integral_of_compact_support (k := Icc (-R) R) isCompact_Icc
    · have hp : Continuous (fun p : ℝ × ℝ ↦ (!₂[p.1, p.2] : ℝ^2)) := by fun_prop
      exact (φ.contDiff.continuous.comp hp).continuousOn.smul
        (hu.comp hp.continuousOn (fun p hp ↦ by simpa using hp.1))
    · intro t x _ hx
      simp [hR t x hx]
  exact (hc 0 (show (0 : ℝ) ∈ Ici 0 from le_rfl)).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- A bounded time cutoff preserves an integrable pairing in a real normed space. -/
theorem integrableOn_initialTimeCutoff_smul {f : ℝ^2 → E}
    (hf : IntegrableOn f forwardHalfSpace) (ε : ℝ) :
    IntegrableOn (fun p ↦ initialTimeCutoff ε (p 0) • f p) forwardHalfSpace := by
  apply hf.bdd_smul 1
  · exact ((contDiff_initialTimeCutoff ε).continuous.comp
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).continuous).aestronglyMeasurable
  · exact ae_of_all _ (fun p ↦ norm_initialTimeCutoff_le ε (p 0))

/-- The initial cutoff tends to one in every integrable pairing in a real normed space. -/
theorem tendsto_integral_initialTimeCutoff_smul
    {f : ℝ^2 → E} (hf : IntegrableOn f forwardHalfSpace) :
    Tendsto (fun ε : ℝ ↦ ∫ p : ℝ^2 in forwardHalfSpace, initialTimeCutoff ε (p 0) • f p) (𝓝[>] 0)
      (𝓝 (∫ p : ℝ^2 in forwardHalfSpace, f p)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun p ↦ ‖f p‖)
  · exact Eventually.of_forall fun ε ↦
      (integrableOn_initialTimeCutoff_smul hf ε).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with p
    simpa only [norm_smul, one_mul] using
      mul_le_mul_of_nonneg_right (norm_initialTimeCutoff_le ε (p 0)) (norm_nonneg (f p))
  · exact hf.norm
  · filter_upwards [self_mem_ae_restrict forwardHalfSpace.isOpen.measurableSet] with p hp
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < p 0 / 2 from half_pos hp))] with ε hε hε'
    rw [initialTimeCutoff_one hε (by
      have h : ε < p 0 / 2 := hε'
      linarith), one_smul]

/-- A compact scalar test makes a locally integrable vector density integrable. -/
theorem integrableOn_test_smul {u : ℝ^2 → E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace)) (φ : InitialValueTestFunction) :
    IntegrableOn (fun p ↦ φ p • u p) forwardHalfSpace :=
  hu.integrable_smul_left_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport

/-- The boundary kernel paired with a compact test and vector density is integrable. -/
theorem integrableOn_derivCutoff_test_smul {u : ℝ^2 → E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (φ : InitialValueTestFunction) (ε : ℝ) :
    IntegrableOn (fun p ↦ deriv (initialTimeCutoff ε) (p 0) • (φ p • u p)) forwardHalfSpace := by
  have hc : Continuous (fun p : ℝ^2 ↦ deriv (initialTimeCutoff ε) (p 0) * φ p) :=
    ((continuous_deriv_initialTimeCutoff ε).comp
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).continuous).mul φ.contDiff.continuous
  simpa only [IntegrableOn, mul_smul] using
    hu.integrable_smul_left_of_hasCompactSupport hc (φ.hasCompactSupport.mul_left)

/-- The initial boundary kernel recovers a limit of compact test pairings. -/
theorem tendsto_integral_derivCutoff_test_smul [CompleteSpace E] {u : ℝ^2 → E} {a : E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace)) (φ : InitialValueTestFunction)
    (htrace : Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] • u !₂[t, x]) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun ε : ℝ ↦ ∫ p : ℝ^2 in forwardHalfSpace,
      deriv (initialTimeCutoff ε) (p 0) • (φ p • u p)) (𝓝[>] 0) (𝓝 a) := by
  have hlim := tendsto_integral_deriv_initialTimeCutoff_smul
    (integrableOn_sliceIntegral (integrableOn_test_smul hu φ)) htrace
  refine hlim.congr fun ε ↦ ?_
  rw [integral_forwardHalfSpace_eq (integrableOn_derivCutoff_test_smul hu φ ε)]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ (integral_smul _ _).symm

/-- Differentiating the cutoff separates the initial boundary kernel from the
interior weak integrand, for an arbitrary real normed state space. -/
theorem integrand_interiorCutoffTest (u q : ℝ^2 → E) (φ : InitialValueTestFunction) {ε : ℝ}
    (hε : 0 < ε) (p : ℝ^2) :
    InteriorWeakForm.integrand u q (interiorCutoffTest φ hε) p = initialTimeCutoff ε (p 0) •
      InteriorWeakForm.integrand u q φ p + deriv (initialTimeCutoff ε) (p 0) • (φ p • u p) := by
  have hχ : DifferentiableAt ℝ (fun p : ℝ^2 ↦ initialTimeCutoff ε (p 0)) p :=
    ((contDiff_initialTimeCutoff ε).differentiable (by norm_num) _).comp p
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hd (i : Fin 2) : (∂[i] (fun q : ℝ^2 ↦ initialTimeCutoff ε (q 0))) p =
        (if i = 0 then 1 else 0) * deriv (initialTimeCutoff ε) (p 0) := by
    rw [partialDeriv_comp_real (u := fun q : ℝ^2 ↦ q 0) (x := p) i
      ((contDiff_initialTimeCutoff ε).differentiable (by norm_num) _)
      (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).differentiableAt]
    rw [partialDeriv_coord]
  unfold InteriorWeakForm.integrand
  change (∂[0] (fun q ↦ initialTimeCutoff ε (q 0) * φ q)) p • u p +
      (∂[1] (fun q ↦ initialTimeCutoff ε (q 0) * φ q)) p • q p = _
  rw [partialDeriv_mul hχ φ.contDiff.differentiable_one.differentiableAt,
    partialDeriv_mul hχ φ.contDiff.differentiable_one.differentiableAt, hd 0, hd 1]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false, one_mul, zero_mul, zero_add]
  module

/-- Local integrability for the restricted measure controls compact pairings
even when their support meets time zero. -/
theorem integrableOn_initialWeakIntegrand {u q : ℝ^2 → E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace)) (φ : InitialValueTestFunction) :
    IntegrableOn (InteriorWeakForm.integrand u q φ) forwardHalfSpace :=
  (hu.integrable_smul_left_of_hasCompactSupport
    (φ.continuous_partialDeriv 0) (φ.hasCompactSupport_partialDeriv 0)).add
    (hq.integrable_smul_left_of_hasCompactSupport
      (φ.continuous_partialDeriv 1) (φ.hasCompactSupport_partialDeriv 1))

end PDE.Hyperbolic.ConservationLaw
