/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.Norm.SpatialSupremum
public import PDE.Representations.Similarity.Pointwise
import PDE.Representations.Similarity.Calculus

/-!
# Supremum-norm blow-up of similarity profiles

The spatial supremum norm of a similarity ansatz, and the transfer of amplitude growth to
finite-time blow-up. Both the spatial and value spaces are generic: the spatial
space is a real module and the profile may take values in any real normed space, including
complex and vector-valued spaces.

No PDE enters. One nonzero profile value suffices for divergence of the extended supremum;
boundedness of the profile supplies finite slices and hence finite-time blow-up. The results
are pointwise; for Sobolev or `Lᵖ` quotient spaces one has to construct the dilation action first
and then use `NormBlowsUpAt.of_smul`.
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime

open Filter Topology
open PDE.Representations.Similarity
open scoped ENNReal

/-- A nonzero spatial dilation preserves the profile's extended spatial supremum, while the
amplitude multiplies it by its absolute value. The identity remains valid for unbounded
profiles, whose supremum is `⊤`. -/
theorem spatial_sup_norm_scaled_profile_ansatz
    {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [Norm E] [SMul ℝ E] [NormSMulClass ℝ E]
    (profile : V → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center : V) (t : ℝ) (hspatial : spatialScale t ≠ 0) :
    spatialSupNorm
        (scaledProfileAnsatz profile amplitudeScale spatialScale center) t =
      ENNReal.ofReal |amplitudeScale t| *
        ⨆ y, ENNReal.ofReal ‖profile y‖ := by
  unfold spatialSupNorm
  simp_rw [scaledProfileAnsatz, norm_smul, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _)]
  rw [← ENNReal.mul_iSup]
  exact congrArg (ENNReal.ofReal |amplitudeScale t| * ·) <|
    (centered_dilation_surjective hspatial center).iSup_comp
      (fun y ↦ ENNReal.ofReal ‖profile y‖)

/-- A bounded profile has finite spatial supremum after any real amplitude and spatial scaling.
The dilation need not be invertible for this upper bound. -/
theorem spatial_sup_norm_scaled_profile_ansatz_ne_top
    {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : V → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center : V) (t : ℝ) (hbounded : Bornology.IsBounded (Set.range profile)) :
    spatialSupNorm
      (scaledProfileAnsatz profile amplitudeScale spatialScale center) t ≠ ⊤ := by
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  apply (spatial_sup_norm_ne_top_iff _ _).2
  refine ⟨|amplitudeScale t| * C, fun x ↦ ?_⟩
  rw [scaledProfileAnsatz, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC _ (Set.mem_range_self _)) (abs_nonneg _)

/-- Growth at one fixed similarity coordinate forces growth of the spatial supremum norm.

The corresponding physical point may move with time. Nonvanishing of the spatial scale makes
that point available through inverse dilation. -/
theorem tendsto_spatial_sup_norm_scaled_profile_ansatz_nhds_top
    {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [Norm E] [SMul ℝ E]
    {l : Filter ℝ}
    (profile : V → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center y : V)
    (hspatial : ∀ᶠ t in l, spatialScale t ≠ 0)
    (hsample : Tendsto (fun t ↦ ‖amplitudeScale t • profile y‖) l atTop) :
    Tendsto
      (spatialSupNorm
        (scaledProfileAnsatz profile amplitudeScale spatialScale center))
      l (nhds ⊤) := by
  apply tendsto_spatial_sup_norm_nhds_top_of_sample
    (fun t ↦ center + (spatialScale t)⁻¹ • y)
  refine hsample.congr' ?_
  filter_upwards [hspatial] with t ht
  rw [scaled_profile_ansatz_at_inverse_dilation _ _ _ _ _ _ ht]

/-- A backward self-similar profile with one nonzero value has divergent extended spatial
supremum whenever its amplitude exponent is positive.

The spatial exponent is unrestricted: it changes the moving point used to sample the fixed
profile coordinate, but not the amplitude growth. The profile may be unbounded. -/
theorem tendsto_spatial_sup_norm_backward_self_similar_ansatz_nhds_top
    {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : V → E)
    (alpha beta singularTime : ℝ) (center : V)
    (halpha : 0 < alpha)
    (y : V) (hy : profile y ≠ 0) :
    Tendsto
      (spatialSupNorm (backwardSelfSimilarAnsatz profile alpha beta singularTime center))
      (nhdsWithin singularTime (Set.Iio singularTime)) (nhds ⊤) := by
  apply tendsto_spatial_sup_norm_scaled_profile_ansatz_nhds_top
    profile
    (backwardPowerScale alpha singularTime)
    (backwardPowerScale beta singularTime) center y
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (backward_power_scale_pos ht).ne'
  · have hproduct :
        Tendsto
          (fun t ↦ backwardPowerScale alpha singularTime t * ‖profile y‖)
          (nhdsWithin singularTime (Set.Iio singularTime)) atTop :=
      Filter.Tendsto.atTop_mul_const (norm_pos_iff.mpr hy)
        (tendsto_backward_power_scale_at_top halpha)
    refine Filter.Tendsto.congr' ?_ hproduct
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (backward_power_scale_pos ht)]

/-- A bounded backward self-similar profile with a nonzero value blows up when its amplitude
exponent is positive. Boundedness supplies finite spatial slices before the singular time. -/
theorem backward_self_similar_ansatz_blows_up_at
    {V E : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : V → E)
    (alpha beta singularTime : ℝ) (center : V)
    (halpha : 0 < alpha)
    (y : V) (hy : profile y ≠ 0)
    (hbounded : Bornology.IsBounded (Set.range profile)) :
    SpatialSupNormBlowsUpAt
      (backwardSelfSimilarAnsatz profile alpha beta singularTime center)
      singularTime :=
  ⟨tendsto_spatial_sup_norm_backward_self_similar_ansatz_nhds_top
      profile alpha beta singularTime center halpha y hy,
    Eventually.of_forall fun t ↦
      spatial_sup_norm_scaled_profile_ansatz_ne_top profile
        (backwardPowerScale alpha singularTime) (backwardPowerScale beta singularTime)
        center t hbounded⟩

end PDE.Solution.Singularity.FiniteTime
