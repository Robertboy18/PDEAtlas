/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.ParametrizedArea

/-!
# Hausdorff measure under approximation by an injective linear map

Comparing pairwise distances with those of a linear map reduces local area estimates
to Mathlib's exact linear area formula. The target may have larger dimension than the
source; neither a square derivative nor an inverse onto an ambient open set is required.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {X Y Z : Type*} [Nonempty X]
variable [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- A comparison of pairwise distances bounds the Hausdorff measure of one image
by that of another. Injectivity is needed only for the comparison parametrization. -/
theorem euclideanHausdorffMeasure_image_le_of_dist_le
    {s : Set X} {f : X → Y} {g : X → Z} {K : ℝ≥0}
    (hg : InjOn g s)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y))
    (d : ℕ) :
    Measure.euclideanHausdorffMeasure d (f '' s) ≤
      (K : ℝ≥0∞) ^ d * Measure.euclideanHausdorffMeasure d (g '' s) := by
  classical
  let h : Z → Y := fun z ↦ f (invFunOn g s z)
  have hh : LipschitzOnWith K h (g '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    have hz' := invFunOn_pos hz
    have hw' := invFunOn_pos hw
    simpa only [h, hz'.2, hw'.2] using
      hfg _ hz'.1 _ hw'.1
  have himage : h '' (g '' s) = f '' s := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, invFunOn_mem hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨g x, mem_image_of_mem g hx, ?_⟩
      change f (invFunOn g s (g x)) = f x
      rw [hg.leftInvOn_invFunOn hx]
  simpa only [himage, ENNReal.rpow_natCast] using
    hh.euclideanHausdorffMeasure_image_le d

end MeasureTheory

namespace HasStrictFDerivAt

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Close to a point with injective strict derivative, pairwise distances of the map
and of its derivative differ by at most any prescribed factor greater than one. -/
theorem exists_nhds_dist_comparison
    {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) (hA : Function.Injective A)
    {c : ℝ} (hc : 1 < c) :
    ∃ s ∈ 𝓝 x, ∀ y ∈ s, ∀ z ∈ s,
      dist (f y) (f z) ≤ c * dist (A y) (A z) ∧
      dist (A y) (A z) ≤ c * dist (f y) (f z) := by
  obtain ⟨K, hKpos, hK⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hA
  have hKpos' : 0 < (K : ℝ) := hKpos
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  let δ : ℝ≥0 := ⟨(c - 1) / (c * K), by positivity⟩
  have hδpos : 0 < δ := by
    change 0 < (c - 1) / (c * K)
    positivity
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds (Or.inr hδpos)
  refine ⟨s, hs, fun y hy z hz ↦ ?_⟩
  have herr := happ y hy z hz
  have hanti := hK.le_mul_dist y z
  rw [dist_eq_norm, dist_eq_norm] at hanti
  have hδK : (δ : ℝ) * K = (c - 1) / c := by
    change (c - 1) / (c * (K : ℝ)) * K = (c - 1) / c
    field_simp
  have herr' : ‖f y - f z - A (y - z)‖ ≤ (c - 1) / c * ‖A y - A z‖ := by
    calc
      _ ≤ δ * ‖y - z‖ := herr
      _ ≤ δ * (K * ‖A y - A z‖) := mul_le_mul_of_nonneg_left hanti δ.coe_nonneg
      _ = (c - 1) / c * ‖A y - A z‖ := by rw [← mul_assoc, hδK]
  have hupper : ‖f y - f z‖ ≤ ‖f y - f z - (A y - A z)‖ + ‖A y - A z‖ :=
    norm_le_norm_sub_add _ _
  have hlower : ‖A y - A z‖ ≤ ‖f y - f z - (A y - A z)‖ + ‖f y - f z‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_sub_add (A y - A z) (f y - f z)
  rw [map_sub] at herr'
  have hfrac : (c - 1) / c ≤ c - 1 := by
    apply (div_le_iff₀ hcpos).2
    nlinarith
  have hfracmul : ((c - 1) / c) * c = c - 1 := div_mul_cancel₀ _ hcpos.ne'
  constructor
  · simp only [dist_eq_norm]
    have := mul_le_mul_of_nonneg_right hfrac (norm_nonneg (A y - A z))
    nlinarith
  · simp only [dist_eq_norm]
    have herr'' := mul_le_mul_of_nonneg_left herr' hcpos.le
    rw [← mul_assoc, mul_comm c ((c - 1) / c), hfracmul] at herr''
    have := mul_le_mul_of_nonneg_left hlower hcpos.le
    nlinarith

end HasStrictFDerivAt

namespace HasStrictFDerivAt

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [MeasurableSpace F] [BorelSpace F]

/-- The area of an image near a point with injective strict derivative is bounded
above and below by the linear volume factor, with arbitrarily small multiplicative error. -/
theorem exists_nhds_area_comparison
    {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasStrictFDerivAt f A x) (hA : Function.Injective A)
    {c : ℝ≥0} (hc : 1 < c) :
    ∃ s ∈ 𝓝 x, ∀ t ⊆ s,
      Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) (f '' t) ≤
          (c : ℝ≥0∞) ^ Module.finrank ℝ E *
            (ENNReal.ofReal A.toLinearMap.normDet * volume t) ∧
      ENNReal.ofReal A.toLinearMap.normDet * volume t ≤
          (c : ℝ≥0∞) ^ Module.finrank ℝ E *
            Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) (f '' t) := by
  obtain ⟨s, hs, hdist⟩ := hf.exists_nhds_dist_comparison hA
    (show 1 < (c : ℝ) from hc)
  refine ⟨s, hs, fun t ht ↦ ?_⟩
  have hft : InjOn f t := by
    intro y hy z hz heq
    apply hA
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [heq, dist_self, mul_zero] using (hdist y (ht hy) z (ht hz)).2
  have hlinear :
      Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) (A '' t) =
        ENNReal.ofReal A.toLinearMap.normDet * volume t :=
    A.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume t
  rw [← hlinear]
  constructor
  · exact euclideanHausdorffMeasure_image_le_of_dist_le hA.injOn
      (fun y hy z hz ↦ (hdist y (ht hy) z (ht hz)).1) (Module.finrank ℝ E)
  · exact euclideanHausdorffMeasure_image_le_of_dist_le hft
      (fun y hy z hz ↦ (hdist y (ht hy) z (ht hz)).2) (Module.finrank ℝ E)

end HasStrictFDerivAt
