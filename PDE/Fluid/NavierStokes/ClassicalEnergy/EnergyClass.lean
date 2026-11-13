/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.ClassicalEnergy.Gradient
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import PDE.Analysis.MeasureTheory.Lp.PairingConvergence
import PDE.FDeriv.PartialDeriv.Energy
import PDE.FDeriv.SpaceTime

/-!
# Gradient bounds of the classical energy class from the slice gradient

The operator norm of the derivative of a velocity slice is at most the Frobenius norm of the
slice gradient, so square-integrable slice gradients give the `gradient_memLp` field of
`ClassicalEnergyClass`, and an integrable bound on their squared `L²` norms gives
`gradient_sq_integrableOn`. The squared `L²` norm of the slice gradient is the sum of the
squared `L²` norms of the coordinate derivatives `∂ⱼuᵢ`. Measurability in time of the squared
`L²` norm of the slice derivative follows from continuity of the derivative on the open slab.
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace MeasureTheory IncompressibleFlow PDE PDE.Common

set_option linter.missingDocs true

variable {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}

/-- The operator norm of the slice derivative is at most the norm of the slice gradient. -/
theorem norm_fderiv_le_norm_sliceGradient {t : ℝ} (ht : 0 < t) {x : ℝ^n}
    (hd : DifferentiableAt ℝ (velocitySlice u t) x) :
    ‖fderiv ℝ (velocitySlice u t) x‖ ≤ ‖sliceGradient u (timeSpaceCons t x)‖ := by
  have hentry (i j : Fin n) : sliceGradient u (timeSpaceCons t x) (i, j) =
      fderiv ℝ (velocitySlice u t) x (EuclideanSpace.single j 1) i := by
    rw [sliceGradient_timeSpaceCons_apply u ht]
    exact (partialDeriv_apply j i hd).symm
  have hsq : ‖fderiv ℝ (velocitySlice u t) x‖ ^ 2 ≤
      ‖sliceGradient u (timeSpaceCons t x)‖ ^ 2 := by
    refine (fderiv ℝ (velocitySlice u t) x).norm_sq_le_sum_norm_apply_single_sq.trans_eq ?_
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hentry, EuclideanSpace.real_norm_sq_eq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- A continuously differentiable slice with square-integrable slice gradient has
square-integrable derivative. -/
theorem memLp_fderiv_velocitySlice_of_memLp_sliceGradient {t : ℝ} (ht : 0 < t)
    (hC : ContDiff ℝ 1 (velocitySlice u t))
    (hD : MemLp (spatialGradientSlice (sliceGradient u) t) 2 volume) :
    MemLp (fderiv ℝ (velocitySlice u t)) 2 volume :=
  hD.of_le (hC.continuous_fderiv one_ne_zero).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦
      norm_fderiv_le_norm_sliceGradient ht (hC.differentiable one_ne_zero x))

/-- The `L²` norm of the slice derivative is at most that of the slice gradient. -/
theorem toReal_eLpNorm_fderiv_velocitySlice_le {t : ℝ} (ht : 0 < t)
    (hC : ContDiff ℝ 1 (velocitySlice u t))
    (hD : MemLp (spatialGradientSlice (sliceGradient u) t) 2 volume) :
    (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal ≤
      (eLpNorm (spatialGradientSlice (sliceGradient u) t) 2 volume).toReal := by
  refine ENNReal.toReal_mono hD.eLpNorm_ne_top ?_
  exact eLpNorm_mono_ae (hC.continuous_fderiv one_ne_zero).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦
      norm_fderiv_le_norm_sliceGradient ht (hC.differentiable one_ne_zero x))

/-- Square-integrable coordinate derivatives give a square-integrable slice gradient. -/
theorem memLp_spatialGradientSlice_sliceGradient_of_components {t : ℝ} (ht : 0 < t)
    (h : ∀ i j : Fin n, MemLp (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) 2 volume) :
    MemLp (spatialGradientSlice (sliceGradient u) t) 2 volume := by
  refine MemLp.of_eval_piLp fun ij ↦ ?_
  convert h ij.1 ij.2 using 1
  funext x
  exact sliceGradient_timeSpaceCons_apply u ht x ij.1 ij.2

/-- The squared `L²` norm of the slice gradient is the sum of the squared `L²` norms of the
coordinate derivatives. -/
theorem sq_toReal_eLpNorm_spatialGradientSlice_sliceGradient {t : ℝ} (ht : 0 < t)
    (h : ∀ i j : Fin n, MemLp (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) 2 volume) :
    (eLpNorm (spatialGradientSlice (sliceGradient u) t) 2 volume).toReal ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        (eLpNorm (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) 2 volume).toReal ^ 2 := by
  have hint (i j : Fin n) :
      Integrable (fun x ↦ (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) x ^ 2) volume :=
    (h i j).integrable_sq
  have hcomp (i j : Fin n) :
      (eLpNorm (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) 2 volume).toReal ^ 2 =
        ∫ x, (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) x ^ 2 := by
    rw [← PDE.Analysis.integral_norm_sq_eq_eLpNorm_toReal_sq (h i j)]
    simp only [Real.norm_eq_abs, sq_abs]
  have hpt (x : ℝ^n) : ‖spatialGradientSlice (sliceGradient u) t x‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, (∂[j] (fun y ↦ u (timeSpaceCons t y) i)) x ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
    simp only [spatialGradientSlice, sliceGradient_timeSpaceCons_apply u ht]
  simp only [hcomp]
  rw [← PDE.Analysis.integral_norm_sq_eq_eLpNorm_toReal_sq
      (memLp_spatialGradientSlice_sliceGradient_of_components ht h),
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hint i j

/-- For a velocity that is `C¹` on the open slab, the squared `L²` norm of the slice derivative
is almost everywhere strongly measurable in time. -/
theorem aestronglyMeasurable_sq_eLpNorm_fderiv_velocitySlice {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 u z) :
    AEStronglyMeasurable
      (fun t ↦ (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal ^ 2)
      (volume.restrict (Set.Ioc 0 T)) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hcont : ContinuousOn (fun p : ℝ × ℝ^n ↦ ‖fderiv ℝ (velocitySlice u p.1) p.2‖)
      (Set.Ioo 0 T ×ˢ Set.univ) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ^n ↦
        ‖(fderiv ℝ u (timeSpaceCons p.1 p.2)).comp (embedWithTimeZeroCLM n)‖)
        (Set.Ioo 0 T ×ˢ Set.univ) := by
      intro p hp
      have hz : timeSpaceCons p.1 p.2 ∈ finiteTimeDomain n T := by
        simpa [finiteTimeDomain] using hp.1
      have h1 : ContinuousAt (fun p : ℝ × ℝ^n ↦ fderiv ℝ u (timeSpaceCons p.1 p.2)) p :=
        ((hu _ hz).continuousAt_fderiv one_ne_zero).comp
          (f := fun p : ℝ × ℝ^n ↦ timeSpaceCons p.1 p.2)
          (contDiff_timeSpaceCons_uncurry n (m := 0)).continuous.continuousAt
      exact (h1.clm_comp continuousAt_const).norm.continuousWithinAt
    refine hc.congr fun p hp ↦ ?_
    have hz : timeSpaceCons p.1 p.2 ∈ finiteTimeDomain n T := by
      simpa [finiteTimeDomain] using hp.1
    have hd : HasFDerivAt (velocitySlice u p.1)
        ((fderiv ℝ u (timeSpaceCons p.1 p.2)).comp (embedWithTimeZeroCLM n)) p.2 :=
      ((hu _ hz).differentiableAt one_ne_zero).hasFDerivAt.comp p.2
        (hasFDerivAt_timeSpaceCons_spatial n p.1 p.2)
    rw [hd.fderiv]
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ^n ↦ ‖fderiv ℝ (velocitySlice u p.1) p.2‖ₑ ^ (2 : ℝ))
      ((volume.restrict (Set.Ioo 0 T)).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (ℝ^n))), Measure.prod_restrict]
    have := (hcont.aemeasurable (μ := (volume : Measure ℝ).prod (volume : Measure (ℝ^n)))
      (measurableSet_Ioo.prod MeasurableSet.univ)).enorm.pow_const (2 : ℝ)
    simpa only [enorm_norm] using this
  refine (((hmeas.lintegral_prod_right'.pow_const (1 / 2 : ℝ)).ennreal_toReal.pow_const
    2).aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hCt : ContDiff ℝ 1 (velocitySlice u t) := contDiff_iff_contDiffAt.mpr fun x ↦
    (hu _ (by simpa [finiteTimeDomain] using ht)).comp x
      (contDiff_timeSpaceCons_spatial n t (m := 1)).contDiffAt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (hCt.continuous_fderiv one_ne_zero).aestronglyMeasurable]
  norm_num

/-- The field `gradient_sq_integrableOn` of `ClassicalEnergyClass` from an integrable bound on
the squared `L²` norms of the slice gradient. -/
theorem integrableOn_sq_eLpNorm_fderiv_velocitySlice {T : ℝ}
    (hu : ∀ z ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 u z)
    (hC : ∀ t ∈ Set.Ioc 0 T, ContDiff ℝ 1 (velocitySlice u t))
    (hD : ∀ t ∈ Set.Ioc 0 T, MemLp (spatialGradientSlice (sliceGradient u) t) 2 volume)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioc 0 T))
    (hle : ∀ t ∈ Set.Ioc 0 T,
      (eLpNorm (spatialGradientSlice (sliceGradient u) t) 2 volume).toReal ^ 2 ≤ g t) :
    IntegrableOn (fun t ↦ (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal ^ 2)
      (Set.Ioc 0 T) := by
  refine Integrable.mono' hg (aestronglyMeasurable_sq_eLpNorm_fderiv_velocitySlice hu) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (pow_le_pow_left₀ ENNReal.toReal_nonneg
    (toReal_eLpNorm_fderiv_velocitySlice_le ht.1 (hC t ht) (hD t ht)) 2).trans (hle t ht)

end NavierStokes
