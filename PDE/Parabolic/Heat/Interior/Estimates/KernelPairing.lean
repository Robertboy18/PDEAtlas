/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Interior.Estimates.Representation
import PDE.FDeriv.Laplacian.Congruence
import PDE.DistributionTheory.TestFunction.LaplacianCommutator
import PDE.FDeriv.SpaceTime.Translation
import PDE.Analysis.Calculus.SpaceTime.Regularity
import Mathlib.MeasureTheory.Integral.Prod
import CAS.ExactTactic

/-!
# A local heat representation with no derivatives of the field

Spatial integration by parts turns the localized heat residual into finitely
many weighted convolutions. All spacetime integrability follows from compact
support and the original continuous classical jets. Differentiation of the
replacement kernel is in its source variable, accounting for the minus sign
in the spatial terms.
-/

@[expose] public section

open PDE (partialDeriv laplacian)

open Filter MeasureTheory Metric Set
open scoped Topology ContDiff

namespace HeatEquation

variable {n : ℕ}

/-- Near the half cylinder, a classical heat field equals a finite sum of
fixed smoothing kernels applied to the field itself, so no norm or derivative
of the field enters through a source term. -/
theorem unitCutoff_eq_weighted_kernel_integrals
    {G : ℝ^n × ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hmatch : ∀ (x y : ℝ^n) (t s : ℝ),
      ‖x‖ < 5 / 8 → -3 / 8 < t → t ≤ 0 →
      ‖y‖ ≤ 7 / 8 → -1 ≤ s → s ≤ 0 →
      (3 / 4 ≤ ‖y‖ ∨ s ≤ -1 / 2) →
      G ((x, t) - (y, s)) = fundamentalSolutionHeat (x - y) (t - s))
    {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    {Dt : ℝ^n × ℝ → ℝ}
    (hΩ : IsOpen Ω) (hball : closedBall 0 1 ⊆ Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ Icc (-1) 0))
    (hDx : ContinuousOn Dx (Ω ×ˢ Icc (-1) 0))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ Icc (-1) 0))
    (hDt : ContinuousOn Dt (Ω ×ˢ Icc (-1) 0))
    (hspace : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1)
    (hhessian : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1)
    (htime : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      HasDerivWithinAt (u p.1) (Dt p) (Icc (-1) 0) p.2)
    (hheat : ∀ p ∈ Ω ×ˢ Icc (-1) 0,
      Dt p - laplacian (fun y ↦ u y p.2) p.1 = 0)
    {x : ℝ^n} {t : ℝ} (hx : ‖x‖ < 5 / 8) (ht : -3 / 8 < t) (ht0 : t ≤ 0) :
    u x t =
      (∫ q in tsupport (unitSpatialCutoff n) ×ˢ Icc (-1) 0,
        ((deriv unitTimeCutoff q.2 * unitSpatialCutoff n q.1 +
          unitTimeCutoff q.2 * laplacian (unitSpatialCutoff n) q.1) * u q.1 q.2) *
            G ((x, t) - q)) +
      ∑ i : Fin n, ∫ q in tsupport (unitSpatialCutoff n) ×ˢ Icc (-1) 0,
        (-2 * unitTimeCutoff q.2 * (∂[i] (unitSpatialCutoff n : ℝ^n → ℝ)) q.1 * u q.1 q.2) *
          fderiv ℝ G ((x, t) - q) (EuclideanSpace.single i 1, 0) := by
  let χ := unitSpatialCutoff n
  let η := unitTimeCutoff
  let Q := tsupport χ ×ˢ Icc (-1 : ℝ) 0
  let R : ℝ^n × ℝ → ℝ := fun q ↦
    deriv η q.2 * (χ q.1 * u q.1 q.2) +
      η q.2 * (χ q.1 * Dt q - laplacian (fun z ↦ χ z * u z q.2) q.1)
  let A : ℝ^n × ℝ → ℝ := fun q ↦
    ((deriv η q.2 * χ q.1 + η q.2 * laplacian χ q.1) * u q.1 q.2) * G ((x, t) - q)
  let D : Fin n → ℝ^n × ℝ → ℝ := fun i q ↦
    (-2 * η q.2 * (∂[i] (χ : ℝ^n → ℝ)) q.1 * u q.1 q.2) *
      fderiv ℝ G ((x, t) - q) (EuclideanSpace.single i 1, 0)
  have hχΩ : tsupport χ ⊆ Ω := fun y hy ↦ hball (closedBall_subset_closedBall
    (by norm_num [χ, unitSpatialCutoff]) (χ.tsupport_eq ▸ hy))
  have hQ : IsCompact Q := χ.hasCompactSupport.prod isCompact_Icc
  have huQ : ContinuousOn u.uncurry Q := hu.mono (prod_mono_left hχΩ)
  have hη : ContDiff ℝ 1 η := contDiff_unitTimeCutoff
  have hGshift : Continuous (fun q : ℝ^n × ℝ ↦ G ((x, t) - q)) :=
    hG.continuous.comp (continuous_const.sub continuous_id)
  have hA : ContinuousOn A Q := by
    have hcoef : Continuous (fun q : ℝ^n × ℝ ↦
        deriv η q.2 * χ q.1 + η q.2 * laplacian χ q.1) :=
      ((hη.continuous_deriv_one.comp continuous_snd).mul
      (χ.continuous.comp continuous_fst)).add
        ((hη.continuous.comp continuous_snd).mul
          ((χ.contDiff (n := 2)).continuous_coordinate_laplacian.comp continuous_fst))
    exact (hcoef.continuousOn.mul huQ).mul hGshift.continuousOn
  have hD (i : Fin n) : ContinuousOn (D i) Q := by
    have hp : Continuous (∂[i] (χ : ℝ^n → ℝ)) :=
      (PDE.contDiff_partialDeriv_of_succ (m := 1) (χ.contDiff (n := 2))).continuous
    exact (((continuous_const.mul (hη.continuous.comp continuous_snd)).mul
      (hp.comp continuous_fst)).continuousOn.mul huQ).mul
        (((hG.continuous_fderiv (by simp)).comp
          (continuous_const.sub continuous_id)).clm_apply continuous_const).continuousOn
  have hR : ContinuousOn R (univ ×ˢ Icc (-1) 0) :=
    continuousOn_spaceTimeCutoff_heatResidual hΩ hu hDx hDxx hDt hspace hhessian
      χ.contDiff hχΩ hη
  have hRG : IntegrableOn (fun q ↦ R q * G ((x, t) - q)) Q :=
    ((hR.mono (prod_mono_left (subset_univ _))).mul
      hGshift.continuousOn).integrableOn_compact hQ
  have hfub (v : ℝ^n × ℝ → ℝ) (hv : IntegrableOn v Q) :
      (∫ q in Q, v q) = ∫ s in Icc (-1 : ℝ) 0, ∫ y in tsupport χ, v (y, s) := by
    have hp : Integrable v
        ((volume.restrict (tsupport χ)).prod (volume.restrict (Icc (-1 : ℝ) 0))) := by
      rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
    change (∫ q in tsupport χ ×ˢ Icc (-1 : ℝ) 0, v q) = _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hp]
  have hz (i : Fin n) (y : ℝ^n) (hy : y ∉ tsupport χ) : (∂[i] (χ : ℝ^n → ℝ)) y = 0 := by
    simp only [partialDeriv, fderiv_of_notMem_tsupport ℝ hy, zero_apply]
  have hAz (s : ℝ) (y : ℝ^n) (hy : y ∉ tsupport χ) : A (y, s) = 0 := by
    simp [A, image_eq_zero_of_notMem_tsupport hy,
      EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hy]
  have hDz (i : Fin n) (s : ℝ) (y : ℝ^n) (hy : y ∉ tsupport χ) : D i (y, s) = 0 := by
    simp [D, hz i y hy]
  have hAs (s : ℝ) (hs : s ∈ Icc (-1) 0) :
      IntegrableOn (fun y ↦ A (y, s)) (tsupport χ) :=
    (hA.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy ↦ ⟨hy, hs⟩)).integrableOn_compact χ.hasCompactSupport
  have hDs (i : Fin n) (s : ℝ) (hs : s ∈ Icc (-1) 0) :
      IntegrableOn (fun y ↦ D i (y, s)) (tsupport χ) :=
    ((hD i).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun y hy ↦ ⟨hy, hs⟩)).integrableOn_compact χ.hasCompactSupport
  have hslices (s : ℝ) (hs : s ∈ Icc (-1) 0) :
      ContDiffOn ℝ 2 (fun y ↦ u y s) Ω :=
    PDE.Analysis.contDiffOn_two_slice_of_space_derivatives hΩ hDxx hspace hhessian hs
  have hslice (s : ℝ) (hs : s ∈ Icc (-1) 0) :
      (∫ y in tsupport χ, R (y, s) * G ((x, t) - (y, s))) =
        ∫ y in tsupport χ, A (y, s) + ∑ i, D i (y, s) := by
    let H : ℝ^n → ℝ := fun y ↦ G ((x, t) - (y, s))
    have hH : ContDiff ℝ 2 H :=
      (hG.of_le (by simp)).comp (contDiff_const.sub (contDiff_id.prodMk contDiff_const))
    have heq (y : ℝ^n) (hy : y ∈ tsupport χ) :
        R (y, s) * G ((x, t) - (y, s)) =
          H y * (deriv η s * (χ y * u y s) +
            η s * (χ y * laplacian (fun z ↦ u z s) y -
              laplacian (fun z ↦ χ z * u z s) y)) := by
      have hheat' := sub_eq_zero.mp (hheat (y, s) ⟨hχΩ hy, hs⟩)
      dsimp [R, H]
      rw [hheat']
      cas
    have hzero (y : ℝ^n) (hy : y ∉ tsupport χ) :
        H y * (deriv η s * (χ y * u y s) +
          η s * (χ y * laplacian (fun z ↦ u z s) y -
            laplacian (fun z ↦ χ z * u z s) y)) = 0 := by
      rw [spatialCutoff_heatResidual_eq_zero_of_notMem_tsupport
        (laplacian (fun z ↦ u z s) y) hy,
        image_eq_zero_of_notMem_tsupport hy]
      simp
    rw [setIntegral_congr_fun χ.hasCompactSupport.measurableSet heq,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      PDE.DistributionTheory.integral_linear_laplacian_commutator_mul_eq_sum
        hΩ χ.contDiff χ.hasCompactSupport hχΩ (hslices s hs) hH,
      integral_add (hAs s hs) (integrable_finsetSum Finset.univ fun i _ ↦ hDs i s hs),
      integral_finsetSum Finset.univ (fun i _ ↦ hDs i s hs)]
    congr 1
    · exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hAz s)).symm
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hDz i s)]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      dsimp only [H, D]
      rw [PDE.partialDeriv_sub_prod i (x, t) y s (hG.differentiable (by simp) _)]
      cas
  have hsum : IntegrableOn (fun q ↦ A q + ∑ i, D i q) Q :=
    (hA.integrableOn_compact hQ).add
      (integrable_finsetSum Finset.univ fun i _ ↦ (hD i).integrableOn_compact hQ)
  calc
    u x t = ∫ q in Q, R q * G ((x, t) - q) :=
      unitCutoff_eq_kernel_integral hG.continuous hmatch hΩ hball
        hu hDx hDxx hDt hspace hhessian htime hheat hx ht ht0
    _ = ∫ q in Q, A q + ∑ i, D i q := by
      rw [hfub _ hRG, hfub _ hsum]
      exact setIntegral_congr_fun measurableSet_Icc hslice
    _ = _ := by
      rw [integral_add (hA.integrableOn_compact hQ)
        (integrable_finsetSum Finset.univ fun i _ ↦ (hD i).integrableOn_compact hQ),
        integral_finsetSum Finset.univ (fun i _ ↦ (hD i).integrableOn_compact hQ)]

end HeatEquation
