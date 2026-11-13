/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CylinderIntegral
public import PDE.Hyperbolic.HamiltonJacobi.Weak.ConeComparison

/-!
# Passing cone energies and residual budgets to the limit

Lipschitz continuity controls the mollified density on every fixed spatial ball.
Dominated convergence then gives convergence of its cone energy at each time.
Fubini identifies the iterated source budget in the smooth cone comparison with
the compact spacetime integral of the residual.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Metric Filter Set
open scoped Convolution Topology RealInnerProductSpace

variable {n : ℕ}

/-- Lebesgue measure on space-time `ℝⁿ × ℝ` is an additive Haar measure. -/
instance isAddHaarMeasure_volume_spaceTime : (volume : Measure (ℝ^n × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The integral of the mollified density converges on every spatial ball. -/
theorem tendsto_ballIntegral_mollified_forwardExtension {w : ℝ^n × ℝ → ℝ} {K : NNReal}
    (hw : LipschitzOnWith K w {z | 0 ≤ z.2}) {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ^n × ℝ)}
    {l : Filter ι} [l.IsCountablyGenerated] (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (c : ℝ^n)
    (r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun i ↦ PDE.Analysis.ballIntegral n (fun x ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] forwardExtension w) (x, t))
        c r) l (𝓝 (PDE.Analysis.ballIntegral n (fun x ↦ w (x, t)) c r)) := by
  have hLip := lipschitzWith_forwardExtension hw
  have hslice : Continuous (fun x : ℝ^n ↦ forwardExtension w (x, t)) :=
    hLip.continuous.comp (continuous_id.prodMk continuous_const)
  have hsmall : ∀ᶠ i in l, (φ i).rOut ≤ 1 :=
    (hφ.eventually (Iio_mem_nhds zero_lt_one)).mono fun _ hi ↦ hi.le
  have hbound : ∀ᶠ i in l, ∀ x : ℝ^n, ‖((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        forwardExtension w) (x, t)‖ ≤ K + ‖forwardExtension w (x, t)‖ := by
    filter_upwards [hsmall] with i hi
    intro x
    have hdist := (φ i).dist_normed_convolution_le
      (μ := (volume : Measure (ℝ^n × ℝ))) hLip.continuous.aestronglyMeasurable
      (fun y hy ↦ (hLip.dist_le_mul y (x, t)).trans
        (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le (NNReal.coe_nonneg K)))
    have hd : dist (((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        forwardExtension w) (x, t)) (forwardExtension w (x, t)) ≤ K :=
      hdist.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (NNReal.coe_nonneg K))
    calc
      _ = ‖(((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          forwardExtension w) (x, t) - forwardExtension w (x, t)) +
            forwardExtension w (x, t)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        (by simpa only [dist_eq_norm] using hd) le_rfl)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (ℝ^n)).restrict (ball c r)) (F := fun i x ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] forwardExtension w) (x, t))
    (bound := fun x ↦ K + ‖forwardExtension w (x, t)‖) (f := fun x ↦ forwardExtension w (x, t))
    (Eventually.of_forall fun i ↦ (((φ i).hasCompactSupport_normed.continuous_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (φ i).continuous_normed
          hLip.continuous.locallyIntegrable).comp
            (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (hbound.mono fun _ hi ↦ Eventually.of_forall hi)
    ((continuous_const.add hslice.norm).continuousOn.integrableOn_compact
      (isCompact_closedBall c r) |>.mono_set ball_subset_closedBall) (Eventually.of_forall fun x ↦
      ContDiffBump.convolution_tendsto_right_of_continuous hφ hLip.continuous (x, t))
  simpa only [PDE.Analysis.ballIntegral, forwardExtension, max_eq_left ht,
    Function.comp_def, id_eq] using hlim

/-- The iterated residual budget on a compact cylinder tends to zero. Fubini
connects it to the spacetime residual integral. -/
theorem tendsto_integral_ball_mollifiedTransportResidual {H : ℝ^n → ℝ} (hH : ContDiff ℝ 2 H)
    {u v w : ℝ^n × ℝ → ℝ} {Ku Kv Kw : NNReal} (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2})
    (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) (hw : LipschitzOnWith Kw w {z | 0 ≤ z.2})
    (heq : ∀ᵐ z ∂(volume : Measure (ℝ^n × ℝ)).restrict {z | 0 < z.2},
      fderiv ℝ w z (0, 1) + ⟪drift H u v z, ∇ (fun x ↦ w (x, z.2)) z.1⟫ = 0)
    {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ^n × ℝ)} {l : Filter ι} [l.IsCountablyGenerated] {A : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn)
    (c : ℝ^n) (L : ℝ) {a d : ℝ} (ha : 0 < a) (had : a ≤ d) :
    Tendsto (fun i ↦ ∫ s in a..d, ∫ x in closedBall c L,
      ‖mollifiedTransportResidual (μ := volume) H (φ i) u v w (x, s)‖) l (𝓝 0) := by
  have hcompact := (isCompact_closedBall c L).prod (isCompact_Icc (a := a) (b := d))
  have hlim : Tendsto (fun i ↦ ∫ z in closedBall c L ×ˢ Icc a d,
      ‖mollifiedTransportResidual (μ := volume) H (φ i) u v w z‖) l (𝓝 0) :=
    tendsto_setIntegral_norm_mollifiedTransportResidual
    (μ := volume) hH hu hv hw heq hφ hφ_ratio hcompact ha (fun _ hz ↦ hz.2.1)
  apply hlim.congr'
  exact Eventually.of_forall fun i ↦ (PDE.Analysis.intervalIntegral_closedBall_eq_setIntegral_prod
      (continuous_mollifiedTransportResidual (μ := volume) hH hu hv hw (φ i)).norm c L had).symm

end HamiltonJacobi.Weak
