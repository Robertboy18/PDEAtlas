/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.WeakGradient
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Local representatives from bounded weak gradients

An integrable function with bounded weak gradient on an open domain has a
Lipschitz representative on every interior half ball. No bound or continuity
of the function itself is required. Small mollifications have the same
gradient bound on the half ball; their almost everywhere limit inherits the
Lipschitz estimate and extends to the ambient space.

This localizes the bounded weak gradient theorem. It lets interior
Schauder estimates construct classical representatives from raw H¹ data.
The approximation and embedding argument is the one in Evans, §§5.3.1 and
5.6.2.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Metric
open scoped Convolution NNReal Topology

namespace SobolevSpace

open Approximation

variable {n : ℕ}

/-- A locally bounded weak gradient supplies the missing continuous
representative of the function on an interior half ball. Only integrability
of that function on the outer domain is assumed. -/
theorem exists_lipschitz_representative_on_ball_of_weak_derivative_bound
    {Ω : Set ℝ^n} (hΩ : IsOpen Ω) {f : ℝ^n → ℝ}
    (hf : IntegrableOn f Ω) (g : Fin n → ℝ^n → ℝ)
    (hg : ∀ i, HasWeakDerivativeOn Ω [i] f (g i))
    (C : Fin n → ℝ≥0)
    (hC : ∀ i, ∀ᵐ x ∂volume.restrict Ω, ‖g i x‖ ≤ C i)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Ω) :
    ∃ v : ℝ^n → ℝ, LipschitzWith (∑ i, C i) v ∧
      v =ᵐ[volume.restrict (ball z (R / 2))] f := by
  have hF : LocallyIntegrable (Ω.indicator f) volume :=
    (hf.integrable_indicator hΩ.measurableSet).locallyIntegrable
  have hCi (i : Fin n) : ∀ᵐ x ∂volume, ‖Ω.indicator (g i) x‖ ≤ C i := by
    filter_upwards [(ae_restrict_iff' hΩ.measurableSet).mp (hC i)] with x hx
    rw [norm_indicator_eq_indicator_norm]
    exact indicator_apply_le' hx fun _ ↦ NNReal.coe_nonneg _
  let r : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp only [r]; positivity
  let φ : ℕ → ContDiffBump (0 : ℝ^n) := fun k ↦
    { rIn := r k
      rOut := 2 * r k
      rIn_pos := hr k
      rIn_lt_rOut := by linarith [hr k] }
  let μ : ℕ → Mollifier n := fun k ↦
    { ρ := (φ k).normed volume
      smooth := (φ k).contDiff_normed
      compactSupport := (φ k).hasCompactSupport_normed
      nonneg := (φ k).nonneg_normed
      integral_one := (φ k).integral_normed }
  let u : ℕ → ℝ^n → ℝ := fun k ↦
    ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Ω.indicator f)
  have hu (k : ℕ) : u k = mollify (μ k) 1 (Ω.indicator f) := by
    have hscaled : scaled (μ k) 1 = (φ k).normed volume := by
      rw [scaled_of_pos (μ k) zero_lt_one]
      simp only [inv_one, one_pow, one_smul, one_mul, μ]
    simp only [u, mollify, hscaled]
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hout : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) := by
    simpa only [φ, mul_zero] using tendsto_const_nhds.mul hr0
  have hLip : ∀ᶠ k in atTop, LipschitzOnWith (∑ i, C i) (u k) (ball z (R / 2)) := by
    filter_upwards [hout.eventually (gt_mem_nhds (by positivity : 0 < R / 2))]
      with k hk
    rw [hu k]
    have hsmooth := mollify_contDiff_of_pos (μ k) zero_lt_one (Ω.indicator f) hF
    have hpartial (x : ℝ^n) (hx : x ∈ ball z (R / 2)) (i : Fin n) :
        ‖(∂[i] (mollify (μ k) 1 (Ω.indicator f))) x‖ ≤ C i := by
      have hnear : closedBall x (1 * (φ k).rOut) ⊆ Ω :=
        (closedBall_subset_ball' (by linarith [mem_ball.mp hx])).trans hball
      have hcomm :=
        iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn
          (μ k) zero_lt_one
          (show tsupport (μ k).ρ ⊆ closedBall 0 (φ k).rOut by
            simpa only [μ] using (φ k).tsupport_normed_eq (μ := volume) |>.subset)
          (by simp : [i] ≠ []) hF (hg i) x hnear
      change (∂[i] (mollify (μ k) 1 (Ω.indicator f))) x =
        mollify (μ k) 1 (Ω.indicator (g i)) x at hcomm
      rw [hcomm]
      exact norm_mollify_le_of_ae_bound (μ k) zero_lt_one (hCi i) x
    apply (convex_ball z (R / 2)).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ ↦ hsmooth.differentiable (by simp) x)
    intro x hx
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ (mollify (μ k) 1 (Ω.indicator f)) x‖ ≤ ((∑ i, C i : ℝ≥0) : ℝ)
    apply ContinuousLinearMap.opNorm_le_bound _ (NNReal.coe_nonneg _)
    intro v
    rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ ?_).trans_eq
      (by rw [NNReal.coe_sum, Finset.sum_mul] : ∑ i, (C i : ℝ) * ‖v‖ = _))
    rw [norm_smul, mul_comm]
    exact mul_le_mul (hpartial x hx i) (PiLp.norm_apply_le v i) (norm_nonneg _) (C i).coe_nonneg
  have hae : ∀ᵐ x ∂volume, Tendsto (fun k ↦ u k x) atTop (𝓝 (Ω.indicator f x)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hout
      (Eventually.of_forall fun _ ↦ le_rfl) hF
  let good : Set ℝ^n :=
    {x | x ∈ ball z (R / 2) ∧ Tendsto (fun k ↦ u k x) atTop (𝓝 (f x))}
  have hgood : LipschitzOnWith (∑ i, C i) f good := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto (hx.2.dist hy.2)
      (hLip.mono fun k hk ↦ hk.dist_le_mul x hx.1 y hy.1)
  obtain ⟨v, hv, heq⟩ := hgood.extend_real
  refine ⟨v, hv, ?_⟩
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem isOpen_ball.measurableSet]
    with x hx hxball
  have hxΩ : x ∈ Ω := hball ((ball_subset_ball (by linarith : R / 2 ≤ R)) hxball)
  apply (heq ?_).symm
  exact ⟨hxball, by simpa only [indicator_of_mem hxΩ] using hx⟩

end SobolevSpace
