/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.DivergenceTrace
public import PDE.Analysis.Calculus.EuclideanBall
public import PDE.Analysis.Calculus.MovingBall
import PDE.Analysis.Calculus.Divergence.Continuity
import CAS.ExactTactic

/-!
# Smooth transport estimates on shrinking balls

Reynolds transport and the ball divergence theorem give an energy inequality
for a nonnegative smooth density. A bound on the drift speed makes the lateral
flux nonpositive. The remaining terms are its divergence and the actual
transport residual.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Metric Set
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

/-- The coordinate ball divergence theorem in vector and inner-product form. -/
theorem ballIntegral_divergence_eq_sphereIntegral_inner_normal
    [Fact (0 < n)] {F : ℝ^n → ℝ^n} (hF : ContDiff ℝ 1 F)
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    ballIntegral n (∇· F) c r =
      sphereIntegral n (fun x ↦ ⟪F x, NormedSpace.normalize (x - c)⟫) c r := by
  have hcoord (i : Fin n) : ContDiff ℝ 1 (fun x ↦ F x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  change ballIntegral n (fun x ↦ ∇· F x) c r = _
  simpa only [divergence, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
    using ballIntegral_divergence_eq_sphereIntegral_normal_flux
      (fun i x ↦ F x i) hcoord c hr

/-- The lateral flux through a ball shrinking at speed `R` is nonpositive
when the density is nonnegative and the drift speed is at most `R`. -/
theorem neg_sphereIntegral_flux_sub_le_zero
    {w : ℝ^n → ℝ} {b : ℝ^n → ℝ^n}
    (hw : Continuous w) (hb : Continuous b) (c : ℝ^n) {r R : ℝ} (hr : 0 < r)
    (hw0 : ∀ x ∈ sphere c r, 0 ≤ w x)
    (hbR : ∀ x ∈ sphere c r, ‖b x‖ ≤ R) :
    -sphereIntegral n (fun x ↦ w x * ⟪b x, NormedSpace.normalize (x - c)⟫) c r -
      R * sphereIntegral n w c r ≤ 0 := by
  let X : sphere (0 : ℝ^n) 1 → ℝ^n := fun ω ↦ c + r • (ω : ℝ^n)
  have hX : Continuous X := continuous_const.add (continuous_subtype_val.const_smul r)
  have hnormal (ω : sphere (0 : ℝ^n) 1) :
      NormedSpace.normalize (X ω - c) = (ω : ℝ^n) := by
    simp only [X, add_sub_cancel_left, NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp ω.property)]
  have hmem (ω : sphere (0 : ℝ^n) 1) : X ω ∈ sphere c r := by
    simp only [mem_sphere, dist_eq_norm, X, add_sub_cancel_left, norm_smul,
      mem_sphere_zero_iff_norm.mp ω.property, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hint : Integrable (fun ω : sphere (0 : ℝ^n) 1 ↦
      w (X ω) * ⟪b (X ω), (ω : ℝ^n)⟫) ((volume : Measure (ℝ^n)).toSphere) :=
    ((hw.comp hX).mul ((hb.comp hX).inner continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hwi : Integrable (fun ω ↦ w (X ω)) ((volume : Measure (ℝ^n)).toSphere) :=
    (hw.comp hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : ∫ ω, -R * w (X ω) ∂((volume : Measure (ℝ^n)).toSphere) ≤
      ∫ ω, w (X ω) * ⟪b (X ω), (ω : ℝ^n)⟫
        ∂((volume : Measure (ℝ^n)).toSphere) := by
    apply integral_mono (hwi.const_mul _) hint
    intro ω
    have hinner := abs_real_inner_le_norm (b (X ω)) (ω : ℝ^n)
    rw [mem_sphere_zero_iff_norm.mp ω.property, mul_one] at hinner
    have hlow : -R ≤ ⟪b (X ω), (ω : ℝ^n)⟫ := by
      have h := (neg_le_abs _).trans (hinner.trans (hbR (X ω) (hmem ω)))
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hlow (hw0 (X ω) (hmem ω))]
  rw [integral_const_mul] at hle
  have hscaled := mul_le_mul_of_nonneg_left hle (pow_nonneg (abs_nonneg r) (n - 1))
  unfold sphereIntegral
  change -( |r| ^ (n - 1) * ∫ ω,
      w (X ω) * ⟪b (X ω), NormedSpace.normalize (X ω - c)⟫
        ∂((volume : Measure (ℝ^n)).toSphere)) -
    R * (|r| ^ (n - 1) * ∫ ω, w (X ω) ∂((volume : Measure (ℝ^n)).toSphere)) ≤ 0
  simp_rw [hnormal]
  nlinarith

/-- Reynolds transport, Gauss, and the drift speed bound give the cone energy
inequality with the norm of the actual transport residual as source. -/
theorem deriv_ballIntegral_shrinking_le
    [Fact (0 < n)] {w : ℝ → ℝ^n → ℝ} {b : ℝ^n → ℝ^n}
    (hw : ContDiff ℝ 1 (Function.uncurry w)) (hb : ContDiff ℝ 1 b)
    (c : ℝ^n) {R T t K : ℝ} (hr : 0 < R * (T - t))
    (hw0 : ∀ x ∈ closedBall c (R * (T - t)), 0 ≤ w t x)
    (hbR : ∀ x ∈ sphere c (R * (T - t)), ‖b x‖ ≤ R)
    (hbK : ∀ x ∈ ball c (R * (T - t)), ∇· b x ≤ K) :
    deriv (fun s ↦ ballIntegral n (w s) c (R * (T - s))) t ≤
      K * ballIntegral n (w t) c (R * (T - t)) +
        ballIntegral n (fun x ↦
          ‖fderiv ℝ (Function.uncurry w) (t, x) (1, 0) +
            fderiv ℝ (w t) x (b x)‖) c (R * (T - t)) := by
  let r := R * (T - t)
  let wt : ℝ^n → ℝ := fun x ↦ fderiv ℝ (Function.uncurry w) (t, x) (1, 0)
  let residual : ℝ^n → ℝ := fun x ↦ wt x + fderiv ℝ (w t) x (b x)
  let F : ℝ^n → ℝ^n := fun x ↦ w t x • b x
  have hws : ContDiff ℝ 1 (w t) := hw.comp (contDiff_const.prodMk contDiff_id)
  have hF : ContDiff ℝ 1 F := hws.smul hb
  have hwt : Continuous wt := (hw.continuous_fderiv one_ne_zero).clm_apply
    continuous_const |>.comp (continuous_const.prodMk continuous_id)
  have hres : Continuous residual :=
    hwt.add ((hws.continuous_fderiv one_ne_zero).clm_apply hb.continuous)
  have hint {f : ℝ^n → ℝ} (hf : Continuous f) : IntegrableOn f (ball c r) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hpoint (x : ℝ^n) (hx : x ∈ ball c r) :
      wt x ≤ K * w t x + ‖residual x‖ - ∇· F x := by
    have hdiv := divergence_smul
      (hws.differentiable one_ne_zero x) (hb.differentiable one_ne_zero x)
    have hmul := mul_le_mul_of_nonneg_left (hbK x hx)
      (hw0 x (ball_subset_closedBall hx))
    have hnorm := le_abs_self (residual x)
    rw [← Real.norm_eq_abs] at hnorm
    dsimp [residual, F] at *
    linarith
  have hintle : ballIntegral n wt c r ≤
      K * ballIntegral n (w t) c r + ballIntegral n (fun x ↦ ‖residual x‖) c r -
        ballIntegral n (∇· F) c r := by
    have hsum : IntegrableOn (fun x ↦ K * w t x + ‖residual x‖) (ball c r) :=
      ((hint hws.continuous).const_mul K).add (hint hres.norm)
    have h := integral_mono_ae (hint hwt)
      (hsum.sub (hint hF.continuous_divergence))
      ((ae_restrict_mem measurableSet_ball).mono hpoint)
    change ∫ x in ball c r, wt x ≤
      ∫ x in ball c r, (K * w t x + ‖residual x‖ - ∇· F x) at h
    rw [integral_sub hsum (hint hF.continuous_divergence),
      integral_add ((hint hws.continuous).const_mul K) (hint hres.norm),
      integral_const_mul] at h
    exact h
  have hflux := neg_sphereIntegral_flux_sub_le_zero hws.continuous hb.continuous c hr
    (fun x hx ↦ hw0 x (sphere_subset_closedBall hx)) hbR
  have hgauss := ballIntegral_divergence_eq_sphereIntegral_inner_normal hF c hr
  simp only [F, real_inner_smul_left] at hgauss
  rw [hgauss] at hintle
  have hρ : HasDerivAt (fun s : ℝ ↦ R * (T - s)) (-R) t := by cas
  rw [(hasDerivAt_ballIntegral_moving w hw c _ hρ hr).deriv]
  change ballIntegral n wt c r + -R * sphereIntegral n (w t) c r ≤ _
  change ballIntegral n wt c r ≤ _ at hintle
  change -sphereIntegral n _ c r - R * sphereIntegral n (w t) c r ≤ 0 at hflux
  change _ ≤ K * ballIntegral n (w t) c r +
    ballIntegral n (fun x ↦ ‖residual x‖) c r
  linarith

end PDE.Analysis
