/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.RadialSquareFlux.Punctured
public import PDE.Spaces.Sobolev.Inequalities.Hardy.Ball
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# The radial square flux for punctured classical H¹ data

Hardy's inequality supplies inverse-square integrability. Weak derivative uniqueness
identifies the classical gradient away from the centre, and Hölder supplies the
remaining integrability. No value or limit is prescribed at the centre.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.RadialSquareFlux

open MeasureTheory Metric Set Filter SobolevSpace SobolevSpace.GraphSpace NormedSpace
open scoped Topology RealInnerProductSpace Sobolev

variable {n : ℕ}

/-- A classical representative off one point has the actual Sobolev gradient almost everywhere. -/
theorem weakGradient_eq_gradient_ae_punctured [Fact (0 < n)]
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (U : H¹(Ω)) {c : ℝ^n} {w : ℝ^n → ℝ}
    (hw : ∀ x ∈ Ω, x ≠ c → ContDiffAt ℝ 1 w x)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n Ω] w) :
    (∇ U : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] gradient w := by
  let : Nontrivial (ℝ^n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using (Fact.out : 0 < n))
  let A := Ω \ {c}
  have hA : IsOpen A := hΩ.sdiff isClosed_singleton
  have hμ : domainMeasure n A = domainMeasure n Ω := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne c] with x hx
    simp [A, hx]
  have hcoord (i : Fin n) :
      (fun x ↦ (∇ U) x i) =ᵐ[domainMeasure n Ω] ∂[i] w := by
    have hweak := (hasWeakDerivativeOn_wkpGradientCLM U i).congr_ae hbase
      (Filter.EventuallyEq.refl _ _)
    have hweakA := hweak.mono hA.measurableSet sdiff_subset
    have hclass := hasWeakDerivativeOn_of_contDiffAt_one hA
      (fun x hx ↦ hw x hx.1 hx.2) i
    have h := hweakA.unique_ae hA hclass
    rwa [hμ] at h
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  apply PiLp.ext
  intro i
  exact (hx i).trans (gradient_apply_eq_partialDeriv w x i).symm

/-- Sobolev membership gives all three integrable densities in the radial flux formula. -/
theorem integrable_radial_densities_of_h1 (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r)
    (U : H¹(ball (0 : ℝ^n) r)) {w : ℝ^n → ℝ}
    (hw : ∀ x ∈ ball 0 r, x ≠ 0 → ContDiffAt ℝ 1 w x)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n (ball 0 r)] w) :
    IntegrableOn (fun x ↦ w x ^ 2 / ‖x‖) (ball 0 r) ∧
      IntegrableOn (fun x ↦ w x * fderiv ℝ w x (normalize x)) (ball 0 r) ∧
      IntegrableOn (fun x ↦ w x ^ 2 / ‖x‖ ^ 2) (ball 0 r) := by
  let : Fact (0 < n) := ⟨by omega⟩
  have hmem : MemLp w 2 (domainMeasure n (ball 0 r)) :=
    (memLp_congr_ae hbase).mp (Lp.memLp (wkpBaseCoordinateCLM U))
  have hHardy : MemLp (fun x ↦ w x / ‖x‖) 2 (domainMeasure n (ball 0 r)) :=
    (memLp_congr_ae (hbase.mono fun x hx ↦ by rw [hx])).mp
      (SobolevSpace.Hardy.memLp_div_norm_h1_ball hn hr U)
  have hgrad : MemLp (gradient w) 2 (domainMeasure n (ball 0 r)) :=
    (memLp_congr_ae (weakGradient_eq_gradient_ae_punctured isOpen_ball U hw hbase)).mp
      (Lp.memLp (∇ U))
  have hnormal : AEStronglyMeasurable (normalize : ℝ^n → ℝ^n)
      (domainMeasure n (ball 0 r)) := by
    exact (measurable_norm.inv.smul measurable_id).aestronglyMeasurable
  have hrad : MemLp (fun x ↦ fderiv ℝ w x (normalize x)) 2
      (domainMeasure n (ball 0 r)) := by
    have hm : AEStronglyMeasurable (fun x ↦ fderiv ℝ w x (normalize x))
        (domainMeasure n (ball 0 r)) := by
      simpa only [inner_gradient_left] using hgrad.aestronglyMeasurable.inner (𝕜 := ℝ) hnormal
    apply hgrad.of_le hm
    apply Eventually.of_forall
    intro x
    rw [← inner_gradient_left]
    have hnrm : ‖normalize x‖ ≤ 1 := by
      by_cases hx : x = 0
      · simp [hx]
      · exact (norm_normalize hx).le
    exact (norm_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hnrm)
  refine ⟨?_, hmem.integrable_mul hrad, ?_⟩
  · simpa only [IntegrableOn, pow_two, div_eq_mul_inv, Pi.mul_def, mul_assoc, domainMeasure]
      using hmem.integrable_mul hHardy
  · simpa only [IntegrableOn, div_pow, domainMeasure] using
      (memLp_two_iff_integrable_sq hHardy.aestronglyMeasurable).mp hHardy

/-- The exact radial square-flux identity for H¹ data that are C¹ away from the centre.
The outer boundary value is classical; no smoothness or limit is required at the centre. -/
theorem radial_square_flux_of_h1 (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r)
    (U : H¹(ball (0 : ℝ^n) r)) {w : ℝ^n → ℝ}
    (hw : ∀ x ∈ closedBall 0 r, x ≠ 0 → ContDiffAt ℝ 1 w x)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n (ball 0 r)] w) :
    ((n : ℝ) - 1) * (∫ x in ball (0 : ℝ^n) r, w x ^ 2 / ‖x‖) +
      2 * (∫ x in ball (0 : ℝ^n) r, w x * fderiv ℝ w x (normalize x)) =
        sphereIntegral n (fun x ↦ w x ^ 2) 0 r := by
  let : Fact (0 < n) := ⟨by omega⟩
  obtain ⟨hweight, hprod, hHardy⟩ :=
    integrable_radial_densities_of_h1 hn hr U (fun x hx ↦ hw x (ball_subset_closedBall hx)) hbase
  have hD : IntegrableOn (fun x ↦ ((n : ℝ) - 1) * w x ^ 2 / ‖x - 0‖ +
      2 * w x * fderiv ℝ w x (normalize (x - 0))) (ball 0 r) := by
    simpa only [IntegrableOn, sub_zero, mul_div_assoc, mul_assoc, Pi.add_def] using
      (hweight.const_mul ((n : ℝ) - 1)).add (hprod.const_mul 2)
  have h := integral_radial_sq_eq_sphereIntegral_of_integrable hr hw hD
    (by simpa only [sub_zero] using hHardy)
  simpa only [sub_zero, mul_div_assoc, mul_assoc,
    integral_add (hweight.const_mul ((n : ℝ) - 1)) (hprod.const_mul 2), integral_const_mul] using h

end PDE.Analysis.RadialSquareFlux
