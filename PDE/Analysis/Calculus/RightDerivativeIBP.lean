/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Singular endpoint integration by parts with right derivatives

Continuity and right derivatives suffice for the improper FTC and product IBP.
This admits continuous piecewise smooth coefficients at their interior knots;
endpoint values are supplied as one-sided limits of the relevant flux.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace PDE.Analysis

/-- Singular-endpoint FTC with right derivatives. Continuous piecewise smooth
functions are admitted without differentiability at their interior knots. -/
theorem integral_Ioo_eq_sub_of_hasDeriv_right_of_tendsto
    {a b fa fb : ℝ} {f f' : ℝ → ℝ} (hab : a < b)
    (hc : ContinuousOn f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hi : IntegrableOn f' (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    (∫ x in Ioo a b, f' x) = fb - fa := by
  classical
  let F := Function.update (Function.update f a fa) b fb
  have hF : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_sdiff_right, Ico_sdiff_left]
    refine ⟨⟨hc, ?_⟩, ?_⟩
    · exact fun _ ↦ ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hab] with x hx
        using (Function.update_of_ne hx.1.ne' _ _).symm
  have hFd : ∀ x ∈ Ioo a b, HasDerivWithinAt F (f' x) (Ioi x) x := by
    intro x hx
    apply (hd x hx).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy
      simp only [F, Function.update_of_ne hy.2.ne, Function.update_of_ne hy.1.ne']
    · simp only [F, Function.update_of_ne hx.2.ne, Function.update_of_ne hx.1.ne']
  have hint : IntervalIntegrable f' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
    exact hi
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab.le hF hFd hint
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at h
  simpa [F, hab.ne, hab.ne'] using h

/-- Integration by parts with endpoint fluxes and right derivative witnesses. -/
theorem integral_Ioo_mul_deriv_right
    {a b left right : ℝ} {f f' g g' : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hgd : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (hi : IntegrableOn (fun x ↦ f' x * g x) (Ioo a b))
    (hj : IntegrableOn (fun x ↦ f x * g' x) (Ioo a b))
    (ha : Tendsto (fun x ↦ f x * g x) (𝓝[>] a) (𝓝 left))
    (hb : Tendsto (fun x ↦ f x * g x) (𝓝[<] b) (𝓝 right)) :
    (∫ x in Ioo a b, f x * g' x) =
      right - left - ∫ x in Ioo a b, f' x * g x := by
  have h := integral_Ioo_eq_sub_of_hasDeriv_right_of_tendsto hab (hf.mul hg)
    (fun x hx ↦ (hfd x hx).mul (hgd x hx)) (hi.add hj) ha hb
  rw [integral_add hi hj] at h
  linarith

end PDE.Analysis
