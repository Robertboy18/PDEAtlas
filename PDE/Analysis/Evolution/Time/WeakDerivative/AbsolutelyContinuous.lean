/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Weak derivatives of absolutely continuous trajectories

A locally integrable trajectory that is absolutely continuous on every
interval, with a locally integrable almost-everywhere derivative, has that
derivative as its distributional time derivative.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A locally integrable absolutely continuous trajectory whose locally
integrable classical derivative agrees almost everywhere with `g` has global
weak time derivative `g`. -/
theorem HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    {f g : ℝ → X}
    (hf : LocallyIntegrable f (volume : Measure ℝ))
    (hg : LocallyIntegrable g (volume : Measure ℝ))
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x ∂volume, HasDerivAt f (g x) x) :
    HasWeakTimeDerivativeOn Set.univ f g := by
  refine ⟨hf.locallyIntegrableOn Set.univ,
    hg.locallyIntegrableOn Set.univ, ?_⟩
  intro ell φ hφ hφcompact _hsupp
  obtain ⟨r, hrpos, hr⟩ :=
    hφcompact.isBounded.subset_ball_lt (0 : ℝ) (0 : ℝ)
  rw [Real.ball_zero_eq_Ioo] at hr
  have hsuppφ : Function.support φ ⊆ Ioc (-r) r :=
    (subset_closure.trans hr).trans Ioo_subset_Ioc_self
  have hsuppDeriv : Function.support (deriv φ) ⊆ Ioc (-r) r :=
    (support_deriv_subset.trans hr).trans Ioo_subset_Ioc_self
  have hsuppLeft :
      Function.support (fun t ↦ ell (g t) * φ t) ⊆ Ioc (-r) r := by
    intro t ht
    apply hsuppφ
    intro hzero
    exact ht (by simp [hzero])
  have hsuppRight :
      Function.support (fun t ↦ ell (f t) * deriv φ t) ⊆
        Ioc (-r) r := by
    intro t ht
    apply hsuppDeriv
    intro hzero
    exact ht (by simp [hzero])
  have hφneg : φ (-r) = 0 := by
    by_contra hne
    have hmem := hr (subset_closure (Function.mem_support.mpr hne))
    exact (lt_irrefl (-r)) hmem.1
  have hφpos : φ r = 0 := by
    by_contra hne
    have hmem := hr (subset_closure (Function.mem_support.mpr hne))
    exact (lt_irrefl r) hmem.2
  have hpairAC :
      AbsolutelyContinuousOnInterval (ell ∘ f) (-r) r :=
    ell.lipschitzWith.comp_absolutelyContinuousOnInterval (hAC (-r) r)
  have hφAC : AbsolutelyContinuousOnInterval φ (-r) r :=
    (hφ.of_le (by simp)).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hpairDeriv :
      ∀ᵐ x ∂volume, HasDerivAt (ell ∘ f) (ell (g x)) x := by
    filter_upwards [hderiv] with x hx
    exact ell.hasFDerivAt.comp_hasDerivAt x hx
  have hderivIntegral :
      (∫ x in -r..r, deriv (ell ∘ f) x * φ x) =
        ∫ x in -r..r, ell (g x) * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hpairDeriv] with x hx _hx
    rw [hx.deriv]
  have hparts := hpairAC.integral_mul_deriv_eq_deriv_mul hφAC
  calc
    (∫ t, ell (g t) * φ t) =
        ∫ t in -r..r, ell (g t) * φ t :=
      (intervalIntegral.integral_eq_integral_of_support_subset
        hsuppLeft).symm
    _ = -(∫ t in -r..r, ell (f t) * deriv φ t) := by
      rw [← hderivIntegral]
      rw [hφneg, hφpos] at hparts
      have hparts' :
          (∫ t in -r..r, ell (f t) * deriv φ t) =
            -(∫ x in -r..r, deriv (ell ∘ f) x * φ x) := by
        simpa only [Function.comp_apply, mul_zero, neg_zero, zero_sub]
          using hparts
      rw [hparts']
      ring
    _ = -(∫ t, ell (f t) * deriv φ t) := by
      rw [intervalIntegral.integral_eq_integral_of_support_subset
        hsuppRight]

end PDE.Analysis.Evolution
