/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Temporal.IntegratedVelocity
public import PDE.Analysis.Evolution.Time.WeakDerivative.InitialPrimitive
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Integrating an autonomous weak wave

Solving the differentiated equation and integrating its displacement constructs a
solution of the original equation. The initial acceleration must satisfy the original
equation at the initial time. The velocity identity then determines the integration
constant in the spatial equation. This construction requires no Galerkin compatibility
between separate solves.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational.IsGelfandWeakWaveSolution

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
  {B : V →L[ℝ] StrongDual ℝ V}
  {ell ellDot z : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
  {v : Lp V 2 (volume.restrict (Ioc a b))}
  {w : Lp H 2 (volume.restrict (Ioc a b))}
  {q₀ h₀ : V} {p₁ : H} {ell₀ : StrongDual ℝ V}

/-- Integrate a weak wave for the differentiated load. The compatibility equation
fixes the initial acceleration; both initial traces and the original spatial equation
are conclusions of the construction. -/
theorem exists_integral_weakWave_with_primitive
    (hv : IsGelfandWeakWaveSolution T (fun _ ↦ B) ellDot v w z h₀ p₁)
    (hell : ∀ᵐ t ∂volume.restrict (Ioc a b), ell t = ell₀ + ∫ s in a..t, ellDot s)
    (hcompat : T.pivotToDual p₁ + B q₀ = ell₀) :
    ∃ u : Lp V 2 (volume.restrict (Ioc a b)),
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u
        (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) v)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) w)
        q₀ (T.inclusion h₀) ∧
      HasWeakTimeDerivativeOn (Ioo a b) u v ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), u t = q₀ + ∫ s in a..t, v s := by
  have hab := hv.interval_nonempty
  let μ := volume.restrict (Ioc a b)
  obtain ⟨Q, hQ, hQa, hQint, hQAC, hQderiv, hQweak⟩ := exists_initial_primitive_L2 v q₀
  have hQmem : MemLp Q 2 μ := memLp_restrict_Ioc_of_continuousOn hQ.continuousOn
  let u : Lp V 2 μ := hQmem.toLp Q
  let velocity : Lp H 2 μ := T.inclusion.compLpL 2 μ v
  let acceleration : Lp (StrongDual ℝ V) 2 μ := T.pivotToDual.compLpL 2 μ w
  have huAE : (u : ℝ → V) =ᵐ[μ] Q := hQmem.coeFn_toLp
  have hvAE : (velocity : ℝ → H) =ᵐ[μ] fun t ↦ T.inclusion (v t) := T.inclusion.coeFn_compLpL v
  have haAE : (acceleration : ℝ → StrongDual ℝ V) =ᵐ[μ]
      fun t ↦ T.pivotToDual (w t) := T.pivotToDual.coeFn_compLpL w
  refine ⟨u, ⟨hab, ⟨hab, by simp, fun x τ ↦ integrable_pivotVelocityTimeTest T x τ.toLp velocity,
    fun x τ ↦ ?_⟩, fun x τ ↦ ?_, ?_⟩, ?_, ?_⟩
  · have hparts := τ.integrationByParts_inner hab.le (T.inclusion x)
      (T.inclusion.lipschitzWith.comp_absolutelyContinuousOnInterval hQAC)
      (hQderiv.mono fun t ht ↦ T.inclusion.hasFDerivAt.comp_hasDerivAt t ht)
    have htime : (∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion x) * τ.derivToLp t ∂μ) =
        ∫ t in a..b, inner ℝ (T.inclusion (Q t)) (T.inclusion x) * τ.derivFun t := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine integral_congr_ae ?_
      filter_upwards [huAE, τ.derivMemLp.coeFn_toLp] with t ht hτ
      rw [ht, show τ.derivToLp t = τ.derivFun t from hτ]
    have hforce : (∫ t, T.pivotToDual (velocity t) x * τ.toLp t ∂μ) =
        ∫ t in a..b, inner ℝ (T.inclusion (v t)) (T.inclusion x) * τ.toFun t := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine integral_congr_ae ?_
      filter_upwards [hvAE, τ.memLp.coeFn_toLp] with t ht hτ
      rw [ht, show τ.toLp t = τ.toFun t from hτ]
      rfl
    simp only [zero_apply, zero_mul, integral_zero, add_zero]
    rw [htime, hforce]
    simpa only [Function.comp_apply, hQa] using hparts
  · have htime : (∫ t, inner ℝ (velocity t) (T.inclusion x) * τ.derivToLp t ∂μ) =
        ∫ t, inner ℝ (T.inclusion (v t)) (T.inclusion x) * τ.derivToLp t ∂μ :=
      integral_congr_ae (hvAE.mono fun t ht ↦ by simp only [ht])
    have hforce : (∫ t, acceleration t x * τ.toLp t ∂μ) =
        ∫ t, T.pivotToDual (w t) x * τ.toLp t ∂μ :=
      integral_congr_ae (haAE.mono fun t ht ↦ by simp only [ht])
    rw [htime, hforce]
    simpa only [zero_apply, zero_mul, integral_zero, add_zero] using
      hv.displacementIdentity.equation x τ
  · have hInt (t : ℝ) (ht : t ∈ Icc a b) :
        (∫ s in a..t, z s) = (∫ s in a..t, ellDot s) - B (∫ s in a..t, v s) := by
      have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc_left (Icc_subset_uIcc ht)
      have hvint := (intervalIntegrable_coeFn_L2_restrict_Ioc v hab.le).mono_set hsub
      rw [← B.intervalIntegral_comp_comm hvint, ← intervalIntegral.integral_sub
        ((intervalIntegrable_coeFn_L2_restrict_Ioc ellDot hab.le).mono_set hsub)
        (intervalIntegrable_iff.mpr (B.integrable_comp hvint.def')),
        intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
      exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2)
        hv.acceleration_eq_residualAE)
    filter_upwards [haAE, huAE, hv.pivotVelocity_eq_initial_add_integral_ae,
      hell, ae_restrict_mem measurableSet_Ioc] with t hat hut hwt helt ht
    change acceleration t + B (u t) = ell t
    rw [hat, hut, hwt, hInt t (Ioc_subset_Icc_self ht),
      hQint t (Ioc_subset_Icc_self ht), map_add, helt, ← hcompat]
    abel
  · exact hQweak.congr_ae_restrict measurableSet_Ioo
      (huAE.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      Filter.EventuallyEq.rfl
  · filter_upwards [huAE, ae_restrict_mem measurableSet_Ioc] with t ht htI
    exact ht.trans (hQint t (Ioc_subset_Icc_self htI))

/-- Integrating the differentiated wave gives the original weak equation and
its energy-space time derivative. -/
theorem exists_integral_weakWave (hv : IsGelfandWeakWaveSolution T (fun _ ↦ B) ellDot v w z h₀ p₁)
    (hell : ∀ᵐ t ∂volume.restrict (Ioc a b), ell t = ell₀ + ∫ s in a..t, ellDot s)
    (hcompat : T.pivotToDual p₁ + B q₀ = ell₀) :
    ∃ u : Lp V 2 (volume.restrict (Ioc a b)),
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u
        (T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) v)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) w)
        q₀ (T.inclusion h₀) ∧
      HasWeakTimeDerivativeOn (Ioo a b) u v := by
  obtain ⟨u, hu, hdu, _⟩ := hv.exists_integral_weakWave_with_primitive hell hcompat
  exact ⟨u, hu, hdu⟩

end Hyperbolic.Variational.IsGelfandWeakWaveSolution
