/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.IntegratedTrajectory
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Weak wave trajectories with square-integrable forcing

An integrable primitive satisfies the endpoint weak time identity by absolute
continuity. Applying this fact to a continuous energy trajectory gives the
Gelfand weak wave formulation for square-integrable forcing.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.1, definition of a weak solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

/-- An interval-integrable primitive satisfies every admissible endpoint
time test, with the prescribed initial value. -/
theorem initial_identity_of_integrable_primitive
    {a b : ℝ} (hab : a ≤ b) (τ : TimeTest a b)
    {q g : ℝ → ℝ} (hg : IntervalIntegrable g volume a b) (q₀ : ℝ)
    (hq : ∀ t ∈ Icc a b, (∫ s in a..t, g s) = q t - q₀) :
    -(∫ t in a..b, q t * τ.derivFun t) =
      (∫ t in a..b, g t * τ.toFun t) + q₀ * τ.toFun a := by
  let Q := fun t ↦ q₀ + ∫ s in a..t, g s
  have hQ : AbsolutelyContinuousOnInterval Q a b :=
    ((LipschitzWith.const q₀).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hg.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hd : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt Q (g t) t := by
    filter_upwards [hg.ae_hasDerivAt_integral.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioc] with t ht hmem
    exact (ht (by rw [uIcc_of_le hab]; exact Ioc_subset_Icc_self hmem)
      a left_mem_uIcc).const_add q₀
  have hparts := τ.integrationByParts_inner hab (1 : ℝ) hQ hd
  have hzero : Q a = q₀ := by simp only [Q, intervalIntegral.integral_same, add_zero]
  have hleft : (∫ t in a..b, Q t * τ.derivFun t) = ∫ t in a..b, q t * τ.derivFun t :=
    intervalIntegral.integral_congr fun t ht ↦ by
      simp only [Q, hq t (by simpa only [uIcc_of_le hab] using ht), add_sub_cancel]
  simpa only [RCLike.inner_apply, conj_trivial, one_mul, hzero, hleft] using hparts

open Hyperbolic.Variational
open scoped Topology InnerProductSpace BigOperators ENNReal

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A continuous energy trajectory with square-integrable forcing determines a weak solution in
the sense of Evans, §7.2.1. Only the force is allowed to be discontinuous; both time identities
include the original initial data. -/
theorem exists_weakWave_of_integrable_integral_equations
    (T : GelfandTriple (V := V) (H := H))
    (B : V →L[ℝ] StrongDual ℝ V)
    {a b : ℝ} {ell : ℝ → StrongDual ℝ V}
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    {u : ℝ → V × H} (hu : Continuous u) (x : V × H)
    (hab : a < b)
    (hq : ∀ t ∈ Icc a b,
      (∫ s in a..t, (u s).2) = T.inclusion (u t).1 - T.inclusion x.1)
    (hp : ∀ t ∈ Icc a b,
      (∫ s in a..t, ell s - B (u s).1) =
        T.pivotToDual (u t).2 - T.pivotToDual x.2) :
    ∃ (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
      (qLp : Lp V 2 (volume.restrict (Ioc a b)))
      (pLp : Lp H 2 (volume.restrict (Ioc a b)))
      (accLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)] ell ∧
      (qLp : ℝ → V) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ (u t).1) ∧
      (pLp : ℝ → H) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ (u t).2) ∧
      (accLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
        (fun t ↦ ell t - B (u t).1) ∧
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ellLp qLp pLp accLp x.1 x.2 := by
  let acc := fun t ↦ ell t - B (u t).1
  have hqMem : MemLp (fun t ↦ (u t).1) 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hu.fst.continuousOn
  have hpMem : MemLp (fun t ↦ (u t).2) 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hu.snd.continuousOn
  have haccMem : MemLp acc 2 (volume.restrict (Ioc a b)) := hell.sub (B.comp_memLp' hqMem)
  let qLp := hqMem.toLp (fun t ↦ (u t).1)
  let pLp := hpMem.toLp (fun t ↦ (u t).2)
  let accLp := haccMem.toLp acc
  have hqAE := hqMem.coeFn_toLp
  have hpAE := hpMem.coeFn_toLp
  have haccAE := haccMem.coeFn_toLp
  refine ⟨hell.toLp ell, qLp, pLp, accLp, hell.coeFn_toLp, hqAE, hpAE, haccAE, ?_⟩
  refine {
    interval_nonempty := hab
    displacementIdentity := {
      interval_nonempty := hab
      integrable_form := by simp
      integrable_forcing := fun w τ ↦ integrable_pivotVelocityTimeTest T w τ.toLp pLp
      equation := fun w τ ↦ ?_ }
    velocityIdentity := fun w τ ↦ ?_
    equationAE := ?_ }
  · have hscalar (t : ℝ) (ht : t ∈ Icc a b) :
        (∫ s in a..t, ⟪(u s).2, T.inclusion w⟫_ℝ) =
          ⟪T.inclusion (u t).1, T.inclusion w⟫_ℝ -
            ⟪T.inclusion x.1, T.inclusion w⟫_ℝ := by
      have hint : IntervalIntegrable (fun s ↦ (u s).2) volume a t :=
        hu.snd.intervalIntegrable (μ := volume) a t
      have heq := congrArg (innerSL ℝ (T.inclusion w)) (hq t ht)
      rw [← (innerSL ℝ (T.inclusion w)).intervalIntegral_comp_comm hint] at heq
      simpa only [innerSL_apply_apply, inner_sub_right, real_inner_comm] using heq
    have htime :
        (∫ t, ⟪T.inclusion (qLp t), T.inclusion w⟫_ℝ * τ.derivToLp t
          ∂volume.restrict (Ioc a b)) =
        ∫ t in a..b, ⟪T.inclusion (u t).1, T.inclusion w⟫_ℝ * τ.derivFun t := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine integral_congr_ae ?_
      filter_upwards [hqAE, τ.derivMemLp.coeFn_toLp] with t ht hτ
      change τ.derivToLp t = τ.derivFun t at hτ
      rw [ht, hτ]
    have hforce :
        (∫ t, T.pivotToDual (pLp t) w * τ.toLp t ∂volume.restrict (Ioc a b)) =
        ∫ t in a..b, ⟪(u t).2, T.inclusion w⟫_ℝ * τ.toFun t := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine integral_congr_ae ?_
      filter_upwards [hpAE, τ.memLp.coeFn_toLp] with t ht hτ
      change τ.toLp t = τ.toFun t at hτ
      rw [ht, hτ]
      rfl
    simp only [zero_apply, zero_mul, integral_zero, add_zero]
    rw [htime, hforce]
    exact τ.initial_identity_of_integral_eq hab.le (hu.snd.inner continuous_const)
      ⟪T.inclusion x.1, T.inclusion w⟫_ℝ hscalar
  · have hi : IntervalIntegrable acc volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
        (haccMem.integrable (by norm_num))
    have hg : IntervalIntegrable (fun t ↦ acc t w) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr
        ((ContinuousLinearMap.apply ℝ ℝ w).integrable_comp hi.1)
    have hscalar (t : ℝ) (ht : t ∈ Icc a b) :
        (∫ s in a..t, acc s w) =
          ⟪(u t).2, T.inclusion w⟫_ℝ - ⟪x.2, T.inclusion w⟫_ℝ := by
      have hint : IntervalIntegrable acc volume a t := hi.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le hab.le]
        exact Icc_subset_Icc le_rfl ht.2)
      have heq := congrArg (fun l : StrongDual ℝ V ↦ l w) (hp t ht)
      change (∫ s in a..t, acc s) w =
        (T.pivotToDual (u t).2 - T.pivotToDual x.2) w at heq
      rw [ContinuousLinearMap.intervalIntegral_apply hint] at heq
      simpa only [sub_apply, GelfandTriple.pivotToDual_apply] using heq
    have htime :
        (∫ t, ⟪pLp t, T.inclusion w⟫_ℝ * τ.derivToLp t
          ∂volume.restrict (Ioc a b)) =
        ∫ t in a..b, ⟪(u t).2, T.inclusion w⟫_ℝ * τ.derivFun t := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine integral_congr_ae ?_
      filter_upwards [hpAE, τ.derivMemLp.coeFn_toLp] with t ht hτ
      change τ.derivToLp t = τ.derivFun t at hτ
      rw [ht, hτ]
    have hforce :
        (∫ t, accLp t w * τ.toLp t ∂volume.restrict (Ioc a b)) =
        ∫ t in a..b, acc t w * τ.toFun t := by
      rw [intervalIntegral.integral_of_le hab.le]
      refine integral_congr_ae ?_
      filter_upwards [haccAE, τ.memLp.coeFn_toLp] with t ht hτ
      change τ.toLp t = τ.toFun t at hτ
      rw [ht, hτ]
    rw [htime, hforce]
    exact initial_identity_of_integrable_primitive hab.le τ hg ⟪x.2, T.inclusion w⟫_ℝ hscalar
  · filter_upwards [haccAE, hqAE, hell.coeFn_toLp] with t ht hqt helt
    rw [ht, hqt, helt]
    exact sub_add_cancel _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy
