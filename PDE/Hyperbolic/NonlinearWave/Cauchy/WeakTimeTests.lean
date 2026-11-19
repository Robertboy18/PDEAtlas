/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.IntegratedTrajectory

/-!
# Endpoint time tests and Bochner weak waves

Square-integrable function representatives are converted into the
Gelfand weak wave formulation. Both initial traces are kept in the time-test identities.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

open Hyperbolic.Variational
open scoped Topology InnerProductSpace BigOperators ENNReal

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Square-integrable trajectories satisfying both endpoint time-test identities
are Gelfand weak waves, with the prescribed Cauchy traces. No time continuity
is needed to pass from function representatives to the Bochner spaces. -/
theorem exists_weakWave_of_memLp_timeTests (T : GelfandTriple (V := V) (H := H))
    (B : V →L[ℝ] StrongDual ℝ V) {a b : ℝ} {ell : ℝ → StrongDual ℝ V}
    (hell : MemLp ell 2 (volume.restrict (Ioc a b))) {u : ℝ → V × H}
    (hu : MemLp u 2 (volume.restrict (Ioc a b))) (x : V × H) (hab : a < b)
    (hq : ∀ (w : V) (τ : TimeTest a b), -(∫ t in a..b, ⟪T.inclusion (u t).1,
      T.inclusion w⟫_ℝ * τ.derivFun t) = (∫ t in a..b, ⟪(u t).2, T.inclusion w⟫_ℝ * τ.toFun t) +
      ⟪T.inclusion x.1, T.inclusion w⟫_ℝ * τ.toFun a)
    (hp : ∀ (w : V) (τ : TimeTest a b), -(∫ t in a..b, ⟪(u t).2, T.inclusion w⟫_ℝ * τ.derivFun t) =
      (∫ t in a..b, (ell t - B (u t).1) w * τ.toFun t) + ⟪x.2, T.inclusion w⟫_ℝ * τ.toFun a) :
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
    (ContinuousLinearMap.fst ℝ V H).comp_memLp' hu
  have hpMem : MemLp (fun t ↦ (u t).2) 2 (volume.restrict (Ioc a b)) :=
    (ContinuousLinearMap.snd ℝ V H).comp_memLp' hu
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
  · have htime :
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
    exact hq w τ
  · have htime :
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
    exact hp w τ
  · filter_upwards [haccAE, hqAE, hell.coeFn_toLp] with t ht hqt helt
    rw [ht, hqt, helt]
    exact sub_add_cancel _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy
