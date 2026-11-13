/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic

/-!
# Continuous integral trajectories as Bochner weak waves

Continuous forcing and a continuous energy trajectory satisfying the integrated
wave equations determine four Bochner classes on a bounded time interval:
load, displacement, velocity, and acceleration. Their almost-everywhere identities
and the scalar time-test formula give the weak wave equation with its initial terms.

The construction uses a Gelfand triple and a continuous bilinear form. It requires
neither symmetry nor coercivity, and only the pivot space must be complete.
Initial terms come from the continuous trajectory, not from evaluating arbitrary
representatives of the Bochner classes.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.1, definition of a weak solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology InnerProductSpace Interval BigOperators ENNReal

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Inside a tested integral over `(a, b]`, an `L²` class and the Bochner realization of a time
test may be replaced by pointwise representatives. -/
private theorem integral_mul_eq_intervalIntegral {E : Type*} {a b : ℝ} (hab : a ≤ b)
    {X x : ℝ → E} (hX : X =ᵐ[volume.restrict (Ioc a b)] x) (Φ : ℝ → ℝ) {φ : ℝ → ℝ}
    (hΦ : Φ =ᵐ[volume.restrict (Ioc a b)] φ) (F : E → ℝ) :
    ∫ t, F (X t) * Φ t ∂volume.restrict (Ioc a b) = ∫ t in a..b, F (x t) * φ t := by
  rw [intervalIntegral.integral_of_le hab]
  exact integral_congr_ae (by filter_upwards [hX, hΦ] with t h1 h2; rw [h1, h2])

/-- Continuous trajectories satisfying both integrated wave equations give a weak solution in the
sense of Evans, §7.2.1, with the same initial data. All four Bochner representatives are
identified almost everywhere, including the prescribed forcing and the acceleration `ell - B q`.
No symmetry or coercivity is needed for this passage from integrated equations to the weak
formulation. -/
theorem exists_weakWave_of_continuous_integral_equations (T : GelfandTriple (V := V) (H := H))
    (B : V →L[ℝ] StrongDual ℝ V) {ell : ℝ → StrongDual ℝ V} (hell : Continuous ell) {u : ℝ → V × H}
    (hu : Continuous u) (x : V × H) {a b : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Icc a b, (∫ s in a..t, (u s).2) = T.inclusion (u t).1 - T.inclusion x.1)
    (hp : ∀ t ∈ Icc a b, (∫ s in a..t, ell s - B (u s).1) =
      T.pivotToDual (u t).2 - T.pivotToDual x.2) :
    ∃ (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
      (qLp : Lp V 2 (volume.restrict (Ioc a b))) (pLp : Lp H 2 (volume.restrict (Ioc a b)))
      (accLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)] ell ∧
      (qLp : ℝ → V) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ (u t).1) ∧
      (pLp : ℝ → H) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ (u t).2) ∧
      (accLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ ell t - B (u t).1) ∧
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ellLp qLp pLp accLp x.1 x.2 := by
  let acc := fun t ↦ ell t - B (u t).1
  have hacc : Continuous acc := hell.sub (B.continuous.comp hu.fst)
  have hellMem : MemLp ell 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hell.continuousOn
  have hqMem : MemLp (fun t ↦ (u t).1) 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hu.fst.continuousOn
  have hpMem : MemLp (fun t ↦ (u t).2) 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hu.snd.continuousOn
  have haccMem : MemLp acc 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hacc.continuousOn
  refine ⟨hellMem.toLp ell, hqMem.toLp _, hpMem.toLp _, haccMem.toLp acc, hellMem.coeFn_toLp,
    hqMem.coeFn_toLp, hpMem.coeFn_toLp, haccMem.coeFn_toLp, ⟨hab, ⟨hab, by simp,
      fun w τ ↦ integrable_pivotVelocityTimeTest T w τ.toLp _, fun w τ ↦ ?_⟩, fun w τ ↦ ?_, ?_⟩⟩
  · have hscalar (t : ℝ) (ht : t ∈ Icc a b) : (∫ s in a..t, ⟪(u s).2, T.inclusion w⟫_ℝ) =
        ⟪T.inclusion (u t).1, T.inclusion w⟫_ℝ - ⟪T.inclusion x.1, T.inclusion w⟫_ℝ := by
      have heq := congrArg (innerSL ℝ (T.inclusion w)) (hq t ht)
      rw [← (innerSL ℝ (T.inclusion w)).intervalIntegral_comp_comm
        (hu.snd.intervalIntegrable (μ := volume) a t)] at heq
      simpa only [innerSL_apply_apply, inner_sub_right, real_inner_comm] using heq
    simp only [zero_apply, zero_mul, integral_zero, add_zero]
    rw [integral_mul_eq_intervalIntegral hab.le hqMem.coeFn_toLp τ.derivToLp
        τ.derivMemLp.coeFn_toLp fun y ↦ ⟪T.inclusion y, T.inclusion w⟫_ℝ,
      integral_mul_eq_intervalIntegral hab.le hpMem.coeFn_toLp τ.toLp τ.memLp.coeFn_toLp
        fun y ↦ T.pivotToDual y w]
    exact τ.initial_identity_of_integral_eq hab.le (hu.snd.inner continuous_const) _ hscalar
  · have hscalar (t : ℝ) (ht : t ∈ Icc a b) :
        (∫ s in a..t, acc s w) = ⟪(u t).2, T.inclusion w⟫_ℝ - ⟪x.2, T.inclusion w⟫_ℝ := by
      have heq := congrArg (fun l : StrongDual ℝ V ↦ l w) (hp t ht)
      change (∫ s in a..t, acc s) w = (T.pivotToDual (u t).2 - T.pivotToDual x.2) w at heq
      rw [ContinuousLinearMap.intervalIntegral_apply
        (hacc.intervalIntegrable (μ := volume) a t)] at heq
      simpa only [sub_apply, GelfandTriple.pivotToDual_apply] using heq
    rw [integral_mul_eq_intervalIntegral hab.le hpMem.coeFn_toLp τ.derivToLp
        τ.derivMemLp.coeFn_toLp fun y ↦ ⟪y, T.inclusion w⟫_ℝ,
      integral_mul_eq_intervalIntegral hab.le haccMem.coeFn_toLp τ.toLp τ.memLp.coeFn_toLp
        fun l ↦ l w]
    exact τ.initial_identity_of_integral_eq hab.le
      ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp hacc) _ hscalar
  · filter_upwards [haccMem.coeFn_toLp, hqMem.coeFn_toLp, hellMem.coeFn_toLp] with t ht hqt helt
    rw [ht, hqt, helt]
    exact sub_add_cancel _ _

end Hyperbolic.Variational
