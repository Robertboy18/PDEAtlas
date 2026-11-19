/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting

/-!
# Moving a pivot-valued perturbation into the load

A bounded map from the energy space to the pivot space sends an `L²` state to
an `L²` load. Subtracting this load from the forcing leaves the integrated
equation for the principal form. The maps may depend measurably on time.
No positivity or symmetry of the perturbation is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- An energy-to-pivot perturbation of a coercive form satisfies a Gårding
inequality with explicit constants. -/
theorem garding_bound_of_coercive_principal
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    (A : V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] H)
    {C : ℝ} (hC : 0 < C) (hA : ∀ v, C * ‖v‖ ^ 2 ≤ A v v) (v : V) :
    C / 2 * ‖v‖ ^ 2 ≤
      (A + T.pivotToDual.comp R) v v +
        (‖R‖ ^ 2 / (2 * C)) * ‖T.inclusion v‖ ^ 2 := by
  have hinner : -‖R‖ * ‖v‖ * ‖T.inclusion v‖ ≤
      inner ℝ (R v) (T.inclusion v) := by
    have h := (abs_real_inner_le_norm (R v) (T.inclusion v)).trans
      (mul_le_mul_of_nonneg_right (R.le_opNorm v) (norm_nonneg _))
    nlinarith [neg_abs_le (inner ℝ (R v) (T.inclusion v))]
  have hdiv : (‖R‖ ^ 2 / (2 * C)) * (2 * C) = ‖R‖ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  have hs := sq_nonneg (C * ‖v‖ - ‖R‖ * ‖T.inclusion v‖)
  have hb := hA v
  change C / 2 * ‖v‖ ^ 2 ≤ A v v + inner ℝ (R v) (T.inclusion v) + _
  nlinarith

/-- Removing a time-dependent pivot perturbation changes only the forcing.
The `L²` load may be any representative of the pointwise lower-order expression. -/
theorem IsGelfandIntegratedWeakSolution.sub_timeDependent_pivot_perturbation
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    (A : ℝ → V →L[ℝ] StrongDual ℝ V) (R : ℝ → V →L[ℝ] H)
    (hA : ∀ v, AEStronglyMeasurable (fun t ↦ A t v) (volume.restrict (Ioc a b)))
    (M : ℝ) (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖A t‖ ≤ M)
    {f r : Lp H 2 (volume.restrict (Ioc a b))}
    {u : Lp V 2 (volume.restrict (Ioc a b))} {uInit : H}
    (hr : (r : ℝ → H) =ᵐ[volume.restrict (Ioc a b)] fun t ↦ R t (u t))
    (hu : IsGelfandIntegratedWeakSolution T
      (fun t ↦ A t + T.pivotToDual.comp (R t))
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u uInit) :
    IsGelfandIntegratedWeakSolution T A
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) (f - r)) u uInit := by
  let μ := volume.restrict (Ioc a b)
  let F := T.pivotToDual.compLpL 2 μ f
  let G := T.pivotToDual.compLpL 2 μ (f - r)
  have hF : (F : ℝ → StrongDual ℝ V) =ᵐ[μ] fun t ↦ T.pivotToDual (f t) :=
    T.pivotToDual.coeFn_compLpL f
  have hG : (G : ℝ → StrongDual ℝ V) =ᵐ[μ]
      fun t ↦ T.pivotToDual (f t) - T.pivotToDual (R t (u t)) := by
    filter_upwards [T.pivotToDual.coeFn_compLpL (f - r), Lp.coeFn_sub f r, hr]
      with t ht hsub hrt
    rw [ht, hsub, Pi.sub_apply, hrt, map_sub]
  have hintA (v : V) (τ : TimeTest a b) :
      Integrable (fun t ↦ A t (u t) v * τ.toLp t) μ :=
    integrable_timeDependentBilinearTimeTest A v τ.toLp hA M hbound u
  refine ⟨hu.interval_nonempty, hintA,
    fun v τ ↦ integrable_dualTimeTest v τ.toLp G, ?_⟩
  intro v τ
  have hint : (∫ t, G t v * τ.toLp t ∂μ) =
      (∫ t, F t v * τ.toLp t ∂μ) -
        (∫ t, (A t + T.pivotToDual.comp (R t)) (u t) v * τ.toLp t ∂μ) +
        ∫ t, A t (u t) v * τ.toLp t ∂μ := by
    rw [← integral_sub (integrable_dualTimeTest v τ.toLp F)
      (hu.integrable_form v τ)]
    have hsub : Integrable
        (fun t ↦ F t v * τ.toLp t -
          (A t + T.pivotToDual.comp (R t)) (u t) v * τ.toLp t) μ :=
      (integrable_dualTimeTest v τ.toLp F).sub (hu.integrable_form v τ)
    rw [← integral_add hsub (hintA v τ)]
    apply integral_congr_ae
    filter_upwards [hF, hG] with t ht hgt
    simp only [ht, hgt, sub_apply, add_apply, ContinuousLinearMap.comp_apply]
    ring
  have heq := hu.equation v τ
  change -(∫ t, inner ℝ (T.inclusion (u t)) (T.inclusion v) *
      τ.derivToLp t ∂μ) + _ = (∫ t, G t v * τ.toLp t ∂μ) + _
  rw [hint]
  linarith

/-- A pivot-valued lower-order term can be moved to the forcing without
changing the state or its initial trace. -/
theorem IsGelfandIntegratedWeakSolution.sub_pivot_perturbation
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
    (A : V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] H)
    {f : Lp H 2 (volume.restrict (Ioc a b))}
    {u : Lp V 2 (volume.restrict (Ioc a b))} {uInit : H}
    (hu : IsGelfandIntegratedWeakSolution T
      (fun _ ↦ A + T.pivotToDual.comp R)
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u uInit) :
    IsGelfandIntegratedWeakSolution T (fun _ ↦ A)
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
        (f - R.compLpL 2 (volume.restrict (Ioc a b)) u)) u uInit :=
  hu.sub_timeDependent_pivot_perturbation (fun _ ↦ A) (fun _ ↦ R)
    (fun _ ↦ aestronglyMeasurable_const) ‖A‖
    (Filter.Eventually.of_forall fun _ ↦ le_rfl) (R.coeFn_compLpL u)

end PDE.Analysis.Evolution
