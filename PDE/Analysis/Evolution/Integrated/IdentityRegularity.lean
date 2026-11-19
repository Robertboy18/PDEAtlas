/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
public import PDE.Analysis.Evolution.LionsMagenes.Basic.IdentityEvolution
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# Strong time regularity from a Hilbert-valued weak equation

Let `u` and `g` be Bochner L² classes on a finite time interval. The identity
`-∫ ⟪u,v⟫ τ' = ∫ ⟪g,v⟫ τ + ⟪x,v⟫ τ(a)` specifies the derivative and initial
trace without choosing continuous representatives of either class.

The integrated-evolution theorem, with zero spatial form, constructs
a continuous representative and identifies its initial trace. The identity
Gelfand triple then gives absolute continuity and the strong derivative `g`
almost everywhere. Its energy identity retains both endpoint times.

The tests are `TimeTest a b`: they have a specified classical derivative on
the closed interval, both functions are in L², and the test vanishes at the
final endpoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Interval

namespace PDE.Analysis.Evolution

/-- Recover a strongly absolutely continuous representative and its prescribed
initial value from the weak equation against every endpoint time test. The
velocity is only Bochner L²; neither its continuity nor pointwise derivatives
of the original state representative are assumed. -/
theorem exists_absolutelyContinuous_representative_of_timeTest
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    {a b : ℝ} (hab : a < b)
    (u g : Lp H 2 (volume.restrict (Ioc a b))) (x : H)
    (h : ∀ (v : H) (τ : TimeTest a b),
      -(∫ t, ⟪u t, v⟫_ℝ * τ.derivFun t ∂volume.restrict (Ioc a b)) =
        (∫ t, ⟪g t, v⟫_ℝ * τ.toFun t ∂volume.restrict (Ioc a b)) +
          ⟪x, v⟫_ℝ * τ.toFun a) :
    ∃ w : ℝ → H,
      ContinuousOn w (Icc a b) ∧
      w =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ u t) ∧
      w a = x ∧
      AbsolutelyContinuousOnInterval w a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt w (g t) t) ∧
      ∀ s t, s ∈ Icc a b → t ∈ Icc a b →
        ‖w t‖ ^ 2 - ‖w s‖ ^ 2 = 2 * ∫ r in s..t, ⟪g r, u r⟫_ℝ := by
  let : MeasurableSpace (StrongDual ℝ H) := borel _
  let : BorelSpace (StrongDual ℝ H) := ⟨rfl⟩
  let ν := volume.restrict (Ioc a b)
  let T := GelfandTriple.identity H
  let ell : Lp (StrongDual ℝ H) 2 ν := T.pivotToDual.compLpL 2 ν g
  have hell : (ell : ℝ → StrongDual ℝ H) =ᵐ[ν]
      fun t ↦ T.pivotToDual (g t) := T.pivotToDual.coeFn_compLpL g
  have hu : IsGelfandIntegratedWeakSolution T (fun _ ↦ 0) (fun t ↦ ell t) u x := by
    refine ⟨hab, ?_, ?_, ?_⟩
    · intro v τ
      simp only [zero_apply, zero_mul]
      exact integrable_zero _ _ _
    · intro v τ
      exact integrable_dualTimeTest v τ.toLp ell
    · intro v τ
      have htime :
          (∫ t, ⟪T.inclusion (u t), T.inclusion v⟫_ℝ * τ.derivToLp t ∂ν) =
            ∫ t, ⟪u t, v⟫_ℝ * τ.derivFun t ∂ν := by
        apply integral_congr_ae
        filter_upwards [τ.derivMemLp.coeFn_toLp] with t ht
        change ⟪u t, v⟫_ℝ * τ.derivToLp t = ⟪u t, v⟫_ℝ * τ.derivFun t
        rw [show τ.derivToLp t = τ.derivFun t from ht]
      have hload :
          (∫ t, ell t v * τ.toLp t ∂ν) =
            ∫ t, ⟪g t, v⟫_ℝ * τ.toFun t ∂ν := by
        apply integral_congr_ae
        filter_upwards [hell, τ.memLp.coeFn_toLp] with t ht hτ
        rw [ht, GelfandTriple.pivotToDual_apply]
        change ⟪g t, v⟫_ℝ * τ.toLp t = ⟪g t, v⟫_ℝ * τ.toFun t
        rw [show τ.toLp t = τ.toFun t from hτ]
      change -(∫ t, ⟪T.inclusion (u t), T.inclusion v⟫_ℝ * τ.derivToLp t ∂ν) +
        (∫ t, (0 : H →L[ℝ] StrongDual ℝ H) (u t) v * τ.toLp t ∂ν) =
          (∫ t, ell t v * τ.toLp t ∂ν) + ⟪x, T.inclusion v⟫_ℝ * τ.toFun a
      rw [htime, hload]
      simpa only [zero_apply, zero_mul, integral_zero, add_zero, T, ν,
        GelfandTriple.identity_inclusion_apply] using h v τ
  have hzero : ∀ᵐ _t ∂ν, ‖(0 : H →L[ℝ] StrongDual ℝ H)‖ ≤ (0 : ℝ) :=
    Filter.Eventually.of_forall fun _ ↦ le_of_eq ContinuousLinearMap.opNorm_zero
  obtain ⟨d, E, _hd, hx, hres⟩ :=
    hu.exists_continuousPivotEvolutionOn_initial_L2
      (fun _ ↦ aestronglyMeasurable_const) 0 hzero hab
  have hd : (d : ℝ → StrongDual ℝ H) =ᵐ[ν] fun t ↦ T.pivotToDual (g t) := by
    filter_upwards [hres, hell] with t ht he
    have ht' : d t = ell t := by simpa only [zero_apply, sub_zero] using ht
    exact ht'.trans he
  have hsub : Ioc a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioc_subset_Icc_self
  have hae : E.representative =ᵐ[ν] fun t ↦ u t := by
    simpa only [T, ν, GelfandTriple.identity_inclusion_apply] using
      E.ae_eq_inclusion.filter_mono
        (MeasureTheory.ae_mono (volume.restrict_mono_set hsub))
  refine ⟨E.representative, ?_, hae, hx,
    E.integratedDerivative.absolutelyContinuousOnInterval_identity,
    E.integratedDerivative.ae_hasDerivAt_identity_of_ae_eq hab hd, ?_⟩
  · simpa only [uIcc_of_le hab.le] using E.continuousOn
  · intro s t hs ht
    rw [E.energyIdentity s t
      (by simpa only [uIcc_of_le hab.le] using hs)
      (by simpa only [uIcc_of_le hab.le] using ht)]
    congr 1
    apply intervalIntegral.integral_congr_ae
    have hdvol := (ae_restrict_iff' measurableSet_Ioc).1 hd
    filter_upwards [hdvol] with r hr hrt
    have hrab : r ∈ Ioc a b := by
      rcases mem_uIoc.mp hrt with hst | hts
      · exact ⟨hs.1.trans_lt hst.1, hst.2.trans ht.2⟩
      · exact ⟨ht.1.trans_lt hts.1, hts.2.trans hs.2⟩
    rw [hr hrab, GelfandTriple.pivotToDual_apply]
    rfl

end PDE.Analysis.Evolution
