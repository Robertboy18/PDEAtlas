/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.ReflectedExtension
import PDE.Analysis.Evolution.LionsMagenes.Basic.RegularizedEnergy
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.DualExtension
import PDE.Analysis.Evolution.LionsMagenes.Regularity.LocalRepresentative
import PDE.Analysis.Evolution.Time.WeakDerivative.Localization

/-!
# Cutoff-reflected Gelfand evolutions

Reflection supplies `L²` data on a larger interval around `[a,b]`. A smooth
cutoff supported in that interval converts the reflected trajectory into a
global Gelfand evolution while leaving it unchanged near the original closed
interval.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

section Cutoff

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A finite-interval evolution admits a global cutoff-reflected
Lions–Magenes evolution.  The cutoff is identically one near the whole
closed interval `[a,b]`; reflection gives `L²` data on a larger
open interval, and the cutoff removes the irrelevant constant tails of the
dual primitive. -/
theorem ContinuousPivotEvolutionOnOpen.exists_reflectedCutoffEvolution
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (E : ContinuousPivotEvolutionOnOpen T u g a b)
    (hab : a < b) (hu : MemLp u 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b)))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      closure (Function.support χ) ⊆ reflectedTimeDomain a b ∧
      (∀ t ∈ Set.Icc a b, χ =ᶠ[nhds t] (1 : ℝ → ℝ)) ∧
      Nonempty (ContinuousPivotEvolution T
        (fun t ↦ χ t • reflectedIntervalExtension a b u t)
        (fun t ↦ χ t • reflectedDerivativeExtension a b g t +
          deriv χ t • T.energyToDual (reflectedIntervalExtension a b u t))) := by
  obtain ⟨χ, hχ, hχcompact, hχsupp, hχone⟩ := exists_smooth_cutoff_Icc_tsupport_Ioo
    (by linarith : 2 * a - b < a) hab.le (by linarith : b < 2 * b - a)
  let uR : ℝ → V := reflectedIntervalExtension a b u
  let gR : ℝ → StrongDual ℝ V := reflectedDerivativeExtension a b g
  let fR : ℝ → StrongDual ℝ V := reflectedDualPrimitive T E t₀
  let uχ : ℝ → V := fun t ↦ χ t • uR t
  let gχ : ℝ → StrongDual ℝ V := fun t ↦ χ t • gR t + deriv χ t • T.energyToDual (uR t)
  have huR : MemLp uR 2 volume := memLp_reflectedIntervalExtension hu
  -- the reflected dual primitive is `T.energyToDual ∘ uR` on the reflected domain
  have hfRlocal : ∀ᵐ t ∂volume, t ∈ reflectedTimeDomain a b →
      fR t = T.energyToDual (uR t) := by
    have hreflect := ae_reflectedDualEndpointExtension_eq_energyToDual T E hab ht₀
    rw [← reflectedDualPrimitive_eq_reflectedDualEndpointExtension
      T E hab ht₀ (hg.integrable (by norm_num))] at hreflect
    exact (ae_restrict_iff' (by simpa only [reflectedTimeDomain] using
      (measurableSet_Ioo : MeasurableSet (Ioo (2 * a - b) (2 * b - a))))).1 hreflect
  have hfχ : (fun t ↦ χ t • fR t) =ᵐ[volume] fun t ↦ T.energyToDual (uχ t) := by
    filter_upwards [hfRlocal] with t ht
    by_cases hχt : χ t = 0
    · simp [uχ, hχt]
    · change χ t • fR t = T.energyToDual (χ t • uR t)
      rw [map_smul, ht (hχsupp (subset_closure hχt))]
  have hgχraw : (fun t ↦ χ t • gR t + deriv χ t • fR t) =ᵐ[volume] gχ := by
    filter_upwards [hfRlocal] with t ht
    by_cases hdt : deriv χ t = 0
    · simp [gχ, hdt]
    · simp only [gχ, ht (hχsupp (tsupport_deriv_subset (subset_closure hdt)))]
  have hχTop := hχ.continuous.memLp_top_of_hasCompactSupport hχcompact volume
  have hdχTop := (contDiff_infty_iff_deriv.mp hχ).2.continuous.memLp_top_of_hasCompactSupport
    hχcompact.deriv volume
  refine ⟨χ, hχ, hχcompact, by simpa only [reflectedTimeDomain] using hχsupp, hχone,
    nonempty_continuousPivotEvolution T (hχTop.smul huR)
      (memLp_two_cutoffGelfandDerivative T χ uR gR
        (hχTop.smul (memLp_reflectedDerivativeExtension hg))
        (hdχTop.smul (huR.continuousLinearMap_comp T.energyToDual)))
      (((hasWeakTimeDerivative_reflectedDualPrimitive T E t₀
        (hg.integrable (by norm_num))).smul_contDiff_global χ hχ hχcompact
          fun _ _ ↦ mem_univ _).congr_ae hfχ hgχraw)⟩

end Cutoff

end PDE.Analysis.Evolution
