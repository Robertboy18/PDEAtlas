/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion

/-!
# Time regularity through a factored energy pairing

When the Gelfand energy map factors through a weaker space `X`, an `X`-valued
weak time derivative suffices for pivot continuity. The derivative hypothesis
uses ordinary smooth compactly supported distributional tests. The constant
is chosen before the trajectory and its derivative.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution

open MeasureTheory Set
open scoped ENNReal

variable {V H X : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]

/-- A factorization of the energy pairing gives a uniform pivot estimate for
trajectories with a weak derivative in the factor space. -/
theorem GelfandTriple.exists_continuous_representative_of_factorization
    (T : GelfandTriple (V := V) (H := H)) (A : V →L[ℝ] X)
    (B : X →L[ℝ] StrongDual ℝ V)
    (hfactor : ∀ v, T.energyToDual v = B (A v))
    {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Lp V 2 (volume.restrict (Ioc a b)))
      (g : Lp X 2 (volume.restrict (Ioc a b))),
      HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ A (u t)) (fun t ↦ g t) →
      ∃ v : ℝ → H, ContinuousOn v (Icc a b) ∧
        v =ᵐ[volume.restrict (Ioc a b)] (fun t ↦ T.inclusion (u t)) ∧
        ∀ t ∈ Icc a b, ‖v t‖ ≤ C * (‖u‖ + ‖g‖) := by
  let C := √(‖T.inclusion‖ ^ 2 / (b - a) + 2 * ‖B‖)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro u g h
  let gD := B.compLp g
  have hgD : (fun t ↦ B (g t)) =ᵐ[volume.restrict (Ioo a b)] gD :=
    (B.coeFn_compLp' g).symm.filter_mono
      (ae_mono (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl))
  have hD : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ T.energyToDual (u t)) (fun t ↦ gD t) := by
    apply (h.map B).congr_ae_restrict measurableSet_Ioo _ hgD
    exact Filter.Eventually.of_forall fun t ↦ (hfactor (u t)).symm
  obtain ⟨Eopen⟩ := hD.nonempty_continuousPivotEvolutionOnOpen (T := T) hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn T hab (Lp.memLp u) (Lp.memLp gD)
  have hsub : Ioc a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioc_subset_Icc_self
  refine ⟨E.representative, ?_,
    E.ae_eq_inclusion.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)), ?_⟩
  · simpa only [uIcc_of_le hab.le] using E.continuousOn
  · intro t ht
    have hu : ‖u‖ ≤ ‖u‖ + ‖g‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hg : ‖gD‖ ≤ ‖B‖ * (‖u‖ + ‖g‖) :=
      (B.norm_compLp_le g).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _))
          (norm_nonneg _))
    have hbound := E.norm_representative_le_of_L2_norm_le hab
      (add_nonneg (norm_nonneg u) (norm_nonneg g)) hu hg t ht
    calc
      ‖E.representative t‖ ≤
          √(‖T.inclusion‖ ^ 2 * (‖u‖ + ‖g‖) ^ 2 / (b - a) +
            2 * (‖u‖ + ‖g‖) * (‖B‖ * (‖u‖ + ‖g‖))) := hbound
      _ = √((‖T.inclusion‖ ^ 2 / (b - a) + 2 * ‖B‖) * (‖u‖ + ‖g‖) ^ 2) := by
        congr 1
        ring
      _ = C * (‖u‖ + ‖g‖) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end PDE.Analysis.Evolution
