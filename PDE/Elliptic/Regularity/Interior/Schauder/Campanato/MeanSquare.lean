/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Campanato.Representative
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Spaces.Sobolev.Compactness.Rellich.CellAverages

/-!
# Hölder representatives from squared mean oscillation

The quadratic form of the Campanato criterion applies directly to local
energy estimates. Local square integrability supplies the integrability in
Jensen's inequality; decay of squared mean oscillation then gives the linear
mean-oscillation bound used to construct a Hölder representative.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

namespace PDE.Elliptic.Regularity.Campanato

variable {n : ℕ}

/-- A locally square-integrable field with squared mean oscillation bounded by
`M² r^(2γ)` has a Hölder representative. Neither a pointwise representative nor
its regularity is assumed. The constant is uniform in the field and ball. -/
theorem exists_holderOnWith_representative_of_meanSquare
    {γ : ℝ≥0} (hγ : 0 < γ) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (f : ℝ^n → ℝ) (M : ℝ≥0),
      (∀ K : Set ℝ^n, IsCompact K → MemLp f 2 (volume.restrict K)) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      (∀ x ∈ ball z R, ∀ r, 0 < r → r ≤ R →
        (⨍ y in closedBall x r, ‖f y - ⨍ w in closedBall x r, f w‖ ^ 2) ≤
          (M * r ^ (γ : ℝ)) ^ 2) →
      ∃ g : ℝ^n → ℝ, Continuous g ∧ HolderOnWith (C * M) γ g (ball z (R / 8)) ∧
        g =ᵐ[volume.restrict (ball z (R / 8))] f := by
  obtain ⟨C, hC, hrep⟩ := exists_holderOnWith_representative (n := n) hγ
  refine ⟨C, hC, ?_⟩
  intro f M hf z R hR hcamp
  have hloc : LocallyIntegrable f volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact MemLp.integrable (by norm_num) (hf K hK)
  apply hrep f M hloc z R hR
  intro x hx r hr hrR
  have : IsFiniteMeasure (volume.restrict (closedBall x r)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hsmall : MemLp
      (fun y ↦ f y - ⨍ w in closedBall x r, f w) 2
      (volume.restrict (closedBall x r)) :=
    (hf _ (isCompact_closedBall x r)).sub (memLp_const _)
  have hJ := SobolevSpace.GraphSpace.Rellich.sq_setAverage_le_setAverage_sq
    (closedBall x r) (measure_closedBall_pos volume x hr).ne'
    (measure_closedBall_lt_top.ne)
    (fun y ↦ ‖f y - ⨍ w in closedBall x r, f w‖)
    (MemLp.integrable (by norm_num) hsmall.norm) hsmall.norm.integrable_sq
  have hbound := hJ.trans (hcamp x hx r hr hrR)
  have hnonneg : 0 ≤ (M : ℝ) * r ^ (γ : ℝ) := by positivity
  nlinarith

end PDE.Elliptic.Regularity.Campanato
