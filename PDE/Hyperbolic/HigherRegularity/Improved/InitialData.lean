/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.StrongLoad
public import PDE.Elliptic.Variational.PivotOperator
public import PDE.Hyperbolic.WeakWave.Autonomous.ClassicalCoefficients

/-!
# Initial elliptic loads for the full autonomous wave

An `H² ∩ H¹₀` initial displacement has an `L²` full elliptic load, including
the drift and potential. The weak product rule identifies its pivot image with
the original form. Its norm is controlled by the `H²` datum alone.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

open BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full elliptic load of every `H² ∩ H¹₀` initial value lies in `L²` and has a
uniform `H²` bound. The constant is fixed before the displacement is chosen. -/
theorem exists_initial_full_load_bound
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
    (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary 1 (B i) Ω) (hC : ContDiffUpToBoundary 0 C Ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : W^{2,2}(Ω)) (g : H¹₀(Ω)),
      lowerOrderCLM (k := 1) (m := 2) (by omega) G = h10SubtypeL g →
      ∃ Lg : DerivLp n 2 Ω,
        (h10L2GelfandTriple hopen).pivotToDual Lg =
          classicalAutonomousWaveForm hopen hbounded hA hB hC g ∧
        ‖Lg‖ ≤ K * ‖G‖ := by
  let A₁ := fun i j ↦ (hA i j).toWkpSpaceOn hopen hbounded ∞
  let R := lowerOrderOperator (fun i ↦ mulLpLeft ((hB i).toLp hopen hbounded ∞))
    (mulLpLeft (hC.toLp hopen hbounded ∞))
  refine ⟨‖strongLoadCLM A₁‖ + ‖R‖, by positivity, fun G g hG ↦ ?_⟩
  have hg : ‖g‖ ≤ ‖G‖ := by
    have hh := norm_lowerOrderCLM_apply_le (p := 2) (by omega : 1 ≤ 2) G
    rwa [hG] at hh
  refine ⟨strongLoad A₁ G + R g, ?_, ?_⟩
  · have hp := pivotToDual_strongLoad hopen A₁ G g hG
    rw [map_add, hp]
    rw [classicalAutonomousWaveForm, fullDivergenceForm_eq_principal_add_pivot_comp hopen]
    change variableCoeffForm (multiplicationCoefficientOperator (coefficientBase A₁)) g +
      (h10L2GelfandTriple hopen).pivotToDual (R g) = _
    have hcoeff : coefficientBase A₁ = fun i j ↦ (hA i j).toLp hopen hbounded ∞ := by
      funext i j
      exact (hA i j).toWkpSpaceOn_base_eq_toLp hopen hbounded ∞
    rw [hcoeff]
    rfl
  · calc
      _ ≤ ‖strongLoad A₁ G‖ + ‖R g‖ := norm_add_le _ _
      _ ≤ ‖strongLoadCLM A₁‖ * ‖G‖ + ‖R‖ * ‖G‖ := add_le_add (norm_strongLoad_le A₁ G)
        ((R.le_opNorm g).trans (mul_le_mul_of_nonneg_left hg (norm_nonneg R)))
      _ = _ := (add_mul _ _ _).symm

end SobolevSpace.GraphSpace
