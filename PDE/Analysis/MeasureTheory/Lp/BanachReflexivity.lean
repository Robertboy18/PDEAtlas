/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.BanachReflexivity.Pairing
public import PDE.Analysis.Normed.Reflexivity

/-!
# The bidual step in Bochner Lp reflexivity

For a reflexive target, two surjective Bochner dual pairings imply surjectivity of the
canonical Lp bidual inclusion. The proof uses the Bochner pairing and pointwise
composition by the inverse of the target's canonical bidual isometry.

The two dual pairings are hypotheses. Discharging them needs a Banach-valued
Radon–Nikodym representation, so the result reduces Bochner reflexivity to that step.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NormedSpace

/-- A reflexive real normed space has reflexive continuous dual. -/
theorem surjective_inclusionInDoubleDual_dual
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : Function.Surjective (inclusionInDoubleDual ℝ F)) :
    Function.Surjective (inclusionInDoubleDual ℝ (StrongDual ℝ F)) := by
  intro H
  refine ⟨H.comp (inclusionInDoubleDual ℝ F), ?_⟩
  ext v
  obtain ⟨f, rfl⟩ := hF v
  rfl

end NormedSpace

namespace MeasureTheory.Lp

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

/-- Bochner dual representation for `F` and `F*`, together with reflexivity of `F`,
implies reflexivity of `Lp F`. The two representation assumptions are stated
as surjectivity of Mathlib's pairings. -/
theorem surjective_inclusionInDoubleDual_of_surjective_dualPairing
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (hP : Function.Surjective
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing μ q p))
    (hQ : Function.Surjective
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ (StrongDual ℝ F))).lpPairing
        (𝕜 := ℝ) (E := StrongDual ℝ (StrongDual ℝ F)) (F := StrongDual ℝ F) (G := ℝ) μ p q)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (Lp F p μ)) := by
  let e := LinearIsometryEquiv.ofSurjective
    (NormedSpace.inclusionInDoubleDualLi ℝ (E := F)) hF
  let P := (ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing μ q p
  let Q := (ContinuousLinearMap.id ℝ (StrongDual ℝ (StrongDual ℝ F))).lpPairing
        (𝕜 := ℝ) (E := StrongDual ℝ (StrongDual ℝ F)) (F := StrongDual ℝ F) (G := ℝ) μ p q
  intro H
  obtain ⟨v, hv⟩ := hQ (H.comp P)
  let u : Lp F p μ :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp (𝕜 := ℝ) (𝕜' := ℝ) v
  refine ⟨u, ?_⟩
  ext Λ
  obtain ⟨g, hg⟩ := hP Λ
  change P g = Λ at hg
  rw [← hg]
  change P g u = H (P g)
  have hv' := congrArg (fun T : StrongDual ℝ (Lp (StrongDual ℝ F) q μ) ↦ T g) hv
  change Q v g = H (P g) at hv'
  calc
    P g u = Q v g := by
      simp only [P, Q, ContinuousLinearMap.lpPairing_eq_integral,
        ContinuousLinearMap.id_apply]
      apply integral_congr_ae
      filter_upwards [ContinuousLinearMap.coeFn_compLp (𝕜 := ℝ) (𝕜' := ℝ)
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap v] with x hx
      change g x (u x) = v x (g x)
      rw [hx]
      exact congrArg (fun w : StrongDual ℝ (StrongDual ℝ F) ↦ w (g x))
        (e.apply_symm_apply (v x))
    _ = H (P g) := hv'

end MeasureTheory.Lp
