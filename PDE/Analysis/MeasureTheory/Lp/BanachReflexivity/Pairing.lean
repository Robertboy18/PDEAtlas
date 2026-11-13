/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.BanachReflexivity.DualMeasure

/-!
# Reconstruction of Bochner functionals from indicator tests

Mathlib's continuous bilinear integral pairing already applies to a Banach space and its
continuous dual. Density of simple functions shows that a conjugate-Lp density agreeing
with a functional on constant-vector indicators represents that functional everywhere.

The strongly measurable density is a hypothesis. The results give the extension step
that follows a Banach-valued Radon–Nikodym theorem and a conjugate-Lp estimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

/-- The Bochner dual pairing on a constant-vector indicator is a set integral. -/
theorem dualPairing_indicatorConstLp (g : Lp (StrongDual ℝ F) q μ)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : F) :
    (ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing μ q p g
        (indicatorConstLp p hs hμs c) = ∫ x in s, g x c ∂μ := by
  rw [ContinuousLinearMap.lpPairing_eq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)]
    with x hx
  simp only [ContinuousLinearMap.id_apply, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Constant-vector indicators determine a Bochner Lp functional for every finite
exponent. No countability or separability assumption on the target is needed. -/
theorem eq_dualPairing_of_indicator_eq (hp : p ≠ ∞)
    (Λ : StrongDual ℝ (Lp F p μ)) (g : Lp (StrongDual ℝ F) q μ)
    (hset : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : F),
      Λ (indicatorConstLp p hs hμs c) = ∫ x in s, g x c ∂μ) :
    Λ = (ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing μ q p g := by
  let T := (ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing μ q p g
  ext f
  apply Lp.induction hp (fun v ↦ Λ v = T v) ?_ ?_ ?_ f
  · intro c s hs hμs
    change Λ (indicatorConstLp p hs hμs.ne c) =
      T (indicatorConstLp p hs hμs.ne c)
    exact (hset s hs hμs.ne c).trans (dualPairing_indicatorConstLp g hs hμs.ne c).symm
  · intro f k hf hk _ ihf ihk
    simp only [map_add, ihf, ihk]
  · exact isClosed_eq Λ.continuous T.continuous

/-- A conjugate-Lp density for the dual-valued measure represents the original
functional. The hypothesis states precisely the remaining density-identification step. -/
theorem eq_dualPairing_of_dualVectorMeasure_eq [IsFiniteMeasure μ] (hp : p ≠ ∞)
    (Λ : StrongDual ℝ (Lp F p μ)) (g : Lp (StrongDual ℝ F) q μ)
    (hset : ∀ (s : Set α) (_hs : MeasurableSet s) (c : F),
      dualVectorMeasure hp Λ s c = ∫ x in s, g x c ∂μ) :
    Λ = (ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing μ q p g := by
  apply eq_dualPairing_of_indicator_eq hp Λ g
  intro s hs hμs c
  simpa only [dualVectorMeasure_apply hp Λ hs] using hset s hs c

end MeasureTheory.Lp
