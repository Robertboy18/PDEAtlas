/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.ContinuousFamily
public import PDE.Analysis.Calculus.SpaceTime.ForwardSpatialJet

/-!
# Odd-dimensional wave potentials of forward forcing slices

`C^(k+2)` regularity within the forward half-space supplies a continuously
indexed family of `C²` wave potentials in dimension `2k+3`. The index is clipped at zero.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- A forward forcing slice gives a `C²` potential in space and signed age. -/
theorem contDiff_two_oddWavePotential_forward (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (a : ℝ) :
    ContDiff ℝ 2 (oddWavePotential k (fun x ↦ f (timeSpaceCons (max 0 a) x))) :=
  contDiff_oddWavePotential k 2 (hf.contDiff_forward_spatialSlice (le_max_left 0 a))

/-- Every jet through order two varies continuously through source time and age zero. -/
theorem continuous_iteratedFDeriv_oddWavePotential_forward (k : ℕ) {f : ℝ^(2 * k + 3 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun p : ℝ × ℝ^(2 * k + 3 + 1) ↦ iteratedFDeriv ℝ j
      (oddWavePotential k (fun x ↦ f (timeSpaceCons (max 0 p.1) x))) p.2) := by
  apply continuous_iteratedFDeriv_oddWavePotential_family k j
    (f := fun a x ↦ f (timeSpaceCons (max 0 a) x))
  · intro a
    have hslice : ContDiff ℝ (k + 2) (fun x ↦ f (timeSpaceCons (max 0 a) x)) :=
      hf.contDiff_forward_spatialSlice (le_max_left 0 a)
    exact hslice.of_le (by norm_cast; omega)
  · exact fun i hi ↦ hf.continuous_iteratedFDeriv_forward_spatialSlice
      (by exact_mod_cast hi.trans (Nat.add_le_add_left hj k))

end WaveEquation
