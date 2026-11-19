/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.EvenDimensions.ContinuousFamily
public import PDE.Analysis.Calculus.SpaceTime.ForwardSpatialJet

/-!
# Even-dimensional waves of forward forcing slices

The homogeneous wave with zero displacement and the forcing slice as
velocity is the Duhamel kernel. `C^(k+2)` regularity on the forward half-space
gives its jointly continuous jets through order two, including age zero.
No temporal derivative of a clipped forcing extension is taken.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- Every forward forcing slice gives a `C²` wave in space and signed age. -/
theorem contDiff_two_evenWaveSolution_forward (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (a : ℝ) :
    ContDiff ℝ 2 (evenWaveSolution k (fun _ ↦ 0) (fun x ↦ f (timeSpaceCons (max 0 a) x))) :=
  contDiff_two_evenWaveSolution k contDiff_const
    (hf.contDiff_forward_spatialSlice (le_max_left 0 a))

/-- The spatial and age jets of the forcing kernel are jointly continuous. -/
theorem continuous_iteratedFDeriv_evenWaveSolution_forward (k : ℕ) {f : ℝ^(2 * k + 2 + 1) → ℝ}
    (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun p : ℝ × ℝ^(2 * k + 2 + 1) ↦ iteratedFDeriv ℝ j
      (evenWaveSolution k (fun _ ↦ 0) (fun x ↦ f (timeSpaceCons (max 0 p.1) x))) p.2) := by
  apply continuous_iteratedFDeriv_evenWaveSolution_family k j
    (g := fun _ _ ↦ 0) (h := fun a x ↦ f (timeSpaceCons (max 0 a) x))
  · exact fun _ ↦ contDiff_const
  · intro a
    have hslice : ContDiff ℝ (k + 2) (fun x ↦ f (timeSpaceCons (max 0 a) x)) :=
      hf.contDiff_forward_spatialSlice (le_max_left 0 a)
    exact hslice.of_le (by norm_cast; omega)
  · intro i _
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
      (continuous_const : Continuous (fun _ : ℝ × ℝ^(2 * k + 2) ↦ (0 : ℝ^(2 * k + 2) [×i]→L[ℝ] ℝ)))
  · exact fun i hi ↦ hf.continuous_iteratedFDeriv_forward_spatialSlice
      (by exact_mod_cast hi.trans (Nat.add_le_add_left hj k))

end WaveEquation
