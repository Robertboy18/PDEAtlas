/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Affine.IteratedDerivative
public import PDE.Analysis.Calculus.SpaceTime.ForwardDerivative

/-!
# Spatial jets of a field regular within forward time

Finite regularity within the closed forward half-space supplies actual spatial
derivatives at every nonnegative time. Clipping only the time index gives a
continuous family of these jets on all real indices; it asserts no time
differentiability of the clipped field.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis
open scoped ContDiff

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A field regular within forward time has regular spatial slices at time zero too. -/
theorem ContDiffOn.contDiff_forward_spatialSlice
    {q : ℕ∞} {f : ℝ^(n + 1) → E}
    (hf : ContDiffOn ℝ q f {p | 0 ≤ p 0}) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ q (fun x ↦ f (timeSpaceCons t x)) :=
  hf.comp_contDiff (contDiff_timeSpaceCons_spatial n t) (fun _ ↦ by simpa using ht)

/-- Every available spatial jet is jointly continuous in the clipped time index and space.
No derivative across the initial hyperplane is assumed. -/
theorem ContDiffOn.continuous_iteratedFDeriv_forward_spatialSlice
    {q : ℕ∞ω} {f : ℝ^(n + 1) → E}
    (hf : ContDiffOn ℝ q f {p | 0 ≤ p 0}) {j : ℕ} (hj : j ≤ q) :
    Continuous (fun p : ℝ × ℝ^n ↦
      iteratedFDeriv ℝ j (fun x ↦ f (timeSpaceCons (max 0 p.1) x)) p.2) := by
  let g (t : ℝ) : ℝ^n →ᴬ[ℝ] ℝ^(n + 1) :=
    { toFun := timeSpaceCons (max 0 t)
      linear := (embedWithTimeZeroCLM n).toLinearMap
      map_vadd' := by
        intro x y
        ext i
        cases i using Fin.cases <;> simp
      cont := (contDiff_timeSpaceCons_spatial n (max 0 t) (m := 0)).continuous }
  have hL (t : ℝ) : (g t).contLinear = embedWithTimeZeroCLM n := by
    rfl
  have hg : Continuous (fun p : ℝ × ℝ^n ↦ g p.1 p.2) :=
    (contDiff_timeSpaceCons_uncurry n (m := 0)).continuous.comp
      ((continuous_const.max continuous_fst).prodMk continuous_snd)
  exact PDE.continuous_iteratedFDeriv_affine_family hf uniqueDiffOn_forward_halfSpace
    g (embedWithTimeZeroCLM n) hL hg (fun t _ ↦ le_max_left 0 t) hj
