/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.EvenDimensions.Descent
public import PDE.Hyperbolic.Models.Wave.OddDimensions.ContinuousFamily

/-!
# Continuously indexed even-dimensional waves

The constant-coordinate lift and restriction preserve joint continuity
of the finite spatial and signed-age jets. The assertion includes age zero.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

variable {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]

/-- Finite data jets give jointly continuous jets of the descended wave. -/
theorem continuous_iteratedFDeriv_evenWaveSolution_family (k s : ℕ) {g h : A → ℝ^(2 * k + 2) → ℝ}
    (hg : ∀ a, ContDiff ℝ (k + (s + 1)) (g a)) (hh : ∀ a, ContDiff ℝ (k + s) (h a))
    (hgj : ∀ j ≤ k + (s + 1),
      Continuous (fun p : A × ℝ^(2 * k + 2) ↦ iteratedFDeriv ℝ j (g p.1) p.2))
    (hhj : ∀ j ≤ k + s, Continuous (fun p : A × ℝ^(2 * k + 2) ↦ iteratedFDeriv ℝ j (h p.1) p.2)) :
    Continuous (fun p : A × ℝ^(2 * k + 2 + 1) ↦
      iteratedFDeriv ℝ s (evenWaveSolution k (g p.1) (h p.1)) p.2) := by
  have hgO (a : A) : ContDiff ℝ (k + (s + 1))
      (g a ∘ (coordinateProjection : ℝ^(2 * k + 3) →L[ℝ] ℝ^(2 * k + 2))) :=
    (hg a).comp coordinateProjection.contDiff
  have hhO (a : A) : ContDiff ℝ (k + s)
      (h a ∘ (coordinateProjection : ℝ^(2 * k + 3) →L[ℝ] ℝ^(2 * k + 2))) :=
    (hh a).comp coordinateProjection.contDiff
  have hgjO (j : ℕ) (hj : j ≤ k + (s + 1)) : Continuous (fun p : A × ℝ^(2 * k + 3) ↦
        iteratedFDeriv ℝ j (g p.1 ∘ coordinateProjection) p.2) :=
    PDE.continuous_iteratedFDeriv_comp_linear_family (f := g) (j := j)
      (L := fun _ ↦ coordinateProjection)
      (fun a ↦ (hg a).of_le (by exact_mod_cast hj)) (hgj j hj) continuous_const
  have hhjO (j : ℕ) (hj : j ≤ k + s) : Continuous (fun p : A × ℝ^(2 * k + 3) ↦
        iteratedFDeriv ℝ j (h p.1 ∘ coordinateProjection) p.2) :=
    PDE.continuous_iteratedFDeriv_comp_linear_family (f := h) (j := j)
      (L := fun _ ↦ coordinateProjection)
      (fun a ↦ (hh a).of_le (by exact_mod_cast hj)) (hhj j hj) continuous_const
  have hO (a : A) : ContDiff ℝ s
      (oddWaveSolution k (g a ∘ coordinateProjection) (h a ∘ coordinateProjection)) :=
    contDiff_oddWaveSolution k s
      (g := g a ∘ coordinateProjection) (h := h a ∘ coordinateProjection) (hgO a) (hhO a)
  let L : ℝ^(2 * k + 2 + 1) →L[ℝ] ℝ^(2 * k + 3 + 1) :=
    (spaceTimeContinuousLinearEquiv (2 * k + 3)).symm.toContinuousLinearMap ∘L
      (coordinateInclusion.prodMap (ContinuousLinearMap.id ℝ ℝ)) ∘L
        (spaceTimeContinuousLinearEquiv (2 * k + 2)).toContinuousLinearMap
  have he (a : A) : evenWaveSolution k (g a) (h a) =
      oddWaveSolution k (g a ∘ coordinateProjection) (h a ∘ coordinateProjection) ∘ L := by
    funext p
    simp only [L, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_prodMap',
      Prod.map_apply, ContinuousLinearMap.id_apply, spaceTimeContinuousLinearEquiv_apply,
      spaceTimeContinuousLinearEquiv_symm_apply, joinSpaceTime, splitSpaceTime,
      evenWaveSolution, spaceTimeUncurry]
  have hjet := PDE.continuous_iteratedFDeriv_comp_linear_family
    (f := fun a ↦ oddWaveSolution k (g a ∘ coordinateProjection) (h a ∘ coordinateProjection))
    (L := fun _ ↦ L) hO (continuous_iteratedFDeriv_oddWaveSolution_family k s
      (g := fun a ↦ g a ∘ coordinateProjection) (h := fun a ↦ h a ∘ coordinateProjection)
      hgO hhO hgjO hhjO) continuous_const
  exact hjet.congr (fun p ↦ congrArg (fun f ↦ iteratedFDeriv ℝ s f p.2) (he p.1).symm)

end WaveEquation
