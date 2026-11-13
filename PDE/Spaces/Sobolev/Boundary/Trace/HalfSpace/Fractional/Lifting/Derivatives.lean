/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Regularity
public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Derivatives
import PDE.Spaces.Sobolev.Calculus.Slicing.Tangential

/-!
# Derivatives of the mollified extension

Tangential differentiation acts on the mollifier. Normal differentiation also
acts on the height cutoff, leaving a second term controlled by the boundary
`Lᵖ` norm. Both formulas use the same signed kernel profiles as the fractional
energy estimate.
-/

@[expose] public section

open PDE (coordinateLine)
open MeasureTheory Set

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem differentiableAt_mollifiedExtension (μ : Mollifier n)
    {g : ℝ^n → F} (hg : LocallyIntegrable g volume)
    {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    DifferentiableAt ℝ (mollifiedExtension μ g) (joinTangentialNormal (x, t)) := by
  apply ((contDiffOn_mollifiedExtension μ hg).contDiffAt
    ((HalfSpace.isOpen_upper (n + 1)).mem_nhds ?_)).differentiableAt (by simp)
  rw [upper_eq_preimage_split_snd_Ioi]
  simpa using ht

/-- Each tangential derivative uses the corresponding zero-mean spatial profile. -/
theorem partialDeriv_mollifiedExtension_castSucc (μ : Mollifier n)
    {g : ℝ^n → F} (hg : LocallyIntegrable g volume)
    {t : ℝ} (ht : 0 < t) (i : Fin n) (x : ℝ^n) :
    (∂[i.castSucc] (mollifiedExtension μ g)) (joinTangentialNormal (x, t)) =
      heightCutoff t • (t⁻¹ • ∫ z, μ.spatialDerivativeProfile i z • g (x - t • z)) := by
  rw [← partialDeriv_tangentialSlice t x
    (differentiableAt_mollifiedExtension μ hg ht x) i]
  have hs : tangentialSlice (mollifiedExtension μ g) t =
      fun y ↦ heightCutoff t • mollifyVector μ t g y := by
    funext y
    simp [tangentialSlice]
  rw [hs]
  simpa only [partialDeriv_mollifyVector_scale μ hg ht] using
    (PDE.partialDeriv_const_smul (heightCutoff t) (i := i) (f := mollifyVector μ t g) (x := x))

/-- The normal derivative differentiates both the cutoff and the mollification scale. -/
theorem partialDeriv_mollifiedExtension_last (μ : Mollifier n)
    {g : ℝ^n → F} (hg : LocallyIntegrable g volume)
    {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    (∂[Fin.last n] (mollifiedExtension μ g)) (joinTangentialNormal (x, t)) =
      deriv heightCutoff t • mollifyVector μ t g x +
        heightCutoff t • (t⁻¹ • ∫ z, μ.normalDerivativeProfile z • g (x - t • z)) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine _ _
    (differentiableAt_mollifiedExtension μ hg ht x), joinTangentialNormal_last]
  have hline :
      mollifiedExtension μ g ∘ coordinateLine (Fin.last n) (joinTangentialNormal (x, t)) =
        fun r ↦ heightCutoff r • mollifyVector μ r g x := by
    funext r
    have he : coordinateLine (Fin.last n) (joinTangentialNormal (x, t)) r =
        joinTangentialNormal (x, r) := by
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [coordinateLine]
    simp [he]
  rw [hline]
  have hc : HasDerivAt heightCutoff (deriv heightCutoff t) t :=
    (contDiff_heightCutoff.differentiable (by simp)).differentiableAt.hasDerivAt
  simpa only [add_comm] using (hc.fun_smul (hasDerivAt_mollifyVector_scale μ hg ht x)).deriv

end SobolevSpace.Trace.HalfSpace
