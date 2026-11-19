/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Laplacian
public import Mathlib.Analysis.Calculus.Deriv.Pow
import CAS.ExactTactic

/-!
# Radial Laplacians at the axis

For a C² profile with `f'(0) = 0`, the punctured radial Laplacian tends to
`n f''(0)`. This is the regular axis value, which differs from evaluating
the totalized quotient at zero.

A profile `f(r) = φ(r²)` automatically has the required trace. Its radial
Laplacian is `2n φ'(r²) + 4r² φ''(r²)` off the axis, and its Euclidean lift
has Laplacian `n f''(0)` at the origin.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Radial

open Filter
open scoped Topology
open PDE.CoordinateSystems

/-- The derivative of a squared-radius profile only requires differentiability
of the outer profile at the squared radius. -/
theorem deriv_comp_sq (φ : ℝ → ℝ) (r : ℝ)
    (hφ : DifferentiableAt ℝ φ (r ^ 2)) :
    deriv (fun ρ : ℝ ↦ φ (ρ ^ 2)) r = 2 * r * deriv φ (r ^ 2) := by
  have hsq : HasDerivAt (fun ρ : ℝ ↦ ρ ^ 2) (2 * r) r := by cas
  simpa [Function.comp_def, mul_comm] using
    (hφ.hasDerivAt.comp (h := fun ρ : ℝ ↦ ρ ^ 2) r hsq).deriv

/-- A squared-radius profile has zero radial derivative at the axis. -/
theorem deriv_comp_sq_zero (φ : ℝ → ℝ) (hφ : DifferentiableAt ℝ φ 0) :
    deriv (fun ρ : ℝ ↦ φ (ρ ^ 2)) 0 = 0 := by
  simpa using deriv_comp_sq φ 0 (by simpa using hφ)

/-- The second derivative of a squared-radius profile is determined by its
local C² germ. -/
theorem secondDeriv_comp_sq (φ : ℝ → ℝ) (r : ℝ)
    (hφ : ContDiffAt ℝ 2 φ (r ^ 2)) :
    deriv (deriv (fun ρ : ℝ ↦ φ (ρ ^ 2))) r =
      2 * deriv φ (r ^ 2) + 4 * r ^ 2 * deriv (deriv φ) (r ^ 2) := by
  have hnear : ∀ᶠ ρ in 𝓝 r, ContDiffAt ℝ 2 φ (ρ ^ 2) :=
    (continuousAt_id.pow 2).eventually (hφ.eventually (by simp))
  have hfirst : deriv (fun ρ : ℝ ↦ φ (ρ ^ 2)) =ᶠ[𝓝 r]
      fun ρ ↦ 2 * ρ * deriv φ (ρ ^ 2) := by
    filter_upwards [hnear] with ρ hρ
    exact deriv_comp_sq φ ρ (hρ.differentiableAt (by norm_num))
  rw [hfirst.deriv_eq]
  have hdφ : ContDiffAt ℝ 1 (deriv φ) (r ^ 2) :=
    hφ.derivWithin (by norm_num)
  have hsq : HasDerivAt (fun ρ : ℝ ↦ ρ ^ 2) (2 * r) r := by cas
  have hcomp := hdφ.differentiableAt_one.hasDerivAt.comp
    (h := fun ρ : ℝ ↦ ρ ^ 2) r hsq
  have hlinear : HasDerivAt (fun ρ : ℝ ↦ 2 * ρ) 2 r := by
    simpa using (hasDerivAt_id r).const_mul 2
  have hprod : HasDerivAt (fun ρ : ℝ ↦ 2 * ρ * deriv φ (ρ ^ 2))
      (2 * deriv φ (r ^ 2) + (2 * r) * (deriv (deriv φ) (r ^ 2) * (2 * r))) r := by
    simpa only [Pi.mul_def, Function.comp_def] using hlinear.mul hcomp
  rw [hprod.deriv]
  ring

/-- The singular radial expression becomes a regular squared-radius formula
in every dimension. -/
theorem radialLaplacian_comp_sq (n : ℕ) (φ : ℝ → ℝ) {r : ℝ}
    (hr : r ≠ 0) (hφ : ContDiffAt ℝ 2 φ (r ^ 2)) :
    radialLaplacian n (fun ρ ↦ φ (ρ ^ 2)) r =
      2 * (n : ℝ) * deriv φ (r ^ 2) +
        4 * r ^ 2 * deriv (deriv φ) (r ^ 2) := by
  rw [radialLaplacian, secondDeriv_comp_sq φ r hφ,
    deriv_comp_sq φ r (hφ.differentiableAt (by norm_num))]
  field_simp [hr]
  ring

/-- A zero first derivative removes the radial singularity: the punctured
radial Laplacian converges to `n f''(0)`. -/
theorem tendsto_radialLaplacian_zero (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (haxis : deriv f 0 = 0) :
    Tendsto (radialLaplacian n f) (𝓝[≠] 0)
      (𝓝 ((n : ℝ) * deriv (deriv f) 0)) := by
  have hdf : ContDiffAt ℝ 1 (deriv f) 0 := hf.derivWithin (by norm_num)
  have hddf : ContinuousAt (deriv (deriv f)) 0 :=
    (hdf.derivWithin (m := 0) (by norm_num)).continuousAt
  have hquot : Tendsto (fun r ↦ deriv f r / r) (𝓝[≠] 0)
      (𝓝 (deriv (deriv f) 0)) := by
    have ht := hdf.differentiableAt_one.hasDerivAt.tendsto_slope
    change Tendsto (fun r ↦ slope (deriv f) 0 r) _ _ at ht
    simpa only [slope_def_field, haxis, sub_zero] using ht
  have hlim := (hddf.tendsto.mono_left nhdsWithin_le_nhds).add
    (hquot.const_mul ((n : ℝ) - 1))
  convert hlim using 1
  · ext r
    simp only [radialLaplacian, div_eq_mul_inv]
    ring
  · congr 1
    ring

/-- An equation on positive radii extends to the axis when its remaining
terms are continuous and the radial trace vanishes. -/
theorem radialLaplacian_axis_equation (n : ℕ) (f g ω : ℝ → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (haxis : deriv f 0 = 0)
    (hg : ContinuousAt g 0) (hω : ContinuousAt ω 0)
    (heq : ∀ᶠ r in 𝓝[>] 0, -(radialLaplacian n f r + g r) = ω r) :
    -((n : ℝ) * deriv (deriv f) 0 + g 0) = ω 0 := by
  have hlim := (((tendsto_radialLaplacian_zero n f hf haxis).mono_left
    (nhdsGT_le_nhdsNE 0)).add
    (hg.tendsto.mono_left nhdsWithin_le_nhds)).neg
  exact tendsto_nhds_unique hlim
    ((hω.tendsto.mono_left nhdsWithin_le_nhds).congr' (EventuallyEq.symm heq))

/-- The origin value of the Euclidean lift agrees with the limiting radial
operator, rather than the totalized radial quotient. -/
theorem laplacian_comp_norm_sq_zero (n : ℕ) (φ : ℝ → ℝ)
    (hφ : ContDiffAt ℝ 2 φ 0) :
    laplacian (fun y : ℝ^n ↦ φ (‖y‖ ^ 2)) 0 =
      (n : ℝ) * deriv (deriv (fun r : ℝ ↦ φ (r ^ 2))) 0 := by
  rw [EuclideanLaplacian.laplacian_comp_norm_sq φ 0 (by simpa using hφ),
    secondDeriv_comp_sq φ 0 (by simpa using hφ)]
  simp
  ring

end PDE.Elliptic.Radial
