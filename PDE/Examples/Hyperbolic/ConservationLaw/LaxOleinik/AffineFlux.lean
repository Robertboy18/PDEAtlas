/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.InitialValue
import CAS.ExactTactic

/-!
# Signed affine shifts in the Lax–Oleinik construction

For the flux `r²/2 + ar + b` the Legendre transform is `(v - a)²/2 - b`
(`affineQuadraticFlux_legendre`). The Lax–Oleinik solution is an essentially bounded
weak solution of the initial-value problem for every essentially bounded datum
(`affineQuadraticFlux_solution`, from `solution_spec_of_continuous_rightInverse`). The
datum `roughDatum = 1 + 𝟙_[0,1]` has a nonzero background and two jumps.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- A quadratic flux with arbitrary linear drift and arbitrary signed offset. -/
def affineQuadraticFlux (a b r : ℝ) : ℝ :=
  r ^ 2 / 2 + a * r + b

/-- The derivative of the flux is `r + a`. -/
theorem affineQuadraticFlux_hasDerivAt (a b r : ℝ) :
    HasDerivAt (affineQuadraticFlux a b) (r + a) r := by
  cas

/-- Every affine shift of the quadratic flux is convex on the whole line. -/
theorem affineQuadraticFlux_convex (a b : ℝ) :
    ConvexOn ℝ univ (affineQuadraticFlux a b) := by
  have hq : ConvexOn ℝ univ (fun r : ℝ ↦ r ^ 2 / 2) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (even_two.convexOn_pow (𝕜 := ℝ)).smul (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
  have ha' : ConvexOn ℝ univ (fun r : ℝ ↦ a * r + b) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ c d _ _ hcd
    simp only [smul_eq_mul]
    apply le_of_eq
    linear_combination -b * hcd
  convert hq.add ha' using 1
  funext r
  simp only [affineQuadraticFlux]
  cas

/-- The Legendre transform of the flux is `(v - a)²/2 - b`. -/
theorem affineQuadraticFlux_legendre (a b v : ℝ) :
    HopfLax1D.legendreTransform (affineQuadraticFlux a b) v =
      (v - a) ^ 2 / 2 - b := by
  have hG : Function.RightInverse (fun q : ℝ ↦ q - a)
      (deriv (affineQuadraticFlux a b)) := by
    intro q
    rw [(affineQuadraticFlux_hasDerivAt a b (q - a)).deriv]
    cas
  rw [HopfLax1D.legendreTransform_eq_of_rightInverse_deriv
    (affineQuadraticFlux_convex a b)
    (fun r ↦ (affineQuadraticFlux_hasDerivAt a b r).differentiableAt) hG]
  dsimp only [affineQuadraticFlux]
  cas

/-- For every essentially bounded datum `g`, the Lax–Oleinik solution is an essentially
bounded weak solution of the initial-value problem. -/
theorem affineQuadraticFlux_solution (a b : ℝ) {g : ℝ → ℝ}
    (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution (affineQuadraticFlux a b) g
      (solution (affineQuadraticFlux a b) g) ∧
      MemLp (solution (affineQuadraticFlux a b) g) ∞ volume := by
  apply solution_spec_of_continuous_rightInverse
    (G := fun q ↦ q - a) (affineQuadraticFlux_convex a b)
    (fun r ↦ (affineQuadraticFlux_hasDerivAt a b r).differentiableAt) _
    (continuous_id.sub continuous_const) hg
  intro q
  rw [(affineQuadraticFlux_hasDerivAt a b (q - a)).deriv]
  cas

/-- A bounded initial state with a nonzero background and two jumps. -/
def roughDatum (x : ℝ) : ℝ :=
  1 + (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) x

/-- `roughDatum` is essentially bounded. -/
theorem roughDatum_memLp : MemLp roughDatum ∞ volume := by
  apply memLp_top_of_bound
    ((measurable_const.add (measurable_const.indicator measurableSet_Icc)
      ).aestronglyMeasurable) 2
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> norm_num [roughDatum, hx]

end PDE.Examples.ConservationLaw.LaxOleinik
