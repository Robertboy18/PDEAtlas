/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.LaxOleinik.NullRepresentative
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.UniformlyConvex
import CAS.ExactTactic

/-!
# A uniformly convex flux with unbounded second derivative

The flux `r⁴/4 + r²/2 + 2r - 3` has second derivative `3r² + 1`, bounded below by one
and with no finite upper bound (`nonquadraticFlux_no_deriv2_upper`). For the two-jump
datum with a spike at one point, the Lax–Oleinik solution is bounded by `2` almost
everywhere, whatever the height of the spike (`nonquadraticFlux_spiked_bound`, from
`ae_norm_solution_le_of_deriv2_lower_bound`).
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- The flux `r⁴/4 + r²/2 + 2r - 3`. -/
def nonquadraticFlux (r : ℝ) : ℝ :=
  r ^ 4 / 4 + r ^ 2 / 2 + 2 * r - 3

/-- The flux is `C²`. -/
theorem nonquadraticFlux_contDiff : ContDiff ℝ 2 nonquadraticFlux := by
  unfold nonquadraticFlux
  fun_prop

/-- The derivative of the flux is `r³ + r + 2`. -/
theorem nonquadraticFlux_deriv (r : ℝ) :
    deriv nonquadraticFlux r = r ^ 3 + r + 2 := by
  cas

/-- The second derivative of the flux is `3r² + 1`. -/
theorem nonquadraticFlux_deriv2 (r : ℝ) :
    deriv (deriv nonquadraticFlux) r = 3 * r ^ 2 + 1 := by
  have hfirst : deriv nonquadraticFlux = fun q ↦ q ^ 3 + q + 2 :=
    funext nonquadraticFlux_deriv
  rw [hfirst]
  cas

/-- A uniform positive lower bound holds at every real state. -/
theorem nonquadraticFlux_deriv2_lower (r : ℝ) :
    1 ≤ deriv (deriv nonquadraticFlux) r := by
  rw [nonquadraticFlux_deriv2]
  nlinarith [sq_nonneg r]

/-- This flux admits no finite global upper bound on its second derivative. -/
theorem nonquadraticFlux_no_deriv2_upper :
    ¬ ∃ B : ℝ, ∀ r, deriv (deriv nonquadraticFlux) r ≤ B := by
  rintro ⟨B, hB⟩
  have h := hB (B + 1)
  rw [nonquadraticFlux_deriv2] at h
  nlinarith [sq_nonneg (B + 5 / 6)]

/-- The solution with the spiked datum is bounded by `2` almost everywhere, for every spike
height `A`. -/
theorem nonquadraticFlux_spiked_bound (A : ℝ) :
    ∀ᵐ p : ℝ^2, ‖solution nonquadraticFlux (spikedDatum A) p‖ ≤ (2 : ℝ) := by
  apply ae_norm_solution_le_of_deriv2_lower_bound nonquadraticFlux_contDiff
    (by norm_num) nonquadraticFlux_deriv2_lower (spikedDatum_memLp A) (K := 2)
  filter_upwards [spikedDatum_ae_eq A] with x hx
  rw [hx]
  by_cases h : x ∈ Set.Icc (0 : ℝ) 1 <;> norm_num [roughDatum, h]

end PDE.Examples.ConservationLaw.LaxOleinik
