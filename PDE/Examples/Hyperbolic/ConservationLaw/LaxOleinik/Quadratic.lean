/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.Potential
public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.InitialValue
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Quadratic
import CAS.ExactTactic

/-!
# Quadratic Lax–Oleinik evolution for arbitrary essentially bounded data

For Burgers' flux `r²/2` and every essentially bounded datum, the derivative of the
Hopf–Lax potential is an essentially bounded weak solution of the initial-value problem
(`quadratic_arbitrary_memLp`, from `potentialDerivative_spec`). The minimizing-footpoint
solution for quadratic fluxes is `affineQuadraticFlux_solution` in
`PDE.Examples.Hyperbolic.ConservationLaw.LaxOleinik.AffineFlux`. For the primitive
`c y` of a constant state `c`, which is not in `L¹`, the Hopf–Lax value is
`c x - t c²/2` (`quadraticValue_affine`).
-/

@[expose] public noncomputable section

open MeasureTheory Set HamiltonJacobi.HopfLax
open PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.LaxOleinik
open scoped ENNReal

namespace PDE.Examples.ConservationLaw.LaxOleinik

/-- The derivative of the Hopf–Lax potential is an essentially bounded weak solution of
Burgers' equation with datum `g`. -/
theorem quadratic_arbitrary_memLp {g : ℝ → ℝ} (hg : MemLp g ∞ volume) :
    IsWeakInitialValueSolution (fun r : ℝ ↦ r ^ 2 / 2) g
      (potentialDerivative (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) g) ∧
    MemLp (potentialDerivative (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) g) ∞ volume := by
  have hconv : ConvexOn ℝ univ (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      ((convexOn_univ_norm (E := ℝ)).pow (fun _ _ ↦ norm_nonneg _) 2).smul
        (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
  have h := potentialDerivative_spec superlinear_norm_sq_div_two hconv hg
  have heq : hamiltonian (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) = fun r ↦ r ^ 2 / 2 := by
    funext r
    simpa only [Real.norm_eq_abs, sq_abs] using hamiltonian_norm_sq_div_two r
  simpa only [heq] using h

/-- The cost at velocity `q` exceeds `c x - t c²/2` by `t (q - c)²/2`. -/
theorem quadraticCost_minus_affine_value (c t x q : ℝ) :
    cost (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) (fun y ↦ c * y) t x q -
      (c * x - t * c ^ 2 / 2) = t / 2 * (q - c) ^ 2 := by
  simp only [cost, smul_eq_mul, Real.norm_eq_abs, sq_abs]
  cas

/-- For the primitive `c y` the Hopf–Lax value is `c x - t c²/2`, attained at velocity
`c`. -/
theorem quadraticValue_affine (c x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    value (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) (fun y ↦ c * y) t x =
      c * x - t * c ^ 2 / 2 := by
  have hlower (q : ℝ) :
      c * x - t * c ^ 2 / 2 ≤
        cost (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) (fun y ↦ c * y) t x q := by
    have h := quadraticCost_minus_affine_value c t x q
    have hs : 0 ≤ t / 2 * (q - c) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith only [h, hs]
  have heq :
      cost (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) (fun y ↦ c * y) t x c =
        c * x - t * c ^ 2 / 2 := by
    have h := quadraticCost_minus_affine_value c t x c
    simpa only [sub_self, zero_pow two_ne_zero, mul_zero, sub_eq_zero] using h
  apply le_antisymm
  · have hb : BddBelow (range
        (cost (fun r : ℝ ↦ ‖r‖ ^ 2 / 2) (fun y ↦ c * y) t x)) :=
      ⟨c * x - t * c ^ 2 / 2, by rintro _ ⟨q, rfl⟩; exact hlower q⟩
    exact (csInf_le hb (mem_range_self c)).trans_eq heq
  · exact le_csInf (range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact hlower q)

end PDE.Examples.ConservationLaw.LaxOleinik
