/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.LaxOleinik.InitialValue

/-!
# Derivatives of the Lax–Oleinik potential

The time-first Euclidean potential is the Hopf–Lax value composed with
the spacetime equivalence. Its initial face is the oriented integral of
the datum. The coordinate equivalence transports Fréchet derivatives,
including their totalization off the differentiability set.

Joint differentiability and the Hamilton–Jacobi equation are established
almost everywhere independently of the fixed-time derivative formula.
Changing the datum on a null set leaves the primitive, potential, and chosen
footpoint solution unchanged pointwise.

In the notation of Evans, §3.4.2, `initialPotential F g` is the function `w` of (24) for the
primitive `h` of (23), and it solves (26) almost everywhere. With a continuous right inverse
`G` of `F'` in place of (28), `solution_ae_eq_partialDeriv_of_continuous_rightInverse`
identifies the formula (29) of Theorem 1 with `w_x`, as (27) anticipates.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equations (23)-(29) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common HamiltonJacobi.HopfLax
open HamiltonJacobi1D
open scoped ENNReal

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- The variational potential in time-first Euclidean coordinates,
continued to nonpositive time by its initial primitive. -/
def initialPotential (F g : ℝ → ℝ) : ℝ^2 → ℝ :=
  forwardValue (HopfLax1D.legendreTransform F)
    (fun x ↦ ∫ s in (0 : ℝ)..x, g s) ∘ scalarSpaceTimeEquiv

/-- The potential has exactly the prescribed integral primitive on its initial
face; no initial representative value is assigned to the solution. -/
theorem initialPotential_zero (F g : ℝ → ℝ) (x : ℝ) :
    initialPotential F g !₂[0, x] = ∫ s in (0 : ℝ)..x, g s := by
  simp [initialPotential]

/-- The time partial is the time component of the joint
derivative in product coordinates. -/
theorem partialDeriv_time_initialPotential (F g : ℝ → ℝ) (p : ℝ^2) :
    (∂[0] (initialPotential F g)) p = fderiv ℝ (forwardValue (HopfLax1D.legendreTransform F)
      (fun x ↦ ∫ s in (0 : ℝ)..x, g s)) (scalarSpaceTimeEquiv p) (0, 1) := by
  rw [partialDeriv, initialPotential, scalarSpaceTimeEquiv.comp_right_fderiv]
  simp

/-- The spatial partial is exactly the potential derivative used in the
weak initial-value construction. -/
theorem partialDeriv_space_initialPotential (F g : ℝ → ℝ) (p : ℝ^2) :
    (∂[1] (initialPotential F g)) p = derivativeSolution F g p := by
  rw [partialDeriv, initialPotential, scalarSpaceTimeEquiv.comp_right_fderiv]
  simp [derivativeSolution, potentialDerivative]

/-- Finiteness of the conjugate and `L∞` initial data give joint
differentiability of the potential almost everywhere. -/
theorem ae_differentiableAt_initialPotential {F g : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite F) (hg : MemLp g ∞ volume) :
    ∀ᵐ p : ℝ^2, DifferentiableAt ℝ (initialPotential F g) p := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_forwardValue
    (superlinear_scalar_legendre hFin) (HopfLax1D.convexOn_legendreTransform hFin)
    (lipschitzWith_intervalIntegral_of_memLp_top hg 0)
  exact (hK.comp scalarSpaceTimeEquiv.toContinuousLinearMap.lipschitzWith).ae_differentiableAt

/-- The partial derivatives satisfy the prescribed
Hamilton–Jacobi equation almost everywhere at positive time. -/
theorem ae_initialPotential_hamiltonJacobi {F g : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite F)
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) (hg : MemLp g ∞ volume) :
    ∀ᵐ p ∂volume.restrict (forwardHalfSpace : Set ℝ^2),
      (∂[0] (initialPotential F g)) p + F ((∂[1] (initialPotential F g)) p) = 0 := by
  have hHJ := ae_forwardValue_residual_eq_zero (superlinear_scalar_legendre hFin)
    (HopfLax1D.convexOn_legendreTransform hFin) (lipschitzWith_intervalIntegral_of_memLp_top hg 0)
  rw [hamiltonian_legendreTransform_eq hFin hconv hF] at hHJ
  have hwhole := (ae_restrict_iff' (isOpen_univ.prod isOpen_Ioi).measurableSet).mp hHJ
  have hnative := measurePreserving_scalarSpaceTimeEquiv.quasiMeasurePreserving.ae hwhole
  filter_upwards [ae_restrict_of_ae hnative,
    ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp hpU
  rw [partialDeriv_time_initialPotential, partialDeriv_space_initialPotential]
  exact hp (by simpa [forwardHalfSpace] using hpU)

/-- The footpoint formula is the spatial derivative almost
everywhere in the positive spacetime half-space. -/
theorem solution_ae_eq_partialDeriv_of_continuous_rightInverse {F G g : ℝ → ℝ}
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) (hG : Function.RightInverse G (deriv F))
    (hcont : Continuous G) (hg : MemLp g ∞ volume) :
    solution F g =ᵐ[volume.restrict forwardHalfSpace] (∂[1] (initialPotential F g)) := by
  have hFin := HopfLax1D.legendreFinite_of_surjective_deriv hconv hF hG.surjective
  have heq := costSolution_ae_eq_indicator_potentialDerivative
    (superlinear_scalar_legendre hFin) (HopfLax1D.convexOn_legendreTransform hFin)
    (fun v ↦ (HopfLax1D.hasDerivAt_legendreTransform_of_continuous_rightInverse
      hconv hF hG (hcont.continuousAt (x := v))).differentiableAt) hg
  filter_upwards [ae_restrict_of_ae heq,
    ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp hpU
  simpa only [Set.indicator_of_mem hpU, partialDeriv_space_initialPotential,
    derivativeSolution, solution] using hp

/-- Null changes of the initial representative leave the selected
footpoint solution unchanged at every spacetime point. -/
theorem solution_congr_ae {F g h : ℝ → ℝ} (hgh : g =ᵐ[volume] h) :
    solution F g = solution F h := by
  have hprimitive : (fun x ↦ ∫ s in (0 : ℝ)..x, g s) =
      (fun x ↦ ∫ s in (0 : ℝ)..x, h s) := by
    funext x
    exact intervalIntegral.integral_congr_ae (hgh.mono fun _ hx _ ↦ hx)
  funext p
  simp only [solution, costSolution, hprimitive]

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
