/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Slope
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.HamiltonJacobi
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Uniqueness in Evans's one-sided entropy class

This is the uniqueness statement of Evans, §3.4.3, Theorem 3.

## How it works

Evans proves the theorem by duality, solving a mollified adjoint transport problem in steps 1-7
of his proof, equations (38)-(52). We use Hamilton–Jacobi potentials instead.
Each bounded weak initial solution constructs its own Lipschitz conservative
potential. Its three-variable Oleinik condition gives semiconcavity.
Hamilton–Jacobi uniqueness identifies the potentials, and uniqueness
of weak spatial derivatives identifies the original solutions almost
everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.3(b), definition of an entropy solution, Theorem 3
  and its proof, equations (38)-(52).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal

namespace PDE.Hyperbolic.ConservationLaw

/-- Bounded weak initial solutions for a convex C² flux are unique in Evans's
Oleinik class. The two essential bounds and slope constants may differ.
The original representatives agree almost everywhere in positive spacetime. -/
theorem IsWeakInitialValueSolution.ae_eq_of_oleinik {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hconv : ConvexOn ℝ univ F) {u v : ℝ^2 → ℝ} (hu : IsWeakInitialValueSolution F g u)
    (hv : IsWeakInitialValueSolution F g v) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hvBdd : MemLp v ∞ (volume.restrict forwardHalfSpace)) (huSlope : ∃ C, HasOleinikBound u C)
    (hvSlope : ∃ C, HasOleinikBound v C) :
    u =ᵐ[volume.restrict forwardHalfSpace] v := by
  obtain ⟨Cu, hCu⟩ := huSlope
  obtain ⟨Cv, hCv⟩ := hvSlope
  obtain ⟨U, hU, hUx⟩ := hu.exists_hamiltonJacobiPotential huBdd hF.continuous
    hCu.1 hCu.ae_time_increment_space
  obtain ⟨V, hV, hVx⟩ := hv.exists_hamiltonJacobiPotential hvBdd hF.continuous
    hCv.1 hCv.ae_time_increment_space
  have hH : ContDiff ℝ 2 (fun r : ℝ^1 ↦ F (r 0)) :=
    hF.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff
  have hHconv : ConvexOn ℝ univ (fun r : ℝ^1 ↦ F (r 0)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    simpa only [PiLp.add_apply, PiLp.smul_apply] using
      hconv.2 (mem_univ (x 0)) (mem_univ (y 0)) ha hb hab
  have hUV : U =ᵐ[SobolevSpace.domainMeasure 2 forwardHalfSpace] V := by
    filter_upwards [ae_restrict_mem forwardHalfSpace.isOpen.measurableSet] with p hp
    have ht : splitSpaceTime p ∈ {z : ℝ^1 × ℝ | 0 ≤ z.2} := by
      change 0 ≤ p 0
      exact le_of_lt hp
    have he := hU.eqOn hH hHconv hV ht
    simpa only [join_splitSpaceTime] using he
  exact (hUx.congr_ae hUV (Filter.EventuallyEq.refl _ _)).unique_ae forwardHalfSpace.isOpen hVx

end PDE.Hyperbolic.ConservationLaw
