/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Fluid.Stokes.Pressure.Polynomial
public import PDE.Fluid.Stokes.Pressure.CompactTests

/-!
# The Stokes pressure on a union of balls with nonconstant force

The union of balls and the polynomial gradient load satisfy the hypotheses of the
pressure theorem. It gives a locally `L²` pressure whose work cancels the load on
every compactly supported `H¹` vector field.
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace PDE.Examples.StokesPressure

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open IncompressibleFlow.Stokes
open scoped ENNReal

/-- The pressure theorem for the nonconstant force on the bounded union of balls. Every
compactly supported `H¹` vector field is a test, and the pressure–load integrand is
integrable. -/
theorem exists_pressure_for_polynomial_force :
    ∃ p : ℝ^3 → ℝ, AEStronglyMeasurable p (domainMeasure 3 domain) ∧
      (∀ K : Set (ℝ^3), IsCompact K → K ⊆ domain → MemLp p 2 (domainMeasure 3 K)) ∧
      ∀ (v : Fin 3 → H¹(domain)) (K : Set (ℝ^3)),
        IsCompact K → K ⊆ domain →
        (∀ j, ∀ᵐ x ∂domainMeasure 3 domain, x ∉ K →
          baseRepresentative (v j) x = 0) →
        Integrable (fun x ↦ p x * (∑ j : Fin 3,
          (v j).val (singleDerivIndex 3 j) x) +
          ∑ j : Fin 3, force x j *
            baseRepresentative (v j) x)
          (domainMeasure 3 domain) ∧
        (∫ x in (domain : Set (ℝ^3)), p x * (∑ j : Fin 3,
          (v j).val (singleDerivIndex 3 j) x) +
          ∑ j : Fin 3, force x j *
            baseRepresentative (v j) x) = 0 := by
  obtain ⟨p, hp, hpLp, htest⟩ :=
    exists_pressure_of_minimizes_energy force 0
      (map_zero _) zero_minimizes_energy
  refine ⟨p, hp, hpLp, fun v K hK hKΩ hv ↦ ?_⟩
  obtain ⟨_, hint, heq⟩ := htest v K hK hKΩ hv
  refine ⟨hint, heq.symm.trans ?_⟩
  have hzero (i j : Fin 3) :
      derivCoordCLM j ((0 : H¹₀(domain; ℝ^3)) i) = 0 := by simp
  calc
    _ = ∫ _x, (0 : ℝ) ∂domainMeasure 3 domain := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure 3 domain)] with x hx
      simp only [hzero, hx, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    _ = 0 := integral_zero _ _

end PDE.Examples.StokesPressure
