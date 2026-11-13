/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.PolynomialFamily.Norms
public import PDE.Hyperbolic.FirstOrder.Viscosity.UniformVelocity

/-!
# Time dependence in the viscous velocity estimate

The velocity estimate `exists_uniform_viscous_approximation_velocity_bound` applies to the
polynomial solution for every fixed time horizon (`exists_velocity_bound`). The same family rules
out a constant that works for all horizons, even with zero transport and zero initial data
(`not_exists_time_uniform_velocity_estimate`). This is a strong-solution example for the bound on
`u_t` in the energy estimate (17) of Evans, §7.3.2, Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2(c), Theorem 2 (Energy estimates), (17),
  p. 426.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily

open Filter MeasureTheory Set PDE.Common
open PDE.Analysis.Evolution PDE.Parabolic.Systems
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Sobolev

attribute [local instance] profileNormedSpace

/-- The polynomial state is a strong solution with the mollified zero initial datum and
forcing `jointForcing`. -/
theorem isStrongTransportDiffusionSolution_vectorState_mollified
    {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    IsStrongTransportDiffusionSolution ε 0 T
      (fun _ _ _ _ ↦ 0)
      (fun p y ↦ wkpBaseCoordinateCLM (jointForcing hT ε p) (timeSpaceCons y.1 y.2))
      (ContinuousLinearMap.piLpMap 2
        (fun _ : Fin 1 ↦ mollifierHkCLM (standardMollifier 1) hε) 0)
      (strongState T) (strongVelocity T) (vectorState 1) := by
  simpa only [map_zero] using isStrongTransportDiffusionSolution_vectorState_jointForcing hT ε

/-- For each horizon `T` the velocity estimate holds for the polynomial state, with one
constant for all `0 < ε ≤ 1`. -/
theorem exists_velocity_bound {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ v : ℝ → PiLp 2 (fun _ : Fin 1 ↦ DerivLp 1 2 univ),
        ContinuousOn v (Icc 0 T) ∧
        (v =ᵐ[volume.restrict (Ioc 0 T)] fun t ↦
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin 1 ↦
            (wkpBaseCoordinateCLM : W^{1,2}(ℝ^1) →L[ℝ] DerivLp 1 2 univ))
              (strongVelocity T t)) ∧
        ∃ t ∈ Icc 0 T,
          IsMaxOn (fun s ↦ ‖vectorState 1 s‖ + ‖v s‖) (Icc 0 T) t ∧
          ‖vectorState 1 t‖ + ‖v t‖ ≤ C * ‖jointForcing hT ε‖ := by
  obtain ⟨C, hC, h⟩ :=
    PDE.Hyperbolic.FirstOrder.exists_uniform_viscous_approximation_velocity_bound hT
      (fun (_ : Fin 1) (_ : SpaceTime 1) ↦ (0 : Matrix (Fin 1) (Fin 1) ℝ))
      (by intros; exact contDiffOn_const)
      (by intros; exact Matrix.isSymm_zero)
      0 (by intros; simp) (by intros; simp)
      (by intros; simp)
  refine ⟨C, hC, fun ε hε hε1 ↦ ?_⟩
  obtain ⟨F, Ft, _hw, _hb, _hd, _ht, he⟩ := h 0 (jointForcing hT ε)
  simpa only [norm_zero, zero_add] using he ε hε hε1
    (strongState T) (strongVelocity T) (vectorState 1)
    (isStrongTransportDiffusionSolution_vectorState_mollified hT hε)

/-- The velocity estimate with the mixed forcing norm cannot hold with one constant for all
horizons `T ≥ 1`. -/
theorem not_exists_time_uniform_velocity_estimate :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 1 ≤ T →
      ∃ v : ℝ → PiLp 2 (fun _ : Fin 1 ↦ DerivLp 1 2 univ),
        ContinuousOn v (Icc 0 T) ∧
        (v =ᵐ[volume.restrict (Ioc 0 T)] fun t ↦
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin 1 ↦
            (wkpBaseCoordinateCLM : W^{1,2}(ℝ^1) →L[ℝ] DerivLp 1 2 univ))
              (strongVelocity T t)) ∧
        ∃ t ∈ Icc 0 T,
          IsMaxOn (fun s ↦ ‖vectorState 1 s‖ + ‖v s‖) (Icc 0 T) t ∧
          ‖vectorState 1 t‖ + ‖v t‖ ≤
            C * (‖forcingLp T (T ^ 2)⁻¹‖ + ‖forcingVelocityLp T (T ^ 2)⁻¹‖) := by
  rintro ⟨C, _hC, h⟩
  apply not_exists_time_uniform_bound
  refine ⟨C, fun T hT ↦ ?_⟩
  rw [← norm_vectorState]
  obtain ⟨v, _hv, _hrep, t, _ht, hmax, hbound⟩ := h T hT
  exact (le_add_of_nonneg_right (norm_nonneg (v T))).trans
    ((hmax ⟨(lt_of_lt_of_le zero_lt_one hT).le, le_rfl⟩).trans hbound)

end PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily
