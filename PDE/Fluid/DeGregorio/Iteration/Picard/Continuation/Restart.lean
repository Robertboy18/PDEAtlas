/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.CoupledShapeRepresentative
public import PDE.Fluid.DeGregorio.Iteration.Picard.RestartTraces

/-!
# Restarting the coupled equation from a closed H² trace

Every closed time slice supplies an H² graph bounded by the original ball.
Its continuous representative and support enclosure meet the hypotheses of
the local Picard theorem. Thus a new lifespan, curve and coupled fields are
constructed from the trace at any time `t ∈ [0, T]`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A coupled solution can be restarted at any closed time, including its
terminal time. The new solution starts from the vorticity at that time, and its
Hilbert coefficient, normalized velocity and spatial derivative match there. It is the
only coupled output from that datum in the enlarged supported H² ball. -/
theorem IsHkFrozenOutput.exists_restart
    {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
    {F : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
    {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hR : 0 ≤ R) (t : Icc (0 : ℝ) T) :
    ∃ (V₀ : W^{2,2}((Set.univ : Set (ℝ^1))))
      (S : ℝ) (hS : 0 < S) (D : NNReal)
      (G : C(Icc (0 : ℝ) S,
        supportedHkBaseBall 1 2 univ
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
            Icc (-(R * Real.exp 2)) (R * Real.exp 2)) D))
      (d z : ℝ → ℝ → ℝ),
      ‖V₀‖ ≤ B ∧
      wkpBaseCoordinateCLM V₀ = (F t).val ∧
      IsHkFrozenOutput hS.le G G V₀ (fun x ↦ w x t) d z ∧
      IsClassicalSolutionOn 1
        ⟨z, fun x s ↦ hilbertPVVelocity (fun y ↦ z y s) x⟩ (Ioo 0 S) ∧
      ((fun x ↦ w x t) = (fun x ↦ z x 0) ∧
        deriv (fun x ↦ w x t) = deriv (fun x ↦ z x 0) ∧
        (fun x ↦ c x t) = (fun x ↦ d x 0) ∧
        (fun x ↦ hkCurveHilbertVelocity hT F x t) =
          (fun x ↦ hkCurveHilbertVelocity hS.le G x 0)) ∧
      ∀ (H : C(Icc (0 : ℝ) S,
          supportedHkBaseBall 1 2 univ
            (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹'
              Icc (-(R * Real.exp 2)) (R * Real.exp 2)) D))
        (e v : ℝ → ℝ → ℝ),
        IsHkFrozenOutput hS.le H H V₀ (fun x ↦ w x t) e v → H = G := by
  obtain ⟨V₀, hVbound, hVbase⟩ := (F t).property.1
  have hrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM V₀) : ℝ → ℝ)
      =ᵐ[volume] fun x ↦ w x t := by
    rw [hVbase]
    exact h.representative t
  obtain ⟨S, hS, D, G, d, z, hG, _, huniq⟩ :=
    exists_hkCurve_local_solution_unique_in_ball hR V₀
      (h.continuous.comp (continuous_id.prodMk continuous_const))
      hrep (fun x hx ↦ h.support x t t.property hx)
  refine ⟨V₀, S, hS, D, G, d, z, hVbound, hVbase, hG,
    hG.isClassicalSolutionOn_hilbertPVVelocity, ?_, huniq⟩
  exact h.spatial_fields_eq_of_base_eq hG t ⟨0, le_rfl, hS.le⟩
    (hVbase.symm.trans hG.initial_base.symm)

end DeGregorio.Iteration
