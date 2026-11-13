/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.JetOperator
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Local maxima and pasting subsolutions

A maximum of two subsolutions is a subsolution. One can therefore raise a
subsolution by a local subsolution, provided the latter is dominated near
the boundary of the patch. These statements use the local `C¹`
viscosity predicate and require no regularity of the Hamiltonian.
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The subsolution predicate depends only on values on its domain. -/
theorem IsSpatialViscositySubsolution.congr {H : E → E → ℝ} {U : Set (E × ℝ)} {u v : E × ℝ → ℝ}
    (hu : IsSpatialViscositySubsolution H U u) (huv : EqOn u v U) :
    IsSpatialViscositySubsolution H U v := by
  refine ⟨hu.1, fun x hx φ hφ hmax ↦ hu.2 x hx φ hφ (hmax.congr ?_ hx)⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [huv hy]

/-- The supersolution predicate depends only on values on its domain. -/
theorem IsSpatialViscositySupersolution.congr {H : E → E → ℝ} {U : Set (E × ℝ)} {u v : E × ℝ → ℝ}
    (hu : IsSpatialViscositySupersolution H U u) (huv : EqOn u v U) :
    IsSpatialViscositySupersolution H U v := by
  refine ⟨hu.1, fun x hx φ hφ hmin ↦ hu.2 x hx φ hφ (hmin.congr ?_ hx)⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [huv hy]

/-- A subsolution restricts to any smaller open domain. -/
theorem IsSpatialViscositySubsolution.mono {H : E → E → ℝ} {U V : Set (E × ℝ)} {u : E × ℝ → ℝ}
    (hu : IsSpatialViscositySubsolution H U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsSpatialViscositySubsolution H V u := by
  refine ⟨hV, fun x hx φ hφ hmax ↦ ?_⟩
  exact hu.2 x (hVU hx) φ hφ ((hmax.isLocalMax (hV.mem_nhds hx)).isLocalMaxOn U)

/-- The maximum of two viscosity subsolutions is a subsolution: an upper
test also touches a branch attaining the maximum at the contact point. -/
theorem IsSpatialViscositySubsolution.max {H : E → E → ℝ} {U : Set (E × ℝ)} {u v : E × ℝ → ℝ}
    (hu : IsSpatialViscositySubsolution H U u) (hv : IsSpatialViscositySubsolution H U v) :
    IsSpatialViscositySubsolution H U (fun x ↦ max (u x) (v x)) := by
  refine ⟨hu.1, fun x hx φ hφ hmax ↦ ?_⟩
  rcases le_total (v x) (u x) with h | h
  · apply hu.2 x hx φ hφ
    exact Filter.EventuallyLE.isLocalMaxOn
      (Eventually.of_forall fun y ↦ sub_le_sub_right (le_max_left (u y) (v y)) (φ y))
      (by rw [max_eq_left h]) hmax
  · apply hv.2 x hx φ hφ
    exact Filter.EventuallyLE.isLocalMaxOn
      (Eventually.of_forall fun y ↦ sub_le_sub_right (le_max_right (u y) (v y)) (φ y))
      (by rw [max_eq_right h]) hmax

/-- A differentiable function with nonpositive classical residual is a
viscosity subsolution. Local extrema identify the test derivative with
the function's derivative. -/
theorem isSpatialViscositySubsolution_of_differentiableOn {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u : E × ℝ → ℝ} (hU : IsOpen U) (hu : DifferentiableOn ℝ u U)
    (hres : ∀ x ∈ U, spatialJetOperator H (x, fderiv ℝ u x) ≤ 0) :
    IsSpatialViscositySubsolution H U u := by
  refine ⟨hU, fun x hx φ hφ hmax ↦ ?_⟩
  have hd := (hu x hx).differentiableAt (hU.mem_nhds hx)
  have hzero := (hmax.isLocalMax (hU.mem_nhds hx)).hasFDerivAt_eq_zero
    (hd.hasFDerivAt.sub hφ.differentiableAt_one.hasFDerivAt)
  have heq : fderiv ℝ u x = fderiv ℝ φ x := sub_eq_zero.mp hzero
  have h := hres x hx
  rwa [heq, spatialJetOperator_fderiv hφ.differentiableAt_one] at h

namespace Perron

/-- Raising a subsolution by another subsolution on an open patch preserves
the viscosity inequality if the patch agrees with the original function
near each exterior point. The dominance condition includes the patch boundary. -/
theorem isSpatialViscositySubsolution_piecewise_max {H : E → E → ℝ} {U V : Set (E × ℝ)}
    {u ψ : E × ℝ → ℝ} [DecidablePred (· ∈ V)] (hu : IsSpatialViscositySubsolution H U u)
    (hV : IsOpen V) (hψ : IsSpatialViscositySubsolution H (U ∩ V) ψ)
    (hglue : ∀ x ∈ U, x ∉ V → ∀ᶠ y in 𝓝[U] x, y ∈ V → ψ y ≤ u y) :
    IsSpatialViscositySubsolution H U (V.piecewise (fun y ↦ max (u y) (ψ y)) u) := by
  refine ⟨hu.1, fun x hx φ hφ hmax ↦ ?_⟩
  by_cases hxV : x ∈ V
  · apply ((hu.mono (hu.1.inter hV) inter_subset_left).max hψ).2 x ⟨hx, hxV⟩ φ hφ
    apply (hmax.mono inter_subset_left).congr _ ⟨hx, hxV⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [piecewise_eq_of_mem V _ _ hy.2]
  · apply hu.2 x hx φ hφ
    apply hmax.congr _ hx
    filter_upwards [hglue x hx hxV] with y hy
    by_cases hyV : y ∈ V
    · rw [piecewise_eq_of_mem V _ _ hyV, max_eq_left (hy hyV)]
    · rw [piecewise_eq_of_notMem V _ _ hyV]

end Perron

end HamiltonJacobi
