/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Equilibria
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Reducing a given small complete profile

The first integral of the second-order profile supplies its augmented
ODE. Complete-orbit containment places this same profile on the invariant
graph. Projection gives the scalar ODE and its two end limits.
-/

@[expose] public noncomputable section

open Filter Metric
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Evolution

/-- A small complete viscous profile is the lift of its center
coordinate, which satisfies the reduced equation with the original end limits. -/
theorem IsViscousProfile.scalar_reduction {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : Differentiable ℝ flux)
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) (q uR : ℝ^m) (eig : Fin m → ℝ)
    (heig : Function.Injective eig) (k : Fin m) (hdiag : ∀ i, fderiv ℝ flux q (b i) = eig i • b i)
    {φ : (Option (Fin m) → ℝ) → (Option (Fin m) → ℝ)}
    (hproject : ∀ ξ, φ (diagonalCenterProjection (augmentedProfileRate eig k) ξ) = φ ξ) {ρ μ : ℝ}
    (hcontain : ∀ u : C(ℝ, Option (Fin m) → ℝ), (∀ t, u t ∈ ball 0 ρ) →
      (∀ t, HasDerivAt u (fun i ↦ augmentedProfileRate eig k i * u t i +
      augmentedProfileRemainder flux q b.equivFunL (u t) i) t) → ∀ t, u t = φ (u t))
    {v : ℝ → ℝ^m} (hv : IsViscousProfile flux q uR (eig k + μ) v)
    (hsmall : ∀ t, augmentedProfileCoordinates b.equivFunL (v t - q, μ) ∈ ball 0 ρ) :
    let x := fun t ↦ b.equivFunL (v t - q) k
    (∀ t, v t = profileGraph q b.equivFunL k φ (x t, μ)) ∧
      (∀ t, HasDerivAt x (reducedProfileField flux q b.equivFunL k φ (x t, μ)) t) ∧
      Tendsto x atBot (𝓝 0) ∧ Tendsto x atTop (𝓝 (b.equivFunL (uR - q) k)) := by
  let X : C(ℝ, Option (Fin m) → ℝ) := ⟨fun t ↦ augmentedProfileCoordinates b.equivFunL (v t - q, μ),
      (augmentedProfileCoordinates b.equivFunL).continuous.comp
        ((hv.contDiff.continuous.sub continuous_const).prodMk continuous_const)⟩
  have hX (t : ℝ) : HasDerivAt X (fun i ↦ augmentedProfileRate eig k i * X t i +
        augmentedProfileRemainder flux q b.equivFunL (X t) i) t := by
    have hv' : HasDerivAt v (flux (v t) - flux q - (eig k + μ) • (v t - q)) t := by
      rw [← hv.first_integral hflux t]
      exact (hv.contDiff.differentiable (by norm_num) t).hasDerivAt
    have hd := (augmentedProfileCoordinates b.equivFunL).hasFDerivAt.comp_hasDerivAt t
      ((hv'.sub_const q).prodMk (hasDerivAt_const t μ))
    rwa [augmentedProfileCoordinates_integrated_field b flux q eig k hdiag (v t) μ] at hd
  have hsame := hcontain X hsmall hX
  let x := fun t ↦ b.equivFunL (v t - q) k
  have hgraph (t : ℝ) : φ (profileCenterCoordinates k (x t, μ)) = X t := by
    have hp := hproject (X t)
    rw [diagonalCenterProjection_augmentedProfileRate eig heig k] at hp
    exact hp.trans (hsame t).symm
  change (∀ t, v t = profileGraph q b.equivFunL k φ (x t, μ)) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    simp only [profileGraph, hgraph, X, ContinuousMap.coe_mk,
      profileStateProjection_augmentedProfileCoordinates, add_sub_cancel]
  · intro t
    have hd := (ContinuousLinearMap.proj (some k) :
      (Option (Fin m) → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t (hX t)
    simpa only [reducedProfileField, hgraph, augmentedProfileRate, sub_self,
      zero_mul, zero_add, ContinuousLinearMap.proj_apply, Function.comp_def,
      X, ContinuousMap.coe_mk, augmentedProfileCoordinates_some, x] using hd
  · simpa only [Function.comp_def, sub_self, map_zero, Pi.zero_apply] using
      ((continuous_apply k).comp b.equivFunL.continuous).continuousAt.tendsto.comp
        (hv.tendsto_atBot.sub_const q)
  · exact ((continuous_apply k).comp b.equivFunL.continuous).continuousAt.tendsto.comp
      (hv.tendsto_atTop.sub_const q)

end PDE.Hyperbolic.ConservationLaw.System
