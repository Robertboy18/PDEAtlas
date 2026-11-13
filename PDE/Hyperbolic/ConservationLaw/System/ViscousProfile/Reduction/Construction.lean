/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Local
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Curvature
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.VectorField

/-!
# Constructing the local profile graph from the flux

The smooth flux supplies an augmented remainder with zero first jet.
The local invariant-graph theorem constructs the graph, including containment
of all small complete orbits. Its physical reduced equation is the integrated
profile equation, and its scalar curvature is the directional
derivative of the characteristic speed.
-/

@[expose] public noncomputable section

open Filter Metric
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Evolution

/-- Construct a C² graph for a selected simple characteristic family of a
smooth flux. The graph, its curvature, and its differential invariance are
conclusions. The local eigenvector and speed enter only through their
eigenvalue identity and first derivatives. -/
theorem exists_local_profile_graph {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Module.Basis ι ℝ E) {flux : E → E} (hflux : ContDiff ℝ ∞ flux) (q : E)
    (eig : ι → ℝ) (heig : Function.Injective eig) (k : ι)
    (hdiag : ∀ i, fderiv ℝ flux q (b i) = eig i • b i) {r : E → E} {a : E → ℝ}
    (hr : DifferentiableAt ℝ r q) (ha : DifferentiableAt ℝ a q) (hrq : r q = b k)
    (haq : a q = eig k) (heigen : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y (r y) = a y • r y) {R : ℝ}
    (hR : 0 < R) :
    ∃ (ρ : ℝ) (φ : (Option ι → ℝ) → (Option ι → ℝ)),
      0 < ρ ∧ ρ < R ∧ ContDiff ℝ 2 φ ∧ φ 0 = 0 ∧
      HasFDerivAt φ (diagonalCenterProjection (augmentedProfileRate eig k)) 0 ∧
      (∀ ξ, diagonalCenterProjection (augmentedProfileRate eig k) (φ ξ) =
        diagonalCenterProjection (augmentedProfileRate eig k) ξ) ∧
      (∀ ξ, φ (diagonalCenterProjection (augmentedProfileRate eig k) ξ) = φ ξ) ∧
      (∀ ξ, φ ξ none = ξ none) ∧
      (∀ z, φ (profileCenterCoordinates k z) ∈ ball 0 ρ →
        fderiv ℝ (profileGraph q b.equivFunL k φ) z
            (reducedProfileField flux q b.equivFunL k φ z, 0) =
          flux (profileGraph q b.equivFunL k φ z) - flux q -
            (eig k + z.2) • (profileGraph q b.equivFunL k φ z - q)) ∧
      iteratedDeriv 2 (fun s ↦ reducedProfileField flux q b.equivFunL k φ (s, 0)) 0 =
        fderiv ℝ a q (b k) ∧
      (∀ x ∈ ball 0 ρ,
        (∀ i, augmentedProfileRate eig k i * x i +
          augmentedProfileRemainder flux q b.equivFunL x i = 0) → x = φ x) ∧
      (∀ u : C(ℝ, Option ι → ℝ), (∀ t, u t ∈ ball 0 ρ) →
        (∀ t, HasDerivAt u (fun i ↦ augmentedProfileRate eig k i * u t i +
          augmentedProfileRemainder flux q b.equivFunL (u t) i) t) →
        ∀ t, u t = φ (u t)) := by
  let N := augmentedProfileRemainder flux q b.equivFunL
  let rate := augmentedProfileRate eig k
  have hN : ContDiff ℝ ∞ N := contDiff_augmentedProfileRemainder hflux q b.equivFunL
  have hN0 : N 0 = 0 := augmentedProfileRemainder_zero flux q b.equivFunL
  have hDN0 : fderiv ℝ N 0 = 0 := (hasFDerivAt_augmentedProfileRemainder_zero q b.equivFunL
      ((hflux.differentiable (by simp)) q)).fderiv
  obtain ⟨ρ, φ, hρ, hρR, hφ, hφ0, hDφ, hproj, hφproj, hinvariant, heq, horbit⟩ :=
    exists_local_diagonalInvariantGraph rate hN hN0 hDN0 hR
  have hparameter (ξ : Option ι → ℝ) : φ ξ none = ξ none := by
    have hp := congrFun (hproj ξ) none
    simpa only [diagonalCenterProjection_apply, rate, augmentedProfileRate, ite_true] using hp
  refine ⟨ρ, φ, hρ, hρR, hφ, hφ0, hDφ, hproj, hφproj, hparameter, ?_, ?_, heq, horbit⟩
  · intro z hz
    apply fderiv_profileGraph_apply_reducedProfileField b flux q eig heig k hdiag z
      (hφ.differentiable (by norm_num) _) (hparameter _)
    exact hinvariant (profileCenterCoordinates k z) (rate_mul_profileCenterCoordinates eig k z) hz
  · exact iteratedDeriv_two_augmentedProfileRemainder_graph b
      (hflux.of_le (by simp)) q eig k hdiag hr ha hrq haq heigen hφ.contDiffAt hφ0 hDφ
      (fun s ↦ hparameter (profileCenterCoordinates k (s, 0)))

end PDE.Hyperbolic.ConservationLaw.System
