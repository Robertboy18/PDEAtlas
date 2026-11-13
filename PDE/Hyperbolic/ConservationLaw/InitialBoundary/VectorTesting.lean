/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff

/-!
# Finite-coordinate vector tests for initial weak equations

The scalar-test Bochner equation is equivalent to the classical
vector-test equation with derivatives and Euclidean pairings. Finite
coordinate projections commute with integration. This includes the zero state
dimension, where both equations have no scalar coordinates.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions InnerProductSpace

namespace PDE.Hyperbolic.ConservationLaw

variable {m : ℕ} {u q : ℝ^2 → ℝ^m} {g : ℝ → ℝ^m}

private theorem initialWeakPairing_apply
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (hg : LocallyIntegrable g volume) (φ : InitialValueTestFunction) (i : Fin m) :
    ((∫ p in forwardHalfSpace, InteriorWeakForm.integrand u q φ p) + ∫ x : ℝ, φ !₂[0, x] • g x) i =
      (∫ p in forwardHalfSpace, (∂[0] (φ : ℝ^2 → ℝ)) p * u p i + (∂[1] (φ : ℝ^2 → ℝ)) p * q p i) +
      ∫ x : ℝ, φ !₂[0, x] * g x i := by
  let L : ℝ^m →L[ℝ] ℝ := EuclideanSpace.proj i
  have hs := L.integral_comp_comm (integrableOn_initialWeakIntegrand hu hq φ)
  have hgi : Integrable (fun x : ℝ ↦ φ !₂[0, x] • g x) :=
    hg.integrable_smul_left_of_hasCompactSupport
      (φ.contDiff.continuous.comp (by fun_prop)) φ.hasCompactSupport_initialSlice
  have hi := L.integral_comp_comm hgi
  change L ((∫ p in forwardHalfSpace, InteriorWeakForm.integrand u q φ p) +
    ∫ x : ℝ, φ !₂[0, x] • g x) = _
  rw [map_add, ← hs, ← hi]
  rfl

/-- Scalar C¹ tests with a vector Bochner identity are equivalent to arbitrary
vector C¹ tests with Euclidean pairings, including the initial face. -/
theorem initialWeak_eq_zero_iff_vectorTests
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace))
    (hg : LocallyIntegrable g volume) :
    (∀ φ : InitialValueTestFunction,
      (∫ p in forwardHalfSpace, InteriorWeakForm.integrand u q φ p) +
        ∫ x : ℝ, φ !₂[0, x] • g x = 0) ↔
    (∀ ψ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ^m),
      (∫ p in forwardHalfSpace,
        ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪q p, (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ) +
        ∫ x : ℝ, ⟪g x, ψ !₂[0, x]⟫_ℝ = 0) := by
  classical
  constructor
  · intro h ψ
    let a (i : Fin m) : InitialValueTestFunction :=
      TestFunction.postcompCLM (EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ) ψ
    have hd (r : Fin 2) (i : Fin m) (p : ℝ^2) :
        (∂[r] ((a i) : ℝ^2 → ℝ)) p = (∂[r] (ψ : ℝ^2 → ℝ^m)) p i :=
      (partialDeriv_apply r i ψ.contDiff.differentiable_one.differentiableAt).symm
    have hs (p : ℝ^2) : ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪q p, (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ =
          ∑ i : Fin m, ((∂[0] ((a i) : ℝ^2 → ℝ)) p * u p i +
            (∂[1] ((a i) : ℝ^2 → ℝ)) p * q p i) := by
      simp [hd, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_add_distrib]
    have hi (x : ℝ) : ⟪g x, ψ !₂[0, x]⟫_ℝ =
        ∑ i : Fin m, a i !₂[0, x] * g x i := by
      simp [a, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    have hsi (i : Fin m) : IntegrableOn (fun p ↦ (∂[0] ((a i) : ℝ^2 → ℝ)) p * u p i +
          (∂[1] ((a i) : ℝ^2 → ℝ)) p * q p i) forwardHalfSpace :=
      (EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ).integrable_comp
        (integrableOn_initialWeakIntegrand hu hq (a i))
    have hii (i : Fin m) : Integrable (fun x : ℝ ↦ a i !₂[0, x] * g x i) :=
      (EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ).integrable_comp
        (hg.integrable_smul_left_of_hasCompactSupport
          ((a i).contDiff.continuous.comp (by fun_prop)) (a i).hasCompactSupport_initialSlice)
    simp_rw [hs, hi]
    rw [integral_finsetSum _ (fun i _ ↦ hsi i), integral_finsetSum _ (fun i _ ↦ hii i),
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← initialWeakPairing_apply hu hq hg (a i) i, h (a i)]
    rfl
  · intro h φ
    ext i
    let e : ℝ^m := EuclideanSpace.single i 1
    let L : ℝ →L[ℝ] ℝ^m := (ContinuousLinearMap.id ℝ ℝ).smulRight e
    let ψ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ^m) := TestFunction.postcompCLM L φ
    have hd (r : Fin 2) (p : ℝ^2) :
        (∂[r] (ψ : ℝ^2 → ℝ^m)) p = (∂[r] (φ : ℝ^2 → ℝ)) p • e := by
      change fderiv ℝ (L ∘ φ) p (EuclideanSpace.single r 1) = _
      rw [fderiv_comp p L.differentiableAt φ.contDiff.differentiable_one.differentiableAt]
      rw [L.fderiv]
      rfl
    have hs (p : ℝ^2) : ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪q p, (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ =
          (∂[0] (φ : ℝ^2 → ℝ)) p * u p i + (∂[1] (φ : ℝ^2 → ℝ)) p * q p i := by
      simp [hd, e, inner_smul_right, EuclideanSpace.inner_single_right]
    have hi (x : ℝ) : ⟪g x, ψ !₂[0, x]⟫_ℝ = φ !₂[0, x] * g x i := by
      change ⟪g x, φ !₂[0, x] • e⟫_ℝ = _
      simp [e, inner_smul_right, EuclideanSpace.inner_single_right]
    have hv := h ψ
    simp_rw [hs, hi] at hv
    rw [initialWeakPairing_apply hu hq hg φ i]
    exact hv

end PDE.Hyperbolic.ConservationLaw
