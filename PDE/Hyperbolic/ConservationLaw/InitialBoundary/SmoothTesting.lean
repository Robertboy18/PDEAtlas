/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.TimeCutoff
public import PDE.Analysis.Integration.CompactSupportLimit
public import PDE.DistributionTheory.TestFunction.NonnegativeApproximation

/-!
# Smooth testing of initial-boundary weak equations

Uniform approximation of the value and first spatial and temporal jets extends
the weak equation from smooth tests to C¹ tests. The same compact support controls the initial
slice.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common TopologicalSpace
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For locally integrable density and flux up to time zero, smooth testing
suffices for the initial-boundary weak equation with all C¹ tests. -/
theorem initialWeak_eq_zero_of_smooth {u q : ℝ^2 → E} {g : ℝ → E}
    (hu : LocallyIntegrable u (volume.restrict forwardHalfSpace))
    (hq : LocallyIntegrable q (volume.restrict forwardHalfSpace)) (hg : LocallyIntegrable g volume)
    (h : ∀ a : 𝓓((⊤ : Opens ℝ^2), ℝ), (∫ p in forwardHalfSpace,
      (∂[0] (a : ℝ^2 → ℝ)) p • u p + (∂[1] (a : ℝ^2 → ℝ)) p • q p) + ∫ x : ℝ, a !₂[0, x] • g x = 0)
    (φ : InitialValueTestFunction) :
    (∫ p in forwardHalfSpace, InteriorWeakForm.integrand u q φ p) +
      ∫ x : ℝ, φ !₂[0, x] • g x = 0 := by
  obtain ⟨K, a, hK, _, hφK, haK, hconv⟩ :=
    TestFunction.exists_smooth_jet_approximation_preserving_nonneg φ
  let b : ℕ → InitialValueTestFunction := fun k ↦
    .mk (a k) ((a k).contDiff.of_le (by simp)) (a k).hasCompactSupport (a k).tsupport_subset
  have hlim (v : ℝ^2 → E)
      (hv : LocallyIntegrable v (volume.restrict forwardHalfSpace)) (r : Fin 2) :
      Tendsto (fun k ↦ ∫ p in forwardHalfSpace, (∂[r] ((a k) : ℝ^2 → ℝ)) p • v p) atTop
        (𝓝 (∫ p in forwardHalfSpace, (∂[r] (φ : ℝ^2 → ℝ)) p • v p)) := by
    apply tendsto_integral_smul_of_uniformOn_compact hK
      (hv.integrableOn_isCompact hK) (φ.continuous_partialDeriv r)
      (fun k ↦ (b k).continuous_partialDeriv r)
    · exact fun p hp ↦ φ.partialDeriv_eq_zero_of_notMem_tsupport (fun hpφ ↦ hp (hφK hpφ)) r
    · exact Eventually.of_forall fun k p hp ↦ (b k).partialDeriv_eq_zero_of_notMem_tsupport
          (fun hpa ↦ hp ((haK k).1 hpa)) r
    · exact (hconv [r] (by simp)).tendstoUniformlyOn
  let S : Set ℝ := (fun p : ℝ^2 ↦ p 1) '' K
  have hS : IsCompact S := hK.image (EuclideanSpace.proj 1).continuous
  have hsupp {f : ℝ^2 → ℝ} (hf : tsupport f ⊆ K) : ∀ x ∉ S, f !₂[0, x] = 0 :=
    fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hp ↦ hx ⟨!₂[0, x], hf hp, by simp⟩
  have hinit : Tendsto (fun k ↦ ∫ x : ℝ, a k !₂[0, x] • g x) atTop
      (𝓝 (∫ x : ℝ, φ !₂[0, x] • g x)) := by
    apply tendsto_integral_smul_of_uniformOn_compact hS
      (hg.integrableOn_isCompact hS) (φ.contDiff.continuous.comp (by fun_prop))
      (fun k ↦ (a k).contDiff.continuous.comp (by fun_prop)) (hsupp hφK)
      (Eventually.of_forall fun k ↦ hsupp (haK k).1)
    exact ((hconv [] (by simp)).comp (fun x : ℝ ↦ !₂[0, x])).tendstoUniformlyOn
  have hall := ((hlim u hu 0).add (hlim q hq 1)).add hinit
  have hint (v : ℝ^2 → E) (hv : LocallyIntegrable v (volume.restrict forwardHalfSpace))
      (ψ : InitialValueTestFunction) (r : Fin 2) :
      IntegrableOn (fun p ↦ (∂[r] (ψ : ℝ^2 → ℝ)) p • v p) forwardHalfSpace :=
    hv.integrable_smul_left_of_hasCompactSupport
      (ψ.continuous_partialDeriv r) (ψ.hasCompactSupport_partialDeriv r)
  rw [← integral_add (hint u hu φ 0) (hint q hq φ 1)] at hall
  apply tendsto_nhds_unique hall
  refine tendsto_const_nhds.congr fun k ↦ ?_
  change 0 = ((∫ p in forwardHalfSpace, (∂[0] ((b k) : ℝ^2 → ℝ)) p • u p) +
    ∫ p in forwardHalfSpace, (∂[1] ((b k) : ℝ^2 → ℝ)) p • q p) + ∫ x : ℝ, a k !₂[0, x] • g x
  rw [← integral_add (hint u hu (b k) 0) (hint q hq (b k) 1)]
  exact (h (a k)).symm

end PDE.Hyperbolic.ConservationLaw
