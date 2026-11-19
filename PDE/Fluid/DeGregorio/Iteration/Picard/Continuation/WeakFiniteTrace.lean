/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakH2Bound
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTraceRescaled
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Terminal traces from the weak H² continuation estimate

A normalized rescaled trajectory with locally bounded supported H² graphs
and a uniform H¹ bound has a constructed H² terminal state at finite time.
The weak energy estimate supplies the uniform graph bound, the PDE
supplies L² time control, and weak closedness constructs the terminal graph.
The hypotheses are a supported H² bound on each compact subinterval of `(a, T)` and
a uniform H¹ bound.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio

/-- Uniform H¹ control gives a supported H² terminal state for a locally H²-bounded
normalized rescaled trajectory. The limit includes the coupled velocity, the
normalization rate, and the vorticity time derivative. -/
theorem IsClassicalRescaledSolutionOn.exists_h2_terminal_of_local_h2_h1
    {fields : Fields} {ρ : ℝ → ℝ} {a t₀ T R M : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T) (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hlocal : ∀ c d : ℝ, Icc c d ⊆ Ioo a T →
      ∃ B : NNReal, ∀ t ∈ Icc c d, F t ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hH1 : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ M) :
    ∃ (B : NNReal) (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ) (C : NNReal),
      ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ K ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      (∀ t ∈ Ioo t₀ T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ C * (T - t)) ∧
      (∀ A : Set ℝ, IsCompact A →
        TendstoUniformlyOn (fun t x ↦ fields.vorticity x t) v (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.vorticity x t))
          (deriv v) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ fields.velocity x t))
          (hilbertPV v) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t x ↦ fields.velocity x t)
          (hilbertPVVelocity v) (𝓝[<] T) A) ∧
      Tendsto ρ (𝓝[<] T) (𝓝 (-hilbertPVVelocity v R / R)) ∧
      ∀ x, Tendsto (deriv (fields.vorticity x)) (𝓝[<] T)
        (𝓝 ((-hilbertPVVelocity v R / R + hilbertPV v x) * v x -
          ((-hilbertPVVelocity v R / R) * x + hilbertPVVelocity v x) * deriv v x)) := by
  obtain ⟨r₀, _, hbound⟩ :=
    hsol.exists_uniform_h2_of_local_h2_h1 ht₀ hR hK hlocal hrep hzero hnormalized hH1
  let H := succOrderAssemblyNormBound 1 1 *
    (2 * M + Real.sqrt ((M ^ 2 + ‖r₀‖ ^ 2) * Real.exp (11 * M * (T - t₀))))
  have hM : 0 ≤ M := (add_nonneg lpNorm_nonneg lpNorm_nonneg).trans (hH1 t₀ ht₀)
  have hH : 0 ≤ H :=
    mul_nonneg succOrderAssemblyNormBound_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hM) (Real.sqrt_nonneg _))
  have hsub : Ioo t₀ T ⊆ Ioo a T := fun _ ht ↦ ⟨ht₀.1.trans ht.1, ht.2⟩
  refine ⟨⟨H, hH⟩, ?_⟩
  exact (hsol.mono hsub).exists_h2_terminal_normalized (B := ⟨H, hH⟩) ht₀.2 hR hK
    (fun t ht ↦ hbound t (Ioo_subset_Ico_self ht))
    (fun t ht ↦ hrep t (hsub ht)) (fun t ht ↦ hzero t (hsub ht))
    (fun t ht ↦ hnormalized t (hsub ht))

end DeGregorio
