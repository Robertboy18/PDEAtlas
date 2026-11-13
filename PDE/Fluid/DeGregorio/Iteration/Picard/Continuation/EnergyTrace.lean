/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.EnergyGraph
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTraceRescaled

/-!
# Terminal states from the smooth rescaled H¹ bound

The coupled H² energy estimate and the rescaled finite-trace construction
compose directly. A uniform H¹ bound on the normalized rescaled
vorticity constructs its supported H² terminal graph and all coupled traces.
Joint C³ regularity is assumed on the open cylinder `ℝ × (a, T)`, and the H² bound
up to `T` is derived.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio

/-- A smooth normalized rescaled trajectory with uniformly bounded H¹ norm
has a constructed supported H² terminal state. The quantitative graph radius
comes from the initial H² energy and the H¹ Grönwall coefficient. The
velocity, rate, and vorticity time derivative have the corresponding traces. -/
theorem IsClassicalRescaledSolutionOn.exists_h2_terminal_of_h1On
    {fields : Fields} {ρ : ℝ → ℝ} {F : ℝ → DerivLp 1 2 univ} {L R B a t₀ T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hw : ContDiffOn ℝ 3 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T) (hL : 0 ≤ L) (hR : 0 < R)
    (hsupp : ∀ t ∈ Ioo a T, tsupport (fun x ↦ fields.vorticity x t) ⊆ Ioo (-L) L)
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hinput : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t)) :
    let H := 4 * succOrderAssemblyNormBound 1 1 *
      Real.sqrt (sobolevEnergyTwo fields.vorticity L t₀ * Real.exp (11 * B * (T - t₀)))
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ) (C : NNReal),
      ‖U‖ ≤ H ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-L) L) H ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ Icc (-L) L ∧
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
  let H := 4 * succOrderAssemblyNormBound 1 1 *
    Real.sqrt (sobolevEnergyTwo fields.vorticity L t₀ * Real.exp (11 * B * (T - t₀)))
  have hH : 0 ≤ H :=
    mul_nonneg (mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg) (Real.sqrt_nonneg _)
  have hsub : Ioo t₀ T ⊆ Ioo a T := fun _ ht ↦ ⟨ht₀.1.trans ht.1, ht.2⟩
  have hrestricted : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo t₀ T) :=
    { regularity :=
        { vorticity_differentiableAt := by
            intro x t ht
            exact hsol.regularity.vorticity_differentiableAt (hsub ht)
          velocity_differentiableAt := by
            intro x t ht
            exact hsol.regularity.velocity_differentiableAt (hsub ht) }
      transport := by
        intro x t ht
        exact hsol.transport (hsub ht)
      biotSavart := by
        intro t ht
        exact hsol.biotSavart (hsub ht) }
  have hbound := hsol.mem_supportedHkBaseBall_of_h1On hw ht₀ hL hR hsupp hzero hnormalized
    hinput hrep
  exact hrestricted.exists_h2_terminal_normalized (B := ⟨H, hH⟩) ht₀.2 hR isCompact_Icc
    (fun t ht ↦ hbound t (Ioo_subset_Ico_self ht))
    (fun t ht ↦ hrep t (hsub ht)) (fun t ht ↦ hzero t (hsub ht))
    (fun t ht ↦ hnormalized t (hsub ht))

end DeGregorio
