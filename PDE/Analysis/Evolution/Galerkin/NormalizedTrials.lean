/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Evolution.Galerkin.RegularTrials
public import PDE.Analysis.Normed.KernelDensity

/-!
# Galerkin trials preserving a scalar normalization

A continuous scalar constraint selects a closed subspace of the Hilbert pivot.
Regular vectors satisfying that constraint are dense in its kernel. Applying the
regular trial construction there gives nested orthogonal trials with exact regular
reconstructions, all satisfying the normalization.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A scalar normalization can be imposed before constructing the dense regular
trial spaces. Projections have norm at most one in the inherited Hilbert norm,
and every reconstructed trial state satisfies the constraint exactly. -/
theorem exists_stableTrialSystem_with_kernel_reconstruction
    {R : Type*} [AddCommGroup R] [Module ℝ R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] [ContinuousSMul ℝ R] [SeparableSpace H]
    (J : R →ₗ[ℝ] H) (hJ : DenseRange J) (L : H →L[ℝ] ℝ) :
    ∃ trials : StableTrialSystem (GelfandTriple.identity L.ker),
      Monotone trials.space ∧ trials.stabilityConstant = 1 ∧
        ∃ reconstruct : ∀ n, trials.space n →L[ℝ] R,
          ∀ n (u : trials.space n), J (reconstruct n u) = ((u : L.ker) : H) := by
  let K := (L.toLinearMap.comp J).ker
  let J₀ : K →ₗ[ℝ] L.ker := (J.comp K.subtype).codRestrict L.ker
    (fun v ↦ v.property)
  have hJ₀ : DenseRange J₀ := by
    apply (Submodule.dense_comap_ker J.range hJ L).mono
    intro x hx
    change ∃ r, J r = (x : H) at hx
    obtain ⟨r, hr⟩ := hx
    have hrK : r ∈ K := by
      change L (J r) = 0
      rw [hr]
      exact x.property
    exact ⟨⟨r, hrK⟩, Subtype.ext hr⟩
  obtain ⟨trials, hmono, hconstant, reconstruct, hreconstruct⟩ :=
    exists_stableTrialSystem_with_reconstruction J₀ hJ₀
  refine ⟨trials, hmono, hconstant, fun n ↦ K.subtypeL.comp (reconstruct n), ?_⟩
  intro n u
  exact congrArg Subtype.val (hreconstruct n u)

end PDE.Analysis.Evolution
