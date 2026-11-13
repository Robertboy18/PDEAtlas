/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Patching
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Translation of autonomous viscosity subsolutions

Space, time, and value translations preserve the equation with an autonomous
Hamiltonian. The domain condition is explicit so that the same lemma applies
to forward shifts and to backward shifts on a smaller time domain.
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Translate a subsolution in spacetime and subtract a constant. Autonomy
ensures that moving the contact point does not change the Hamiltonian. -/
theorem IsSpatialViscositySubsolution.translate_sub_const {H : E → ℝ} {U V : Set (E × ℝ)}
    {u : E × ℝ → ℝ} (hu : IsSpatialViscositySubsolution (fun p _ ↦ H p) U u) (a : E × ℝ) (c : ℝ)
    (hV : IsOpen V) (hmap : MapsTo (· + a) V U) :
    IsSpatialViscositySubsolution (fun p _ ↦ H p) V (fun z ↦ u (z + a) - c) := by
  refine ⟨hV, fun z hz φ hφ hcontact ↦ ?_⟩
  let ψ : E × ℝ → ℝ := fun w ↦ φ (w - a) + c
  have hψ : ContDiffAt ℝ 1 ψ (z + a) := by
    have hφ' : ContDiffAt ℝ 1 φ ((z + a) - a) := by simpa using hφ
    exact (hφ'.comp (z + a) (contDiffAt_id.sub contDiffAt_const)).add contDiffAt_const
  have htest : IsLocalMaxOn (fun w ↦ u w - ψ w) U (z + a) := by
    apply IsLocalMax.isLocalMaxOn
    have hnear : ∀ᶠ w in 𝓝 (z + a),
        u ((w - a) + a) - c - φ (w - a) ≤ u (z + a) - c - φ z := by
      have h := hcontact.isLocalMax (hV.mem_nhds hz)
      have hc : Tendsto (fun w : E × ℝ ↦ w - a) (𝓝 (z + a)) (𝓝 z) := by
        have hc : ContinuousAt (fun w : E × ℝ ↦ w - a) (z + a) :=
          continuousAt_id.sub continuousAt_const
        change Tendsto _ _ (𝓝 ((z + a) - a)) at hc
        simpa using hc
      exact hc h
    filter_upwards [hnear] with w hw
    dsimp only [ψ]
    simp only [sub_add_cancel, add_sub_cancel_right] at *
    linarith only [hw]
  have hd : fderiv ℝ ψ (z + a) = fderiv ℝ φ z := by
    simp only [ψ, fderiv_add_const, fderiv_comp_sub, add_sub_cancel_right]
  have h := hu.2 (z + a) (hmap hz) ψ hψ htest
  rw [← spatialJetOperator_fderiv (H := fun p _ ↦ H p) hψ.differentiableAt_one] at h
  rw [← spatialJetOperator_fderiv (H := fun p _ ↦ H p) hφ.differentiableAt_one]
  simpa only [spatialJetOperator, hd] using h

end HamiltonJacobi
