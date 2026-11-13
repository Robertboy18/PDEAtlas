/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Convergence

/-!
# Real smooth data in the supported Sobolev class

The Sobolev graph uses one-dimensional Euclidean coordinates, while the
transport equation uses ordinary real coordinates. The fixed coordinate
equivalence transports smooth compact data into that graph and returns the
same real L² function. This supplies initial data for the supported
Sobolev iteration class without a separate derivative certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Common PDE.Analysis.Evolution

namespace SobolevSpace.GraphSpace

/-- Smooth compact data on the real line define an element of a
supported Sobolev ball of any finite order. Its returned real coordinate
agrees almost everywhere with the original function. -/
theorem exists_supportedHkBaseBall_real_of_contDiff
    {k : ℕ} {K : Set ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hK : MeasurableSet K) (hsupport : Function.support f ⊆ K) :
    ∃ (B : ℝ)
      (F : supportedHkBaseBall 1 k univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B),
      0 < B ∧
        (oneDimensionalPushforwardL2 (F : DerivLp 1 2 univ) : ℝ → ℝ) =ᵐ[volume] f := by
  have hfe : ContDiff ℝ (⊤ : ℕ∞) (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) :=
    hf.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).contDiff
  have hce : HasCompactSupport (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) :=
    hc.comp_homeomorph (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).toHomeomorph
  have hKe : MeasurableSet (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) :=
    hK.preimage (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).continuous.measurable
  have hsupporte : Function.support (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) ⊆
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) ⁻¹' K :=
    fun _ hx ↦ hsupport hx
  obtain ⟨B, F, hB, hF⟩ :=
    exists_supportedHkBaseBall_of_contDiff (k := k) (Ω := univ) hfe hce hKe hsupporte
  refine ⟨B, F, hB, ?_⟩
  have hmp : MeasurePreserving (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
      (volume : Measure ℝ) (domainMeasure 1 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      measurePreserving_equivOfUnique_symm
  filter_upwards [oneDimensionalPushforwardL2_ae (F : DerivLp 1 2 univ),
    hmp.quasiMeasurePreserving.ae hF] with x hx hy
  simpa only [Function.comp_apply, (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).apply_symm_apply]
    using hx.trans hy

open scoped ContDiff Sobolev in
/-- Smooth compactly supported functions are representatives of H² graphs. -/
theorem exists_h2_of_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ Q : W^{2,2}(ℝ^1), realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q) = g := by
  obtain ⟨_, G, _, hG⟩ := exists_supportedHkBaseBall_real_of_contDiff (k := 2) hg hc
    MeasurableSet.univ (subset_univ _)
  obtain ⟨Q, _, hQbase⟩ := G.property.1
  refine ⟨Q, (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _)
    hg.continuous).mp ?_⟩
  apply (realLineRepresentative_lowerOrder_ae Q).symm.trans
  rw [hQbase]
  exact hG

end SobolevSpace.GraphSpace
