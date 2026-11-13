/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Translation
public import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.LocalApproximation
import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar

/-!
# Sobolev approximation on an inward translation patch

Translate the center of convolution into the domain. The interior weak-derivative
identity then identifies every classical derivative with the translated mollification
of the corresponding weak derivative, extended by zero as an `Lᵖ` function.
Translation continuity gives convergence of all coordinates in the finite Sobolev graph.
The zero extension is used only in `Lᵖ`, never as a Sobolev function across the boundary.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Approximation.UpToBoundary

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Smooth local approximants in the full `W^{k,p}` graph norm on a patch admitting
uniform inward translations. The geometric condition is independent of `k` and `p`. -/
theorem local_approximation {Ω V : Set (ℝ^n)} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hp : p ≠ ∞) (U : W^{k,p}(Ω)) (v : ℝ^n) {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ ε ∈ Ioo 0 δ, ∀ x ∈ V ∩ Ω, Metric.closedBall (x + ε • v) ε ⊆ Ω) :
    ∃ f : ℕ → ℝ^n → ℝ, (∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m)) ∧
      ∃ A : ℕ → W^{k,p}(V ∩ Ω),
        (∀ m, baseRepresentative (A m) =ᵐ[domainMeasure n (V ∩ Ω)] f m) ∧
        Tendsto A atTop (𝓝 (restrictCLM (hV.inter hΩ).measurableSet inter_subset_right U)) := by
  let Ω' : TopologicalSpace.Opens ℝ^n := ⟨Ω, hΩ⟩
  let V' : TopologicalSpace.Opens ℝ^n := ⟨V, hV⟩
  obtain ⟨f, hf, A, hA, hlim⟩ := VectorValued.UpToBoundary.local_approximation
    (Ω := Ω') (V := V') hp (VectorValued.scalarEquiv.symm U) v hδ hball
  let e := VectorValued.scalarEquiv (k := k) (p := p) (Ω := V' ⊓ Ω')
  refine ⟨f, hf, fun m ↦ e (A m), ?_, ?_⟩
  · intro m
    change ((A m).val (baseIndex n k) : ℝ^n → ℝ) =ᵐ[domainMeasure n (V' ⊓ Ω')] f m
    simpa only [baseIndex_toList, iteratedPartialDeriv] using hA m (baseIndex n k)
  · have hres : e (VectorValued.restrictCLM (inf_le_right : V' ⊓ Ω' ≤ Ω')
        (VectorValued.scalarEquiv.symm U)) =
        restrictCLM (hV.inter hΩ).measurableSet inter_subset_right U := by
      rfl
    simpa only [Function.comp_def, hres] using (e.continuous.tendsto _).comp hlim

end SobolevSpace.Approximation.UpToBoundary
