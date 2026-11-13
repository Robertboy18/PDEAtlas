/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Evolution.TimeDerivative
public import PDE.Analysis.Evolution.Time.ExponentialConvergence
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Sobolev convergence from coordinate limits and time derivatives

Limits of the `Lᵖ` coordinates satisfy the weak spatial derivative identities
by closedness of the graph space. Exponential bounds on coordinate
time derivatives give a limit in that space, together with a graph-norm rate.
Neither a graph-norm derivative nor a Sobolev limiting state is assumed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Convergence of all derivative coordinates is convergence in the finite
Sobolev ambient product. -/
theorem tendsto_ambient_of_coordinates {ι : Type*} {l : Filter ι}
    {u : ι → WkpAmbientOn n k p Ω} {v : WkpAmbientOn n k p Ω}
    (h : ∀ a, Tendsto (fun s ↦ u s a) l (𝓝 (v a))) :
    Tendsto u l (𝓝 v) := by
  let e := PiLp.continuousLinearEquiv p ℝ (fun _ : DerivIndex n k ↦ DerivLp n p Ω)
  exact e.symm.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

/-- Coordinate limits of Sobolev elements form a Sobolev element.
The limiting spatial weak-derivative identities follow from closedness. -/
theorem WkpSpaceOn.exists_limit_of_coordinates {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{k,p}(Ω)} {v : WkpAmbientOn n k p Ω}
    (h : ∀ a, Tendsto (fun s ↦ (u s).val a) l (𝓝 (v a))) :
    ∃ V : W^{k,p}(Ω), V.val = v ∧ Tendsto u l (𝓝 V) := by
  have hamb := tendsto_ambient_of_coordinates h
  have hv : v ∈ wkpSubmoduleOn n k p Ω :=
    (isClosed_WkpSubmoduleOn n k p Ω).mem_of_tendsto hamb
      (Filter.Eventually.of_forall fun s ↦ (u s).property)
  exact ⟨⟨v, hv⟩, rfl, tendsto_subtype_rng.mpr hamb⟩

/-- Exponentially decaying coordinate time derivatives yield a limit in the
Sobolev graph norm. The velocity is initially only an ambient `Lᵖ` tuple. -/
theorem WkpSpaceOn.exists_limit_of_coordinate_deriv_norm_le_exp
    {u : ℝ → W^{k,p}(Ω)} {v : ℝ → WkpAmbientOn n k p Ω}
    {a C γ : ℝ} (hγ : 0 < γ)
    (hderiv : ∀ t ∈ Ici a, ∀ i,
      HasDerivAt (fun s ↦ (u s).val i) (v t i) t)
    (hmeas : AEStronglyMeasurable v (volume.restrict (Ioi a)))
    (hbound : ∀ t ∈ Ioi a, ∑ i, ‖v t i‖ ≤ C * Real.exp (-γ * t)) :
    ∃ limit : W^{k,p}(Ω), Tendsto u atTop (𝓝 limit) ∧
      ∀ t ∈ Ici a, ‖limit - u t‖ ≤ C * Real.exp (-γ * t) / γ := by
  obtain ⟨L, hL, hrate⟩ :=
    PDE.Analysis.Evolution.exists_limit_of_hasDerivAt_norm_le_exp hγ
      (fun t ht ↦ hasDerivAt_ambient_of_coordinates (hderiv t ht)) hmeas
      (fun t ht ↦ (PiLp.norm_le_sum_norm (v t)).trans (hbound t ht))
  have hgraph : L ∈ wkpSubmoduleOn n k p Ω :=
    (isClosed_WkpSubmoduleOn n k p Ω).mem_of_tendsto hL
      (Filter.Eventually.of_forall fun t ↦ (u t).property)
  exact ⟨⟨L, hgraph⟩, tendsto_subtype_rng.mpr hL, hrate⟩

end SobolevSpace.GraphSpace
