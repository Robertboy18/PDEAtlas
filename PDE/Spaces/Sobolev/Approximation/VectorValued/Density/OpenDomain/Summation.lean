/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.LocallyFinite
public import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.Partition
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Topology
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Summation of Banach-valued interior approximations

An absolutely summable series in the complete Sobolev graph has the expected pointwise
sum in every derivative coordinate almost everywhere. A locally finite sum of smooth
Banach-valued functions is smooth on the open domain where its supports are locally finite.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Manifold Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Absolute graph-norm summability gives the expected almost everywhere sum in every
Banach-valued derivative coordinate. -/
theorem coordinate_tsum_ae (E : ℕ → W^{k,p}(Ω; F))
    (hE : Summable (fun i ↦ ‖E i‖)) (a : DerivIndex n k) :
    ((∑' i, E i).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ ∑' i, (E i).val a x := by
  let B := coordinateCLM (F := F) (p := p) (Ω := Ω) a
  have hB : Summable (fun i ↦ ‖B (E i)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun i ↦ norm_coordinate_le a (E i)) hE
  have he : (∑' i, ‖B (E i)‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hB
  change (fun x ↦ B (∑' i, E i) x) =ᵐ[domainMeasure n Ω] _
  rw [B.map_tsum hE.of_norm]
  exact Lp.coeFn_tsum he

omit [Fact (1 ≤ p)] [CompleteSpace F] in
/-- Local finiteness inside an open set suffices for smoothness of a sum of ambient smooth
Banach-valued functions. No behavior is prescribed at boundary points. -/
theorem contDiffOn_finsum_of_locallyFinite (Ω : Opens ℝ^n)
    (f : ℕ → ℝ^n → F) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfin : LocallyFinite (fun i ↦ (Subtype.val : Ω → ℝ^n) ⁻¹' support (f i))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ ∑ᶠ i, f i x) Ω :=
  SobolevSpace.Approximation.OpenDomain.contDiffOn_finsum_of_locallyFinite Ω f hf hfin

end SobolevSpace.VectorValued
