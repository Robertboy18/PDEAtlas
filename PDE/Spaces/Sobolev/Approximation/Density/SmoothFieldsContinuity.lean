/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFields
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Continuous families of smooth Sobolev functions

A family of smooth functions on `ℝ^n` whose derivatives of order at most `k` lie in `Lᵖ` and
depend continuously on a parameter in the `Lᵖ` seminorm is a continuous path in `W^{k,p}(ℝ^n)`.
Each coordinate of the graph norm is the `Lᵖ` norm of a coordinate word of partial derivatives,
which is bounded at every point by the full derivative of the same order. The same holds for
the components of smooth vector fields.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open scoped ENNReal Sobolev Topology

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SobolevSpace.GraphSpace

/-- A family of smooth functions whose derivatives through order `k` depend continuously on the
parameter in `Lᵖ` is a continuous path in `W^{k,p}(ℝ^n)`. -/
theorem continuous_wkpOfContDiff {X : Type*} [TopologicalSpace X] {G : X → ℝ^n → ℝ}
    (hG : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (G τ))
    (hmem : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (G τ)) p volume)
    (hlim : ∀ τ₀, ∀ m ≤ k, Tendsto (fun τ ↦ eLpNorm (iteratedFDeriv ℝ m (G τ) -
      iteratedFDeriv ℝ m (G τ₀)) p volume) (𝓝 τ₀) (𝓝 0)) :
    Continuous (fun τ ↦ (wkpOfContDiff (G τ) (hG τ) (hmem τ) : W^{k,p}(ℝ^n))) := by
  refine continuous_induced_rng.2 ((PiLp.continuous_toLp p _).comp (continuous_pi fun a ↦ ?_))
  refine continuous_iff_continuousAt.2 fun τ₀ ↦ ?_
  have hmemP (τ : X) : MemLp (fun x ↦ iteratedPartialDeriv a.toList (G τ) x) p
      (domainMeasure n Set.univ) :=
    PDE.memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv (hG τ) a.toList
      ((hmem τ a.toList.length a.toList_length_le).restrict Set.univ)
  change Tendsto (fun τ ↦ (hmemP τ).toLp _) (𝓝 τ₀) (𝓝 ((hmemP τ₀).toLp _))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have hm := a.toList_length_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hlim τ₀ a.toList.length hm) (fun _ ↦ zero_le) fun τ ↦ ?_
  have hsub := PDE.iteratedPartialDeriv_sub_of_contDiff a.toList
    ((hG τ).of_le (by exact_mod_cast le_top)) ((hG τ₀).of_le (by exact_mod_cast le_top))
  simp only [domainMeasure, Measure.restrict_univ]
  change eLpNorm ((fun x ↦ iteratedPartialDeriv a.toList (G τ) x) -
    fun x ↦ iteratedPartialDeriv a.toList (G τ₀) x) p volume ≤ _
  have hdiff : (fun x ↦ iteratedPartialDeriv a.toList (G τ) x) -
      (fun x ↦ iteratedPartialDeriv a.toList (G τ₀) x) =
      fun x ↦ iteratedPartialDeriv a.toList (G τ - G τ₀) x := by
    rw [hsub]
    rfl
  rw [hdiff]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (G τ - G τ₀) := (hG τ).sub (hG τ₀)
  refine eLpNorm_mono ((PDE.contDiff_top_iteratedPartialDeriv hcd a.toList).continuous
    |>.aestronglyMeasurable) fun x ↦ ?_
  refine (PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
    (hcd.contDiffAt.of_le (by exact_mod_cast le_top))).trans (le_of_eq ?_)
  rw [iteratedFDeriv_sub ((hG τ).of_le (by exact_mod_cast le_top))
    ((hG τ₀).of_le (by exact_mod_cast le_top))]

/-- The vector form of `continuous_wkpOfContDiff`, for the components of smooth vector fields. -/
theorem continuous_vectorWkpOfContDiff {X : Type*} [TopologicalSpace X] {U : X → ℝ^n → ℝ^n}
    (hU : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (U τ))
    (hmem : ∀ τ, ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m (U τ)) p volume)
    (hlim : ∀ τ₀, ∀ m ≤ k, Tendsto (fun τ ↦ eLpNorm (iteratedFDeriv ℝ m (U τ) -
      iteratedFDeriv ℝ m (U τ₀)) p volume) (𝓝 τ₀) (𝓝 0)) :
    Continuous (fun τ ↦ (vectorWkpOfContDiff (U τ) (hU τ) (hmem τ) : Fin n → W^{k,p}(ℝ^n))) := by
  refine continuous_pi fun i ↦ ?_
  refine continuous_wkpOfContDiff (G := fun τ x ↦ U τ x i) _ _ fun τ₀ m hm ↦ ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim τ₀ m hm)
    (fun _ ↦ zero_le) fun τ ↦ ?_
  have hc (τ : X) : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ U τ x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hU τ)
  refine eLpNorm_mono (((hc τ).continuous_iteratedFDeriv (by exact_mod_cast le_top)).sub
    ((hc τ₀).continuous_iteratedFDeriv (by exact_mod_cast le_top))).aestronglyMeasurable
    fun x ↦ ?_
  rw [Pi.sub_apply, Pi.sub_apply, ← iteratedFDeriv_sub_apply
    ((hc τ).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hc τ₀).contDiffAt.of_le (by exact_mod_cast le_top)),
    ← iteratedFDeriv_sub_apply ((hU τ).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hU τ₀).contDiffAt.of_le (by exact_mod_cast le_top))]
  exact PDE.norm_iteratedFDeriv_component_le ((hU τ).sub (hU τ₀)) i m x

/-- The norm of a smooth Sobolev element is at most the sum, over its coordinates, of the `Lᵖ`
norms of the full derivatives of the corresponding orders. -/
theorem norm_wkpOfContDiff_le (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) p volume) :
    ‖(wkpOfContDiff f hf hmem : W^{k,p}(ℝ^n))‖ ≤
      ∑ a : DerivIndex n k, (eLpNorm (iteratedFDeriv ℝ a.toList.length f) p volume).toReal := by
  refine (PiLp.norm_le_sum_norm ((wkpOfContDiff f hf hmem : W^{k,p}(ℝ^n)) :
    WkpAmbientOn n k p Set.univ)).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  have hmemP : MemLp (fun x ↦ iteratedPartialDeriv a.toList f x) p
      (domainMeasure n Set.univ) :=
    PDE.memLp_iteratedPartialDeriv_of_memLp_iteratedFDeriv hf a.toList
      ((hmem a.toList.length a.toList_length_le).restrict Set.univ)
  change ‖hmemP.toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  refine ENNReal.toReal_mono (hmem _ a.toList_length_le).eLpNorm_ne_top ?_
  simp only [domainMeasure, Measure.restrict_univ]
  exact eLpNorm_mono ((PDE.contDiff_top_iteratedPartialDeriv hf a.toList).continuous
    |>.aestronglyMeasurable) fun x ↦ PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
      (hf.contDiffAt.of_le (by exact_mod_cast le_top))

end SobolevSpace.GraphSpace
