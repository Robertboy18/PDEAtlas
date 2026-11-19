/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.HigherOrder
public import PDE.Analysis.MeasureTheory.ContinuousRepresentative.Linearity

/-!
# Continuous dependence of classical whole-space Sobolev representatives

The canonical real representative defines a bounded linear map into bounded
continuous functions above the first-derivative threshold. Uniqueness of
continuous representatives gives linearity. The closed graph theorem gives
continuity from convergence in L² and uniform convergence of representatives.

Consequently, a Sobolev-continuous trajectory has representatives that vary
continuously in the uniform norm. Higher spatial smoothness follows from
the same canonical representative and the higher embedding threshold.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BesselPotentialSpace BoundedContinuousFunction Topology

namespace SobolevSpace.Fractional.HsSpaceReal

variable {n : ℕ} {s : ℝ}

/-- The canonical representative, bundled as a real linear map into bounded
continuous functions. -/
def c1RepresentativeLinearMap (hs : (n : ℝ) < 2 * (s - 1)) :
    HsSpaceReal n s →ₗ[ℝ] (ℝ^n →ᵇ ℝ) where
  toFun f := Complex.reCLM.compLeftContinuousBounded (ℝ^n)
    (BesselPotentialSpace.c1Representative (by simpa using hs) f.1)
  map_add' f g := by
    have hs0 : 0 ≤ s := by have hn := Nat.cast_nonneg (α := ℝ) n; linarith
    apply DFunLike.coe_injective
    apply map_add_of_continuous_ae_eq
      (fun u : HsSpaceReal n s ↦ (u.contDiff_c1Representative hs).continuous)
      (fun u ↦ u.c1Representative_ae_eq hs hs0)
    rw [map_add]
    exact Lp.coeFn_add _ _
  map_smul' c f := by
    have hs0 : 0 ≤ s := by have hn := Nat.cast_nonneg (α := ℝ) n; linarith
    apply DFunLike.coe_injective
    apply map_smul_of_continuous_ae_eq
      (fun u : HsSpaceReal n s ↦ (u.contDiff_c1Representative hs).continuous)
      (fun u ↦ u.c1Representative_ae_eq hs hs0)
    rw [map_smul]
    exact Lp.coeFn_smul _ _

/-- The bundled map has the original canonical point values. -/
theorem c1RepresentativeLinearMap_apply (hs : (n : ℝ) < 2 * (s - 1))
    (f : HsSpaceReal n s) (x : ℝ^n) :
    c1RepresentativeLinearMap hs f x = f.c1Representative hs x := rfl

/-- The representative map has a sequentially closed graph in the uniform norm. -/
theorem c1RepresentativeLinearMap_seqClosedGraph
    (hs : (n : ℝ) < 2 * (s - 1))
    (u : ℕ → HsSpaceReal n s) (U : HsSpaceReal n s) (F : ℝ^n →ᵇ ℝ)
    (hu : Tendsto u atTop (𝓝 U))
    (hF : Tendsto (c1RepresentativeLinearMap hs ∘ u) atTop (𝓝 F)) :
    F = c1RepresentativeLinearMap hs U := by
  have hs0 : 0 ≤ s := by have hn := Nat.cast_nonneg (α := ℝ) n; linarith
  have hbase := tendstoInMeasure_of_tendsto_Lp
    (((toL2FunCLM n hs0).continuous.tendsto U).comp hu)
  obtain ⟨σ, hσ, hlim⟩ := hbase.exists_seq_tendsto_ae
  have hrows : ∀ᵐ x ∂volume, ∀ j : ℕ,
      c1RepresentativeLinearMap hs (u j) x = toL2FunCLM n hs0 (u j) x :=
    ae_all_iff.mpr fun j ↦ (u j).c1Representative_ae_eq hs hs0
  apply DFunLike.coe_injective
  apply Measure.eq_of_ae_eq (μ := volume) _ F.continuous
    (c1RepresentativeLinearMap hs U).continuous
  filter_upwards [hlim, hrows, U.c1Representative_ae_eq hs hs0] with x hx hr hU
  have hFx : Tendsto (fun j ↦ c1RepresentativeLinearMap hs (u (σ j)) x)
      atTop (𝓝 (F x)) :=
    (((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto F).comp hF).comp
      hσ.tendsto_atTop
  have heq : F x = toL2FunCLM n hs0 U x :=
    tendsto_nhds_unique hFx (hx.congr (fun j ↦ (hr (σ j)).symm))
  exact heq.trans hU.symm

/-- The canonical real Sobolev representative depends continuously on its
datum in the uniform norm. -/
def c1RepresentativeCLM (hs : (n : ℝ) < 2 * (s - 1)) :
    HsSpaceReal n s →L[ℝ] (ℝ^n →ᵇ ℝ) :=
  ContinuousLinearMap.ofSeqClosedGraph (c1RepresentativeLinearMap_seqClosedGraph hs)

/-- The continuous linear embedding preserves the canonical point values. -/
theorem c1RepresentativeCLM_apply (hs : (n : ℝ) < 2 * (s - 1))
    (f : HsSpaceReal n s) (x : ℝ^n) :
    c1RepresentativeCLM hs f x = f.c1Representative hs x := rfl

/-- The bounded linear representative has every classical derivative supplied
by the strict higher-order Sobolev threshold. -/
theorem contDiff_c1RepresentativeCLM_of_order {r : ℕ}
    (hs : (n : ℝ) < 2 * (s - 1)) (hr : (n : ℝ) < 2 * (s - r))
    (f : HsSpaceReal n s) :
    ContDiff ℝ r (c1RepresentativeCLM hs f : ℝ^n → ℝ) :=
  f.contDiff_c1Representative_of_order hs hr

end SobolevSpace.Fractional.HsSpaceReal
