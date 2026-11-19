/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.VectorSemigroup
public import PDE.Parabolic.Heat.WholeSpace.GaussianFlowL2
public import PDE.Fluid.Incompressible.LerayProjection.Sobolev

/-!
# The initial trace of the heat flow in `L²`

The heat flow `e^{tΔ} f` of a square-integrable vector field on `ℝⁿ` tends to `f` in `L²` as
`t → 0⁺` (`tendsto_eLpNorm_gaussianFlow_sub_self`): as an element of vector `H⁰` the field is
moved by the strongly continuous heat semigroup, whose components are the heat flows of the
components. At positive times the heat flow depends only on the almost-everywhere class of the
data (`gaussianFlow_congr_ae`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal ENNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- The heat flow at a positive time depends only on the almost-everywhere class of the data. -/
theorem gaussianFlow_congr_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t : ℝ} (ht : 0 < t) {f g : ℝ^n → E} (h : f =ᵐ[volume] g) :
    gaussianFlow t f = gaussianFlow t g := by
  funext x
  rw [gaussianFlow_apply ht, gaussianFlow_apply ht]
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- **The heat flow has the initial trace `f` in `L²`.** For a square-integrable vector field
`f` on `ℝⁿ`, `‖e^{tΔ} f - f‖_{L²} → 0` as `t → 0⁺`. -/
theorem tendsto_eLpNorm_gaussianFlow_sub_self {f : ℝ^n → ℝ^n} (hf : MemLp f 2 volume) :
    Tendsto (fun t ↦ eLpNorm (gaussianFlow t f - f) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  have hj (j : Fin n) : MemLp (fun x ↦ f x j) 2 (domainMeasure n univ) := by
    have h := (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).comp_memLp' hf
    simp only [domainMeasure, Measure.restrict_univ]
    exact h
  set U : VectorH n 0 := WithLp.toLp 2 fun j ↦ lpToZeroOrder ((hj j).toLp _)
  have hbase (j : Fin n) : baseRepresentative (U j) =ᵐ[volume] fun x ↦ f x j := by
    have h := (hj j).coeFn_toLp
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  -- the row of `e^{tΔ} U - U` is `e^{tΔ} f - f`
  have hrow {t : ℝ} (ht : 0 < t) : eLpNorm (gaussianFlow t f - f) 2 volume ≤
      ENNReal.ofReal ‖vectorHeat n 0 t.toNNReal U - U‖ := by
    have hT : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
    have hcomp (j : Fin n) : baseRepresentative ((vectorHeat n 0 t.toNNReal U - U) j)
        =ᵐ[volume] fun x ↦ (gaussianFlow t f x - f x) j := by
      have h₁ := baseRepresentative_sub_ae (vectorHeat n 0 t.toNNReal U j) (U j)
      simp only [domainMeasure, Measure.restrict_univ] at h₁
      have h₂ := baseRepresentative_heatSobolev t.toNNReal (U j)
      rw [hT, gaussianFlow_congr_ae ht (hbase j)] at h₂
      filter_upwards [h₁, h₂, hbase j] with x e₁ e₂ e₃
      rw [PiLp.sub_apply, e₁, vectorHeat_apply, e₂, e₃, PiLp.sub_apply,
        gaussianFlow_component t one_le_two hf x j]
    have hae : (l2SobolevRow (baseIndex n 0) (vectorHeat n 0 t.toNNReal U - U) : ℝ^n → ℝ^n)
        =ᵐ[volume] gaussianFlow t f - f := by
      have h := Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex n 0)
        ((vectorHeat n 0 t.toNNReal U - U) j))
      simp only [domainMeasure, Measure.restrict_univ] at h
      filter_upwards [h, ae_all_iff.mpr hcomp] with x e₁ e₂
      refine PiLp.ext fun j ↦ ?_
      rw [l2SobolevRow_apply, e₁ j, wkpCoordinateCLM_apply]
      exact e₂ j
    have hnorm := IncompressibleFlow.norm_l2SobolevRow_le (baseIndex n 0)
      (vectorHeat n 0 t.toNNReal U - U)
    rw [Lp.norm_def] at hnorm
    simp only [domainMeasure, Measure.restrict_univ] at hnorm
    rw [← eLpNorm_congr_ae hae]
    have hfin : eLpNorm (⇑(l2SobolevRow (baseIndex n 0) (vectorHeat n 0 t.toNNReal U - U))) 2
        volume ≠ ⊤ := by
      simpa only [domainMeasure, Measure.restrict_univ] using
        Lp.eLpNorm_ne_top (l2SobolevRow (baseIndex n 0) (vectorHeat n 0 t.toNNReal U - U))
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hlim : Tendsto (fun t : ℝ ↦ vectorHeat n 0 t.toNNReal U) (𝓝[>] 0) (𝓝 U) := by
    have h0 : Tendsto Real.toNNReal (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have h := ((continuous_vectorHeat U).tendsto 0).comp h0
    rwa [vectorHeat_zero] at h
  have hlim' : Tendsto (fun t : ℝ ↦ ENNReal.ofReal ‖vectorHeat n 0 t.toNNReal U - U‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht using hrow ht

end HeatEquation.WholeSpace
