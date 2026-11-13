/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative.CutoffBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing boundary-strip integrals

Normal cutoff errors converge by dominated convergence: boundary vanishing gives a
uniform bound on the cutoff-test product, and the cutoff derivative eventually vanishes
at every interior point. Local integrability suffices, including both endpoint exponents.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Extension.GraphSpace.HalfSpace

open Set MeasureTheory Function Filter TopologicalSpace
open SobolevSpace.GraphSpace
open _root_.SobolevSpace.HalfSpace
open scoped ENNReal Topology Distributions RealInnerProductSpace

variable (n : ℕ)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]
variable [Fact (0 < n)]

local notation "μ₊" => (domainMeasure n ℝ^n₊)

/-- A smooth test vanishing on the boundary cancels the derivative of the boundary cutoff.
The linear vanishing estimate cancels the inverse cutoff scale, leaving an integrable
bound supported on a shrinking strip. This includes both endpoints `p = 1` and `p = ∞`. -/
theorem tendsto_integral_mul_cutoff_deriv_of_zero_on_boundary
    (u : DerivLp n p ℝ^n₊) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψ : ∀ x : ℝ^n, x (PDE.Common.lastIndex (n := n)) = 0 → ψ x = 0) :
    Tendsto (fun m ↦ ∫ x, u x *
      (∂[PDE.Common.lastIndex (n := n)]
        (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x ∂ μ₊)
      atTop (𝓝 (0 : ℝ)) := by
  let i : Fin n := PDE.Common.lastIndex (n := n)
  let ψi : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) ψ
  obtain ⟨Mψ, hMψ⟩ := (ψi.hasCompactSupport.isCompact_range
    ψi.contDiff.continuous).isBounded.subset_closedBall (0 : ℝ)
  have hM (x : ℝ^n) : |(∂[i] ψ.toFun) x| ≤ max Mψ 0 := by
    have he : ψi x = (∂[i] ψ.toFun) x := testFunction_lineDerivCLM_apply ψ _ x
    have hb : |(∂[i] ψ.toFun) x| ≤ Mψ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, he] using
        hMψ (Set.mem_range_self x)
    exact hb.trans (le_max_left _ _)
  -- Use the canonical bound so it matches `abs_partialDeriv_cutoffAway_last_le`.
  let C : ℝ := Classical.choose exists_bound_fderiv_smoothTransition_on_Icc
  let K : Set (ℝ^n) := tsupport (⇑ψ)
  have hKcomp : IsCompact K := ψ.hasCompactSupport.isCompact
  let bound : ℝ^n → ℝ := fun x ↦ (2 * C * max Mψ 0) * |(K.indicator fun x ↦ (u : ℝ^n → ℝ) x) x|
  have hbound : Integrable bound μ₊ :=
    ((((Lp.memLp u).locallyIntegrable (Fact.out : (1 : ℝ≥0∞) ≤ p)).integrableOn_isCompact
      hKcomp).integrable_indicator hKcomp.measurableSet).abs.const_mul _
  have hMeas (m : ℕ) : AEStronglyMeasurable (fun x ↦ (u : ℝ^n → ℝ) x *
      ((∂[i] (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x) * (⇑ψ) x) μ₊ :=
    ((Lp.memLp u).aestronglyMeasurable.mul
      (continuous_partialDeriv_cutoffAway (n := n) (δ := δSeq m) i).aestronglyMeasurable).mul
      ψ.contDiff.continuous.aestronglyMeasurable
  have hxΩ : ∀ᵐ x ∂ μ₊, x ∈ ℝ^n₊ := by
    simpa [domainMeasure] using ae_restrict_mem (measurableSet_upper (n := n))
  have hLim : ∀ᵐ x ∂ μ₊,
      Tendsto (fun m ↦ u x * (∂[i]
        (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hxΩ] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_partialDeriv_cutoffAway_eq_zero n hx] with m hm
    simp only [i, hm, mul_zero, zero_mul]
  have hDom (m : ℕ) : ∀ᵐ x ∂ μ₊, ‖(u : ℝ^n → ℝ) x *
      ((∂[i] (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x) * (⇑ψ) x‖ ≤
        bound x := by
    filter_upwards [hxΩ] with x hx
    by_cases hxK : x ∈ K
    · calc
        ‖u x * (∂[i]
          (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x‖
            = |u x| * |(∂[i]
                (_root_.SobolevSpace.HalfSpace.cutoffAway (n := n) (δSeq m))) x * ψ x| := by
                  simp only [Real.norm_eq_abs, abs_mul, mul_assoc]
        _ ≤ |u x| * (2 * C * max Mψ 0) := by
          gcongr
          exact abs_partialDeriv_cutoffAway_mul_testFunction_le n ψ hψ (le_max_right Mψ 0) hM
            (δSeq_pos m) hx
        _ = bound x := by simp only [bound, indicator_of_mem hxK, mul_comm]
    · simp [image_eq_zero_of_notMem_tsupport hxK, bound, indicator_of_notMem hxK]
  simpa using tendsto_integral_of_dominated_convergence (f := 0) bound hMeas hbound hDom hLim

end SobolevSpace.Extension.GraphSpace.HalfSpace
