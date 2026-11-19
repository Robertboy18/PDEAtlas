/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Estimates
public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.FirstDerivative
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Classical
import PDE.Analysis.MeasureTheory.Lp.RadialPower

/-!
# The angular boundary barrier belongs to H¹

For dimensions at least two, the barrier's gradient has square-integrable size
`r^(a-1)` for every `0 < a ≤ 1`. The centre need only be outside the open domain:
it may be a boundary point. We construct an element of the Sobolev graph
space and identify both its value and its derivative coordinates.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.BoundaryContinuity

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set ℝ^n}

/-- The singular angular barrier has an `H¹` representative on
every bounded open domain which avoids its vertex. No boundary smoothness is needed. -/
theorem exists_angularPowerBarrier_h1 (hn : 2 ≤ n) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    {N z : ℝ^n} (hN : ‖N‖ = 1) (hz : z ∉ Ω) :
    ∃ U : W^{1,2}(Ω),
      (U.val (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        (fun x ↦ angularPowerBarrier a N (x - z)) ∧
      ∀ i : Fin n, (U.val (singleDerivIndex n i) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        ∂[i] (fun x ↦ angularPowerBarrier a N (x - z)) := by
  let b : ℝ^n → ℝ := fun x ↦ angularPowerBarrier a N (x - z)
  have hne (x : ℝ^n) (hx : x ∈ Ω) : x - z ≠ 0 := by
    intro heq
    exact hz (sub_eq_zero.mp heq ▸ hx)
  have hreg (x : ℝ^n) (hx : x ∈ Ω) : ContDiffAt ℝ 1 b x :=
    (angularPowerBarrier_contDiffAt a N (hne x hx)).comp x
      (contDiffAt_id.sub contDiffAt_const)
  have hdim : 1 ≤ Module.finrank ℝ (ℝ^n) := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hrad : MemLp (fun x : ℝ^n ↦ ‖x - z‖ ^ a) 2 (domainMeasure n Ω) :=
    memLp_norm_sub_rpow_of_isBounded hdim (by norm_num) (by norm_num)
      (by norm_num only [ENNReal.toReal_ofNat, finrank_euclideanSpace_fin]; linarith) z hbounded
  have hradD : MemLp (fun x : ℝ^n ↦ ‖x - z‖ ^ (a - 1)) 2 (domainMeasure n Ω) :=
    memLp_norm_sub_rpow_of_isBounded hdim (by norm_num) (by norm_num)
      (by norm_num only [ENNReal.toReal_ofNat, finrank_euclideanSpace_fin]; linarith) z hbounded
  have hbase : MemLp b 2 (domainMeasure n Ω) := by
    have hc : ContinuousOn b Ω :=
      fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt
    apply (hrad.const_mul 3).mono' (hc.aestronglyMeasurable hΩ.measurableSet)
    filter_upwards [self_mem_ae_restrict hΩ.measurableSet] with x hx
    have hb := angularPowerBarrier_bounds a hN (hne x hx)
    have hb0 : 0 ≤ b x := by
      dsimp [b]
      exact (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)).trans hb.1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb0] using hb.2
  have hderiv (i : Fin n) : MemLp (∂[i] b) 2 (domainMeasure n Ω) := by
    have hc : ContinuousOn (∂[i] b) Ω :=
      fun x hx ↦ (contDiffAt_partialDeriv 0 (hreg x hx) i).continuousAt.continuousWithinAt
    apply (hradD.const_mul 5).mono' (hc.aestronglyMeasurable hΩ.measurableSet)
    filter_upwards [self_mem_ae_restrict hΩ.measurableSet] with x hx
    have hshift : (∂[i] b) x =
        (∂[i] (angularPowerBarrier a N)) (x - z) := by
      unfold partialDeriv b
      rw [fderiv_comp_sub]
    rw [Real.norm_eq_abs, hshift]
    exact abs_partialDeriv_angularPowerBarrier_le ha.le ha1 hN (hne x hx) i
  obtain ⟨U, hU⟩ := exists_of_contDiffOn_memLp
    (p := (2 : ℝ≥0∞)) hΩ (fun x hx ↦ (hreg x hx).contDiffWithinAt) (fun α ↦ by
      rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
      · simpa only [baseIndex_toList, iteratedPartialDeriv] using hbase
      · simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hderiv i)
  refine ⟨U, ?_, fun i ↦ ?_⟩
  · simpa only [baseIndex_toList, iteratedPartialDeriv] using hU (baseIndex n 1)
  · simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hU (singleDerivIndex n i)

end PDE.Elliptic.BoundaryContinuity
