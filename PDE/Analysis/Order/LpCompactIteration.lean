/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Order.MonotoneIteration
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Monotone iteration through a compact inclusion

Suppose `T = J ∘ R ∘ N`, where `R` is a bounded linear solution operator,
`J` is a compact inclusion into real `Lᵖ`, and `N` is continuous with linear
norm growth. If `T` is increasing and has ordered lower and upper barriers,
its lower iterates converge to the least fixed point between the barriers.

The compact set containing the orbit is not assumed. An order interval in
real `Lᵖ` is norm bounded, the growth estimate bounds `R ∘ N` on that
interval, and compactness of `J` gives a compact set containing every iterate
after the first one. Continuity of `R ∘ N` also gives convergence in the
stronger space. In elliptic applications these spaces are `L²` and `H¹₀`.
-/

@[expose] public section

noncomputable section

namespace PDE.OrderInterval

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pointwise order bounds give a norm bound without a finite-measure assumption. -/
private theorem norm_le_of_mem_lp_Icc
    {lower upper u : Lp ℝ p μ} (hu : u ∈ Icc lower upper) :
    ‖u‖ ≤ ‖upper - lower‖ + ‖lower‖ := by
  have hl : ∀ᵐ x ∂μ, lower x ≤ u x := AEEqFun.coeFn_le.mpr hu.1
  have hr : ∀ᵐ x ∂μ, u x ≤ upper x := AEEqFun.coeFn_le.mpr hu.2
  have hnorm : ‖u - lower‖ ≤ ‖upper - lower‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hl, hr, Lp.coeFn_sub u lower,
      Lp.coeFn_sub upper lower] with x hx hy hsub hsub'
    simp only [hsub, hsub', Pi.sub_apply, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hx),
      abs_of_nonneg (sub_nonneg.mpr (hx.trans hy))]
    exact sub_le_sub_right hy _
  calc
    ‖u‖ = ‖(u - lower) + lower‖ := by rw [sub_add_cancel]
    _ ≤ ‖u - lower‖ + ‖lower‖ := norm_add_le _ _
    _ ≤ ‖upper - lower‖ + ‖lower‖ := add_le_add_left hnorm _

/-- Compactness of the inclusion and linear growth of the nonlinear load
produce a convergent monotone orbit. No compactness or convergence of the
orbit is assumed. The lifted iterates converge in the stronger space too. -/
theorem exists_tendsto_iterate_of_compact_factor
    (J : V →L[ℝ] Lp ℝ p μ) (hJ : IsCompactOperator J)
    (R : Lp ℝ p μ →L[ℝ] V) (N : Lp ℝ p μ → Lp ℝ p μ)
    (hN : Continuous N) {A C : ℝ} (hC : 0 ≤ C)
    (hNgrowth : ∀ w, ‖N w‖ ≤ A + C * ‖w‖)
    (hT : Monotone (fun w ↦ J (R (N w))))
    (lower upper : Lp ℝ p μ) (hlr : lower ≤ upper)
    (hlower : lower ≤ J (R (N lower)))
    (hupper : J (R (N upper)) ≤ upper) :
    ∃ w, IsLeast
        {z | z ∈ Icc lower upper ∧ J (R (N z)) = z} w ∧
      Tendsto (fun k : ℕ ↦ (fun z ↦ J (R (N z)))^[k] lower) atTop (𝓝 w) ∧
      Tendsto (fun k : ℕ ↦ R (N ((fun z ↦ J (R (N z)))^[k] lower)))
        atTop (𝓝 (R (N w))) := by
  let T : Lp ℝ p μ → Lp ℝ p μ := fun w ↦ J (R (N w))
  let Q : ℝ := ‖upper - lower‖ + ‖lower‖
  let M : ℝ := ‖R‖ * (A + C * Q)
  have hbound {w : Lp ℝ p μ} (hw : w ∈ Icc lower upper) :
      ‖R (N w)‖ ≤ M := by
    calc
      ‖R (N w)‖ ≤ ‖R‖ * ‖N w‖ := R.le_opNorm _
      _ ≤ ‖R‖ * (A + C * ‖w‖) :=
        mul_le_mul_of_nonneg_left (hNgrowth w) (norm_nonneg _)
      _ ≤ M := mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left
          (norm_le_of_mem_lp_Icc hw) hC) A) (norm_nonneg _)
  obtain ⟨K, hK, hJK⟩ := hJ.image_closedBall_subset_compact (f := J.toLinearMap) M
  have horbit : ∀ k : ℕ, T^[k] lower ∈ insert lower K := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      apply mem_insert_of_mem
      rw [Function.iterate_succ_apply']
      apply hJK
      refine ⟨R (N (T^[k] lower)), ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hbound (iterate_mem_Icc T hT hlower hupper ⟨le_rfl, hlr⟩ k)
  have hTcont : Continuous T := J.continuous.comp (R.continuous.comp hN)
  obtain ⟨w, _, hw⟩ := exists_tendsto_of_monotone_of_isCompact
    (hT.monotone_iterate_of_le_map hlower) (hK.insert lower) horbit
  refine ⟨w, ?_, hw, (R.continuous.comp hN).continuousAt.tendsto.comp hw⟩
  exact isLeast_fixedPoint_Icc_of_tendsto_iterate T hT hlr hlower hupper
    hTcont.continuousAt hw

end PDE.OrderInterval
