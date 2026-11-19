/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.OriginQuotient
public import PDE.Analysis.Calculus.Parity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Compactly supported functions with endpoint corners

A bounded, compactly supported measurable function on the line that vanishes and
is differentiable at the origin has its quotient by the coordinate in every `Lᵖ`;
its product with the coordinate lies in every `Lᵖ` as well. A function that is `C²`
on `(-L, L)` and zero outside has an almost everywhere differentiable derivative:
the endpoints `±L` may be corners. These are the integrability facts behind the
singular Hilbert cancellation.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

namespace PDE.Analysis.Calculus

/-- A bounded compact measurable function, differentiable and zero at the
origin, has its coordinate quotient in every Lᵖ space. -/
theorem memLp_div_id_of_bounded_compactSupport
    {η : ℝ → ℝ} {M d : ℝ} (hc : HasCompactSupport η) (hm : Measurable η)
    (hb : ∀ x, ‖η x‖ ≤ M) (hd : HasDerivAt η d 0) (hzero : η 0 = 0)
    (p : ℝ≥0∞) : MemLp (fun x ↦ η x / x) p volume := by
  have hlim : Tendsto (fun x ↦ η x / x) (𝓝[≠] 0) (𝓝 d) := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using hd.tendsto_slope_zero
  have he := hlim.norm.eventually (gt_mem_nhds (lt_add_one ‖d‖))
  obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  have hM : 0 ≤ M := (norm_nonneg (η 0)).trans (hb 0)
  have hs : HasCompactSupport (fun x ↦ η x / x) := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using hc.mul_right (f' := fun x ↦ x⁻¹)
  apply hs.memLp_of_bound (hm.div measurable_id).aestronglyMeasurable
    (max (‖d‖ + 1) (M / δ))
  filter_upwards with x
  by_cases hx0 : x = 0
  · simp only [hx0, div_zero, norm_zero]
    exact (by positivity : (0 : ℝ) ≤ ‖d‖ + 1).trans (le_max_left _ _)
  by_cases hx : |x| < δ
  · exact (hlocal ⟨by simpa using hx, hx0⟩).le.trans (le_max_left _ _)
  · rw [norm_div, Real.norm_eq_abs x]
    exact (div_le_div₀ hM (hb x) hδ (not_lt.mp hx)).trans (le_max_right _ _)

/-- Compact support controls multiplication by the coordinate. -/
theorem memLp_id_mul_of_bounded_compactSupport
    {η : ℝ → ℝ} {M : ℝ} (hc : HasCompactSupport η) (hm : Measurable η)
    (hb : ∀ x, ‖η x‖ ≤ M) (p : ℝ≥0∞) :
    MemLp (fun x ↦ x * η x) p volume := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn (f := fun x : ℝ ↦ x)
    continuousOn_id
  have hs : HasCompactSupport (fun x ↦ x * η x) := hc.mul_left
  apply hs.memLp_of_bound (measurable_id.mul hm).aestronglyMeasurable (max 0 R * M)
  filter_upwards with x
  by_cases hx : x ∈ tsupport η
  · rw [norm_mul]
    exact mul_le_mul ((hR x hx).trans (le_max_right _ _)) (hb x)
      (norm_nonneg _) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero]
    exact mul_nonneg (le_max_left _ _) ((norm_nonneg (η 0)).trans (hb 0))

/-- A function zero on a right half-line has zero totalized derivative there,
even when the endpoint is a corner. -/
theorem deriv_eq_zero_of_zero_on_Ici {q : ℝ → ℝ} {L x : ℝ}
    (hs : ∀ y, L ≤ y → q y = 0) (hx : L ≤ x) : deriv q x = 0 := by
  by_cases hd : DifferentiableAt ℝ q x
  · have hz : HasDerivWithinAt q 0 (Ici x) x :=
      (hasDerivWithinAt_const x (Ici x) (0 : ℝ)).congr
        (fun y hy ↦ hs y (hx.trans hy)) (hs x hx)
    exact (uniqueDiffWithinAt_Ici x).eq_deriv _ hd.hasDerivAt.hasDerivWithinAt hz
  · exact deriv_zero_of_not_differentiableAt hd

/-- Interior C² regularity and exterior zero values permit only two exceptional
points for differentiability of the classical derivative. -/
theorem ae_differentiableAt_deriv_of_contDiffOn_support
    {q : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hq : ContDiffOn ℝ 2 q (Ioo (-L) L))
    (hs : ∀ x, L ≤ |x| → q x = 0) :
    ∀ᵐ x, DifferentiableAt ℝ (deriv q) x := by
  have hn (a : ℝ) : ∀ᵐ x ∂volume, x ≠ a :=
    compl_mem_ae_iff.mpr (measure_singleton a)
  filter_upwards [hn (-L), hn L] with x hleft hright
  by_cases hx : x ∈ Ioo (-L) L
  · exact ((hq.contDiffAt (isOpen_Ioo.mem_nhds hx)).derivWithin
      (m := 1) (by norm_num)).differentiableAt one_ne_zero
  · have hout : L < |x| := by
      rcases le_total 0 x with hp | hn
      · rw [abs_of_nonneg hp]
        have : ¬x < L := fun h ↦ hx ⟨by linarith, h⟩
        exact lt_of_le_of_ne (not_lt.mp this) hright.symm
      · rw [abs_of_nonpos hn]
        have : ¬-L < x := fun h ↦ hx ⟨h, by linarith⟩
        have := lt_of_le_of_ne (not_lt.mp this) hleft
        linarith
    have heq : q =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [continuous_abs.continuousAt.eventually (lt_mem_nhds hout)] with y hy
      exact hs y hy.le
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
      (heq.deriv.trans (Eventually.of_forall fun y ↦ deriv_const y (0 : ℝ)))

end PDE.Analysis.Calculus
