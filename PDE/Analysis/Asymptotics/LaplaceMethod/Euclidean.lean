/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Hessian.Gaussian
public import PDE.Analysis.Calculus.Hessian.QuadraticMinimum

/-!
# Laplace asymptotics in Euclidean space

At a unique interior minimum on a compact set, local C² regularity and positivity
of the Hessian determine the leading Gaussian constant. Compactness and
strict minimality supply the lower bound needed for dominated convergence.
The amplitude need only be continuous and may take values in a real Banach space.

The main limit is stated first with spatial scale `ε`, then with large parameter
`t = ε⁻²` and the usual exponential normalization. A compactly supported amplitude
also gives a whole-space integral.

Evans, §4.5.2, proves Laplace's method in one dimension as the ratio limit (24), for a
continuous phase of at least quadratic growth with a unique minimum; the Gaussian constant
cancels there and no Hessian appears. Here the limit is absolute and in any dimension, and
`tendsto_laplace_integral_compact` identifies the constant `(2π)^(n/2) / √(det D²φ(x₀))`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.2, the lemma (Asymptotics), (24), and its proof,
  p. 217. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Asymptotics

open Filter MeasureTheory Set Metric
open scoped Topology

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The leading Laplace limit at a unique nondegenerate interior minimum of a compact set.
The phase is only required to be C² near the minimum and continuous on the integration set.
The amplitude may take values in any real Banach space, including complex Banach spaces
by restriction of scalars. -/
theorem tendsto_laplace_integral_compact
    {K : Set (ℝ^n)} {x₀ : ℝ^n}
    (hK : IsCompact K) (hx : x₀ ∈ interior K)
    {φ : ℝ^n → ℝ} (hφ : ContinuousOn φ K)
    (hregular : ContDiffAt ℝ 2 φ x₀)
    (hstrict : ∀ y ∈ K, y ≠ x₀ → φ x₀ < φ y)
    (hH : ∀ v : ℝ^n, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ φ) x₀ v v)
    {a : ℝ^n → E} (ha : ContinuousOn a K) :
    Tendsto (fun ε : ℝ ↦ (ε ^ n)⁻¹ •
      ∫ y in K, Real.exp (-(φ y - φ x₀) / ε ^ 2) • a y)
      (𝓝[>] 0)
      (𝓝 (((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt (hessianMatrix φ x₀).det) • a x₀)) := by
  have hxK : x₀ ∈ K := interior_subset hx
  have hxnhds : K ∈ 𝓝 x₀ := mem_interior_iff_mem_nhds.mp hx
  have hminimum : IsMinOn φ K x₀ := fun y hy ↦
    (eq_or_ne y x₀).elim (fun h ↦ h ▸ le_rfl) fun h ↦ (hstrict y hy h).le
  have hstationary := (hminimum.isLocalMin hxnhds).fderiv_eq_zero
  obtain ⟨c, hc, hlower⟩ :=
    exists_quadratic_lower_bound_on_compact hK hx hφ hregular hstrict hH
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn ha
  let shift (ε : ℝ) (z : ℝ^n) := x₀ + ε • z
  let integrand (ε : ℝ) (y : ℝ^n) := Real.exp (-(φ y - φ x₀) / ε ^ 2) • a y
  let F (ε : ℝ) := (shift ε ⁻¹' K).indicator (integrand ε ∘ shift ε)
  have hshift (ε : ℝ) : Continuous (shift ε) := by fun_prop
  have hmeas (ε : ℝ) : AEStronglyMeasurable (F ε) := by
    have hs : MeasurableSet (shift ε ⁻¹' K) := hK.measurableSet.preimage (hshift ε).measurable
    have hi : ContinuousOn (integrand ε) K :=
      (((hφ.sub continuousOn_const).neg.div_const (ε ^ 2)).rexp).smul ha
    exact (aestronglyMeasurable_indicator_iff hs).mpr
      ((hi.comp (hshift ε).continuousOn fun _ h ↦ h).aestronglyMeasurable hs)
  have hbound (ε : ℝ) (hε : 0 < ε) (z : ℝ^n) : ‖F ε z‖ ≤ Real.exp (-c * ‖z‖ ^ 2) * M := by
    by_cases hz : shift ε z ∈ K
    · have hscale : c * ‖z‖ ^ 2 ≤ (φ (shift ε z) - φ x₀) / ε ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        refine le_of_eq_of_le ?_ (hlower _ hz)
        simp only [shift, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
        ring
      simp only [F, indicator_of_mem (show z ∈ shift ε ⁻¹' K from hz), Function.comp_apply,
        integrand, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      · simpa only [neg_div, neg_mul] using neg_le_neg hscale
      · exact hM _ hz
    · simp only [F, indicator_of_notMem (show z ∉ shift ε ⁻¹' K from hz), norm_zero]
      exact mul_nonneg (Real.exp_pos _).le ((norm_nonneg (a x₀)).trans (hM x₀ hxK))
  have hmajorant : Integrable fun z : ℝ^n ↦ Real.exp (-c * ‖z‖ ^ 2) * M :=
    (Integrable.of_integral_ne_zero <| by
      rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hc]; positivity).mul_const M
  have hlimit (z : ℝ^n) : Tendsto (fun ε : ℝ ↦ F ε z) (𝓝[>] 0)
      (𝓝 (Real.exp (-fderiv ℝ (fderiv ℝ φ) x₀ z z / 2) • a x₀)) := by
    have hs : Tendsto (fun ε : ℝ ↦ shift ε z) (𝓝[>] 0) (𝓝 x₀) := by
      simpa only [shift, zero_smul, add_zero] using tendsto_const_nhds.add
        ((show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).smul_const z)
    have hp := Real.continuous_exp.continuousAt.tendsto.comp
      (PDE.Analysis.tendsto_rescaled_stationary_phase hregular hstationary z).neg
    have hfull := hp.smul ((ha.continuousAt hxnhds).tendsto.comp hs)
    simp only [neg_div] at hfull ⊢
    refine hfull.congr' ?_
    filter_upwards [hs.eventually hxnhds] with ε hε
    simp only [F, integrand, Function.comp_apply,
      indicator_of_mem (show z ∈ shift ε ⁻¹' K from hε), shift, neg_div]
  have hi := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ)) _
    (.of_forall hmeas)
    (eventually_mem_nhdsWithin.mono fun ε hε ↦ ae_of_all _ (hbound ε hε)) hmajorant
    (ae_of_all _ hlimit)
  rw [integral_smul_const, integral_actual_hessian_gaussian hregular hH] at hi
  refine hi.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp_rw [F, indicator_comp_right]
  change (∫ z, (fun y ↦ K.indicator (integrand ε) (x₀ + y)) (ε • z)) = _
  simpa only [integral_add_left_eq_self, integral_indicator hK.measurableSet,
    finrank_euclideanSpace_fin, integrand] using Measure.integral_comp_smul_of_nonneg volume
      (fun y : ℝ^n ↦ K.indicator (integrand ε) (x₀ + y)) ε (hR := hε.le)

/-- The compact Laplace asymptotic in the large parameter `t = ε⁻²`. -/
theorem tendsto_laplace_integral_compact_atTop
    {K : Set (ℝ^n)} {x₀ : ℝ^n}
    (hK : IsCompact K) (hx : x₀ ∈ interior K)
    {φ : ℝ^n → ℝ} (hφ : ContinuousOn φ K)
    (hregular : ContDiffAt ℝ 2 φ x₀)
    (hstrict : ∀ y ∈ K, y ≠ x₀ → φ x₀ < φ y)
    (hH : ∀ v : ℝ^n, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ φ) x₀ v v)
    {a : ℝ^n → E} (ha : ContinuousOn a K) :
    Tendsto (fun t : ℝ ↦ t ^ ((n : ℝ) / 2) •
      ∫ y in K, Real.exp (-t * (φ y - φ x₀)) • a y)
      atTop
      (𝓝 (((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt (hessianMatrix φ x₀).det) • a x₀)) := by
  have hscale : Tendsto (fun t : ℝ ↦ (Real.sqrt t)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop,
      (eventually_gt_atTop 0).mono fun t ht ↦ inv_pos.mpr (Real.sqrt_pos.mpr ht)⟩
  refine ((tendsto_laplace_integral_compact hK hx hφ hregular hstrict hH ha).comp hscale).congr'
    ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hcoeff : (((Real.sqrt t)⁻¹) ^ n)⁻¹ = t ^ ((n : ℝ) / 2) := by
    rw [inv_pow, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    ring_nf
  have hphase (y : ℝ^n) : -(φ y - φ x₀) / ((Real.sqrt t)⁻¹) ^ 2 = -t * (φ y - φ x₀) := by
    rw [inv_pow, Real.sq_sqrt ht.le, div_inv_eq_mul]
    ring
  simp only [Function.comp_apply, hcoeff, hphase]

/-- The usual exponential normalization retains the value of the phase at its minimum. -/
theorem tendsto_normalized_laplace_integral_compact
    {K : Set (ℝ^n)} {x₀ : ℝ^n}
    (hK : IsCompact K) (hx : x₀ ∈ interior K)
    {φ : ℝ^n → ℝ} (hφ : ContinuousOn φ K)
    (hregular : ContDiffAt ℝ 2 φ x₀)
    (hstrict : ∀ y ∈ K, y ≠ x₀ → φ x₀ < φ y)
    (hH : ∀ v : ℝ^n, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ φ) x₀ v v)
    {a : ℝ^n → E} (ha : ContinuousOn a K) :
    Tendsto (fun t : ℝ ↦ (t ^ ((n : ℝ) / 2) * Real.exp (t * φ x₀)) •
      ∫ y in K, Real.exp (-t * φ y) • a y)
      atTop
      (𝓝 (((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt (hessianMatrix φ x₀).det) • a x₀)) := by
  refine (tendsto_laplace_integral_compact_atTop hK hx hφ hregular hstrict hH ha).congr'
    (.of_forall fun t ↦ ?_)
  have hphase (y : ℝ^n) :
      Real.exp (-t * (φ y - φ x₀)) = Real.exp (t * φ x₀) * Real.exp (-t * φ y) := by
    rw [← Real.exp_add]; ring_nf
  simp only [hphase, mul_smul, integral_smul]

/-- A compact amplitude localizes the whole-space Laplace integral.
Stationarity is explicit because a minimum on a thin support need not be an ambient minimum. -/
theorem tendsto_normalized_laplace_integral_of_hasCompactSupport
    {x₀ : ℝ^n} {φ : ℝ^n → ℝ}
    (hregular : ContDiffAt ℝ 2 φ x₀) (hstationary : fderiv ℝ φ x₀ = 0)
    (hH : ∀ v : ℝ^n, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ φ) x₀ v v)
    {a : ℝ^n → E} (ha : Continuous a)
    (hcompact : HasCompactSupport a) (hφ : ContinuousOn φ (tsupport a))
    (hstrict : ∀ y ∈ tsupport a, y ≠ x₀ → φ x₀ < φ y) :
    Tendsto (fun t : ℝ ↦ (t ^ ((n : ℝ) / 2) * Real.exp (t * φ x₀)) •
      ∫ y, Real.exp (-t * φ y) • a y)
      atTop
      (𝓝 (((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt (hessianMatrix φ x₀).det) • a x₀)) := by
  obtain ⟨c, hc, r, hr, hlocal⟩ := exists_local_quadratic_lower_bound hregular hstationary hH
  obtain ⟨s, hs, hreg⟩ := Metric.eventually_nhds_iff.mp (hregular.eventually (by simp))
  let radius := min r s / 2
  have hmin : 0 < min r s := lt_min hr hs
  have hradr : radius < r := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hrads : radius < s := (half_lt_self hmin).trans_le (min_le_right _ _)
  let K := tsupport a ∪ closedBall x₀ radius
  have hxK : x₀ ∈ interior K := mem_interior_iff_mem_nhds.mpr <|
    mem_of_superset (ball_mem_nhds x₀ (half_pos hmin)) fun y hy ↦
      Or.inr (ball_subset_closedBall hy)
  have hφK : ContinuousOn φ K := hφ.union_of_isClosed
    (fun y hy ↦ (hreg ((mem_closedBall.mp hy).trans_lt hrads)).continuousAt.continuousWithinAt)
    (isClosed_tsupport a) isClosed_closedBall
  have hstrictK : ∀ y ∈ K, y ≠ x₀ → φ x₀ < φ y := by
    rintro y (hy | hy) hne
    · exact hstrict y hy hne
    · have hlower := hlocal (y - x₀) (by
        simpa only [dist_eq_norm] using (mem_closedBall.mp hy).trans_lt hradr)
      rw [add_sub_cancel] at hlower
      exact sub_pos.mp ((mul_pos hc (pow_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) 2)).trans_le
        hlower)
  refine (tendsto_normalized_laplace_integral_compact (hcompact.union (isCompact_closedBall x₀
    radius)) hxK hφK hregular hstrictK hH ha.continuousOn).congr' (.of_forall fun t ↦ ?_)
  dsimp only
  congr 1
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy (Or.inl h), smul_zero]

end PDE.Analysis.Asymptotics
