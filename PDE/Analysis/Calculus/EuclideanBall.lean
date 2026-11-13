/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import CAS.ExactTactic

/-!
# Differential calculus on Euclidean balls

The divergence theorem (Gauss's formula) holds on a Euclidean ball
`B(c, r) ⊆ ℝ^n` for globally `C¹` vector fields `F = (F_1, …, F_n)`:

`∫_{B(c, r)} div F dx = ∫_{∂B(c, r)} F · ν dσ`,

where `ν(x) = (x - c) / ‖x - c‖` is the outward unit normal and the surface
integral is `sphereIntegral` from `PDE.Analysis.Integration.EuclideanBall`.
We also prove that the radial derivative of a ball integral is the sphere
integral, the one-dimensional shell of the polar coarea formula.

Evans states the divergence theorem for a bounded open set with `C¹` boundary (App. C.2,
Theorem 1(ii)) and the radial derivative of ball integrals for continuous summable functions
(App. C.3, Theorem 4(ii)). We prove the first on balls, for fields that are `C¹` on all of
`ℝ^n`, and the second for continuous functions.

## Main results

* `hasDerivAt_ballIntegral_radius`: for continuous `G` and `r > 0`,
  `d/dr ∫_{B(c, r)} G = ∫_{∂B(c, r)} G dσ`.
* `ballIntegral_divergence_eq_sphereIntegral_normal_flux`: Gauss's formula
  on `B(c, r)` for `C¹` fields.

## Implementation notes

No boundary trace theory is used.  The proof works with the compactly
supported `C¹` weight `x ↦ ((a - ‖x - c‖²)⁺)²`, for which integration by
parts against `∂_i F_i` on all of `ℝ^n` is Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.  The
resulting identity holds for every `a`; differentiating it in `a` (a dominated
differentiation of a parametric integral, valid because the level set
`‖x - c‖² = a` is null) produces the weight `(a - ‖x - c‖²)⁺`, and a second
differentiation at `a = r²`, combined with the polar coarea formula, isolates
the flux through the sphere of radius `r`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 1(ii) (the divergence theorem),
  pp. 711-712, and App. C.3, Theorem 4(ii), p. 712. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped BigOperators RealInnerProductSpace Topology

variable {n : ℕ}

private noncomputable def sqPosPart (s : ℝ) : ℝ :=
  if 0 < s then s ^ 2 else 0

private theorem sqPosPart_eq (s : ℝ) :
    sqPosPart s = (max s 0) ^ 2 := by
  by_cases hs : 0 < s
  · simp [sqPosPart, hs, max_eq_left hs.le]
  · have hs' : s ≤ 0 := le_of_not_gt hs
    simp [sqPosPart, hs, max_eq_right hs']

private theorem hasDerivAt_sqPosPart (s : ℝ) :
    HasDerivAt sqPosPart (2 * max s 0) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hevent : sqPosPart =ᶠ[𝓝 s] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hs] with z hz
      have hzlt : z < 0 := Set.mem_Iio.mp hz
      simp [sqPosPart, not_lt.mpr hzlt.le]
    have h := (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hevent
    simpa [max_eq_right hs.le] using h
  · rw [show 2 * max (0 : ℝ) 0 = 0 by simp,
      hasDerivAt_iff_tendsto_slope_left_right]
    constructor
    · refine Filter.tendsto_congr' ?_ |>.mpr tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzlt : z < 0 := Set.mem_Iio.mp hz
      simp [slope, sqPosPart, not_lt.mpr hzlt.le]
    · refine Filter.tendsto_congr' ?_ |>.mpr
        (tendsto_id.mono_left nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzgt : 0 < z := Set.mem_Ioi.mp hz
      simp [slope, sqPosPart, hzgt, hzgt.ne', pow_two]
  · have hevent : sqPosPart =ᶠ[𝓝 s] fun z ↦ z ^ 2 := by
      filter_upwards [Ioi_mem_nhds hs] with z hz
      have hzgt : 0 < z := Set.mem_Ioi.mp hz
      simp [sqPosPart, hzgt]
    have h := (hasDerivAt_pow 2 s).congr_of_eventuallyEq hevent
    simpa [max_eq_left hs.le, pow_one, mul_comm] using h

private theorem contDiff_sqPosPart :
    ContDiff ℝ 1 sqPosPart := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s ↦ (hasDerivAt_sqPosPart s).differentiableAt, ?_⟩
  have hderiv : deriv sqPosPart = fun s ↦ 2 * max s 0 := by
    funext s
    exact (hasDerivAt_sqPosPart s).deriv
  rw [hderiv]
  fun_prop

/-- The compactly supported `C¹` weight used to prove the ball divergence
theorem without assuming a boundary formula. -/
private noncomputable def quadraticBallCutoff
    (c : ℝ^n) (a : ℝ)
    (x : ℝ^n) : ℝ :=
  sqPosPart (a - ‖x - c‖ ^ 2)

private theorem contDiff_quadraticBallCutoff
    (c : ℝ^n) (a : ℝ) :
    ContDiff ℝ 1 (quadraticBallCutoff c a) := by
  apply contDiff_sqPosPart.comp
  exact contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)

private theorem quadraticBallCutoff_eq_zero_of_le
    {c x : ℝ^n} {a : ℝ}
    (h : a ≤ ‖x - c‖ ^ 2) :
    quadraticBallCutoff c a x = 0 := by
  simp [quadraticBallCutoff, sqPosPart, not_lt.mpr (sub_nonpos.mpr h)]

/-- Outside `B̄(c, a + 1)` the squared distance to `c` is at least `a ≥ 0`. -/
private theorem le_norm_sub_sq_of_notMem_closedBall {c x : ℝ^n} {a : ℝ} (ha : 0 ≤ a)
    (hx : x ∉ Metric.closedBall c (a + 1)) : a ≤ ‖x - c‖ ^ 2 := by
  rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hx
  nlinarith

private theorem hasCompactSupport_quadraticBallCutoff
    (c : ℝ^n) {a : ℝ} (ha : 0 ≤ a) :
    HasCompactSupport (quadraticBallCutoff c a) :=
  .intro (isCompact_closedBall c (a + 1)) fun _ hx ↦
    quadraticBallCutoff_eq_zero_of_le (le_norm_sub_sq_of_notMem_closedBall ha hx)

private theorem fderiv_quadraticBallCutoff_apply
    (c : ℝ^n) (a : ℝ)
    (x v : ℝ^n) :
    fderiv ℝ (quadraticBallCutoff c a) x v =
      -4 * max (a - ‖x - c‖ ^ 2) 0 * inner ℝ (x - c) v := by
  let q : ℝ^n → ℝ :=
    fun y ↦ a - ‖y - c‖ ^ 2
  have hq :=
    (hasFDerivAt_const (x := x) a).sub
      (((hasFDerivAt_id x).sub_const c).norm_sq)
  have hs :
      HasDerivAt sqPosPart (2 * max (q x) 0) (q x) :=
    hasDerivAt_sqPosPart (q x)
  have hcomp := hs.hasFDerivAt.comp x hq
  have hfd := hcomp.fderiv
  rw [show quadraticBallCutoff c a = sqPosPart ∘ q by rfl, hfd]
  simp [ContinuousLinearMap.comp_apply, q, inner_sub_left]
  ring

private theorem quadraticBallCutoff_integral_partial
    (F : ℝ^n → ℝ) (hF : ContDiff ℝ 1 F)
    (c : ℝ^n) {a : ℝ} (ha : 0 ≤ a)
    (i : Fin n) :
    (∫ x, quadraticBallCutoff c a x *
        (∂[i] F) x) =
      4 * ∫ x, max (a - ‖x - c‖ ^ 2) 0 * (F x * (x - c) i) := by
  let w := quadraticBallCutoff c a
  let e := EuclideanSpace.single i (1 : ℝ)
  have hw : ContDiff ℝ 1 w := contDiff_quadraticBallCutoff c a
  have hwSupp : HasCompactSupport w := hasCompactSupport_quadraticBallCutoff c ha
  have hDF : Continuous (fun x ↦ fderiv ℝ F x e) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDw : Continuous (fun x ↦ fderiv ℝ w x e) :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hibp : (∫ x, quadraticBallCutoff c a x * (∂[i] F) x) = -∫ x, fderiv ℝ w x e * F x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (ℝ^n)))
      (f := w) (g := F) (v := e)
      ((hDw.mul hF.continuous).integrable_of_hasCompactSupport (hwSupp.fderiv_apply ℝ e).mul_right)
      ((hw.continuous.mul hDF).integrable_of_hasCompactSupport hwSupp.mul_right)
      ((hw.continuous.mul hF.continuous).integrable_of_hasCompactSupport hwSupp.mul_right)
      (fun _ _ ↦ hw.differentiable (by norm_num) |>.differentiableAt)
      (fun _ _ ↦ hF.differentiable (by norm_num) |>.differentiableAt)
  rw [hibp, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [fderiv_quadraticBallCutoff_apply c a x e]
  simp [e, EuclideanSpace.inner_single_right]
  ring

private theorem hasCompactSupport_ballPosPart
    (c : ℝ^n) {a : ℝ} (ha : 0 ≤ a) :
    HasCompactSupport
      (fun x : ℝ^n ↦
        max (a - ‖x - c‖ ^ 2) 0) :=
  .intro (isCompact_closedBall c (a + 1)) fun _ hx ↦
    max_eq_right (sub_nonpos.mpr (le_norm_sub_sq_of_notMem_closedBall ha hx))

private theorem hasDerivAt_max_sub_zero_of_ne
    {a q : ℝ} (h : a ≠ q) :
    HasDerivAt (fun b : ℝ ↦ max (b - q) 0)
      (if q < a then 1 else 0) a := by
  rcases h.lt_or_gt with hlt | hgt
  · have heq : (fun b : ℝ ↦ max (b - q) 0) =ᶠ[𝓝 a] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hlt] with b hb
      exact max_eq_right (sub_nonpos.mpr hb.le)
    simpa [not_lt.mpr hlt.le] using (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq heq
  · have heq : (fun b : ℝ ↦ max (b - q) 0) =ᶠ[𝓝 a] fun b ↦ b - q := by
      filter_upwards [Ioi_mem_nhds hgt] with b hb
      exact max_eq_left (sub_nonneg.mpr hb.le)
    simpa [hgt] using ((hasDerivAt_id a).sub_const q).congr_of_eventuallyEq heq

private theorem hasDerivAt_integral_posPart_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q G : α → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hG : Integrable G μ) {a : ℝ}
    (hlevel : μ {x | q x = a} = 0) :
    HasDerivAt
      (fun b ↦ ∫ x, max (b - q x) 0 * G x ∂μ)
      (∫ x in {x | q x < a}, G x ∂μ) a := by
  let F : ℝ → α → ℝ := fun b x ↦ max (b - q x) 0 * G x
  have hsublevel : MeasurableSet {x | q x < a} := measurableSet_lt hq measurable_const
  have hFmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (F b) μ := .of_forall fun b ↦
    ((measurable_const.sub hq).max measurable_const).aestronglyMeasurable.mul
      hG.aestronglyMeasurable
  -- `b ↦ (b - q)⁺ G` is `|G|`-Lipschitz, and differentiable off the null level set `q = a`
  have hlip : ∀ᵐ x ∂μ, LipschitzOnWith (Real.nnabs ‖G x‖) (F · x) Set.univ :=
    .of_forall fun x ↦ LipschitzOnWith.of_dist_le_mul fun b _ d _ ↦ by
      have h := abs_max_sub_max_le_abs (b - q x) (d - q x) 0
      rw [sub_sub_sub_cancel_right] at h
      simp only [F, Real.dist_eq, Real.coe_nnabs, abs_norm]
      rw [← sub_mul, abs_mul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right h (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hdiff : ∀ᵐ x ∂μ, HasDerivAt (F · x) (Set.indicator {x | q x < a} G x) a := by
    filter_upwards [compl_mem_ae_iff.mpr hlevel] with x hx
    have hne : q x ≠ a := by simpa using hx
    change HasDerivAt (fun b ↦ max (b - q x) 0 * G x) (if q x < a then G x else 0) a
    simpa only [ite_mul, one_mul, zero_mul] using
      (hasDerivAt_max_sub_zero_of_ne hne.symm).mul_const (G x)
  have hFa : Integrable (F a) μ := (hG.norm.const_mul (max a 0)).mono' hFmeas.self_of_nhds
    (.of_forall fun x ↦ by
      simpa only [F, norm_mul, Real.norm_eq_abs, abs_of_nonneg (le_max_right (a - q x) 0)] using
        mul_le_mul_of_nonneg_right (max_le_max (sub_le_self a (hq0 x)) le_rfl) (norm_nonneg (G x)))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (bound := fun x ↦ ‖G x‖)
    (F := F) (s := Set.univ) univ_mem hFmeas hFa
    (hG.aestronglyMeasurable.indicator hsublevel) hlip hG.norm hdiff
  simpa [F, MeasureTheory.integral_indicator, hsublevel] using hderiv.2

private theorem hasDerivAt_integral_sqPosPart_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (q G : α → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (hG : Integrable G μ) {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt
      (fun b ↦ ∫ x, sqPosPart (b - q x) * G x ∂μ)
      (∫ x, 2 * max (a - q x) 0 * G x ∂μ) a := by
  let F : ℝ → α → ℝ := fun b x ↦ sqPosPart (b - q x) * G x
  let F' : ℝ → α → ℝ := fun b x ↦ 2 * max (b - q x) 0 * G x
  have hFmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (F b) μ := .of_forall fun b ↦
    (contDiff_sqPosPart.continuous.measurable.comp
      (measurable_const.sub hq)).aestronglyMeasurable.mul hG.aestronglyMeasurable
  have hFa : Integrable (F a) μ := (hG.norm.const_mul (a ^ 2)).mono' hFmeas.self_of_nhds
    (.of_forall fun x ↦ by
      have hsq : max (a - q x) 0 ^ 2 ≤ a ^ 2 :=
        (sq_le_sq₀ (le_max_right _ _) ha).mpr (max_le (sub_le_self a (hq0 x)) ha)
      simpa only [F, sqPosPart_eq, norm_mul, Real.norm_eq_abs, abs_pow,
        abs_of_nonneg (le_max_right (a - q x) 0)] using
        mul_le_mul_of_nonneg_right hsq (norm_nonneg (G x)))
  -- on `b ∈ (a - 1, a + 1)` the derivative is dominated by `2 (a + 1) |G|`
  have hnorm : ∀ᵐ x ∂μ, ∀ b ∈ Set.Ioo (a - 1) (a + 1), ‖F' b x‖ ≤ 2 * (a + 1) * ‖G x‖ :=
    .of_forall fun x b hb ↦ by
      have hmax : max (b - q x) 0 ≤ a + 1 :=
        max_le ((sub_le_self b (hq0 x)).trans hb.2.le) (by linarith)
      rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * max (b - q x) 0)]
      gcongr
  have hdiff : ∀ᵐ x ∂μ, ∀ b ∈ Set.Ioo (a - 1) (a + 1), HasDerivAt (F · x) (F' b x) b :=
    .of_forall fun x b _ ↦ by
      have hinner : HasDerivAt (fun z : ℝ ↦ z - q x) 1 b := by
        cas
      simpa [F, F', mul_assoc] using
        ((hasDerivAt_sqPosPart (b - q x)).comp b hinner).mul_const (G x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (Ioo_mem_nhds (by linarith : a - 1 < a) (by linarith : a < a + 1)) hFmeas hFa
    ((((measurable_const.sub hq).max measurable_const).const_mul 2).aestronglyMeasurable.mul
      hG.aestronglyMeasurable) hnorm (hG.norm.const_mul _) hdiff).2

/-- The divergence `∑ᵢ ∂ᵢ Fᵢ` of a `C¹` field is continuous. -/
private theorem continuous_divergence {F : Fin n → ℝ^n → ℝ} (hF : ∀ i, ContDiff ℝ 1 (F i)) :
    Continuous fun x ↦ ∑ i : Fin n, (∂[i] (F i)) x :=
  continuous_finsetSum _ fun i _ ↦
    ((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem quadraticBallCutoff_integral_divergence
    (F : Fin n → ℝ^n → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i))
    (c : ℝ^n) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x, quadraticBallCutoff c a x *
        ∑ i : Fin n, (∂[i] (F i)) x) =
      4 * ∫ x, max (a - ‖x - c‖ ^ 2) 0 *
        ∑ i : Fin n, F i x * (x - c) i := by
  have hterm (i : Fin n) : Integrable (fun x ↦ quadraticBallCutoff c a x * (∂[i] (F i)) x) :=
    ((contDiff_quadraticBallCutoff c a).continuous.mul
      (((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport (hasCompactSupport_quadraticBallCutoff c ha).mul_right
  have hradialTerm (i : Fin n) :
      Integrable (fun x ↦ max (a - ‖x - c‖ ^ 2) 0 * (F i x * (x - c) i)) :=
    (by fun_prop : Continuous fun x ↦ max (a - ‖x - c‖ ^ 2) 0 * (F i x * (x - c) i)
      ).integrable_of_hasCompactSupport (hasCompactSupport_ballPosPart c ha).mul_right
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ hterm i, integral_finsetSum _ fun i _ ↦ hradialTerm i,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ quadraticBallCutoff_integral_partial (F i) (hF i) c ha i

/-- A quadratic ball cutoff vanishes beyond any larger closed ball. -/
private theorem sq_radius_le_norm_sq_of_not_mem_closedBall
    (c : ℝ^n) {r b : ℝ} (hr : 0 < r) (hb : b < (r + 1) ^ 2)
    {x : ℝ^n} (hx : x ∉ Metric.closedBall c (r + 1)) :
    b ≤ ‖x - c‖ ^ 2 := by
  rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hx
  nlinarith

/-- An integrand `g(b - ‖x - c‖²) H(x)` with `g = 0` on `(-∞, 0]` and `b < (r + 1)²` has the same
integral over `B̄(c, r + 1)` as over `ℝ^n`. -/
private theorem setIntegral_closedBall_eq_integral (c : ℝ^n) {r b : ℝ} (hr : 0 < r)
    (hb : b < (r + 1) ^ 2) {g : ℝ → ℝ} (hg : ∀ t ≤ 0, g t = 0) (H : ℝ^n → ℝ) :
    ∫ x in Metric.closedBall c (r + 1), g (b - ‖x - c‖ ^ 2) * H x =
      ∫ x, g (b - ‖x - c‖ ^ 2) * H x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [hg _ (sub_nonpos.mpr (sq_radius_le_norm_sq_of_not_mem_closedBall c hr hb hx)), zero_mul]

/-- On `B̄(c, r + 1)`, the sphere `‖x - c‖ = r` is null. -/
private theorem restrict_closedBall_sphere_null [Fact (0 < n)] (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (ℝ^n)).restrict (Metric.closedBall c (r + 1))
      {x : ℝ^n | ‖x - c‖ ^ 2 = r ^ 2} = 0 := by
  have : Nontrivial (ℝ^n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using (Fact.out : 0 < n))
  have hset : {x : ℝ^n | ‖x - c‖ ^ 2 = r ^ 2} = Metric.sphere c r := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_sphere]
    rw [dist_eq_norm]
    exact sq_eq_sq₀ (norm_nonneg (x - c)) hr.le
  rw [hset]
  exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans
    (Measure.addHaar_sphere (μ := (volume : Measure (ℝ^n))) c r).le)

/-- On `B̄(c, r + 1)`, the integral over `‖x - c‖² < r²` is the integral over `B(c, r)`. -/
private theorem setIntegral_sublevel_eq_ballIntegral (G : ℝ^n → ℝ) (c : ℝ^n) {r : ℝ}
    (hr : 0 < r) :
    (∫ x in {x : ℝ^n | ‖x - c‖ ^ 2 < r ^ 2}, G x
      ∂(volume : Measure (ℝ^n)).restrict (Metric.closedBall c (r + 1))) =
        ballIntegral n G c r := by
  have hset : {x : ℝ^n | ‖x - c‖ ^ 2 < r ^ 2} = Metric.ball c r := by
    ext x
    simp only [Set.mem_ofPred_eq, Metric.mem_ball]
    rw [dist_eq_norm]
    exact sq_lt_sq₀ (norm_nonneg (x - c)) hr.le
  rw [hset, Measure.restrict_restrict_of_subset
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)))]
  rfl

/-- Near a positive radius, the quadratic cutoff identity can be restricted
uniformly to a larger compact ball. -/
private theorem quadraticBallCutoff_integral_divergence_restrict_eventually
    (F : Fin n → ℝ^n → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (fun b ↦ ∫ x in Metric.closedBall c (r + 1),
      sqPosPart (b - ‖x - c‖ ^ 2) * ∑ i : Fin n, (∂[i] (F i)) x) =ᶠ[𝓝 (r ^ 2)]
    fun b ↦ 4 * ∫ x in Metric.closedBall c (r + 1),
      max (b - ‖x - c‖ ^ 2) 0 * ∑ i : Fin n, F i x * (x - c) i := by
  filter_upwards [Ioo_mem_nhds (by positivity : (0 : ℝ) < r ^ 2)
    (by nlinarith : r ^ 2 < (r + 1) ^ 2)] with b hb
  rw [setIntegral_closedBall_eq_integral c hr hb.2 (g := sqPosPart)
      (fun t ht ↦ by simp [sqPosPart, not_lt.mpr ht]),
    setIntegral_closedBall_eq_integral c hr hb.2 (g := (max · 0)) (fun t ht ↦ max_eq_right ht)]
  simpa only [quadraticBallCutoff] using quadraticBallCutoff_integral_divergence F hF c hb.1.le

private theorem ballPosPart_integral_divergence_eq_ballIntegral_radial
    [Fact (0 < n)]
    (F : Fin n → ℝ^n → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i))
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (∫ x, max (r ^ 2 - ‖x - c‖ ^ 2) 0 *
        ∑ i : Fin n, (∂[i] (F i)) x) =
      2 * ballIntegral n
        (fun x ↦ ∑ i : Fin n, F i x * (x - c) i) c r := by
  have hK := isCompact_closedBall c (r + 1)
  have hq : Measurable fun x : ℝ^n ↦ ‖x - c‖ ^ 2 := by fun_prop
  have hH : Continuous fun x ↦ ∑ i : Fin n, F i x * (x - c) i := by fun_prop
  -- differentiate the cutoff identity in `b` at `b = r²`
  have hderiv := ((hasDerivAt_integral_sqPosPart_mul _ _ _ hq (fun x ↦ sq_nonneg ‖x - c‖)
    ((continuous_divergence hF).continuousOn.integrableOn_compact hK)
    (sq_nonneg r)).congr_of_eventuallyEq
      (quadraticBallCutoff_integral_divergence_restrict_eventually F hF c hr).symm).unique
    ((hasDerivAt_integral_posPart_mul _ _ _ hq (fun x ↦ sq_nonneg ‖x - c‖)
      (hH.continuousOn.integrableOn_compact hK) (restrict_closedBall_sphere_null c hr)).const_mul 4)
  rw [setIntegral_sublevel_eq_ballIntegral _ c hr] at hderiv
  simp only [mul_assoc, integral_const_mul] at hderiv
  rw [setIntegral_closedBall_eq_integral c hr (by nlinarith) (g := (max · 0))
    (fun t ht ↦ max_eq_right ht)] at hderiv
  linarith

private theorem continuous_sphereIntegral_radius
    (G : ℝ^n → ℝ) (hG : Continuous G)
    (c : ℝ^n) :
    Continuous (sphereIntegral n G c) := by
  unfold sphereIntegral
  refine (continuous_abs.pow (n - 1)).mul ?_
  simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (ℝ^n)).toSphere)
    (f := fun (r : ℝ) (ω : Metric.sphere (0 : ℝ^n) 1) ↦ G (c + r • (ω : ℝ^n)))
    (hG.comp (continuous_const.add (continuous_fst.smul
      (continuous_subtype_val.comp continuous_snd)))) isCompact_univ

/-- The derivative of an integral over `B(c, r)` with respect to a positive
radius is the corresponding surface integral over `∂B(c, r)`. -/
theorem hasDerivAt_ballIntegral_radius
    [Fact (0 < n)]
    (G : ℝ^n → ℝ) (hG : Continuous G)
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (ballIntegral n G c) (sphereIntegral n G c r) r := by
  refine ((continuous_sphereIntegral_radius G hG c).integral_hasStrictDerivAt 0 r).hasDerivAt
    |>.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with s hs
  rw [coarea_formula_ball G c s ((hG.continuousOn.integrableOn_compact
    (isCompact_closedBall c s)).mono_set Metric.ball_subset_closedBall),
    intervalIntegral.integral_of_le hs.le]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

private theorem hasDerivAt_ballPosPart_integral_radius
    [Fact (0 < n)]
    (G : ℝ^n → ℝ) (hG : Continuous G)
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun s ↦
        ∫ x, max (s ^ 2 - ‖x - c‖ ^ 2) 0 * G x)
      (2 * r * ballIntegral n G c r) r := by
  have hsquare : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * r) r := by
    cas
  -- the parameter derivative at `b = r²`, composed with `s ↦ s²`
  have hcomposed := (hasDerivAt_integral_posPart_mul _ (fun x ↦ ‖x - c‖ ^ 2) G (by fun_prop)
    (fun x ↦ sq_nonneg ‖x - c‖)
    (hG.continuousOn.integrableOn_compact (isCompact_closedBall c (r + 1)))
    (restrict_closedBall_sphere_null c hr)).comp (h := fun s : ℝ ↦ s ^ 2) r hsquare
  rw [setIntegral_sublevel_eq_ballIntegral G c hr] at hcomposed
  refine (hcomposed.congr_deriv (mul_comm _ _)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hr (by linarith : r < r + 1)] with s hs
  exact (setIntegral_closedBall_eq_integral c hr (by nlinarith [hs.1, hs.2])
    (g := (max · 0)) (fun t ht ↦ max_eq_right ht) G).symm

/-- Gauss's formula on a positive-radius Euclidean ball, obtained by
differentiating the compactly supported quadratic-cutoff identity. -/
theorem ballIntegral_divergence_eq_sphereIntegral_normal_flux
    [Fact (0 < n)]
    (F : Fin n → ℝ^n → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i))
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    ballIntegral n
        (fun x ↦
          ∑ i : Fin n, (∂[i] (F i)) x)
        c r =
      sphereIntegral n
        (fun x ↦
          ∑ i : Fin n,
            F i x * (NormedSpace.normalize (x - c)) i)
        c r := by
  have hH : Continuous fun x ↦ ∑ i : Fin n, F i x * (x - c) i := by fun_prop
  -- `d/ds ∫ (s² - ‖x - c‖²)⁺ div F = 2 s ∫_{B(c, s)} div F` and `= 2 d/ds ∫_{B(c, s)} F · (x - c)`
  have hderiv := ((hasDerivAt_ballPosPart_integral_radius _ (continuous_divergence hF) c
    hr).congr_of_eventuallyEq (by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      exact (ballPosPart_integral_divergence_eq_ballIntegral_radial F hF c hs).symm)).unique
    ((hasDerivAt_ballIntegral_radius _ hH c hr).const_mul 2)
  -- on the sphere `F · (x - c) = r F · ν`
  have hHN : sphereIntegral n (fun x ↦ ∑ i : Fin n, F i x * (x - c) i) c r =
      r * sphereIntegral n (fun x ↦ ∑ i : Fin n,
        F i x * (NormedSpace.normalize (x - c)) i) c r := by
    rw [sphereIntegral_congr_on_sphere hr (v := fun x ↦ r * ∑ i : Fin n,
      F i x * (NormedSpace.normalize (x - c)) i) fun x hx ↦ ?_]
    · unfold sphereIntegral
      rw [integral_const_mul]
      ring
    have hnorm : ‖x - c‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hx
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [NormedSpace.normalize, hnorm, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
    field_simp
  exact mul_left_cancel₀ hr.ne' (by linarith)

end PDE.Analysis
