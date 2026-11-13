/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHessian
public import PDE.Analysis.Integration.PrincipalValue
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Principal values of the planar Hessian kernels

The kernels `kᵢⱼ = hessianKernel i j` are homogeneous of degree `-2`, so `kᵢⱼ(x - ·) f` is not
integrable near `x` unless `f` vanishes there. They integrate to zero against every weight
invariant under the reflection `z ↦ (-z₀, z₁)` and the swap `z ↦ (z₁, z₀)`: `K₁ = k₀₁` is odd
under the reflection and `K₂ = k₀₀` is odd under the swap. With the disc truncation of
`PDE.Analysis.HasPrincipalValueAt`, the principal value therefore exists for every density that
is Hölder continuous at `x` and has an integrable far part, and it equals the absolutely
convergent integral

`∫_{|x-y|<r} kᵢⱼ(x - y) (f(y) - f(x)) dy + ∫_{U, |x-y|≥r} kᵢⱼ(x - y) f(y) dy`.

The domain `U` may be any measurable set containing the disc, for instance the boxes
`Q_{a,b₁,b₂}(x)` of Chen and Hou I, (3.4).

## Main results

* `integral_mul_hessianKernel_eq_zero`: against a weight invariant under the reflection of the
  first coordinate and under the coordinate swap, every Hessian kernel integrates to zero.
* `integral_hessianKernel_sub_annulus`: the Hessian kernels have zero mean on every annulus.
* `hasPrincipalValueAt_hessianKernel_of_holder`: if `|f(y) - f(x)| ≤ M |x - y|^α` on
  `B(x, r) ⊆ U` and the far part is integrable, the disc-truncated principal value exists and
  equals the integral above.
* `hasPrincipalValueAt_of_integrable`: an absolutely convergent singular integral is its own
  principal value.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace PotentialTheory.Planar

/-- An integrand that changes sign under a linear isometry integrates to zero. -/
theorem integral_eq_zero_of_comp_linearIsometryEquiv_eq_neg (e : ℝ^2 ≃ₗᵢ[ℝ] ℝ^2)
    {g : ℝ^2 → ℝ} (hg : ∀ z, g (e z) = -g z) : ∫ z, g z = 0 := by
  have h := MeasureTheory.integral_comp e g
  simp only [hg, integral_neg] at h
  linarith

/-- **Cancellation of the Hessian kernels.** Against a weight invariant under the reflection of
the first coordinate and under the coordinate swap, every Hessian kernel integrates to zero. -/
theorem integral_mul_hessianKernel_eq_zero (i j : Fin 2) {w : ℝ^2 → ℝ}
    (h₀ : ∀ z, w (PDE.Common.coordinateReflection 0 z) = w z)
    (hσ : ∀ z, w (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) = w z) :
    ∫ z, w z * hessianKernel i j z = 0 := by
  have hoff : ∫ z, w z * hessianKernel 0 1 z = 0 :=
    integral_eq_zero_of_comp_linearIsometryEquiv_eq_neg
      (PDE.Common.coordinateReflectionLinearIsometryEquiv 0) fun z ↦ by
        change w (PDE.Common.coordinateReflection 0 z) *
          hessianKernel 0 1 (PDE.Common.coordinateReflection 0 z) = _
        rw [h₀, hessianKernel_zero_one_coordinateReflection]; ring
  have hdiag : ∫ z, w z * hessianKernel 0 0 z = 0 :=
    integral_eq_zero_of_comp_linearIsometryEquiv_eq_neg
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)) fun z ↦ by
        rw [hσ, hessianKernel_zero_zero_swap]; ring
  fin_cases i <;> fin_cases j
  · exact hdiag
  · exact hoff
  · simpa [hessianKernel_one_zero] using hoff
  · simpa [hessianKernel_one_one, integral_neg] using hdiag

/-- The annulus `ε < |x - y| < r` as a subset of the disc. -/
private theorem measurableSet_annulus (x : ℝ^2) (ε r : ℝ) :
    MeasurableSet (ball x r ∩ {y : ℝ^2 | ε < ‖x - y‖}) :=
  measurableSet_ball.inter
    (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)

/-- The Hessian kernels are bounded by `1/(2ε²)` off the disc of radius `ε`. -/
theorem abs_hessianKernel_le_of_lt (i j : Fin 2) {ε : ℝ} (hε : 0 < ε) {z : ℝ^2} (hz : ε < ‖z‖) :
    |hessianKernel i j z| ≤ 1 / (2 * ε ^ 2) := by
  refine (abs_hessianKernel_le i j z).trans ?_
  gcongr

/-- A Hessian kernel is integrable on every annulus around its pole. -/
theorem integrableOn_hessianKernel_sub_annulus (i j : Fin 2) (x : ℝ^2) {ε r : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y ↦ hessianKernel i j (x - y)) (ball x r ∩ {y | ε < ‖x - y‖}) := by
  refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2))
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
    ((measurable_hessianKernel i j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem (measurableSet_annulus x ε r)] with y hy
  rw [Real.norm_eq_abs]
  exact abs_hessianKernel_le_of_lt i j hε hy.2

/-- The Hessian kernels have zero mean on every annulus. -/
theorem integral_hessianKernel_sub_annulus (i j : Fin 2) (x : ℝ^2) (ε r : ℝ) :
    ∫ y in ball x r ∩ {y | ε < ‖x - y‖}, hessianKernel i j (x - y) = 0 := by
  let A : Set (ℝ^2) := {z | ‖z‖ < r ∧ ε < ‖z‖}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_norm measurable_const).inter
      (measurableSet_lt measurable_const measurable_norm)
  rw [← integral_indicator (measurableSet_annulus x ε r)]
  have hind : (ball x r ∩ {y | ε < ‖x - y‖}).indicator (fun y ↦ hessianKernel i j (x - y)) =
      fun y ↦ A.indicator (fun z ↦ hessianKernel i j z) (x - y) := by
    funext y
    have hiff : y ∈ ball x r ∩ {y | ε < ‖x - y‖} ↔ x - y ∈ A := by
      simp only [mem_inter_iff, mem_ball, dist_eq_norm, A, norm_sub_rev y x]; rfl
    by_cases hy : y ∈ ball x r ∩ {y | ε < ‖x - y‖}
    · rw [indicator_of_mem hy, indicator_of_mem (hiff.mp hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h ↦ hy (hiff.mpr h))]
  rw [hind, integral_sub_left_eq_self (fun z ↦ A.indicator (fun z ↦ hessianKernel i j z) z)]
  have hw : (fun z ↦ A.indicator (fun z ↦ hessianKernel i j z) z) =
      fun z ↦ A.indicator (fun _ ↦ (1 : ℝ)) z * hessianKernel i j z := by
    funext z; by_cases hz : z ∈ A <;> simp [hz]
  rw [hw]
  apply integral_mul_hessianKernel_eq_zero
  · intro z; simp [A, indicator, PDE.Common.norm_coordinateReflection]
  · intro z; simp [A, indicator]

/-- **Existence of the principal value for densities Hölder continuous at the point.**
If `|f(y) - f(x)| ≤ M |x - y|^α` on the disc `B(x, r) ⊆ U` (`α > 0`) and the far part is
integrable, the disc-truncated principal value of `∫_U kᵢⱼ(x - y) f(y) dy` exists and equals
`∫_{B(x,r)} kᵢⱼ(x - y)(f(y) - f(x)) dy + ∫_{U \ B(x,r)} kᵢⱼ(x - y) f(y) dy`. -/
theorem hasPrincipalValueAt_hessianKernel_of_holder (i j : Fin 2) {U : Set (ℝ^2)}
    (hU : MeasurableSet U) {f : ℝ^2 → ℝ} {x : ℝ^2} {r M α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hball : ball x r ⊆ U) (hmeas : AEStronglyMeasurable f)
    (hhol : ∀ y ∈ ball x r, |f y - f x| ≤ M * ‖x - y‖ ^ α)
    (hfar : IntegrableOn (fun y ↦ hessianKernel i j (x - y) * f y) (U \ ball x r)) :
    PDE.Analysis.HasPrincipalValueAt U (fun x y ↦ hessianKernel i j (x - y)) f x
      ((∫ y in ball x r, hessianKernel i j (x - y) * (f y - f x)) +
        ∫ y in U \ ball x r, hessianKernel i j (x - y) * f y) := by
  set k : ℝ^2 → ℝ := fun y ↦ hessianKernel i j (x - y)
  have hkmeas : Measurable k :=
    (measurable_hessianKernel i j).comp (measurable_const.sub measurable_id)
  -- the subtracted integrand is integrable on the disc
  have hg : IntegrableOn (fun y ↦ k y * (f y - f x)) (ball x r) := by
    have hpow : IntegrableOn (fun z : ℝ^2 ↦ |M| / 2 * ‖z‖ ^ (α - 2)) (ball 0 r) := by
      refine integrableOn_ball_of_norm_le_rpow (C := |M| / 2) (α := 2 - α) (by simp)
        (by simp; linarith) (.of_forall fun z ↦ ?_)
        (measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_two, abs_abs, abs_of_nonneg (Real.rpow_nonneg
        (norm_nonneg z) _), show α - 2 = -(2 - α) by ring]
    have hpow' : IntegrableOn (fun y : ℝ^2 ↦ |M| / 2 * ‖x - y‖ ^ (α - 2)) (ball x r) := by
      rw [← integrable_indicator_iff measurableSet_ball]
      convert (hpow.integrable_indicator measurableSet_ball).comp_sub_left x using 1
      funext y
      simp only [indicator, mem_ball, dist_eq_norm, sub_zero, norm_sub_rev y x]
    refine hpow'.mono'
      ((hkmeas.aestronglyMeasurable.mul (hmeas.sub aestronglyMeasurable_const)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · rw [sub_self, mul_zero, norm_zero]
      positivity
    have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx.symm)
    rw [Real.norm_eq_abs, abs_mul]
    calc |k y| * |f y - f x| ≤ 1 / (2 * ‖x - y‖ ^ 2) * (|M| * ‖x - y‖ ^ α) := by
          gcongr
          · exact abs_hessianKernel_le i j (x - y)
          · exact (hhol y hy).trans (by gcongr; exact le_abs_self M)
      _ = |M| / 2 * ‖x - y‖ ^ (α - 2) := by
          rw [Real.rpow_sub hn, Real.rpow_two]; field_simp
  -- decomposition of the truncations
  have hsplit : ∀ ε ∈ Ioo 0 r, U ∩ {y | ε < ‖x - y‖} =
      (ball x r ∩ {y | ε < ‖x - y‖}) ∪ (U \ ball x r) := by
    intro ε hε
    ext y
    constructor
    · rintro ⟨hyU, hyε⟩
      exact (em (y ∈ ball x r)).imp (⟨·, hyε⟩) (⟨hyU, ·⟩)
    · rintro (⟨hyb, hyε⟩ | ⟨hyU, hyb⟩)
      · exact ⟨hball hyb, hyε⟩
      · exact ⟨hyU, hε.2.trans_le ((not_lt.1 fun h ↦ hyb (mem_ball'.2 h)).trans_eq
          (dist_eq_norm x y))⟩
  have hk (y : ℝ^2) : k y * f y = k y * (f y - f x) + k y * f x := by ring
  have hconst (ε : ℝ) (hε : 0 < ε) :=
    (integrableOn_hessianKernel_sub_annulus i j x (r := r) hε).mul_const (f x)
  have hnear (ε : ℝ) (hε : 0 < ε) :
      IntegrableOn (fun y ↦ k y * f y) (ball x r ∩ {y | ε < ‖x - y‖}) :=
    ((hg.mono_set inter_subset_left).add (hconst ε hε)).congr_fun (fun y _ ↦ (hk y).symm)
      (measurableSet_annulus x ε r)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  refine ⟨?_, ?_⟩
  · filter_upwards [hev] with ε hε
    rw [hsplit ε hε]
    exact (hnear ε hε.1).union hfar
  -- the near part converges by dominated convergence
  have hlim : Tendsto (fun ε ↦ ∫ y in ball x r ∩ {y | ε < ‖x - y‖}, k y * (f y - f x))
      (𝓝[>] 0) (𝓝 (∫ y in ball x r, k y * (f y - f x))) := by
    simp_rw [← integral_indicator (measurableSet_annulus x _ r),
      ← integral_indicator measurableSet_ball]
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun ε ↦ (hkmeas.aestronglyMeasurable.mul
        (hmeas.sub aestronglyMeasurable_const)).indicator (measurableSet_annulus x ε r))
      (.of_forall fun ε ↦ .of_forall (norm_indicator_le_of_subset inter_subset_left _))
      (hg.integrable_indicator measurableSet_ball).norm ?_
    filter_upwards [(countable_singleton x).ae_notMem volume] with y hyx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hyx)))]
      with ε hε
    by_cases hyb : y ∈ ball x r
    · rw [indicator_of_mem hyb,
        indicator_of_mem (show y ∈ ball x r ∩ {y | ε < ‖x - y‖} from ⟨hyb, hε.2⟩)]
    · rw [indicator_of_notMem hyb, indicator_of_notMem (fun h ↦ hyb h.1)]
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), PDE.Analysis.principalValueTruncation U
      (fun x y ↦ hessianKernel i j (x - y)) f x ε =
        (∫ y in ball x r ∩ {y | ε < ‖x - y‖}, k y * (f y - f x)) +
          ∫ y in U \ ball x r, hessianKernel i j (x - y) * f y := by
    filter_upwards [hev] with ε hε
    have hdisj : Disjoint (ball x r ∩ {y | ε < ‖x - y‖}) (U \ ball x r) :=
      Set.disjoint_left.mpr fun y hy hy' ↦ hy'.2 hy.1
    have hnearval : ∫ y in ball x r ∩ {y | ε < ‖x - y‖}, k y * f y =
        ∫ y in ball x r ∩ {y | ε < ‖x - y‖}, k y * (f y - f x) := by
      simp_rw [hk]
      rw [integral_add (hg.mono_set inter_subset_left) (hconst ε hε.1), integral_mul_const,
        integral_hessianKernel_sub_annulus, zero_mul, add_zero]
    unfold PDE.Analysis.principalValueTruncation
    rw [hsplit ε hε, setIntegral_union hdisj (hU.diff measurableSet_ball) (hnear ε hε.1) hfar,
      hnearval]
  exact (tendsto_congr' heq).mpr (hlim.add_const _)

/-- An absolutely convergent singular integral is its own principal value. -/
theorem hasPrincipalValueAt_of_integrable {K : ℝ^2 → ℝ^2 → ℝ} {f : ℝ^2 → ℝ} {x : ℝ^2}
    (hint : Integrable fun y ↦ K x y * f y) :
    PDE.Analysis.HasPrincipalValueAt univ K f x (∫ y, K x y * f y) := by
  have hmeas (ε : ℝ) : MeasurableSet {y : ℝ^2 | ε < ‖x - y‖} :=
    measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm
  refine ⟨Eventually.of_forall fun ε ↦ hint.integrableOn, ?_⟩
  have heq (ε : ℝ) : PDE.Analysis.principalValueTruncation univ K f x ε =
      ∫ y, {y : ℝ^2 | ε < ‖x - y‖}.indicator (fun y ↦ K x y * f y) y := by
    unfold PDE.Analysis.principalValueTruncation
    rw [univ_inter, integral_indicator (hmeas ε)]
  rw [show PDE.Analysis.principalValueTruncation univ K f x = fun ε ↦
      ∫ y, {y : ℝ^2 | ε < ‖x - y‖}.indicator (fun y ↦ K x y * f y) y from funext heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖K x y * f y‖)
    (Eventually.of_forall fun ε ↦ hint.aestronglyMeasurable.indicator (hmeas ε))
    (Eventually.of_forall fun ε ↦ Eventually.of_forall fun y ↦ norm_indicator_le_norm_self _ y)
    hint.norm ?_
  filter_upwards [Measure.ae_ne volume x] with y hy
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy))
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  rw [indicator_of_mem (show y ∈ {y : ℝ^2 | ε < ‖x - y‖} from hε.2)]

end PotentialTheory.Planar
