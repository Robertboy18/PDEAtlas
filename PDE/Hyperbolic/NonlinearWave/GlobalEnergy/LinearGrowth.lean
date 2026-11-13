/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSlab
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SupportPropagation
import PDE.FDeriv.Calculus
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticLowerBound

/-!
# Common compact support from separate compact slices

Let `V` be `C¹` with `V 0 = 0` and `V z ≥ -C z²` near zero. Finite propagation for such
potentials carries zero Cauchy data outside a ball across a finite strip, in both time
directions. Baire category supplies a common Cauchy support from separate compact slices of a
`C²` solution, so the solution has common compact support on every finite forward slab.

A continuous reaction `f` with `f(z) = O(z)` near zero is covered through its primitive
`V z = ∫₀ᶻ f`, which satisfies `|V z| ≤ C z²` near zero; no local Lipschitz regularity of `f`
and no sign of the potential is needed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The primitive `V z = ∫₀ᶻ f` of a continuous reaction with linear growth at zero is `C¹`,
vanishes at zero, has derivative `f`, and satisfies `V z ≥ -C z²` near zero. -/
private theorem exists_primitive_of_isBigO {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : f =O[𝓝 0] (fun z : ℝ ↦ z)) :
    ∃ V : ℝ → ℝ, ∃ C : ℝ, ContDiff ℝ 1 V ∧ V 0 = 0 ∧ deriv V = f ∧
      ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z := by
  let V : ℝ → ℝ := fun z ↦ ∫ s in (0 : ℝ)..z, f s
  have hderiv : deriv V = f := funext fun z ↦ hf.deriv_integral f 0 z
  have hV : ContDiff ℝ 1 V := contDiff_one_iff_deriv.mpr
    ⟨fun z ↦ (hf.integral_hasStrictDerivAt 0 z).hasDerivAt.differentiableAt, hderiv ▸ hf⟩
  obtain ⟨C, hC⟩ := hzero.bound
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff_ball.mp hC
  refine ⟨V, max C 0, hV, intervalIntegral.integral_same, hderiv, ?_⟩
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with z hz
  have hz' : |z| < δ := by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz
  have hint : ‖V z‖ ≤ max C 0 * |z| * |z - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hsz : |s| ≤ |z| := by
      rcases le_total 0 z with h0 | h0
      · rw [uIoc_of_le h0] at hs
        rw [abs_of_pos hs.1, abs_of_nonneg h0]
        exact hs.2
      · rw [uIoc_of_ge h0] at hs
        rw [abs_of_nonpos hs.2, abs_of_nonpos h0]
        linarith [hs.1]
    have hfs := hnear s (by simpa only [Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] using hsz.trans_lt hz')
    simp only [Real.norm_eq_abs] at hfs ⊢
    calc
      |f s| ≤ C * |s| := hfs
      _ ≤ max C 0 * |s| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg s)
      _ ≤ max C 0 * |z| := mul_le_mul_of_nonneg_left hsz (le_max_right _ _)
  rw [sub_zero, mul_assoc, ← sq, sq_abs, Real.norm_eq_abs] at hint
  linarith [neg_abs_le (V z)]

/-- A continuous reaction with linear growth at zero cannot create a wave from
zero Cauchy data on a backward cone. No local Lipschitz hypothesis is needed: the
primitive `V z = ∫₀ᶻ f` satisfies `V z ≥ -C z²` near zero, so the quadratic-lower-bound
uniqueness theorem applies. -/
theorem eq_zero_on_closed_backwardCone_of_isBigO [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hf : Continuous f) (hzero : f =O[𝓝 0] (fun z : ℝ ↦ z)) (hu : ContDiff ℝ 2 u) (c : ℝ^n)
    {a T : ℝ}
    (hwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) =
      -f (u (timeSpaceCons t x)))
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) = 0) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  obtain ⟨V, C, hV, hVzero, hderiv, hbound⟩ := exists_primitive_of_isBigO hf hzero
  apply eq_zero_on_closed_backwardCone_of_quadratic_lower_bound hV hVzero hbound hu c _ hpos hvel
  intro t ht x hx
  simp only [semilinearWaveOperator, hderiv, hwave t ht x hx, neg_add_cancel]

/-- Compact Cauchy support propagates at speed one across a finite strip.
The potential is `C¹`, vanishes at zero, and is bounded below by `-C z²` near zero. -/
theorem eq_zero_of_norm_gt_cauchySupport_of_quadratic_lower_bound [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {C a t R : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (hu : ContDiff ℝ 2 u) (hat : a ≤ t)
    (hwave : ∀ s ∈ Ico a t, ∀ y, semilinearWaveOperator V u (timeSpaceCons s y) = 0)
    (hpos : ∀ y : ℝ^n, R < ‖y‖ → u (timeSpaceCons a y) = 0)
    (hvel : ∀ y : ℝ^n, R < ‖y‖ → (∂[0] u) (timeSpaceCons a y) = 0) {x : ℝ^n}
    (hx : R + (t - a) < ‖x‖) :
    u (timeSpaceCons t x) = 0 := by
  have hbase (y : ℝ^n) (hy : y ∈ Metric.closedBall x (t - a)) : R < ‖y‖ := by
    have hy' : ‖y - x‖ ≤ t - a := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    have hn := norm_le_norm_add_norm_sub y x
    linarith
  exact eq_zero_on_closed_backwardCone_of_quadratic_lower_bound hV hVzero hbound hu x
    (fun s hs y _ ↦ hwave s hs y) (fun y hy ↦ hpos y (hbase y hy)) (fun y hy ↦ hvel y (hbase y hy))
    t ⟨hat, le_rfl⟩ x (by simp)

/-- Compact Cauchy support at any time controls the whole finite lifespan slab,
including earlier times. Zero data propagate in both time directions. -/
theorem eq_zero_on_Icc_of_cauchySupport_of_quadratic_lower_bound [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} {C b a T R : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (hu : ContDiff ℝ 2 u) (ha : a ∈ Icc b T)
    (hwave : ∀ s ∈ Icc b T, ∀ y, semilinearWaveOperator V u (timeSpaceCons s y) = 0)
    (hpos : ∀ y : ℝ^n, R < ‖y‖ → u (timeSpaceCons a y) = 0)
    (hvel : ∀ y : ℝ^n, R < ‖y‖ → (∂[0] u) (timeSpaceCons a y) = 0) :
    ∀ t ∈ Icc b T, ∀ x : ℝ^n, R + (T - b) < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  have hreflect (s : ℝ) (y : ℝ^n) :
      coordinateReflection 0 (timeSpaceCons s y) = timeSpaceCons (-s) y := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  intro t ht x hx
  by_cases hat : a ≤ t
  · exact eq_zero_of_norm_gt_cauchySupport_of_quadratic_lower_bound hV hVzero hbound hu hat
      (fun s hs y ↦ hwave s ⟨ha.1.trans hs.1, hs.2.le.trans ht.2⟩ y)
      hpos hvel (by linarith [ha.1, ht.2])
  · let v : ℝ^(n + 1) → ℝ := fun p ↦ u (coordinateReflection 0 p)
    have hv : ContDiff ℝ 2 v := hu.comp
      (coordinateReflectionLinearIsometryEquiv 0).toContinuousLinearEquiv.contDiff
    have he := eq_zero_of_norm_gt_cauchySupport_of_quadratic_lower_bound (u := v) (a := -a)
      (t := -t) (R := R) hV hVzero hbound hv (by linarith) (fun s hs y ↦ ?_) (fun y hy ↦ ?_)
      (fun y hy ↦ ?_) (x := x) (by linarith [ht.1, ha.2])
    · simpa only [v, hreflect, neg_neg] using he
    · have hw := hwave (-s) ⟨by linarith [ht.1, hs.2], by linarith [ha.2, hs.1]⟩ y
      unfold semilinearWaveOperator at hw ⊢
      dsimp only [v]
      rw [waveOperator_comp_timeReflection hu, hreflect]
      exact hw
    · simpa only [v, hreflect, neg_neg] using hpos y hy
    · change (∂[0] (fun p ↦ u (coordinateReflection 0 p))) (timeSpaceCons (-a) y) = 0
      rw [partialDeriv_comp_coordinateReflection_same 0 u _
        (hu.differentiable (by norm_num)).differentiableAt, hreflect, neg_neg, hvel y hy, neg_zero]

/-- Separate compact spatial slices of a `C²` semilinear wave give common compact support on
every finite forward slab, for a `C¹` potential vanishing at zero and bounded below by `-C z²`
near zero. Baire category supplies a common Cauchy support, which finite propagation carries
across the slab. -/
theorem exists_uniform_support_on_Icc_of_compact_slices_of_quadratic_lower_bound [Fact (0 < n)]
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {C : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 ≤ t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, R < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  let I := Ioo (0 : ℝ) (T + 1)
  have hI : IsOpen I := isOpen_Ioo
  let : BaireSpace I := hI.baireSpace
  let : Nonempty I := ⟨⟨(T + 1) / 2, by constructor <;> linarith⟩⟩
  have hc (x : ℝ^n) : Continuous (fun t : I ↦ u (timeSpaceCons t x)) :=
    hu.continuous.comp ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_subtype_val.prodMk continuous_const))
  obtain ⟨a, R, hR⟩ :=
    (dense_locally_uniform_spatial_support hc (fun t ↦ hs t t.property.1.le)).nonempty
  have hR' := (eventually_nhds_subtype_iff I a
    (fun s ↦ ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0)).mp hR
  rw [hI.nhdsWithin_eq a.property] at hR'
  change ∀ᶠ s : ℝ in 𝓝 (a : ℝ), ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0 at hR'
  have hgerm (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) :
      u =ᶠ[𝓝 (timeSpaceCons a x)] fun _ ↦ 0 := by
    have hproj : Tendsto (fun p : ℝ^(n + 1) ↦ p 0) (𝓝 (timeSpaceCons (a : ℝ) x)) (𝓝 (a : ℝ)) :=
      (show Continuous (fun p : ℝ^(n + 1) ↦ p 0) from
        (EuclideanSpace.proj 0).continuous).continuousAt
    have ht : ∀ᶠ p : ℝ^(n + 1) in 𝓝 (timeSpaceCons a x),
        ∀ y : ℝ^n, (R : ℝ) < ‖y‖ → u (timeSpaceCons (p 0) y) = 0 :=
      hproj.eventually (p := fun s ↦ ∀ y : ℝ^n, (R : ℝ) < ‖y‖ → u (timeSpaceCons s y) = 0) hR'
    have hx' : ∀ᶠ p in 𝓝 (timeSpaceCons a x), (R : ℝ) < ‖spatialPart p‖ :=
      ((spatialPartCLM n).continuous.norm.continuousAt).eventually (lt_mem_nhds hx)
    filter_upwards [ht, hx'] with p hp hpx
    simpa only [timeSpaceCons_spatialPart] using hp (spatialPart p) hpx
  have hpos (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) : u (timeSpaceCons a x) = 0 := (hgerm x hx).eq_of_nhds
  have hvel (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) : (∂[0] u) (timeSpaceCons a x) = 0 := by
    rw [PDE.partialDeriv_congr_nhds 0 (hgerm x hx)]
    exact PDE.partialDeriv_const 0
  refine ⟨(R : ℝ) + (T + 1), by positivity, ?_⟩
  intro t ht x hx
  exact eq_zero_on_Icc_of_cauchySupport_of_quadratic_lower_bound hV hVzero hbound hu
    ⟨a.property.1.le, a.property.2.le⟩
    (fun s hsI y ↦ hwave s hsI.1 y) hpos hvel t ⟨ht.1, by linarith [ht.2]⟩ x
    (by simpa only [sub_zero] using hx)

/-- Compact Cauchy support propagates at speed one across a finite strip.
The reaction is continuous with linear growth at zero. -/
theorem eq_zero_of_norm_gt_cauchySupport_of_isBigO [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {a t R : ℝ} (hf : Continuous f) (hzero : f =O[𝓝 0] (fun z : ℝ ↦ z)) (hu : ContDiff ℝ 2 u)
    (hat : a ≤ t)
    (hwave : ∀ s ∈ Ico a t, ∀ y, waveOperator u (timeSpaceCons s y) = -f (u (timeSpaceCons s y)))
    (hpos : ∀ y : ℝ^n, R < ‖y‖ → u (timeSpaceCons a y) = 0)
    (hvel : ∀ y : ℝ^n, R < ‖y‖ → (∂[0] u) (timeSpaceCons a y) = 0) {x : ℝ^n}
    (hx : R + (t - a) < ‖x‖) :
    u (timeSpaceCons t x) = 0 := by
  obtain ⟨V, C, hV, hVzero, hderiv, hbound⟩ := exists_primitive_of_isBigO hf hzero
  refine eq_zero_of_norm_gt_cauchySupport_of_quadratic_lower_bound hV hVzero hbound hu hat
    (fun s hs y ↦ ?_) hpos hvel hx
  simp only [semilinearWaveOperator, hderiv, hwave s hs y, neg_add_cancel]

/-- Compact Cauchy support at any time controls the whole finite lifespan slab,
including earlier times, for a continuous reaction with linear growth at zero. -/
theorem eq_zero_on_Icc_of_cauchySupport_of_isBigO [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {b a T R : ℝ} (hf : Continuous f) (hzero : f =O[𝓝 0] (fun z : ℝ ↦ z)) (hu : ContDiff ℝ 2 u)
    (ha : a ∈ Icc b T)
    (hwave : ∀ s ∈ Icc b T, ∀ y, waveOperator u (timeSpaceCons s y) = -f (u (timeSpaceCons s y)))
    (hpos : ∀ y : ℝ^n, R < ‖y‖ → u (timeSpaceCons a y) = 0)
    (hvel : ∀ y : ℝ^n, R < ‖y‖ → (∂[0] u) (timeSpaceCons a y) = 0) :
    ∀ t ∈ Icc b T, ∀ x : ℝ^n, R + (T - b) < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  obtain ⟨V, C, hV, hVzero, hderiv, hbound⟩ := exists_primitive_of_isBigO hf hzero
  refine eq_zero_on_Icc_of_cauchySupport_of_quadratic_lower_bound hV hVzero hbound hu ha
    (fun s hs y ↦ ?_) hpos hvel
  simp only [semilinearWaveOperator, hderiv, hwave s hs y, neg_add_cancel]

/-- Separate compact spatial slices of a `C²` wave with a continuous reaction of linear growth
at zero give common compact support on every finite forward slab. -/
theorem exists_uniform_support_on_Icc_of_compact_slices_of_isBigO [Fact (0 < n)] {f : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : Continuous f) (hzero : f =O[𝓝 0] (fun z : ℝ ↦ z))
    (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 ≤ t → ∀ x, waveOperator u (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {T : ℝ}
    (hT : 0 ≤ T) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, R < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  obtain ⟨V, C, hV, hVzero, hderiv, hbound⟩ := exists_primitive_of_isBigO hf hzero
  refine exists_uniform_support_on_Icc_of_compact_slices_of_quadratic_lower_bound hV hVzero
    hbound hu (fun t ht x ↦ ?_) hs hT
  simp only [semilinearWaveOperator, hderiv, hwave t ht x, neg_add_cancel]

end WaveEquation
