/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.Similarity.Pointwise
public import PDE.FDeriv.Operators
import CAS.ExactTactic
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.DilationFamily
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Calculus for pointwise similarity transformations

The differential identities behind pointwise similarity reductions, independent of any
particular PDE: vector-valued time chain rules for scaled profiles and forward self-similar
fields, and Euclidean formulas for centered dilations, gradients, Laplacians, and backward
self-similar fields.

The formulas are the chain-rule step from (28) to (29) in Evans, §4.2.2, pp. 185-186. Balance
conditions such as the porous-medium exponent relation (30) are proved together with the
corresponding equation.

The profile is a plain function, and each theorem assumes only the regularity its calculation
needs.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, (27)-(31),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

namespace PDE.Representations.Similarity

open Filter Topology

variable {n : ℕ}

/-- The infinitesimal generator of the scaling
`f(x) ↦ a^amplitudeExponent f(a^spatialExponent x)`.

The first term records amplitude scaling; the finite sum is the derivative along the
Euler vector field `x ↦ x`. -/
noncomputable def scalingGenerator
    (amplitudeExponent spatialExponent : ℝ)
    (profile : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  amplitudeExponent * profile x +
    spatialExponent * ∑ i, x i * (∂[i] profile) x

/-- Vector-valued infinitesimal generator of amplitude scaling and spatial dilation.

For a profile with values in a real normed space, this is
`alpha profile(x) + beta D profile(x)[x]`. -/
noncomputable def similarityGenerator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (amplitudeExponent spatialExponent : ℝ)
    (profile : ℝ^n → E) (x : ℝ^n) : E :=
  amplitudeExponent • profile x +
    spatialExponent • fderiv ℝ profile x x

/-- On scalar profiles, the vector-valued similarity generator agrees with the coordinate-sum
scaling generator. -/
theorem similarityGenerator_eq_scalingGenerator
    (amplitudeExponent spatialExponent : ℝ)
    (profile : ℝ^n → ℝ) (x : ℝ^n) :
    similarityGenerator amplitudeExponent spatialExponent profile x =
      scalingGenerator amplitudeExponent spatialExponent profile x := by
  rw [similarityGenerator, scalingGenerator,
    fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : ℝ ↦ a + b) rfl
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- A centered dilation is smooth at every order. -/
@[fun_prop]
theorem contDiff_centered_dilation
    {k : WithTop ℕ∞} (scale : ℝ) (center : ℝ^n) :
    ContDiff ℝ k (centeredDilation scale center) := by
  unfold centeredDilation
  fun_prop

/-- A fixed-time slice of a scalar-valued scaled profile inherits the profile's regularity. -/
theorem contDiff_scaled_profile_ansatz_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : WithTop ℕ∞}
    (profile : ℝ^n → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center : ℝ^n) (t : ℝ) (hprofile : ContDiff ℝ k profile) :
    ContDiff ℝ k
      (fun x ↦ scaledProfileAnsatz profile amplitudeScale spatialScale center x t) := by
  change
    ContDiff ℝ k
      (fun x ↦ amplitudeScale t •
        profile (centeredDilation (spatialScale t) center x))
  exact contDiff_const.smul
    (hprofile.comp (contDiff_centered_dilation (spatialScale t) center))

/-- A scalar-valued scaled profile is jointly regular on a product domain when its profile and
both time-dependent scales have the corresponding regularity. -/
theorem contDiffOn_prod_scaled_profile_ansatz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : WithTop ℕ∞}
    (profile : ℝ^n → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center : ℝ^n) (I : Set ℝ)
    (hprofile : ContDiff ℝ k profile)
    (hamplitude : ContDiffOn ℝ k amplitudeScale I)
    (hspatial : ContDiffOn ℝ k spatialScale I) :
    ContDiffOn ℝ k
      (fun xt : ℝ^n × ℝ ↦
        scaledProfileAnsatz profile amplitudeScale spatialScale center xt.1 xt.2)
      (Set.univ ×ˢ I) := by
  have hamplitude' :
      ContDiffOn ℝ k (fun xt : ℝ^n × ℝ ↦ amplitudeScale xt.2)
        (Set.univ ×ˢ I) :=
    hamplitude.comp contDiffOn_snd (by
      intro xt hxt
      exact hxt.2)
  have hspatial' :
      ContDiffOn ℝ k (fun xt : ℝ^n × ℝ ↦ spatialScale xt.2)
        (Set.univ ×ˢ I) :=
    hspatial.comp contDiffOn_snd (by
      intro xt hxt
      exact hxt.2)
  have hcoordinate :
      ContDiffOn ℝ k
        (fun xt : ℝ^n × ℝ ↦
          centeredDilation (spatialScale xt.2) center xt.1)
        (Set.univ ×ˢ I) := by
    unfold centeredDilation
    exact hspatial'.smul (contDiffOn_fst.sub contDiffOn_const)
  have hprofile_comp :
      ContDiffOn ℝ k
        (fun xt : ℝ^n × ℝ ↦
          profile (centeredDilation (spatialScale xt.2) center xt.1))
        (Set.univ ×ˢ I) :=
    hprofile.fun_comp_contDiffOn hcoordinate
  change
    ContDiffOn ℝ k
      (fun xt : ℝ^n × ℝ ↦
        amplitudeScale xt.2 •
          profile (centeredDilation (spatialScale xt.2) center xt.1))
      (Set.univ ×ˢ I)
  exact hamplitude'.smul hprofile_comp

/-- Chain rule for an amplitude-scaled profile in normed real vector spaces.

The two scale derivatives contribute an amplitude variation and the profile derivative along
the moving similarity coordinate. The spaces need not be complete. -/
theorem hasDerivAt_scaled_profile_ansatz
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : V → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center x : V) (t amplitudeDerivative spatialDerivative : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation (spatialScale t) center x))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative t)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative t) :
    HasDerivAt
      (fun s ↦ scaledProfileAnsatz
        profile amplitudeScale spatialScale center x s)
      (amplitudeScale t •
          fderiv ℝ profile
            (centeredDilation (spatialScale t) center x)
            (spatialDerivative • (x - center)) +
        amplitudeDerivative •
          profile (centeredDilation (spatialScale t) center x))
      t := by
  have hcoordinate :=
    hspatial.smul_const (x - center)
  have hcomp :=
    hprofile.hasFDerivAt.comp_hasDerivAt t hcoordinate
  change
    HasDerivAt
      (amplitudeScale •
        (profile ∘ fun s ↦ spatialScale s • (x - center)))
      _ t
  exact hamplitude.smul hcomp

/-- A forward self-similar field satisfies the vector-valued generator identity at positive
times.

At the similarity coordinate `y = t⁻ᵝ • (x - center)`, its derivative is
`t^(alpha - 1) • (alpha • profile y - beta • D profile y y)`. -/
theorem hasDerivAt_forward_self_similar_ansatz
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : V → E) (alpha beta : ℝ)
    (center x : V) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation (t ^ beta)⁻¹ center x))
    (ht : 0 < t) :
    HasDerivAt
      (fun s ↦ forwardSelfSimilarAnsatz profile alpha beta center x s)
      (t ^ (alpha - 1) •
        (alpha • profile (centeredDilation (t ^ beta)⁻¹ center x) -
          beta •
            fderiv ℝ profile
              (centeredDilation (t ^ beta)⁻¹ center x)
              (centeredDilation (t ^ beta)⁻¹ center x)))
      t := by
  have ht_ne : t ≠ 0 :=
    ne_of_gt ht
  have hamplitude :
      HasDerivAt (fun s : ℝ ↦ s ^ alpha)
        (alpha * t ^ (alpha - 1)) t := by
    cas using ht
  have hspatial :
      HasDerivAt (fun s : ℝ ↦ (s ^ beta)⁻¹)
        (-beta * t ^ (-beta - 1)) t := by
    have hquotient :
        HasDerivAt (fun s : ℝ ↦ (s ^ beta)⁻¹)
          (-(beta * t ^ (beta - 1)) / (t ^ beta) ^ 2) t := by
      cas using ht
    refine hquotient.congr_deriv ?_
    have hpow : t ^ beta ≠ 0 := (Real.rpow_pos_of_pos ht beta).ne'
    rw [Real.rpow_sub_one ht_ne, Real.rpow_sub_one ht_ne, Real.rpow_neg ht.le]
    field_simp
  unfold forwardSelfSimilarAnsatz
  apply
    (hasDerivAt_scaled_profile_ansatz
      profile (fun s ↦ s ^ alpha) (fun s ↦ (s ^ beta)⁻¹)
      center x t (alpha * t ^ (alpha - 1))
      (-beta * t ^ (-beta - 1)) hprofile hamplitude hspatial).congr_deriv
  have hpower :
      t ^ alpha * t ^ (-beta - 1) =
        t ^ (alpha - 1) * t ^ (-beta) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  have htransport :
      t ^ alpha * (-beta * t ^ (-beta - 1)) =
        t ^ (alpha - 1) * (-beta) * (t ^ beta)⁻¹ := by
    rw [← Real.rpow_neg ht.le beta]
    calc
      _ = -beta * (t ^ alpha * t ^ (-beta - 1)) := by ring
      _ = -beta * (t ^ (alpha - 1) * t ^ (-beta)) := by rw [hpower]
      _ = _ := by ring
  simp only [map_smul, smul_smul]
  rw [htransport]
  rw [show
    centeredDilation (t ^ beta)⁻¹ center x =
      (t ^ beta)⁻¹ • (x - center) by rfl]
  simp only [map_smul, smul_smul]
  module

/-- The derivative of `x ↦ scale • (x - center)` is `scale` times the identity map. -/
theorem hasFDerivAt_centered_dilation
    (scale : ℝ) (center x : ℝ^n) :
    HasFDerivAt (centeredDilation scale center)
      (scale • ContinuousLinearMap.id ℝ (ℝ^n)) x := by
  convert
    ((ContinuousLinearMap.id ℝ (ℝ^n)).hasFDerivAt.sub_const center).const_smul scale
      using 1
  rfl

/-- Coordinate `j` of a centered dilation has derivative `scale δᵢⱼ` in direction `i`. -/
theorem partialDeriv_centered_dilation_apply
    (scale : ℝ) (center x : ℝ^n) (i j : Fin n) :
    (∂[i] (fun y ↦ centeredDilation scale center y j)) x =
      scale * if i = j then 1 else 0 := by
  rw [← partialDeriv_apply i j
    (hasFDerivAt_centered_dilation scale center x).differentiableAt]
  rw [partialDeriv, (hasFDerivAt_centered_dilation scale center x).fderiv]
  simp [eq_comm]

/-- A backward power scale is strictly positive before its singular time. -/
theorem backward_power_scale_pos
    {alpha singularTime t : ℝ} (ht : t < singularTime) :
    0 < backwardPowerScale alpha singularTime t := by
  exact Real.rpow_pos_of_pos (sub_pos.mpr ht) _

/-- A backward power scale with positive exponent diverges as time approaches its singular
time from below. -/
theorem tendsto_backward_power_scale_at_top
    {alpha singularTime : ℝ} (halpha : 0 < alpha) :
    Tendsto (backwardPowerScale alpha singularTime)
      (nhdsWithin singularTime (Set.Iio singularTime)) atTop := by
  have hbase_nhds :
      Tendsto (fun t : ℝ ↦ singularTime - t)
        (nhdsWithin singularTime (Set.Iio singularTime)) (nhds 0) := by
    have hcontinuous :
        ContinuousAt (fun t : ℝ ↦ singularTime - t) singularTime := by
      fun_prop
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hbase_pos :
      ∀ᶠ t in nhdsWithin singularTime (Set.Iio singularTime),
        0 < singularTime - t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr ht
  have hbase :
      Tendsto (fun t : ℝ ↦ singularTime - t)
        (nhdsWithin singularTime (Set.Iio singularTime))
        (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hbase_nhds, hbase_pos⟩
  exact
    (tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr halpha)).comp hbase

/-- A backward power scale with negative exponent tends to zero as time
approaches its singular time from below. -/
theorem tendsto_backward_power_scale_zero
    {alpha singularTime : ℝ} (halpha : alpha < 0) :
    Tendsto (backwardPowerScale alpha singularTime)
      (nhdsWithin singularTime (Set.Iio singularTime)) (𝓝 0) := by
  have hbase :
      Tendsto (fun t : ℝ ↦ singularTime - t)
        (nhdsWithin singularTime (Set.Iio singularTime)) (𝓝 0) := by
    have hcontinuous :
        ContinuousAt (fun t : ℝ ↦ singularTime - t) singularTime := by
      fun_prop
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hexponent : 0 < -alpha := neg_pos.mpr halpha
  have hpower :=
    (Real.continuousAt_rpow_const 0 (-alpha)
      (Or.inr hexponent.le)).tendsto.comp hbase
  change
    Tendsto (fun t : ℝ ↦ (singularTime - t) ^ (-alpha))
      (nhdsWithin singularTime (Set.Iio singularTime)) (𝓝 0)
  simpa only [Function.comp_def, Real.zero_rpow hexponent.ne'] using hpower

/-- A backward power scale with exponent zero is identically one. -/
@[simp]
theorem backward_power_scale_zero
    (singularTime t : ℝ) :
    backwardPowerScale 0 singularTime t = 1 := by
  simp [backwardPowerScale]

/-- A backward power scale is `C^k` for every `k` before its singular time. -/
theorem contDiffOn_backward_power_scale
    {k : WithTop ℕ∞} (alpha singularTime : ℝ) :
    ContDiffOn ℝ k (backwardPowerScale alpha singularTime) (Set.Iio singularTime) := by
  intro t ht
  unfold backwardPowerScale
  exact (contDiffWithinAt_const.sub contDiffWithinAt_id).rpow_const_of_ne
    (ne_of_gt (sub_pos.mpr ht))

/-- Backward power scales multiply by adding their exponents. -/
theorem backward_power_scale_mul
    {alpha beta singularTime t : ℝ} (ht : t < singularTime) :
    backwardPowerScale alpha singularTime t *
        backwardPowerScale beta singularTime t =
      backwardPowerScale (alpha + beta) singularTime t := by
  have hbase : 0 < singularTime - t := sub_pos.mpr ht
  unfold backwardPowerScale
  rw [← Real.rpow_add hbase]
  congr 1
  ring

/-- A real power of a backward power scale multiplies the two exponents. -/
theorem backward_power_scale_rpow
    {alpha exponent singularTime t : ℝ} (ht : t < singularTime) :
    (backwardPowerScale alpha singularTime t) ^ exponent =
      backwardPowerScale (alpha * exponent) singularTime t := by
  have hbase : 0 < singularTime - t := sub_pos.mpr ht
  unfold backwardPowerScale
  rw [← Real.rpow_mul hbase.le]
  congr 1
  ring

/-- Raising a backward power scale to a natural power multiplies its exponent
by that natural number. -/
theorem backward_power_scale_pow
    {alpha singularTime t : ℝ} (n : ℕ) (ht : t < singularTime) :
    backwardPowerScale alpha singularTime t ^ n =
      backwardPowerScale ((n : ℝ) * alpha) singularTime t := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, backward_power_scale_mul ht]
      congr 2
      push_cast
      ring

/-- Squaring a backward power scale doubles its exponent. -/
theorem backward_power_scale_sq
    {alpha singularTime t : ℝ} (ht : t < singularTime) :
    backwardPowerScale alpha singularTime t ^ 2 =
      backwardPowerScale (2 * alpha) singularTime t := by
  exact backward_power_scale_pow 2 ht

/-- Before the singular time, differentiating a backward power scale raises its exponent by
one and multiplies by the original exponent. -/
theorem hasDerivAt_backward_power_scale
    {alpha singularTime t : ℝ} (ht : t < singularTime) :
    HasDerivAt (backwardPowerScale alpha singularTime)
      (alpha * backwardPowerScale (alpha + 1) singularTime t) t := by
  have hbase : 0 < singularTime - t := sub_pos.mpr ht
  unfold backwardPowerScale
  cas using hbase

/-- Derivative form of `hasDerivAt_backward_power_scale`. -/
theorem deriv_backward_power_scale
    {alpha singularTime t : ℝ} (ht : t < singularTime) :
    deriv (backwardPowerScale alpha singularTime) t =
      alpha * backwardPowerScale (alpha + 1) singularTime t :=
  (hasDerivAt_backward_power_scale ht).deriv

/-- Pulling a scalar profile back by a centered dilation multiplies its gradient by `scale`. -/
theorem gradient_comp_centered_dilation
    (profile : ℝ^n → ℝ) (scale : ℝ) (center x : ℝ^n)
    (hprofile : DifferentiableAt ℝ profile (centeredDilation scale center x)) :
    ∇ (fun y ↦ profile (centeredDilation scale center y)) x =
      scale • ∇ profile (centeredDilation scale center x) := by
  ext i
  simp only [gradient_apply_eq_partialDeriv]
  rw [partialDeriv_comp i profile (centeredDilation scale center) x hprofile
    (hasFDerivAt_centered_dilation scale center x).differentiableAt]
  simp [partialDeriv_centered_dilation_apply, mul_comm]

/-- At fixed time, the gradient of `scaledProfileAnsatz` carries one amplitude factor and one
spatial-scale factor. -/
theorem gradient_scaled_profile_ansatz
    (profile : ℝ^n → ℝ) (amplitudeScale spatialScale : ℝ → ℝ)
    (center x : ℝ^n) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation (spatialScale t) center x)) :
    ∇
        (fun y ↦ scaledProfileAnsatz profile amplitudeScale spatialScale center y t) x =
      (amplitudeScale t * spatialScale t) •
        ∇ profile (centeredDilation (spatialScale t) center x) := by
  ext i
  simp only [gradient_apply_eq_partialDeriv, PiLp.smul_apply, smul_eq_mul]
  change
    (∂[i]
        (fun y ↦ amplitudeScale t *
          profile (centeredDilation (spatialScale t) center y))) x = _
  have hcomp :
      DifferentiableAt ℝ
        (fun y ↦ profile (centeredDilation (spatialScale t) center y)) x :=
    hprofile.comp x
      (hasFDerivAt_centered_dilation (spatialScale t) center x).differentiableAt
  have hmul := partialDeriv_mul (n := n) (i := i)
    (f := fun _ : ℝ^n ↦ amplitudeScale t)
    (g := fun y ↦ profile (centeredDilation (spatialScale t) center y))
    (x := x) (by fun_prop) hcomp
  rw [hmul]
  simp only [partialDeriv_const, zero_mul, zero_add]
  have hgrad := congrArg (fun v : ℝ^n ↦ v i)
    (gradient_comp_centered_dilation profile (spatialScale t) center x hprofile)
  simp only [gradient_apply_eq_partialDeriv, PiLp.smul_apply, smul_eq_mul] at hgrad
  rw [hgrad]
  ring

/-- Divergence gains one spatial-scale factor when a vector field is pulled back by a centered
dilation, in addition to any constant amplitude factor. -/
theorem divergence_smul_comp_centered_dilation
    (field : ℝ^n → ℝ^n) (amplitude scale : ℝ) (center x : ℝ^n)
    (hfield : ∀ i, DifferentiableAt ℝ (fun y ↦ field y i)
      (centeredDilation scale center x)) :
    ∇· (fun y ↦ amplitude • field (centeredDilation scale center y)) x =
      amplitude * scale *
        ∇· field (centeredDilation scale center x) := by
  unfold divergence
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hcomp :
      DifferentiableAt ℝ (fun y ↦ field (centeredDilation scale center y) i) x :=
    (hfield i).comp x
      (hasFDerivAt_centered_dilation scale center x).differentiableAt
  have hmul := partialDeriv_mul (n := n) (i := i)
    (f := fun _ : ℝ^n ↦ amplitude)
    (g := fun y ↦ field (centeredDilation scale center y) i)
    (x := x) (by fun_prop) hcomp
  rw [hmul]
  simp only [partialDeriv_const, zero_mul, zero_add]
  rw [partialDeriv_comp i (fun y ↦ field y i)
    (centeredDilation scale center) x (hfield i)
    (hasFDerivAt_centered_dilation scale center x).differentiableAt]
  simp_rw [partialDeriv_centered_dilation_apply]
  simp
  ring

/-- Advection of two fields pulled back by the same centered dilation gains the product of
the two amplitude factors and one spatial-scale factor.

Only the transported field needs to be differentiable: the advecting field is evaluated
pointwise and supplies the direction in which the derivative is taken. -/
theorem advectiveDerivative_smul_comp_centered_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (advecting : ℝ^n → ℝ^n) (transported : ℝ^n → E)
    (advectingAmplitude transportedAmplitude scale : ℝ)
    (center x : ℝ^n)
    (htransported : DifferentiableAt ℝ transported
      (centeredDilation scale center x)) :
    advectiveDerivative
        (fun y ↦ advectingAmplitude •
          advecting (centeredDilation scale center y))
        (fun y ↦ transportedAmplitude •
          transported (centeredDilation scale center y)) x =
      (advectingAmplitude * transportedAmplitude * scale) •
        advectiveDerivative advecting transported
          (centeredDilation scale center x) := by
  have hcomp :=
    htransported.hasFDerivAt.comp x
      (hasFDerivAt_centered_dilation scale center x)
  have hscaled := hcomp.const_smul transportedAmplitude
  unfold advectiveDerivative
  change
    (fderiv ℝ
      (transportedAmplitude • transported ∘ centeredDilation scale center) x)
        (advectingAmplitude • advecting (centeredDilation scale center x)) =
      _
  rw [hscaled.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  simp [mul_assoc]

/-- Pulling a scalar profile back by a centered dilation multiplies its Laplacian by `scale²`.
No regularity of the profile is needed. -/
theorem laplacian_comp_centered_dilation
    (profile : ℝ^n → ℝ) (scale : ℝ) (center x : ℝ^n) :
    laplacian (fun y ↦ profile (centeredDilation scale center y)) x =
      scale ^ 2 * laplacian profile (centeredDilation scale center x) := by
  -- Translation commutes with the coordinate derivatives and the dilation scales each by `scale`;
  -- neither step needs any regularity of `profile`.
  have htrans : laplacian (fun y ↦ (fun z ↦ profile (scale • z)) (y - center)) x =
      laplacian (fun z ↦ profile (scale • z)) (x - center) := by
    unfold laplacian
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h1 : (fun y ↦ (∂[i] fun y ↦ profile (scale • (y - center))) y) =
        fun y ↦ (∂[i] fun z ↦ profile (scale • z)) (y - center) :=
      PDE.partialDeriv_comp_sub i (fun z ↦ profile (scale • z)) center
    rw [h1]
    exact congrFun (PDE.partialDeriv_comp_sub i (∂[i] fun z ↦ profile (scale • z)) center) x
  simpa only [centeredDilation, smul_eq_mul] using
    htrans.trans (PDE.laplacian_comp_smul profile scale (x - center))

/-- At fixed time, the spatial Laplacian of `scaledProfileAnsatz` carries one amplitude factor
and two spatial-scale factors. -/
theorem laplacian_scaled_profile_ansatz
    (profile : ℝ^n → ℝ) (amplitudeScale spatialScale : ℝ → ℝ)
    (center x : ℝ^n) (t : ℝ) :
    laplacian
        (fun y ↦ scaledProfileAnsatz profile amplitudeScale spatialScale center y t) x =
      amplitudeScale t * spatialScale t ^ 2 *
        laplacian profile (centeredDilation (spatialScale t) center x) := by
  change
    laplacian
        (fun y ↦ amplitudeScale t *
          profile (centeredDilation (spatialScale t) center y)) x =
      _
  rw [laplacian_const_smul (amplitudeScale t) _ x]
  rw [laplacian_comp_centered_dilation profile (spatialScale t) center x]
  ring

/-- Time differentiation of `scaledProfileAnsatz`.

The second summand is the profile gradient contracted with the velocity of the similarity
coordinate. Fixed-rate and modulated similarity reductions both use this identity. -/
theorem deriv_scaled_profile_ansatz
    (profile : ℝ^n → ℝ) (amplitudeScale spatialScale : ℝ → ℝ)
    (center x : ℝ^n) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile (centeredDilation (spatialScale t) center x))
    (hamplitude : DifferentiableAt ℝ amplitudeScale t)
    (hspatial : DifferentiableAt ℝ spatialScale t) :
    deriv
        (fun s ↦ scaledProfileAnsatz profile amplitudeScale spatialScale center x s) t =
      deriv amplitudeScale t *
          profile (centeredDilation (spatialScale t) center x) +
        amplitudeScale t * deriv spatialScale t *
          ∑ i, (∂[i] profile)
            (centeredDilation (spatialScale t) center x) * (x - center) i := by
  have hinner :=
    hspatial.hasDerivAt.smul_const (x - center)
  have hcomp :=
    hprofile.hasFDerivAt.comp_hasDerivAt t hinner
  have hproduct :=
    hamplitude.hasDerivAt.mul hcomp
  change
    deriv
        (amplitudeScale *
          (profile ∘ fun s ↦ spatialScale s • (x - center))) t =
      _
  rw [hproduct.deriv, fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [Function.comp_apply, centeredDilation]
  simp_rw [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  calc
    (∑ i, amplitudeScale t *
        ((∂[i] profile) (spatialScale t • (x - center)) *
          (deriv spatialScale t * (x - center) i))) =
        ∑ i, (amplitudeScale t * deriv spatialScale t) *
          ((∂[i] profile) (spatialScale t • (x - center)) *
            (x - center) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.mul_sum]

/-- Vector-valued time differentiation of a backward self-similar field produces the
similarity generator. -/
theorem hasDerivAt_backward_self_similar_ansatz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ^n → E) (alpha beta singularTime : ℝ)
    (center x : ℝ^n) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation (backwardPowerScale beta singularTime t) center x))
    (ht : t < singularTime) :
    HasDerivAt
      (fun s ↦
        backwardSelfSimilarAnsatz profile alpha beta singularTime center x s)
      (backwardPowerScale (alpha + 1) singularTime t •
        similarityGenerator alpha beta profile
          (centeredDilation (backwardPowerScale beta singularTime t) center x))
      t := by
  unfold backwardSelfSimilarAnsatz
  apply
    (hasDerivAt_scaled_profile_ansatz profile
      (backwardPowerScale alpha singularTime)
      (backwardPowerScale beta singularTime) center x t
      (alpha * backwardPowerScale (alpha + 1) singularTime t)
      (beta * backwardPowerScale (beta + 1) singularTime t)
      hprofile (hasDerivAt_backward_power_scale ht)
      (hasDerivAt_backward_power_scale ht)).congr_deriv
  have htimeScale :
      backwardPowerScale alpha singularTime t *
          (beta * backwardPowerScale (beta + 1) singularTime t) =
        backwardPowerScale (alpha + 1) singularTime t * beta *
          backwardPowerScale beta singularTime t := by
    calc
      _ = beta *
          (backwardPowerScale alpha singularTime t *
            backwardPowerScale (beta + 1) singularTime t) := by
        ring
      _ = beta * backwardPowerScale (alpha + (beta + 1)) singularTime t := by
        rw [backward_power_scale_mul ht]
      _ = beta * backwardPowerScale ((alpha + 1) + beta) singularTime t := by
        congr 2
        ring
      _ = beta *
          (backwardPowerScale (alpha + 1) singularTime t *
            backwardPowerScale beta singularTime t) := by
        rw [backward_power_scale_mul ht]
      _ = _ := by
        ring
  unfold similarityGenerator
  rw [smul_add]
  simp only [map_smul, smul_smul]
  rw [show
    centeredDilation (backwardPowerScale beta singularTime t) center x =
      backwardPowerScale beta singularTime t • (x - center) by rfl]
  simp only [map_smul, smul_smul]
  rw [htimeScale]
  module

/-- Time differentiation of a scalar backward self-similar field produces the scaling generator.

Parabolic similarity reductions start from this identity. The common factor has exponent
`alpha + 1`; the spatial contribution is rewritten in terms of the similarity coordinate rather
than the original displacement `x - center`. -/
theorem deriv_backward_self_similar_ansatz
    (profile : ℝ^n → ℝ) (alpha beta singularTime : ℝ)
    (center x : ℝ^n) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation (backwardPowerScale beta singularTime t) center x))
    (ht : t < singularTime) :
    deriv
        (fun s ↦
          backwardSelfSimilarAnsatz profile alpha beta singularTime center x s) t =
      backwardPowerScale (alpha + 1) singularTime t *
        scalingGenerator alpha beta profile
          (centeredDilation (backwardPowerScale beta singularTime t) center x) := by
  unfold backwardSelfSimilarAnsatz
  rw [deriv_scaled_profile_ansatz profile
    (backwardPowerScale alpha singularTime)
    (backwardPowerScale beta singularTime) center x t hprofile
    (hasDerivAt_backward_power_scale ht).differentiableAt
    (hasDerivAt_backward_power_scale ht).differentiableAt]
  rw [deriv_backward_power_scale ht, deriv_backward_power_scale ht]
  have htimeScale :
      backwardPowerScale alpha singularTime t *
          (beta * backwardPowerScale (beta + 1) singularTime t) =
        backwardPowerScale (alpha + 1) singularTime t * beta *
          backwardPowerScale beta singularTime t := by
    calc
      _ = beta *
          (backwardPowerScale alpha singularTime t *
            backwardPowerScale (beta + 1) singularTime t) := by
        ring
      _ = beta * backwardPowerScale (alpha + (beta + 1)) singularTime t := by
        rw [backward_power_scale_mul ht]
      _ = beta * backwardPowerScale ((alpha + 1) + beta) singularTime t := by
        congr 2
        ring
      _ = beta *
          (backwardPowerScale (alpha + 1) singularTime t *
            backwardPowerScale beta singularTime t) := by
        rw [backward_power_scale_mul ht]
      _ = _ := by
        ring
  rw [htimeScale]
  unfold scalingGenerator
  simp only [centeredDilation, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add]
  apply congrArg₂ (· + ·)
  · ring
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

end PDE.Representations.Similarity
