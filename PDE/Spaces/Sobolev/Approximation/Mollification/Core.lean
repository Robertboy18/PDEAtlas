/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct -- shake: keep
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import PDE.Common.Euclidean.CoordinateReflection
import CAS.ExactTactic
import PDE.Analysis.MeasureTheory.Lp.CommonSupportConvergence
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Mollifier kernels and pointwise approximation

A mollifier is a smooth, compactly supported, nonnegative kernel `ρ` on `ℝ^n` of total mass one.
Its dilates `ρ_ε(x) = ε^{-n} ρ(x/ε)` form an approximate identity, and convolution
`ρ_ε ⋆ f` regularizes `f` while moving its support by at most the radius of `supp ρ_ε`.
This is the standard smoothing device behind the approximation theorems for Sobolev functions
(Evans, PDE, §5.3, with the kernel facts collected in Evans' Appendix C.5 on convolution and
smoothing).

We define the `Mollifier` structure, the scaled
kernel `scaled`, and two convolution operators: `mollify` for real-valued functions and
`mollifyVector` for functions valued in a real normed space (used to regularize
Banach-valued trajectories in time). We then prove the kernel facts (mass one, support control,
smoothness), the algebraic identities for mollification, and the pointwise, locally uniform and
`Lᵖ` convergence statements that need only continuity of the input. The passage from continuous
compactly supported inputs to general `Lᵖ` inputs, via the `Lᵖ` contraction bound, is in
`Mollification.LpApproximation`.

## Main results

* `Mollifier`, `standardMollifier`: the kernel data and a canonical instance obtained by
  normalizing Mathlib's explicit radial inner-product bump.
* `scaled_integral_one`, `scaled_contDiff`, `scaled_hasCompactSupport`,
  `support_scaled_subset_closedBall`: the properties of `ρ_ε` (smoothness for every `ε`, the
  others for `ε > 0`).
* `norm_mollify_le_of_ae_bound`: `‖ρ_ε ⋆ f‖ ≤ C` pointwise when `‖f‖ ≤ C` almost everywhere.
* `support_mollify_subset_cthickening`, `support_mollify_subset_of_cthickening_subset`: the support
  of `ρ_ε ⋆ f` lies in a collar of width `εR` around `tsupport f`, so mollification stays inside a
  domain once the collar does.
* `mollify_contDiff_of_pos`, `mollifyVector_contDiff_of_pos`: `ρ_ε ⋆ f` is `C^∞` for locally
  integrable `f`.
* `mollify_tendsto_of_continuous`, `mollifyVector_tendsto_of_continuousAt`,
  `mollifyVector_tendstoLocallyUniformly_of_continuous`: convergence `ρ_{ε_m} ⋆ f → f` at
  continuity points, and locally uniformly for continuous `f`.
* `mollifyVector_converges_Lp_of_continuous_compactSupport`: `Lᵖ` convergence for continuous
  compactly supported `f` and `1 ≤ p < ∞`, by dominated convergence on a fixed compact collar.

## Implementation notes

`scaled μ ε` is defined to be `0` for `ε ≤ 0`, so that `ε` may range over all of `ℝ`. The
kernel lemmas carry the hypothesis `0 < ε`, except `scaled_contDiff`, which holds for every `ε`.
Both `mollify` and `mollifyVector` are Mathlib's `MeasureTheory.convolution` with respect to
Lebesgue measure and the bilinear map `ContinuousLinearMap.lsmul`; for real-valued inputs
`convolution_lsmul_eq_mul` rewrites it with ordinary multiplication.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.5, pp. 713-715, for mollifiers and Theorem 7 on their
  properties, and §5.3, pp. 264-268, for their use in approximation by smooth functions.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Convolution
open scoped Pointwise
open scoped Topology


namespace Approximation

variable {n : ℕ}

/-- A mollifier on `ℝ^n`: a smooth, compactly supported, nonnegative kernel of integral `1`
(Evans §5.3 uses one such kernel, the standard mollifier). -/
structure Mollifier (n : ℕ) where
  /-- The smooth nonnegative kernel, normalized below to have integral one. -/
  ρ : ℝ^n → ℝ
  /-- The kernel is smooth to every finite order. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  /-- The kernel vanishes outside a compact subset of `ℝ^n`. -/
  compactSupport : HasCompactSupport ρ
  /-- The kernel is pointwise nonnegative. -/
  nonneg : ∀ x, 0 ≤ ρ x
  /-- The kernel has total mass one with respect to Lebesgue measure. -/
  integral_one : (∫ x, ρ x) = 1

/-!
## Existence of mollifiers

Most theorems take the mollifier as a parameter. A canonical choice lets later theorems
drop that argument.
Normalizing Mathlib's explicit inner-product bump preserves its radial symmetry.
-/

open scoped RealInnerProductSpace

/-- The explicit inner-product bump of inner radius one and outer radius two, normalized
to have integral one. This choice is radial, hence invariant under every coordinate reflection. -/
noncomputable def standardMollifier (n : ℕ) : Mollifier n := by
  let base := ContDiffBumpBase.ofInnerProductSpace (ℝ^n)
  let b : ℝ^n → ℝ := base.toFun 2
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) b :=
    base.smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      fun _ ↦ ⟨one_lt_two, mem_univ _⟩
  have hb_nonneg : ∀ x, 0 ≤ b x := fun x ↦ (base.mem_Icc 2 x).1
  have hb_support : Function.support b = Metric.ball (0 : ℝ^n) 2 :=
    base.support 2 one_lt_two
  have hb_cs : HasCompactSupport b := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^n) 2)
    rw [hb_support]
    exact Metric.ball_subset_closedBall
  have hb_int : Integrable b := hb_smooth.continuous.integrable_of_hasCompactSupport hb_cs
  have hmass : 0 < ∫ x, b x := by
    rw [integral_pos_iff_support_of_nonneg hb_nonneg hb_int, hb_support]
    exact Metric.measure_ball_pos volume 0 zero_lt_two
  exact
    { ρ := fun x ↦ b x / ∫ y, b y
      smooth := hb_smooth.div_const _
      compactSupport := hb_cs.comp_left (g := fun t : ℝ ↦ t / ∫ y, b y) (by simp)
      nonneg := fun x ↦ div_nonneg (hb_nonneg x) hmass.le
      integral_one := by rw [integral_div, div_self hmass.ne'] }

/-- The standard mollifier depends only on the norm, through the normalized smooth transition. -/
theorem standardMollifier_eq_norm (x : ℝ^n) :
    (standardMollifier n).ρ x =
      Real.smoothTransition (2 - ‖x‖) /
        ∫ y : ℝ^n, Real.smoothTransition (2 - ‖y‖) := by
  norm_num [standardMollifier, ContDiffBumpBase.ofInnerProductSpace]

/-- The inner-product bump depends on the norm through a smooth transition. -/
add_decl_doc ContDiffBumpBase.ofInnerProductSpace.eq_1

/-- The standard kernel is unchanged by reflection in any one coordinate. -/
theorem standardMollifier_even_coordinateReflection (i : Fin n) :
    PDE.Common.IsEvenUnderCoordinateReflection i (standardMollifier n).ρ := by
  intro x
  rw [standardMollifier_eq_norm, standardMollifier_eq_norm,
    PDE.Common.norm_coordinateReflection]

/-- `Mollifier n` is inhabited by `standardMollifier n`, so statements may quantify over a
mollifier without an explicit witness. -/
instance instInhabitedMollifier (n : ℕ) : Inhabited (Mollifier n) :=
  ⟨standardMollifier n⟩

/-- The scaled mollifier `ρ_ε(x) = ε^{-n} ρ(x/ε)` (Evans §5.3), with `ρ_ε = 0` for `ε ≤ 0`. -/
noncomputable def scaled (μ : Mollifier n) (ε : ℝ) : ℝ^n → ℝ :=
  if ε ≤ 0 then 0
  else fun x ↦ (ε⁻¹) ^ n * μ.ρ (ε⁻¹ • x)

/-- For `ε > 0` the scaled kernel is `x ↦ ε^{-n} ρ(x/ε)`; this unfolds the `if` in `scaled`. -/
theorem scaled_of_pos (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    scaled μ ε = fun x ↦ (ε⁻¹) ^ n * μ.ρ (ε⁻¹ • x) := by
  have : ¬ε ≤ 0 := not_le.mpr hε
  simp [scaled, this]

/-- Mollification by convolution: `(ρ_ε * f)(x) = ∫ ρ_ε(y) f(x-y) dy` (Evans §5.3). -/
noncomputable def mollify (μ : Mollifier n) (ε : ℝ) (f : ℝ^n → ℝ) : ℝ^n → ℝ :=
  (scaled μ ε) ⋆ f

/-- For real-valued functions, convolution using scalar multiplication is the same as
convolution using ordinary multiplication. -/
theorem convolution_lsmul_eq_mul (f g : ℝ^n → ℝ) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (ℝ^n))] g) =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ,
        (volume : Measure (ℝ^n))] g) := by
  funext x
  simp only [convolution_lsmul, convolution_mul, smul_eq_mul]

/-- Banach-valued mollification by the same scalar approximate identity.
This is the form needed for time regularization of `V`- and `V*`-valued
evolution trajectories in Evans Chapter 7. -/
noncomputable def mollifyVector {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (μ : Mollifier n) (ε : ℝ) (f : ℝ^n → X) : ℝ^n → X :=
  (scaled μ ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f

/-- The scaled kernel `ρ_ε` is pointwise nonnegative for `ε > 0`. -/
theorem scaled_nonneg (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (x : ℝ^n) : 0 ≤ scaled μ ε x := by
  rw [scaled_of_pos (μ := μ) hε]
  have : 0 ≤ (ε⁻¹ : ℝ) ^ n := by positivity
  exact mul_nonneg this (μ.nonneg _)

/-- For `ε > 0` the scaled kernel `ρ_ε` has compact support, namely the `ε`-dilate of the
support of `ρ`. -/
theorem scaled_hasCompactSupport (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaled μ ε) := by
  classical
  have hnot : ¬ε ≤ 0 := not_le.mpr hε
  have hne : (ε⁻¹ : ℝ) ≠ 0 := inv_ne_zero (ne_of_gt hε)
  have hρ : HasCompactSupport (fun x : ℝ^n ↦ μ.ρ (ε⁻¹ • x)) :=
    μ.compactSupport.comp_smul hne
  have hscale : HasCompactSupport (fun x : ℝ^n ↦ (ε⁻¹ : ℝ) ^ n * μ.ρ (ε⁻¹ • x)) := by
    have hpointwise :
        HasCompactSupport
          ((fun _ : ℝ^n ↦ (ε⁻¹ : ℝ) ^ n) * fun x ↦ μ.ρ (ε⁻¹ • x)) :=
      HasCompactSupport.mul_left
        (f := fun _ : ℝ^n ↦ (ε⁻¹ : ℝ) ^ n)
        (f' := fun x ↦ μ.ρ (ε⁻¹ • x)) hρ
    simpa [Pi.mul_def] using hpointwise
  simpa [scaled, hnot] using hscale

/-- The scaled kernel `ρ_ε` is `C^∞`: for `ε > 0` it is `ρ` composed with a linear dilation and
multiplied by a constant, and for `ε ≤ 0` it is zero. -/
theorem scaled_contDiff (μ : Mollifier n) {ε : ℝ} :
    ContDiff ℝ (⊤ : ℕ∞) (scaled μ ε) := by
  classical
  by_cases hnot : ε ≤ 0
  · rw [scaled, ite_eq_left hnot]
    exact contDiff_const
  have hsmul : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ (ε⁻¹ : ℝ) • x) := by
    rw [show (fun x : ℝ^n ↦ (ε⁻¹ : ℝ) • x) =
      (fun _ : ℝ^n ↦ (ε⁻¹ : ℝ)) • (fun x : ℝ^n ↦ x) by rfl]
    exact
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ^n ↦ (ε⁻¹ : ℝ))).smul
        (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ x))
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ μ.ρ ((ε⁻¹ : ℝ) • x)) :=
    μ.smooth.comp hsmul
  have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ^n ↦ (ε⁻¹ : ℝ) ^ n) :=
    contDiff_const
  have : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ (ε⁻¹ : ℝ) ^ n * μ.ρ ((ε⁻¹ : ℝ) • x)) :=
    hconst.mul hcomp
  simpa [scaled, hnot] using this

/-- `∫ ρ_ε = 1` for `ε > 0`. The substitution `x = ε y` produces the Jacobian `ε^n`, which
cancels the prefactor `ε^{-n}` in the definition of `scaled`; the cancellation is checked by the
CAS. -/
theorem scaled_integral_one (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, scaled μ ε x) = 1 := by
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hne : (ε : ℝ) ≠ 0 := ne_of_gt hε
  have hfinrank : Module.finrank ℝ (ℝ^n) = n := by
    simp
  have hscale :
      (∫ x, μ.ρ (ε⁻¹ • x) ∂ (volume : Measure (ℝ^n))) =
        (ε ^ (Module.finrank ℝ (ℝ^n))) • (∫ x,
          μ.ρ x ∂ (volume : Measure (ℝ^n))) := by
    simpa [volume] using
      (Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (ℝ^n)))
        (f := μ.ρ) (R := ε) hε0)
  calc
    (∫ x, scaled μ ε x) = ∫ x, (ε⁻¹ : ℝ) ^ n * μ.ρ (ε⁻¹ • x) := by
      simp [scaled_of_pos (μ := μ) hε]
    _ = (ε⁻¹ : ℝ) ^ n * (∫ x, μ.ρ (ε⁻¹ • x) ∂ (volume : Measure (ℝ^n))) := by
      simpa using
        (MeasureTheory.integral_const_mul (μ := (volume : Measure (ℝ^n)))
          (r := (ε⁻¹ : ℝ) ^ n) (f := fun x ↦ μ.ρ (ε⁻¹ • x)))
    _ = (ε⁻¹ : ℝ) ^ n * ((ε ^ (Module.finrank ℝ (ℝ^n))) * (∫ x, μ.ρ x)) := by
      simp [hscale, smul_eq_mul]
    _ = (∫ x, μ.ρ x) := by
      rw [hfinrank]
      cas
    _ = 1 := by simpa using μ.integral_one

/-- A positive-scale mollification respects an almost-everywhere uniform bound.
The estimate uses the nonnegative kernel of mass one and translation invariance. -/
theorem norm_mollify_le_of_ae_bound
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ^n → ℝ} {C : ℝ}
    (hC : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) (x : ℝ^n) :
    ‖mollify μ ε f x‖ ≤ C := by
  have hshift : ∀ᵐ y ∂volume, ‖f (x - y)‖ ≤ C :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hC
  have hk : Integrable (scaled μ ε) volume :=
    (scaled_contDiff μ).continuous.integrable_of_hasCompactSupport
      (scaled_hasCompactSupport μ hε)
  have hbound :
      ∀ᵐ y ∂volume, ‖scaled μ ε y * f (x - y)‖ ≤ scaled μ ε y * C := by
    filter_upwards [hshift] with y hy
    rw [norm_mul, Real.norm_of_nonneg (scaled_nonneg μ hε y)]
    exact mul_le_mul_of_nonneg_left hy (scaled_nonneg μ hε y)
  have h := norm_integral_le_of_norm_le (hk.mul_const C) hbound
  simpa only [mollify, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, integral_mul_const, scaled_integral_one μ hε, one_mul] using h

/-- The support of `ρ_ε` scales linearly with `ε`: if `tsupport ρ ⊆ closedBall 0 R`, then
`support ρ_ε ⊆ closedBall 0 (ε R)`. -/
theorem support_scaled_subset_closedBall (μ : Mollifier n) {ε R : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R) :
    Function.support (scaled μ ε) ⊆ Metric.closedBall (0 : ℝ^n) (ε * R) := by
  classical
  intro x hx
  have hne : (ε : ℝ) ≠ 0 := ne_of_gt hε
  have hx0 : scaled μ ε x ≠ 0 := by simpa [Function.support] using hx
  have hxρ : μ.ρ (ε⁻¹ • x) ≠ 0 := by
    have hx0' : (ε⁻¹ : ℝ) ^ n * μ.ρ (ε⁻¹ • x) ≠ 0 := by
      simpa [scaled_of_pos (μ := μ) (ε := ε) hε] using hx0
    exact (mul_ne_zero_iff.mp hx0').2
  have hx_ts : (ε⁻¹ • x) ∈ tsupport μ.ρ :=
    subset_tsupport _ (by simpa [Function.support] using hxρ)
  have hx_ball : (ε⁻¹ • x) ∈ Metric.closedBall (0 : ℝ^n) R := hR hx_ts
  have hx_norm' : ‖ε⁻¹ • x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx_ball
  have hx_norm : ‖x‖ ≤ ε * R := by
    calc
      ‖x‖ = ‖ε • (ε⁻¹ • x)‖ := by
        -- `ε • (ε⁻¹ • x) = x`
        have : ε • (ε⁻¹ • x) = x := by
          simp [smul_smul, mul_inv_cancel₀ hne, one_smul]
        simp [this]
      _ = |ε| * ‖ε⁻¹ • x‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ ≤ |ε| * R := by gcongr
      _ = ε * R := by simp [abs_of_pos hε]
  simpa [Metric.mem_closedBall, dist_zero_right] using hx_norm

/-- Mollification can enlarge the support of `f` only by the support radius of the
scaled mollifier.  This is the support-control statement used in Evans' interior
approximation arguments. -/
theorem support_mollify_subset_closedBall_add_support (μ : Mollifier n)
    {ε R : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (f : ℝ^n → ℝ) :
    Function.support (mollify μ ε f) ⊆
      Metric.closedBall (0 : ℝ^n) (ε * R) + Function.support f := by
  have hconv :
      Function.support (mollify μ ε f) ⊆
        Function.support (scaled μ ε) + Function.support f := by
    simpa [mollify] using
      (MeasureTheory.support_convolution_subset
        (μ := (volume : Measure (ℝ^n)))
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := scaled μ ε) (g := f))
  exact hconv.trans
    (add_subset_add (support_scaled_subset_closedBall μ hε hR) Subset.rfl)

/-- If `ε R < δ`, mollification lies in the closed `δ`-thickening of the original
topological support.  In particular, a compactly supported Sobolev field stays
inside an open domain once the mollifier scale is below its boundary collar. -/
theorem support_mollify_subset_cthickening (μ : Mollifier n)
    {ε R δ : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (hscale : ε * R < δ) (f : ℝ^n → ℝ) :
    Function.support (mollify μ ε f) ⊆ Metric.cthickening δ (tsupport f) := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    support_mollify_subset_closedBall_add_support μ hε hR f hx
  have hy_norm : ‖y‖ ≤ ε * R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  apply Metric.mem_cthickening_of_dist_le (y + z) z δ (tsupport f)
    (subset_tsupport f hz)
  exact le_of_lt (by simpa [dist_eq_norm] using lt_of_le_of_lt hy_norm hscale)

/-- Domain form of support control: a collar around `tsupport f` contained in `Ω`
forces every sufficiently small mollification to be supported in `Ω`. -/
theorem support_mollify_subset_of_cthickening_subset (μ : Mollifier n)
    {ε R δ : ℝ} (hε : 0 < ε)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (hscale : ε * R < δ) {Ω : Set (ℝ^n)} (f : ℝ^n → ℝ)
    (hcollar : Metric.cthickening δ (tsupport f) ⊆ Ω) :
    Function.support (mollify μ ε f) ⊆ Ω :=
  (support_mollify_subset_cthickening μ hε hR hscale f).trans hcollar

/-- For `ε > 0` and locally integrable `f`, the mollification `ρ_ε ⋆ f` is `C^∞`. All derivatives
fall on the smooth compactly supported kernel; this is Mathlib's
`HasCompactSupport.contDiff_convolution_left`. -/
theorem mollify_contDiff_of_pos (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (f : ℝ^n → ℝ) :
    LocallyIntegrable f → ContDiff ℝ (⊤ : ℕ∞) (mollify μ ε f) := by
  intro hf
  have hcs : HasCompactSupport (scaled μ ε) := scaled_hasCompactSupport (μ := μ) hε
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (scaled μ ε) := scaled_contDiff (μ := μ)
  simpa [mollify] using
    (hcs.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) (n := (⊤ : ℕ∞)) hcd hf)

/-- Banach-valued mollification is smooth for positive scale whenever the
trajectory is locally Bochner integrable. -/
theorem mollifyVector_contDiff_of_pos {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (f : ℝ^n → X)
    (hf : LocallyIntegrable f (volume : Measure (ℝ^n))) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyVector μ ε f) := by
  have hcs : HasCompactSupport (scaled μ ε) := scaled_hasCompactSupport μ hε
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (scaled μ ε) := scaled_contDiff μ
  simpa [mollifyVector] using
    (hcs.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) (n := (⊤ : ℕ∞)) hcd hf)

/-- Mollification is additive on locally integrable functions. Local integrability, together with
the continuous compactly supported kernel, guarantees that both convolution integrals exist, which
is what is needed to split the integral of the sum. -/
theorem mollify_add_of_pos (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (f g : ℝ^n → ℝ) :
    LocallyIntegrable f → LocallyIntegrable g →
      mollify μ ε (f + g) = mollify μ ε f + mollify μ ε g := by
  intro hf hg
  have hcs : HasCompactSupport (scaled μ ε) := scaled_hasCompactSupport (μ := μ) hε
  have hcont : Continuous (scaled μ ε) := (scaled_contDiff (μ := μ)).continuous
  have hf_ex :
      MeasureTheory.ConvolutionExists (scaled μ ε) f (ContinuousLinearMap.lsmul ℝ ℝ)
        (MeasureSpace.volume : Measure (ℝ^n)) :=
    hcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (MeasureSpace.volume : Measure (ℝ^n))) hcont hf
  have hg_ex :
      MeasureTheory.ConvolutionExists (scaled μ ε) g (ContinuousLinearMap.lsmul ℝ ℝ)
        (MeasureSpace.volume : Measure (ℝ^n)) :=
    hcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (MeasureSpace.volume : Measure (ℝ^n))) hcont hg
  simpa [mollify] using (hf_ex.distrib_add (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (MeasureSpace.volume : Measure (ℝ^n))) (g' := g) hg_ex)

/-- Mollification commutes with negation. Unlike `mollify_add_of_pos` this needs no integrability
hypothesis, because the Bochner integral is homogeneous even for non-integrable integrands. -/
theorem mollify_neg (μ : Mollifier n) (ε : ℝ) (f : ℝ^n → ℝ) :
    mollify μ ε (-f) = -mollify μ ε f := by
  -- `-f = (-1) • f`, and convolution commutes with scalar multiplication.
  simpa [mollify, Pi.neg_apply] using
    (MeasureTheory.convolution_smul (f := scaled μ ε) (g := f) (y := (-1 : ℝ))
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (MeasureSpace.volume : Measure (ℝ^n))))

/-- Mollification respects subtraction of locally integrable functions. -/
theorem mollify_sub_of_pos (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (f g : ℝ^n → ℝ) :
    LocallyIntegrable f → LocallyIntegrable g →
      mollify μ ε (f - g) = mollify μ ε f - mollify μ ε g := by
  intro hf hg
  simpa [sub_eq_add_neg, mollify_neg] using
    (mollify_add_of_pos (μ := μ) (ε := ε) hε f (-g) hf hg.neg)

/-- Banach-valued mollification is additive on locally integrable inputs. -/
theorem mollifyVector_add_of_pos
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (f g : ℝ^n → X) :
    LocallyIntegrable f → LocallyIntegrable g →
      mollifyVector μ ε (f + g) = mollifyVector μ ε f + mollifyVector μ ε g := by
  intro hf hg
  have hcs : HasCompactSupport (scaled μ ε) := scaled_hasCompactSupport (μ := μ) hε
  have hcont : Continuous (scaled μ ε) := (scaled_contDiff (μ := μ)).continuous
  have hf_ex := hcs.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (MeasureSpace.volume : Measure (ℝ^n))) hcont hf
  have hg_ex := hcs.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (MeasureSpace.volume : Measure (ℝ^n))) hcont hg
  simpa [mollifyVector] using
    (hf_ex.distrib_add (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (MeasureSpace.volume : Measure (ℝ^n))) (g' := g) hg_ex)

/-- Banach-valued mollification commutes with negation. -/
theorem mollifyVector_neg
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (μ : Mollifier n) (ε : ℝ) (f : ℝ^n → X) :
    mollifyVector μ ε (-f) = -mollifyVector μ ε f := by
  simpa [mollifyVector, Pi.neg_apply] using
    (MeasureTheory.convolution_smul (f := scaled μ ε) (g := f) (y := (-1 : ℝ))
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (MeasureSpace.volume : Measure (ℝ^n))))

/-- Banach-valued mollification commutes with subtraction on locally
integrable inputs. For `ε ≤ 0` all three mollifications vanish. -/
theorem mollifyVector_sub_of_pos
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (μ : Mollifier n) {ε : ℝ} (f g : ℝ^n → X) :
    LocallyIntegrable f → LocallyIntegrable g →
      mollifyVector μ ε (f - g) = mollifyVector μ ε f - mollifyVector μ ε g := by
  intro hf hg
  rcases le_or_gt ε 0 with hε | hε
  · simp only [mollifyVector, scaled, ite_eq_left hε, zero_convolution, sub_zero]
  simpa [sub_eq_add_neg, mollifyVector_neg] using
    (mollifyVector_add_of_pos (μ := μ) (ε := ε) hε f (-g) hf hg.neg)

/-!
### Approximate identity: pointwise and `Lᵖ` convergence

The basic property of mollifiers is that `ρ_ε ⋆ f → f` as `ε → 0⁺`, in `Lᵖ(ℝ^n)` for `1 ≤ p < ∞` and
`f ∈ Lᵖ`, and locally uniformly for continuous `f`. Evans App. C.5, Theorem 7(iii)-(iv), states the
second and the `L^p_loc` form of the first. Everything is stated for a sequence `ε_m → 0⁺`.

We treat the continuous inputs first: pointwise convergence at continuity points via
`MeasureTheory.convolution_tendsto_right`, local uniformity, and the `Lᵖ` case for continuous
compactly supported `f` by dominated convergence. The extension to all `f ∈ Lᵖ`, by density of `C_c`
in `Lᵖ` and the contraction bound for convolution with a nonnegative kernel of mass one, is carried
out in `Mollification.LpApproximation`.
-/

/-- Supports of a scaled mollifier shrink to the origin as the positive scale
tends to zero.  This topological approximate-identity fact is independent of
the codomain being regularized. -/
theorem tendsto_support_scaled (μ : Mollifier n)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m ↦ Function.support (scaled μ (ε m))) Filter.atTop
      (𝓝 (0 : ℝ^n)).smallSets := by
  have hKμ : IsCompact (tsupport μ.ρ) := by
    simpa [HasCompactSupport] using μ.compactSupport
  have hBμ : Bornology.IsBounded (tsupport μ.ρ) := hKμ.isBounded
  rcases hBμ.subset_closedBall (0 : ℝ^n) with ⟨R0, hR0⟩
  let R : ℝ := max R0 0
  have hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R := by
    intro y hy
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR0 hy)
  rw [Filter.tendsto_smallSets_iff]
  intro U hU
  rcases Metric.mem_nhds_iff.1 hU with ⟨r, hrpos, hrsub⟩
  have hmul0 : Filter.Tendsto (fun m ↦ ε m * R) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using hε0.mul (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ R) _ _)
  have hevent : ∀ᶠ m in (Filter.atTop : Filter ℕ), ε m * R < r :=
    hmul0.eventually (Iio_mem_nhds hrpos)
  filter_upwards [hevent] with m hm
  have hsupp : Function.support (scaled μ (ε m)) ⊆
      Metric.closedBall (0 : ℝ^n) (ε m * R) :=
    support_scaled_subset_closedBall μ (hεpos m) hR
  have hball : Metric.closedBall (0 : ℝ^n) (ε m * R) ⊆
      Metric.ball (0 : ℝ^n) r := by
    intro y hy
    have hylt : dist y 0 < r := lt_of_le_of_lt (by
      simpa [Metric.mem_closedBall] using hy) hm
    simpa [Metric.mem_ball] using hylt
  exact (hsupp.trans hball).trans hrsub

/-- Mollification converges pointwise at every continuity point.  Only local
integrability is needed because every scaled mollifier has compact support.
This is the approximate-identity input used both by the `L^p` convergence
theorem below and by weak fundamental-theorem-of-calculus arguments. -/
theorem mollify_tendsto_of_continuous (μ : Mollifier n)
    {f : ℝ^n → ℝ} (hf_cont : Continuous f)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) (x : ℝ^n) :
    Filter.Tendsto (fun m ↦ mollify μ (ε m) f x)
      Filter.atTop (𝓝 (f x)) := by
  simpa [mollify, MeasureTheory.convolution] using MeasureTheory.convolution_tendsto_right
    (μ := volume) (g := fun _m ↦ f) (φ := fun m ↦ scaled μ (ε m)) (k := fun _m ↦ x)
    (.of_forall fun m y ↦ scaled_nonneg μ (hεpos m) y)
    (.of_forall fun m ↦ scaled_integral_one μ (hεpos m)) (tendsto_support_scaled μ ε hεpos hε0)
    (.of_forall fun _ ↦ hf_cont.aestronglyMeasurable) ((hf_cont.tendsto x).comp Filter.tendsto_snd)
    tendsto_const_nhds

/-- Banach-valued mollification converges at a point of continuity.  Only
local integrability is imposed away from that point. -/
theorem mollifyVector_tendsto_of_continuousAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (μ : Mollifier n) {f : ℝ^n → X}
    (hf_loc : MeasureTheory.LocallyIntegrable f
      (volume : Measure (ℝ^n)))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) {x : ℝ^n}
    (hf : ContinuousAt f x) :
    Filter.Tendsto (fun m ↦ mollifyVector μ (ε m) f x)
      Filter.atTop (𝓝 (f x)) := by
  simpa [mollifyVector, MeasureTheory.convolution] using MeasureTheory.convolution_tendsto_right
    (μ := volume) (g := fun _m ↦ f) (φ := fun m ↦ scaled μ (ε m)) (k := fun _m ↦ x)
    (.of_forall fun m y ↦ scaled_nonneg μ (hεpos m) y)
    (.of_forall fun m ↦ scaled_integral_one μ (hεpos m)) (tendsto_support_scaled μ ε hεpos hε0)
    (.of_forall fun _ ↦ hf_loc.aestronglyMeasurable) (hf.tendsto.comp Filter.tendsto_snd)
    tendsto_const_nhds

/-- Banach-valued mollifications of a continuous function converge at every point. -/
theorem mollifyVector_tendsto_of_continuous
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (μ : Mollifier n) {f : ℝ^n → X} (hf : Continuous f)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) (x : ℝ^n) :
    Filter.Tendsto (fun m ↦ mollifyVector μ (ε m) f x)
      Filter.atTop (𝓝 (f x)) :=
  mollifyVector_tendsto_of_continuousAt μ
    hf.locallyIntegrable ε hεpos hε0 hf.continuousAt

/-- Positive-scale mollification converges locally uniformly to every
continuous Banach-valued function.  The proof applies the approximate
identity theorem jointly to the scale and spatial variables. -/
theorem mollifyVector_tendstoLocallyUniformly_of_continuous
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (μ : Mollifier n) {f : ℝ^n → X} (hf : Continuous f)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
    TendstoLocallyUniformly
      (fun m ↦ mollifyVector μ (ε m) f) f Filter.atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro δ hδ x
  have hmoll : Filter.Tendsto (fun p : ℕ × ℝ^n ↦ mollifyVector μ (ε p.1) f p.2)
      (Filter.atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
    simpa [mollifyVector, MeasureTheory.convolution] using MeasureTheory.convolution_tendsto_right
      (μ := volume) (g := fun _p : ℕ × ℝ^n ↦ f) (φ := fun p ↦ scaled μ (ε p.1)) (k := Prod.snd)
      (.of_forall fun p y ↦ scaled_nonneg μ (hεpos p.1) y)
      (.of_forall fun p ↦ scaled_integral_one μ (hεpos p.1))
      ((tendsto_support_scaled μ ε hεpos hε0).comp Filter.tendsto_fst)
      (.of_forall fun _ ↦ hf.aestronglyMeasurable) ((hf.tendsto x).comp Filter.tendsto_snd)
      Filter.tendsto_snd
  have hdist : Filter.Tendsto (fun p : ℕ × ℝ^n ↦ dist (f p.2) (mollifyVector μ (ε p.1) f p.2))
      (Filter.atTop ×ˢ 𝓝 x) (𝓝 0) := by
    simpa using ((hf.tendsto x).comp Filter.tendsto_snd).dist hmoll
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.eventually_prod_iff.mp (hdist.eventually (Iio_mem_nhds hδ))
  exact ⟨{y | t y}, ht, hs.mono fun m hm y hy ↦ hst hm hy⟩

/-- The `Lᵖ` approximate-identity property for continuous compactly supported Banach-valued
`f` and `1 ≤ p < ∞`: `‖ρ_{ε_m} ⋆ f - f‖_{Lᵖ} → 0` whenever `ε_m → 0⁺`.

For `ε_m ≤ 1` both `ρ_{ε_m} ⋆ f` and `f` vanish outside the fixed compact set
`closedBall 0 R + tsupport f`, on which the convergence is uniform
(`mollifyVector_tendstoLocallyUniformly_of_continuous`); uniform convergence on a common set of
finite measure gives convergence in `Lᵖ`, so the proof does not use `1 ≤ p`. The `[Fact (1 ≤ p)]`
assumption is retained for compatibility with the existing public signature. -/
@[nolint unusedArguments]
theorem mollifyVector_converges_Lp_of_continuous_compactSupport
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    [CompleteSpace X]
    (μ : Mollifier n) (p : ℝ≥0∞) (hp : p ≠ ∞)
    {f : ℝ^n → X} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0)) :
      Filter.Tendsto
        (fun m ↦
          eLpNorm (fun x ↦ mollifyVector μ (ε m) f x - f x) p volume)
        Filter.atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := μ.compactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  have hK := (isCompact_closedBall (0 : ℝ^n) R).add hf_cs
  have hsupp : ∀ᶠ m in Filter.atTop, Function.support (mollifyVector μ (ε m) f) ⊆
      Metric.closedBall 0 R + tsupport f := by
    filter_upwards [hε0.eventually (Iic_mem_nhds zero_lt_one)] with m hm
    have hconv : Function.support (mollifyVector μ (ε m) f) ⊆
        Function.support (scaled μ (ε m)) + Function.support f := by
      simpa [mollifyVector] using support_convolution_subset (μ := volume)
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := scaled μ (ε m)) (g := f)
    exact hconv.trans (add_subset_add ((support_scaled_subset_closedBall μ (hεpos m) hR).trans
      (Metric.closedBall_subset_closedBall (mul_le_of_le_one_left hR0.le hm))) (subset_tsupport f))
  exact tendsto_eLpNorm_sub_of_tendstoUniformlyOn hp hK.measurableSet.nullMeasurableSet
    hK.measure_ne_top (Filter.Eventually.of_forall fun m ↦
      ((mollifyVector_contDiff_of_pos μ (hεpos m) f hf_cont.locallyIntegrable).continuous.sub
        hf_cont).aestronglyMeasurable) hsupp
    ((subset_tsupport f).trans fun y hy ↦ ⟨0, Metric.mem_closedBall_self hR0.le, y, hy, zero_add y⟩)
    (tendstoLocallyUniformly_iff_forall_isCompact.1
      (mollifyVector_tendstoLocallyUniformly_of_continuous μ hf_cont ε hεpos hε0) _ hK)

end Approximation

end SobolevSpace
