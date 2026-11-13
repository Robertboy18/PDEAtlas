/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower.Deriv
public import PDE.Hyperbolic.Models.Wave.Operator
import PDE.Analysis.Calculus.LocalExtension.ForwardBand
import PDE.FDeriv.SpaceTime
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Regular zeros obstruct all-orders smoothness of the quadratic power wave

The equation itself forces its reaction term to inherit two spatial derivatives from a C⁴ solution.
The signed quadratic power cannot have this regularity at a regular zero. A compact smooth datum
equal to the first coordinate near the origin gives both an initial-face obstruction and a
positive-time obstruction. The latter requires only a joint C¹ trace at the initial face: the
implicit function theorem preserves a regular zero into positive time.

The obstruction concerns all-orders smoothness of the quadratic power wave. For `p = 2` the reaction
is not smooth, so the standing hypothesis of Evans, §12.3.2, fails, and the smooth solution
of Theorem 3 of §12.3.3 need not exist. The positive-time obstruction takes the joint C¹ trace as a
hypothesis. Neither obstruction excludes a C² solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, standing hypotheses; §12.3.3, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Metric PDE PDE.Common PDE.Analysis WaveEquation
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A regular zero of a twice differentiable scalar profile prevents its signed
quadratic power from being C². The local inverse transfers any alleged C²
regularity to the scalar reaction at zero. -/
theorem not_contDiffAt_signedPower_two_comp {f : ℝ → ℝ} {a d : ℝ} (hf : ContDiffAt ℝ 2 f a)
    (hd : HasDerivAt f d a) (hd0 : d ≠ 0) (hzero : f a = 0) :
    ¬ ContDiffAt ℝ 2 (fun r ↦ Real.signedPower 2 (f r)) a := by
  intro hcomp
  have hfd := hd.hasFDerivAt_equiv hd0
  let v := hf.localInverse hfd (by norm_num)
  have hv : ContDiffAt ℝ 2 v (f a) := hf.to_localInverse hfd (by norm_num)
  have hva : v (f a) = a := hf.localInverse_apply_image hfd (by norm_num)
  have hright : ∀ᶠ y in 𝓝 (f a), f (v y) = y :=
    (hf.hasStrictFDerivAt' hfd (by norm_num)).eventually_right_inverse
  have hh : ContDiffAt ℝ 2 (fun y ↦ Real.signedPower 2 (f (v y))) (f a) :=
    (hva.symm ▸ hcomp).comp (f a) hv
  have hc : ContDiffAt ℝ 2 (Real.signedPower 2) (f a) :=
    hh.congr_of_eventuallyEq (hright.mono fun y hy ↦ congrArg (Real.signedPower 2) hy.symm)
  exact Real.not_contDiffAt_two_signedPower_two (hzero ▸ hc)

/-- There are compact smooth initial data with a regular zero, equal to the
first spatial coordinate on the unit ball. -/
theorem exists_compact_smooth_coordinate_datum :
    ∃ g : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      EqOn g (fun x ↦ x 0) (closedBall 0 1) := by
  let χ : ContDiffBump (0 : ℝ^3) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨fun x ↦ χ x * x 0, χ.contDiff.mul (EuclideanSpace.proj 0 : ℝ^3 →L[ℝ] ℝ).contDiff,
    χ.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  change χ x * x 0 = x 0
  rw [χ.one_of_mem_closedBall hx, one_mul]

/-- No ambient C⁴ solution with coordinate data near zero can solve the
quadratic power PDE at positive times. Continuity extends the residual to the
initial slice, where it would make the signed quadratic power C². -/
theorem not_contDiff_four_quadratic_wave_of_coordinate_datum {g : ℝ^3 → ℝ}
    (hg : EqOn g (fun x ↦ x 0) (closedBall 0 1)) {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiff ℝ 4 u) (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) +
      Real.signedPower 2 (u (timeSpaceCons t x)) = 0) :
    False := by
  have hsecond (i : Fin 4) : ContDiff ℝ 2 (∂[i] (∂[i] u)) := contDiff_partialDeriv_of_succ (m := 2)
      (contDiff_partialDeriv_of_succ (m := 3) hu)
  have hf : ContDiff ℝ 2 (waveOperator u) := (hsecond 0).sub (ContDiff.sum fun i _ ↦ hsecond i.succ)
  have hz (x : ℝ^3) : waveOperator u (timeSpaceCons 0 x) + Real.signedPower 2 (g x) = 0 := by
    have hc : Continuous (fun t ↦ waveOperator u (timeSpaceCons t x) +
        Real.signedPower 2 (u (timeSpaceCons t x))) := (hf.continuous.add
        ((Real.contDiff_one_signedPower (by norm_num : (1 : ℝ) ≤ 2)).continuous.comp
          hu.continuous)).comp ((contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous.comp
          (continuous_id.prodMk continuous_const))
    have he : EqOn (fun t ↦ waveOperator u (timeSpaceCons t x) +
        Real.signedPower 2 (u (timeSpaceCons t x))) (fun _ ↦ 0) (Ioo 0 T) := fun t ht ↦ hwave t ht x
    have he0 := he.closure hc continuous_const
    rw [closure_Ioo hT.ne] at he0
    simpa only [hposition] using he0 (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
  let e : ℝ^3 := EuclideanSpace.single 0 1
  let c (r : ℝ) := timeSpaceCons 0 (r • e)
  have hcs : ContDiff ℝ 2 c := (contDiff_timeSpaceCons_spatial 3 0 (m := 2)).comp
    (contDiff_id.smul contDiff_const)
  have heq : (fun r ↦ -(waveOperator u (c r))) =ᶠ[𝓝 0] Real.signedPower 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with r hr
    have hnorm : ‖r • e‖ ≤ 1 := by
      have hr' : |r| < 1 := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hr
      simpa [e, norm_smul, PiLp.norm_single, Real.norm_eq_abs] using hr'.le
    have hgx : g (r • e) = r := by
      simpa [e] using hg (mem_closedBall_zero_iff.mpr hnorm)
    have hh := hz (r • e)
    rw [hgx] at hh
    exact (eq_neg_of_add_eq_zero_right hh).symm
  exact Real.not_contDiffAt_two_signedPower_two
    (((hf.comp hcs).neg.contDiffAt).congr_of_eventuallyEq heq.symm)

private theorem exists_positive_regular_zero {F : ℝ × ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hF : ContDiffAt ℝ 1 F (0, 0)) (hzero : (fun r ↦ F (0, r)) =ᶠ[𝓝 0] id) :
    ∃ t ∈ Ioo 0 T, ∃ r d : ℝ, F (t, r) = 0 ∧ HasDerivAt (fun s ↦ F (t, s)) d r ∧ d ≠ 0 := by
  have hdf := hF.hasStrictFDerivAt (by norm_num)
  have hcomp : fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.id ℝ ℝ := by
    have hd := hdf.hasFDerivAt.comp 0 (hasFDerivAt_prodMk_right (𝕜 := ℝ) 0 0)
    have hi := (hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
    exact hd.unique hi
  have hinv : (fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  let ψ := hdf.implicitFunctionOfProdDomain hinv
  have hψ : Tendsto ψ (𝓝 0) (𝓝 0) := hdf.tendsto_implicitFunctionOfProdDomain hinv
  have hgraph : Tendsto (fun t ↦ (t, ψ t)) (𝓝 0) (𝓝 (0, 0)) := tendsto_id.prodMk_nhds hψ
  have hroot : ∀ᶠ t in 𝓝 0, F (t, ψ t) = 0 := by
    simpa only [hzero.eq_of_nhds, id_eq, ψ] using
      hdf.eventually_apply_implicitFunctionOfProdDomain hinv
  let D (q : ℝ × ℝ) := fderiv ℝ F q (0, 1)
  have hD : ContinuousAt D (0, 0) :=
    (hF.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hD0 : D (0, 0) = 1 := by
    have hh := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hcomp
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.id_apply] using hh
  have hdne : ∀ᶠ t in 𝓝 0, D (t, ψ t) ≠ 0 :=
    hgraph.eventually (hD.eventually_ne (hD0 ▸ one_ne_zero))
  have hreg : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ 1 F (t, ψ t) :=
    hgraph.eventually (hF.eventually (by norm_num))
  have hall : ∀ᶠ t in 𝓝[>] 0, t < T ∧ F (t, ψ t) = 0 ∧ D (t, ψ t) ≠ 0 ∧ ContDiffAt ℝ 1 F (t, ψ t) :=
    mem_nhdsWithin_of_mem_nhds (inter_mem (Iio_mem_nhds hT) (hroot.and (hdne.and hreg)))
  obtain ⟨t, ⟨htT, hrt, hdt, hFt⟩, ht⟩ := (hall.and self_mem_nhdsWithin).exists
  refine ⟨t, ⟨ht, htT⟩, ψ t, D (t, ψ t), hrt, ?_, hdt⟩
  exact (hFt.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt _
    ((hasDerivAt_const (ψ t) t).prodMk (hasDerivAt_id (ψ t)))

/-- C⁴ regularity at positive times is already impossible for the quadratic
power wave with coordinate data near the origin and a C¹ forward initial
trace. The implicit function theorem preserves a regular zero into positive time. -/
theorem not_contDiffOn_four_quadratic_wave_of_coordinate_datum {g : ℝ^3 → ℝ}
    (hg : EqOn g (fun x ↦ x 0) (closedBall 0 1)) {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 1 u {z | 0 ≤ z 0 ∧ z 0 < T}) (hu4 : ContDiffOn ℝ 4 u {z | 0 < z 0 ∧ z 0 < T})
    (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) +
      Real.signedPower 2 (u (timeSpaceCons t x)) = 0) :
    False := by
  obtain ⟨v, hv, heq⟩ := exists_contDiffOn_extension_halfOpenBand 0 hT hu
  let e : ℝ^3 := EuclideanSpace.single 0 1
  let c (q : ℝ × ℝ) := timeSpaceCons q.1 (q.2 • e)
  have hc : ContDiff ℝ 4 c := (contDiff_timeSpaceCons_uncurry 3 (m := 4)).comp
    (contDiff_fst.prodMk (contDiff_snd.smul contDiff_const))
  let F (q : ℝ × ℝ) := v (c q)
  have hF : ContDiffAt ℝ 1 F (0, 0) :=
    (hv.contDiffAt ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds
      (by change 0 < T; exact hT))).comp (0, 0)
        (hc.of_le (by norm_num)).contDiffAt
  have hFzero : (fun r ↦ F (0, r)) =ᶠ[𝓝 0] id := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with r hr
    have hnorm : ‖r • e‖ ≤ 1 := by
      have hr' : |r| < 1 := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hr
      simpa [e, norm_smul, PiLp.norm_single, Real.norm_eq_abs] using hr'.le
    change v (timeSpaceCons 0 (r • e)) = r
    rw [heq (by simp only [mem_ofPred_eq, timeSpaceCons_zero, le_refl]), hposition]
    simpa [e] using hg (mem_closedBall_zero_iff.mpr hnorm)
  obtain ⟨t, ht, r, d, hroot, hd, hd0⟩ := exists_positive_regular_zero hT hF hFzero
  have hopen : IsOpen {z : ℝ^4 | 0 < z 0 ∧ z 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hmem : c (t, r) ∈ {z : ℝ^4 | 0 < z 0 ∧ z 0 < T} := by
    simpa only [mem_ofPred_eq, c, timeSpaceCons_zero, mem_Ioo] using ht
  have huc : ContDiffAt ℝ 4 u (c (t, r)) := hu4.contDiffAt (hopen.mem_nhds hmem)
  have hcurve : ContDiffAt ℝ 4 (fun s ↦ c (t, s)) r :=
    hc.contDiffAt.comp r (contDiffAt_const.prodMk contDiffAt_id)
  have hvu : v =ᶠ[𝓝 (c (t, r))] u := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact heq hz.1.le
  have hline : (fun s ↦ F (t, s)) =ᶠ[𝓝 r] (fun s ↦ u (c (t, s))) :=
    hvu.comp_tendsto hcurve.continuousAt
  have hvc : ContDiffAt ℝ 2 (fun s ↦ F (t, s)) r :=
    ((huc.comp r hcurve).of_le (by norm_num)).congr_of_eventuallyEq hline
  have hsecond (i : Fin 4) : ContDiffAt ℝ 2 (∂[i] (∂[i] u)) (c (t, r)) :=
    contDiffAt_partialDeriv 2 (contDiffAt_partialDeriv 3 huc i) i
  have hwc : ContDiffAt ℝ 2 (waveOperator u) (c (t, r)) :=
    (hsecond 0).sub (ContDiffAt.sum fun i _ ↦ hsecond i.succ)
  have hpde : (fun z ↦ Real.signedPower 2 (u z)) =ᶠ[𝓝 (c (t, r))]
      (fun z ↦ -(waveOperator u z)) := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have h := hwave (z 0) hz (spatialPart z)
    simpa only [timeSpaceCons_spatialPart] using eq_neg_of_add_eq_zero_right h
  have hrc : ContDiffAt ℝ 2 (fun z ↦ Real.signedPower 2 (u z)) (c (t, r)) :=
    hwc.neg.congr_of_eventuallyEq hpde
  have hucp : ContDiffAt ℝ 2 (fun s ↦ Real.signedPower 2 (u (c (t, s)))) r :=
    hrc.comp r (hcurve.of_le (by norm_num))
  have hcomp : ContDiffAt ℝ 2 (fun s ↦ Real.signedPower 2 (F (t, s))) r :=
    hucp.congr_of_eventuallyEq (hline.mono fun s hs ↦ congrArg (Real.signedPower 2) hs)
  exact not_contDiffAt_signedPower_two_comp hvc hd hd0 hroot hcomp

/-- Some smooth compact Cauchy data admit no solution that is C⁴ at positive
times and C¹ up to the initial face. This rules out an all-orders interpretation
of the quadratic member of the subcritical power family in this source class. -/
theorem exists_compact_smooth_data_no_positive_smooth_quadratic_wave :
    ∃ g : ℝ^3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ (T : ℝ) (u : ℝ^4 → ℝ), 0 < T →
        ContDiffOn ℝ 1 u {z | 0 ≤ z 0 ∧ z 0 < T} →
        ContDiffOn ℝ 4 u {z | 0 < z 0 ∧ z 0 < T} →
        (∀ x, u (timeSpaceCons 0 x) = g x) →
        (∀ t ∈ Ioo 0 T, ∀ x,
          waveOperator u (timeSpaceCons t x) + Real.signedPower 2 (u (timeSpaceCons t x)) = 0) →
        False := by
  obtain ⟨g, hg, hgs, hcoord⟩ := exists_compact_smooth_coordinate_datum
  exact ⟨g, hg, hgs, fun _ _ hT hu hu4 hpos hw ↦
    not_contDiffOn_four_quadratic_wave_of_coordinate_datum hcoord hT hu hu4 hpos hw⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
