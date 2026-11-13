/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Hausdorff
import PDE.Spaces.Sobolev.Calculus.Slicing.WeakQuadraticFTC
import CAS.ExactTactic

/-!
# Weak H¹ pullback with a positive Jacobian

A real homeomorphism whose inverse is Lipschitz preserves square integrability.
For an increasing C¹ map, substitution in the weak fundamental theorem of
calculus constructs the weak derivative of the pullback. Multiplication by a
bounded C¹ Jacobian then gives the two L² rows of the weighted pullback.

The derivative of the original H¹ function is only an L² class. No classical
derivative of that function is assumed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- The inverse Lipschitz constant bounds distortion of real Lebesgue measure. -/
theorem map_volume_le_of_lipschitz_inverse
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm) :
    Measure.map e volume ≤ (K : ℝ≥0∞) • volume := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply e.continuous.measurable hs, Measure.smul_apply,
    smul_eq_mul]
  have hset : e ⁻¹' s = e.symm '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, e.apply_symm_apply] using hy
  rw [hset]
  simpa only [hausdorffMeasure_real, ENNReal.rpow_one] using
    he.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) s

/-- An inverse Lipschitz bound transports real L² data through the map. -/
theorem memLp_comp_of_lipschitz_inverse
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {v : ℝ → ℝ} (hv : MemLp v 2 volume) :
    MemLp (fun x ↦ v (e x)) 2 volume :=
  (hv.of_measure_le_smul ENNReal.coe_ne_top
    (map_volume_le_of_lipschitz_inverse e he)).comp_of_map e.continuous.aemeasurable

/-- Real L² pullback costs at most the square root of the inverse Lipschitz
constant. -/
theorem norm_toLp_comp_of_lipschitz_inverse
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {v : ℝ → ℝ} (hv : MemLp v 2 volume) :
    ‖(memLp_comp_of_lipschitz_inverse e he hv).toLp (v ∘ e)‖ ≤
      Real.sqrt K * ‖hv.toLp v‖ := by
  have hm := hv.of_measure_le_smul ENNReal.coe_ne_top
    (map_volume_le_of_lipschitz_inverse e he)
  have hle := eLpNorm_le_of_measure_le_smul
    (f := v) (p := 2) (map_volume_le_of_lipschitz_inverse e he)
  rw [eLpNorm_map_measure hm.aestronglyMeasurable e.continuous.aemeasurable] at hle
  have hfinite : (K : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm v 2 volume ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top)
      hv.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hle
  simpa only [Lp.norm_toLp, smul_eq_mul, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.coe_toReal, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow] using hreal

/-- Multiplication by a bounded continuous function preserves `L²`. -/
theorem memLp_mul_of_bounded
    {v m : ℝ → ℝ} {M : ℝ} (hv : MemLp v 2 volume)
    (hm : Continuous m) (hbound : ∀ x, ‖m x‖ ≤ M) :
    MemLp (fun x ↦ v x * m x) 2 volume := by
  apply hv.of_le_mul (c := M) (hv.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  exact .of_forall fun x ↦ by
    change ‖v x * m x‖ ≤ M * ‖v x‖
    rw [norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)

/-- Multiplication by a function bounded by `M` scales the `L²` norm by at most `M`. -/
theorem norm_toLp_mul_of_bounded
    {v m : ℝ → ℝ} {M : ℝ} (hv : MemLp v 2 volume)
    (hm : Continuous m) (hbound : ∀ x, ‖m x‖ ≤ M) :
    ‖(memLp_mul_of_bounded hv hm hbound).toLp (fun x ↦ v x * m x)‖ ≤
      M * ‖hv.toLp v‖ := by
  have hM : 0 ≤ M := (norm_nonneg (m 0)).trans (hbound 0)
  have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (memLp_mul_of_bounded hv hm hbound).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ show ‖v x * m x‖ ≤ M * ‖v x‖ from by
      rw [norm_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)) (2 : ℝ≥0∞)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.eLpNorm_ne_top) hle
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hreal

/-- Substitution in the primitive proves the weak chain rule for an increasing
real homeomorphism. The original derivative only needs to belong to L². -/
theorem hasWeakTimeDerivativeOn_comp_of_positive_jacobian
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {J v g : ℝ → ℝ} {M : ℝ}
    (hJ : Continuous J) (hJpos : ∀ x, 0 ≤ J x)
    (he' : ∀ x, HasDerivAt e (J x) x) (hJbound : ∀ x, ‖J x‖ ≤ M)
    (hv : Continuous v) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ v g) :
    HasWeakTimeDerivativeOn univ (fun x ↦ v (e x)) (fun x ↦ g (e x) * J x) := by
  have hgJ := memLp_mul_of_bounded (memLp_comp_of_lipschitz_inverse e he hg) hJ hJbound
  have hgJloc := hgJ.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : v ∘ e =
      fun x ↦ v (e 0) + ∫ r in 0..x, g (e r) * J r := by
    funext x
    change v (e x) = v (e 0) + ∫ r in 0..x, (g ∘ e) r * J r
    rw [intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      e.continuous.continuousOn (fun y _ ↦ he' y) (fun y _ ↦ hJpos y),
      hweak.intervalIntegral_eq_sub hv]
    cas
  apply HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    (hv.comp e.continuous).locallyIntegrable hgJloc
  · intro a b
    rw [heq]
    exact ((LipschitzWith.const (v (e 0))).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (absolutelyContinuousOnInterval_intervalPrimitive hgJloc 0 a b)
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hgJloc] with x hx
    rw [heq]
    exact (hx 0).const_add (v (e 0))

/-- A bounded C¹ multiplier preserves a continuous weak L² pair, with the
Leibniz derivative constructed from its two original rows. -/
theorem hasWeakTimeDerivativeOn_mul_of_bounded_c1
    {v g m m' : ℝ → ℝ} {M N : ℝ}
    (hv : Continuous v) (hvLp : MemLp v 2 volume) (hg : MemLp g 2 volume)
    (hweak : HasWeakTimeDerivativeOn univ v g)
    (hm : Continuous m) (hm' : Continuous m')
    (hderiv : ∀ x, HasDerivAt m (m' x) x)
    (hmbound : ∀ x, ‖m x‖ ≤ M) (hm'bound : ∀ x, ‖m' x‖ ≤ N) :
    HasWeakTimeDerivativeOn univ (fun x ↦ v x * m x)
      (fun x ↦ g x * m x + v x * m' x) := by
  have hgm := memLp_mul_of_bounded hg hm hmbound
  have hvm' := memLp_mul_of_bounded hvLp hm' hm'bound
  have hmC1 : ContDiff ℝ 1 m := contDiff_one_iff_deriv.mpr
    ⟨fun x ↦ (hderiv x).differentiableAt,
      (funext fun x ↦ (hderiv x).deriv) ▸ hm'⟩
  apply HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    (hv.mul hm).locallyIntegrable
    ((hgm.add hvm').locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  · intro a b
    exact (hweak.absolutelyContinuousOnInterval_of_continuous hv a b).mul
      hmC1.contDiffOn.absolutelyContinuousOnInterval
  · filter_upwards [hweak.ae_hasDerivAt_of_continuous hv] with x hx
    exact hx.mul (hderiv x)

/-- The weighted pullback of an H¹ graph has the exact L² derivative
`g(e(x)) J(x)² + v(e(x)) J'(x)`. Both rows are constructed from the input
graph and the bounds on the coordinate map, which also bound the graph norm. -/
theorem exists_h1_jacobian_weighted_pullback
    (e : ℝ ≃ₜ ℝ) {K : NNReal} (he : LipschitzWith K e.symm)
    {J J' : ℝ → ℝ} {M N : ℝ}
    (hJ : Continuous J) (hJ' : Continuous J')
    (hJpos : ∀ x, 0 ≤ J x)
    (he' : ∀ x, HasDerivAt e (J x) x)
    (hderiv : ∀ x, HasDerivAt J (J' x) x)
    (hJbound : ∀ x, ‖J x‖ ≤ M) (hJ'bound : ∀ x, ‖J' x‖ ≤ N)
    (V : W^{1,2}(ℝ^1)) :
    ∃ W : W^{1,2}(ℝ^1),
      ‖W‖ ≤ Real.sqrt K *
        ((M + N) * ‖realLineCoordinateCLM (baseIndex 1 1) V‖ +
          M * M * ‖realLineCoordinateCLM (singleDerivIndex 1 0) V‖) ∧
      realLineRepresentative W = (fun x ↦ realLineRepresentative V (e x) * J x) ∧
      (realLineCoordinateCLM (singleDerivIndex 1 0) W : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ realLineCoordinateCLM (singleDerivIndex 1 0) V (e x) * J x * J x +
          realLineRepresentative V (e x) * J' x) := by
  let v := realLineRepresentative V
  let g := realLineCoordinateCLM (singleDerivIndex 1 0) V
  have hv := continuous_realLineRepresentative V
  have hvLp := memLp_comp_of_lipschitz_inverse e he (memLp_realLineRepresentative V)
  have hgLp := memLp_comp_of_lipschitz_inverse e he (Lp.memLp g)
  have hgJ := memLp_mul_of_bounded hgLp hJ hJbound
  have hcomp := hasWeakTimeDerivativeOn_comp_of_positive_jacobian e he hJ hJpos he'
    hJbound hv (Lp.memLp g) (hasWeakTimeDerivativeOn_realLineRepresentative V)
  have hprod := hasWeakTimeDerivativeOn_mul_of_bounded_c1 (hv.comp e.continuous)
    hvLp hgJ hcomp hJ hJ' hderiv hJbound hJ'bound
  have hbase := memLp_mul_of_bounded hvLp hJ hJbound
  have hrow := (memLp_mul_of_bounded hgJ hJ hJbound).add
    (memLp_mul_of_bounded hvLp hJ' hJ'bound)
  refine ⟨mkW12OfWeakDerivative hbase hrow hprod, ?_,
    realLineRepresentative_mkW12 hbase hrow hprod ((hv.comp e.continuous).mul hJ), ?_⟩
  · have hM : 0 ≤ M := (norm_nonneg (J 0)).trans (hJbound 0)
    have hN : 0 ≤ N := (norm_nonneg (J' 0)).trans (hJ'bound 0)
    have hvbase : (memLp_realLineRepresentative V).toLp (realLineRepresentative V) =
        realLineCoordinateCLM (baseIndex 1 1) V :=
      Lp.ext ((memLp_realLineRepresentative V).coeFn_toLp.trans
        (realLineCoordinate_ae_representative V).symm)
    have hvnorm := norm_toLp_comp_of_lipschitz_inverse e he (memLp_realLineRepresentative V)
    rw [hvbase] at hvnorm
    have hgnorm := norm_toLp_comp_of_lipschitz_inverse e he (Lp.memLp g)
    rw [Lp.toLp_coeFn] at hgnorm
    have hb := (norm_toLp_mul_of_bounded hvLp hJ hJbound).trans
      (mul_le_mul_of_nonneg_left hvnorm hM)
    have hd := (norm_toLp_mul_of_bounded hgJ hJ hJbound).trans
      (mul_le_mul_of_nonneg_left
        ((norm_toLp_mul_of_bounded hgLp hJ hJbound).trans
          (mul_le_mul_of_nonneg_left hgnorm hM)) hM)
    have hm := (norm_toLp_mul_of_bounded hvLp hJ' hJ'bound).trans
      (mul_le_mul_of_nonneg_left hvnorm hN)
    change ‖realLineH1Jet _ _‖ ≤ _
    apply (norm_realLineH1Jet_le _ _).trans
    rw [MemLp.toLp_add (memLp_mul_of_bounded hgJ hJ hJbound)
      (memLp_mul_of_bounded hvLp hJ' hJ'bound)]
    apply (add_le_add hb ((norm_add_le _ _).trans (add_le_add hd hm))).trans
    apply le_of_eq
    dsimp only [g]
    cas
  · rw [realLineCoordinateCLM_mkW12_single]
    exact hrow.coeFn_toLp

end SobolevSpace.GraphSpace
