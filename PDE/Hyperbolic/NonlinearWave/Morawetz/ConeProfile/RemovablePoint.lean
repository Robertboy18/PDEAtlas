/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Coordinate
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Removing a point from a classical weak derivative

In dimension at least two almost every coordinate line misses the exceptional
point. One-dimensional integration by parts and Fubini therefore identify the
weak derivative from integrability, without any limit at the point.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE SobolevSpace SobolevSpace.Slices

namespace WaveEquation.ConeProfile

variable {n : ℕ}

private theorem hasDerivAt_slice (i : Fin (n + 1)) {f : ℝ^(n + 1) → ℝ}
    (y : ℝ^n) (t : ℝ) (hf : DifferentiableAt ℝ f (joinCoordinate i (y, t))) :
    HasDerivAt (coordinateSlice i f y) ((∂[i] f) (joinCoordinate i (y, t))) t := by
  have hj : HasDerivAt (fun s ↦ joinCoordinate i (y, s))
      (EuclideanSpace.single i 1) t := by
    have h := ((coordinateAxisContinuousLinearMap i).hasDerivAt (x := t)).const_add
      (joinCoordinate i (y, 0))
    have he : coordinateAxisContinuousLinearMap i 1 = EuclideanSpace.single i 1 := by
      ext j
      rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩ <;>
        simp [coordinateAxisContinuousLinearMap]
    simpa only [← joinCoordinate_eq_base_add_axis, he] using h
  exact hf.hasFDerivAt.comp_hasDerivAt t hj

private theorem integrable_mul_test {m : ℕ} {Ω : Set (ℝ^m)} {f ψ : ℝ^m → ℝ}
    (hf : IntegrableOn f Ω) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ω) : Integrable (fun x ↦ f x * ψ x) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right (f := f) (g := ψ)).trans (subset_tsupport ψ))).mp
  exact (hf.mono_set hs).mul_continuousOn hψ.continuousOn hc

/-- An integrable classical derivative off one point is a weak derivative in dimension ≥2. -/
theorem hasWeakDerivativeOn_punctured (hn : 0 < n) {Ω : Set (ℝ^(n + 1))} {c : ℝ^(n + 1)}
    {f : ℝ^(n + 1) → ℝ} (hf : ∀ x ∈ Ω, x ≠ c → DifferentiableAt ℝ f x) (hi : IntegrableOn f Ω)
    (i : Fin (n + 1)) (hdi : IntegrableOn (∂[i] f) Ω) :
    HasWeakDerivativeOn Ω [i] f (∂[i] f) := by
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  refine ⟨hi.locallyIntegrableOn, hdi.locallyIntegrableOn, fun φ hφ ↦ ?_⟩
  have hdφ := (contDiff_top_partialDeriv (i := i) φ.contDiff).continuous
  have hdφc := φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hdφs : tsupport (∂[i] φ.toFun) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (f := φ.toFun) (EuclideanSpace.single i (1 : ℝ))).trans hφ
  let L := fun x ↦ f x * (∂[i] φ.toFun) x
  let R := fun x ↦ (∂[i] f) x * φ x
  let Q := fun x ↦ f x * φ x
  have hL : Integrable L := integrable_mul_test hi hdφ hdφc hdφs
  have hR : Integrable R := integrable_mul_test hdi φ.contDiff.continuous φ.hasCompactSupport hφ
  have hQ : Integrable Q := integrable_mul_test hi φ.contDiff.continuous φ.hasCompactSupport hφ
  have hm : MeasurePreserving (coordinateMeasurableEquiv i).symm
      ((volume : Measure (ℝ^n)).prod volume) volume := by
    simpa only [Measure.volume_eq_prod] using
      (measurePreserving_coordinateMeasurableEquiv i).symm (coordinateMeasurableEquiv i)
  have hLp := hm.integrable_comp_of_integrable hL
  have hRp := hm.integrable_comp_of_integrable hR
  have hQp := hm.integrable_comp_of_integrable hQ
  have hline : ∀ᵐ y : ℝ^n,
      (∫ t, L (joinCoordinate i (y, t))) = -(∫ t, R (joinCoordinate i (y, t))) := by
    filter_upwards [volume.ae_ne (splitCoordinate i c).1,
      hLp.prod_right_ae, hRp.prod_right_ae, hQp.prod_right_ae] with y hy hl hr hq
    have hne (t : ℝ) : joinCoordinate i (y, t) ≠ c := by
      intro he
      apply hy
      have h := congrArg (fun z ↦ (splitCoordinate i z).1) he
      simpa only [split_joinCoordinate] using h
    have hjc : Continuous (fun t ↦ joinCoordinate i (y, t)) :=
      (coordinateContinuousLinearEquiv i).symm.continuous.comp
        (continuous_const.prodMk continuous_id)
    have hdf (t : ℝ) (ht : t ∈ tsupport (coordinateSlice i φ.toFun y)) :
        HasDerivAt (coordinateSlice i f y) ((∂[i] f) (joinCoordinate i (y, t))) t := by
      have hmφ : joinCoordinate i (y, t) ∈ tsupport φ.toFun :=
        tsupport_comp_subset_preimage φ.toFun hjc ht
      exact hasDerivAt_slice i y t (hf _ (hφ hmφ) (hne t))
    have hdg (t : ℝ) (_ : t ∈ tsupport (coordinateSlice i f y)) :
        HasDerivAt (coordinateSlice i φ.toFun y) ((∂[i] φ.toFun) (joinCoordinate i (y, t))) t :=
      hasDerivAt_slice i y t (φ.contDiff.differentiable (by simp) _)
    exact integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      (L := ContinuousLinearMap.mul ℝ ℝ) hdf hdg hl hr hq
  have hglobal : (∫ x, L x) = -(∫ x, R x) := by
    rw [← hm.integral_comp' L, ← hm.integral_comp' R]
    change (∫ x, (L ∘ (coordinateMeasurableEquiv i).symm) x ∂volume.prod volume) =
      -(∫ x, (R ∘ (coordinateMeasurableEquiv i).symm) x ∂volume.prod volume)
    rw [integral_prod _ hLp, integral_prod _ hRp, ← integral_neg]
    exact integral_congr_ae hline
  have hres (q ψ : ℝ^(n + 1) → ℝ) (hs : tsupport ψ ⊆ Ω) :
      (∫ x in Ω, q x * ψ x) = ∫ x, q x * ψ x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), mul_zero]
  simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
    zero_add, pow_one, neg_one_mul] using (hres f (∂[i] φ.toFun) hdφs).trans
      (hglobal.trans (congrArg Neg.neg (hres (∂[i] f) φ.toFun hφ).symm))

end WaveEquation.ConeProfile
