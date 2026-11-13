/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.SecondVariation.LocalMinimizer
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import CAS.ExactTactic

/-!
# The Legendre–Hadamard necessary condition

Paired sine and cosine variations cancel the mixed terms in the second variation.
Their sum isolates the density's Hessian on rank-one matrix directions. A smooth
cutoff then localizes the resulting nonnegativity to any interior point.

For a scalar field (`m = 1`) and `a = 1` the conclusion is the condition (14) of Evans, §8.1.3,
which Evans obtains from the second variation (11) with the zig-zag variations (12) instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.3, (11)-(14), pp. 458-459.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise ContDiff

namespace PDE.CalculusOfVariations

open Analysis

private theorem bilinear_sin_cos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) (t : ℝ) :
    H (Real.sin t • a + Real.cos t • b) (Real.sin t • a + Real.cos t • b) +
      H (Real.cos t • a - Real.sin t • b) (Real.cos t • a - Real.sin t • b) =
        H a a + H b b := by
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul]
  generalize H a a = A, H a b = B, H b a = C, H b b = D
  cas

private theorem nonneg_of_const_add_sq_mul_nonneg {A B : ℝ}
    (h : ∀ t : ℝ, 0 ≤ A + t ^ 2 * B) : 0 ≤ B := by
  by_contra hB
  have hBneg : B < 0 := lt_of_not_ge hB
  have hA : 0 ≤ A := by simpa using h 0
  have ht := h (A / (-B) + 1)
  have hdiv : 0 ≤ A / (-B) := div_nonneg hA (neg_nonneg.mpr hBneg.le)
  have hid : A / (-B) * B = -A := by
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hBneg.ne]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (A / (-B))) hBneg.le]

variable {n m : ℕ}

private def variationJet (v : ℝ^n → ℝ^m) (x : ℝ^n) :
    Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) :=
  (jacobianMatrix v x, (v x, 0))

private def rankOneJet (a : ℝ^m) (ξ : ℝ^n →L[ℝ] ℝ) :
    Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) :=
  (Matrix.of (fun k i ↦ ξ (EuclideanSpace.single i 1) * a k), (0, 0))

private theorem jacobianMatrix_smul_const {g : ℝ^n → ℝ} {x : ℝ^n}
    (hg : DifferentiableAt ℝ g x) (a : ℝ^m) :
    jacobianMatrix (fun y ↦ g y • a) x =
      Matrix.of (fun k i ↦ fderiv ℝ g x (EuclideanSpace.single i 1) * a k) := by
  have hd := hg.hasFDerivAt.smul_const a
  ext k i
  rw [jacobianMatrix_apply_eq_fderiv hd.differentiableAt, hd.fderiv]
  simp

private theorem variationJet_mul_profile
    {g : ℝ^n → ℝ} {x : ℝ^n} (hg : DifferentiableAt ℝ g x)
    (a : ℝ^m) (ξ : ℝ^n →L[ℝ] ℝ)
    {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' (ξ x)) :
    variationJet (fun y ↦ (g y * f (ξ y)) • a) x =
      f (ξ x) • variationJet (fun y ↦ g y • a) x +
        (g x * f') • rankOneJet a ξ := by
  have hc := hf.comp_hasFDerivAt x ξ.hasFDerivAt
  have hd := hg.hasFDerivAt.fun_mul hc
  simp only [Function.comp_def] at hd
  apply Prod.ext
  · dsimp [variationJet, rankOneJet]
    rw [jacobianMatrix_smul_const hd.differentiableAt,
      jacobianMatrix_smul_const hg, hd.fderiv]
    ext k i
    simp only [Matrix.of_apply, add_apply, Pi.smul_apply,
      smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.smul_apply]
    ring
  · dsimp [variationJet, rankOneJet]
    simp only [smul_zero, add_zero, smul_smul, mul_comm]

private theorem nonneg_of_integral_sq_mul_nonneg
    {Ω : Set (ℝ^n)} {H : ℝ^n → ℝ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hH : ContinuousOn H (closure Ω))
    (h : ∀ g : ℝ^n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ω →
      0 ≤ ∫ y in Ω, g y ^ 2 * H y) {x : ℝ^n} (hx : x ∈ Ω) :
    0 ≤ H x := by
  by_contra hxH
  have hxneg : H x < 0 := lt_of_not_ge hxH
  have hnbhd : Ω ∩ {y | H y < 0} ∈ nhds x :=
    inter_mem (hopen.mem_nhds hx)
      (((hH.mono subset_closure).continuousAt (hopen.mem_nhds hx)).eventually_lt_const hxneg)
  obtain ⟨g, hgs, hgK, hg, _, hgx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hnbhd
  have hfinite : volume Ω ≠ ⊤ :=
    ne_top_of_le_ne_top hbounded.isCompact_closure.measure_ne_top
      (measure_mono subset_closure)
  have hi : IntegrableOn (fun y ↦ -(g y ^ 2 * H y)) Ω :=
    (hg.continuous.continuousOn.pow 2 |>.mul hH |>.neg).integrableOn_of_subset_isCompact
      hbounded.isCompact_closure hopen.measurableSet subset_closure hfinite
  have hnonneg : 0 ≤ᵐ[volume.restrict Ω] (fun y ↦ -(g y ^ 2 * H y)) := by
    filter_upwards with y
    change 0 ≤ -(g y ^ 2 * H y)
    by_cases hy : g y = 0
    · simp only [hy, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, neg_zero,
        le_refl]
    · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (hgs (subset_tsupport _ (Function.mem_support.mpr hy))).2.le)
  have hsupp : Function.support g ⊆
      Function.support (fun y ↦ -(g y ^ 2 * H y)) ∩ Ω := by
    intro y hy
    have hy' := hgs (subset_tsupport _ hy)
    exact ⟨neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hy) hy'.2.ne), hy'.1⟩
  have hgpos : 0 < volume (Function.support g) :=
    hg.continuous.isOpen_support.measure_pos volume
      ⟨x, by simp only [Function.mem_support, hgx, ne_eq, one_ne_zero, not_false_eq_true]⟩
  have hpos : 0 < ∫ y in Ω, -(g y ^ 2 * H y) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hi).mpr
      (hgpos.trans_le (measure_mono hsupp))
  rw [integral_neg] at hpos
  exact (not_lt_of_ge (h g hg hgK (hgs.trans inter_subset_left))) (neg_pos.mp hpos)

/-- A classical local minimizer has a nonnegative matrix Hessian on every rank-one
direction at every interior point. The local-minimum hypothesis is the same one
used for the first-order Euler–Lagrange condition, with compactly supported smooth
vector variations. No positivity, stationarity, or second-derivative identity is assumed. -/
theorem lagrangian_hessian_rankOne_nonneg_of_isLocalMin
    {Ω : Set (ℝ^n)}
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u : ℝ^n → ℝ^m}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun z : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L z.1 z.2.1 z.2.2)
      {z | z.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u)
    (hmin : ∀ v : ℝ^n → ℝ^m, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Ω → IsLocalMin
        (fun t : ℝ ↦ lagrangianAction Ω L (fun y ↦ u y + t • v y)) 0)
    {x : ℝ^n} (hx : x ∈ Ω) (a : ℝ^m) (ξ : ℝ^n →L[ℝ] ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ
      (fun z : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L z.1 z.2.1 z.2.2))
      (jacobianMatrix u x, (u x, x))
      (Matrix.of (fun k i ↦ ξ (EuclideanSpace.single i 1) * a k), (0, 0))
      (Matrix.of (fun k i ↦ ξ (EuclideanSpace.single i 1) * a k), (0, 0)) := by
  let J := Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n)
  let q (y : ℝ^n) : J := (jacobianMatrix u y, (u y, y))
  let H (y : ℝ^n) := hL.second (q y)
  let R := rankOneJet a ξ
  have hq : Continuous q :=
    (contDiff_jacobianMatrix hu).continuous.prodMk (hu.continuous.prodMk continuous_id)
  have hmap : MapsTo q (closure Ω) (closure {z : J | z.2.2 ∈ Ω}) :=
    (show MapsTo q Ω {z : J | z.2.2 ∈ Ω} from fun _ hy ↦ hy).closure hq
  have hH : ContinuousOn H (closure Ω) :=
    hL.continuousOn_second.comp hq.continuousOn hmap
  have hfinite : volume Ω ≠ ⊤ :=
    ne_top_of_le_ne_top hbounded.isCompact_closure.measure_ne_top
      (measure_mono subset_closure)
  have hi {w : ℝ^n → J} (hw : Continuous w) :
      IntegrableOn (fun y ↦ H y (w y) (w y)) Ω := by
    have hc := (hH.clm_apply hw.continuousOn).clm_apply hw.continuousOn
    exact hc.integrableOn_of_subset_isCompact hbounded.isCompact_closure
      hopen.measurableSet subset_closure hfinite
  have hj {v : ℝ^n → ℝ^m} (hv : ContDiff ℝ 2 v) : Continuous (variationJet v) :=
    (contDiff_jacobianMatrix hv).continuous.prodMk (hv.continuous.prodMk continuous_const)
  have hpos (v : ℝ^n → ℝ^m) (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v)
      (hvs : tsupport v ⊆ Ω) :
      0 ≤ ∫ y in Ω, H y (variationJet v y) (variationJet v y) := by
    have hp := integral_lagrangian_secondVariation_nonneg_of_isLocalMin
      hopen hbounded hL hu (hv.of_le (by simp)) (hmin v hv hvK hvs)
    convert hp using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy
    exact congrArg (fun B ↦ B (variationJet v y) (variationJet v y))
      (hL.second_eq (show q y ∈ {z : J | z.2.2 ∈ Ω} from hy))
  have hR : ContinuousOn (fun y ↦ H y R R) (closure Ω) :=
    (hH.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hpoint : 0 ≤ H x R R := by
    apply nonneg_of_integral_sq_mul_nonneg hopen hbounded hR ?_ hx
    intro g hg hgK hgs
    let v (y : ℝ^n) := g y • a
    have hv : ContDiff ℝ ∞ v := hg.fun_smul contDiff_const
    apply nonneg_of_const_add_sq_mul_nonneg
      (A := ∫ y in Ω, H y (variationJet v y) (variationJet v y))
    intro t
    let vs (y : ℝ^n) := (g y * Real.sin (t * ξ y)) • a
    let vc (y : ℝ^n) := (g y * Real.cos (t * ξ y)) • a
    have hphase : ContDiff ℝ ∞ (fun y ↦ t * ξ y) := contDiff_const.mul ξ.contDiff
    have hvs : ContDiff ℝ ∞ vs :=
      (hg.mul hphase.sin).fun_smul contDiff_const
    have hvc : ContDiff ℝ ∞ vc :=
      (hg.mul hphase.cos).fun_smul contDiff_const
    have hvsK : HasCompactSupport vs := hgK.mul_right.smul_right
    have hvcK : HasCompactSupport vc := hgK.mul_right.smul_right
    have hvsΩ : tsupport vs ⊆ Ω :=
      (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hgs)
    have hvcΩ : tsupport vc ⊆ Ω :=
      (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left.trans hgs)
    have hsum := add_nonneg (hpos vs hvs hvsK hvsΩ) (hpos vc hvc hvcK hvcΩ)
    have heq (y : ℝ^n) :
        H y (variationJet vs y) (variationJet vs y) +
          H y (variationJet vc y) (variationJet vc y) =
        H y (variationJet v y) (variationJet v y) + t ^ 2 * (g y ^ 2 * H y R R) := by
      have hsin : HasDerivAt (fun r : ℝ ↦ Real.sin (t * r))
          (Real.cos (t * ξ y) * t) (ξ y) := by cas
      have hcos : HasDerivAt (fun r : ℝ ↦ Real.cos (t * r))
          (-Real.sin (t * ξ y) * t) (ξ y) := by cas
      have hs : variationJet vs y = Real.sin (t * ξ y) • variationJet v y +
          Real.cos (t * ξ y) • ((t * g y) • R) := by
        rw [show variationJet vs y = _ from
          variationJet_mul_profile (hg.differentiable (by simp) y) a ξ hsin]
        simp only [smul_smul]
        congr 1
        congr 1
        ring
      have hc : variationJet vc y = Real.cos (t * ξ y) • variationJet v y -
          Real.sin (t * ξ y) • ((t * g y) • R) := by
        rw [show variationJet vc y = _ from
          variationJet_mul_profile (hg.differentiable (by simp) y) a ξ hcos]
        rw [sub_eq_add_neg, ← neg_smul]
        simp only [smul_smul]
        congr 1
        congr 1
        ring
      rw [hs, hc, bilinear_sin_cos]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    rw [← integral_add (hi (hj (hvs.of_le (by simp))))
      (hi (hj (hvc.of_le (by simp))))] at hsum
    simp_rw [heq] at hsum
    have hiR : IntegrableOn (fun y ↦ g y ^ 2 * H y R R) Ω :=
      (hg.continuous.continuousOn.pow 2 |>.mul hR).integrableOn_of_subset_isCompact
        hbounded.isCompact_closure hopen.measurableSet subset_closure hfinite
    rwa [integral_add (hi (hj (hv.of_le (by simp)))) (hiR.const_mul _),
      integral_const_mul] at hsum
  change 0 ≤ hL.second (q x) R R at hpoint
  rw [hL.second_eq (show q x ∈ {z : J | z.2.2 ∈ Ω} from hx)] at hpoint
  exact hpoint

end PDE.CalculusOfVariations
