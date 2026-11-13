/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PlanarMixedFTC
public import PDE.Spaces.Sobolev.Weighted.Parity
import PDE.Spaces.Sobolev.Weighted.Reflection
public import PDE.FDeriv.Calculus
public import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.QuantitativeCutoff
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Polynomial decay from a weighted derivative hierarchy

Write `S = 1 + r² + z²`. For every natural `p ≥ 1`, the mixed derivative of
`S^p u²` is controlled by three successive integrals: `S^(p-1) u²`,
`S^p |∇u|²`, and `S^(p+1) u_rz²`. Compact cutoffs let the planar fundamental
theorem use precisely these levels. The cutoff is already one at the
observation point, so no pointwise limit at infinity is an input.

The cutoff derivative constants come from the fixed bump `standardBump` and
are independent of the field, exponent, and observation point. For a field
with reflection parity, each square density is even. The physical half-space
integrals then give the same pointwise estimate with a factor of two.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace.Slices
open SobolevSpace.Approximation

namespace PDE.Analysis

local notation "S" => (fun x : ℝ^2 ↦ 1 + x 0 ^ 2 + x 1 ^ 2)

private def planeChart : (ℝ × ℝ) →L[ℝ] ℝ^2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single 0 1) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single 1 1)

private theorem planeChart_eq (p : ℝ × ℝ) :
    planeChart p = PDE.Analysis.planeEquiv.symm p := by
  rw [PDE.Analysis.planeEquiv_symm_apply_eq_add]
  ext i
  fin_cases i <;> simp [planeChart]

private theorem planeChart_first :
    planeChart (1, 0) = EuclideanSpace.single 0 1 := by
  simp [planeChart]

private theorem planeChart_second :
    planeChart (0, 1) = EuclideanSpace.single 1 1 := by
  simp [planeChart]

private theorem fderiv_planeChart_first
    {f : ℝ^2 → ℝ} (hf : Differentiable ℝ f) (p : ℝ × ℝ) :
    fderiv ℝ (f ∘ planeChart) p (1, 0) = (∂[0] f) (planeChart p) := by
  rw [fderiv_comp p (hf _) planeChart.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    planeChart_first, partialDeriv]

private theorem fderiv_planeChart_second
    {f : ℝ^2 → ℝ} (hf : Differentiable ℝ f) (p : ℝ × ℝ) :
    fderiv ℝ (f ∘ planeChart) p (0, 1) = (∂[1] f) (planeChart p) := by
  rw [fderiv_comp p (hf _) planeChart.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    planeChart_second, partialDeriv]

/-- Transfer the compact mixed-FTC estimate to the Euclidean partials.
The canonical chart preserves Lebesgue measure. -/
private theorem norm_le_integral_abs_mixedPartialDeriv
    {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f) (x : ℝ^2) :
    |f x| ≤ ∫ y, |(∂[0] (∂[1] f)) y| := by
  let g : ℝ × ℝ → ℝ := f ∘ planeChart
  have hg : ContDiff ℝ 2 g := hf.comp planeChart.contDiff
  have hgCompact : HasCompactSupport g := by
    have hcoords : Continuous (fun y : ℝ^2 ↦ (y 0, y 1)) := by fun_prop
    apply HasCompactSupport.of_support_subset_isCompact
      (hcompact.isCompact.image hcoords)
    intro p hp
    refine ⟨planeChart p, subset_tsupport f hp, ?_⟩
    simpa only [PDE.Analysis.planeEquiv_apply, planeChart_eq] using
      PDE.Analysis.planeEquiv.apply_symm_apply p
  have hfirst :
      (fun p ↦ fderiv ℝ g p (1, 0)) = (∂[0] f) ∘ planeChart :=
    funext (fderiv_planeChart_first (hf.differentiable (by norm_num)))
  have hR : ContDiff ℝ 1 (∂[0] f) := contDiff_partialDeriv_of_succ (m := 1) hf
  have hsecond (p : ℝ × ℝ) :
      fderiv ℝ (fun q ↦ fderiv ℝ g q (1, 0)) p (0, 1) =
        (∂[0] (∂[1] f)) (planeChart p) := by
    rw [hfirst, fderiv_planeChart_second hR.differentiable_one]
    exact partialDeriv_partialDeriv_comm 1 0 hf _
  have h := norm_le_integral_norm_mixed_fderiv hg hgCompact
    (PDE.Analysis.planeEquiv x)
  simp only [hsecond, Real.norm_eq_abs] at h
  have hchange :
      (∫ p : ℝ × ℝ, |(∂[0] (∂[1] f)) (planeChart p)|) = ∫ y, |(∂[0] (∂[1] f)) y| := by
    simpa only [planeChart_eq] using!
      (PDE.Analysis.measurePreserving_planeEquiv.symm
      PDE.Analysis.planeEquiv).integral_comp
        PDE.Analysis.planeEquiv.symm.measurableEmbedding (fun y : ℝ^2 ↦ |(∂[0] (∂[1] f)) y|)
  rw [hchange] at h
  simpa only [g, Function.comp_apply, planeChart_eq,
    MeasurableEquiv.symm_apply_apply] using h

private theorem mixed_product_row
    (f g : ℝ^2 → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ^2) :
    (∂[0] (∂[1] (fun y ↦ f y * g y))) x =
      f x * (∂[0] (∂[1] g)) x + (∂[0] f) x * (∂[1] g) x +
        (∂[1] f) x * (∂[0] g) x + (∂[0] (∂[1] f)) x * g x := by
  have h := iterate_partialDeriv_iterate_partialDeriv_mul
    (0 : Fin 2) 1 1 1 f g hf hg x
  norm_num [Finset.sum_range_succ, Function.iterate_succ_apply] at h
  nlinarith only [h]

private theorem mixed_square
    (u : ℝ^2 → ℝ) (hu : ContDiff ℝ 2 u) (x : ℝ^2) :
    (∂[0] (∂[1] (fun y ↦ u y ^ 2))) x =
      2 * u x * (∂[0] (∂[1] u)) x + 2 * (∂[0] u) x * (∂[1] u) x := by
  rw [show (fun y ↦ u y ^ 2) = (fun y ↦ u y * u y) by funext y; ring,
    mixed_product_row u u hu hu]
  ring

private theorem partialDeriv_weight_pow (p : ℕ) (i : Fin 2) (x : ℝ^2) :
    (∂[i] ((fun y ↦ S y ^ p) : ℝ^2 → ℝ)) x = 2 * (p : ℝ) * x i * S x ^ (p - 1) := by
  have hs : (∂[i] (S : ℝ^2 → ℝ)) x = 2 * x i := by
    fin_cases i <;> cas
  change fderiv ℝ (fun y ↦ S y ^ p) x (EuclideanSpace.single i 1) = _
  rw [fderiv_fun_pow p (show DifferentiableAt ℝ S x by fun_prop)]
  simp only [smul_apply, nsmul_eq_mul, smul_eq_mul]
  change ((p : ℝ) * S x ^ (p - 1)) * (∂[i] (S : ℝ^2 → ℝ)) x = _
  rw [hs]
  ring

private theorem mixed_weight_pow (n : ℕ) (x : ℝ^2) :
    (∂[0] (∂[1] ((fun y ↦ S y ^ (n + 2)) : ℝ^2 → ℝ))) x =
      4 * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * x 0 * x 1 * S x ^ n := by
  have hsub : n + 2 - 1 = n + 1 := by omega
  have hZ : (∂[1] ((fun y ↦ S y ^ (n + 2)) : ℝ^2 → ℝ)) =
      fun y : ℝ^2 ↦ 2 * ((n + 2 : ℕ) : ℝ) * y 1 * S y ^ (n + 1) := by
    funext y
    simpa only [hsub] using partialDeriv_weight_pow (n + 2) 1 y
  rw [hZ, partialDeriv_mul (by fun_prop) (by fun_prop)]
  have hlinear : (∂[0] (fun y : ℝ^2 ↦ 2 * ((n + 2 : ℕ) : ℝ) * y 1)) x = 0 := by
    cas
  rw [hlinear, partialDeriv_weight_pow]
  simp only [zero_mul, zero_add, Nat.add_sub_cancel]
  ring

private theorem abs_mixed_weight_pow_le {p : ℕ} (hp : 1 ≤ p) (x : ℝ^2) :
    |(∂[0] (∂[1] ((fun y ↦ S y ^ p) : ℝ^2 → ℝ))) x| ≤
      (2 * (p : ℝ) ^ 2 - 2 * p) * S x ^ (p - 1) := by
  by_cases hp1 : p = 1
  · subst p
    have hZ : (∂[1] (S : ℝ^2 → ℝ)) = fun y : ℝ^2 ↦ 2 * y 1 := by
      funext y
      cas
    have hRZ : (∂[0] (∂[1] (S : ℝ^2 → ℝ))) x = 0 := by rw [hZ]; cas
    simpa only [pow_one, hRZ, abs_zero, Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
      using (show (0 : ℝ) ≤ 2 * 1 ^ 2 - 2 * 1 by norm_num)
  let n := p - 2
  have hp' : p = n + 2 := by dsimp [n]; omega
  rw [hp', mixed_weight_pow]
  have hsub : n + 2 - 1 = n + 1 := by omega
  simp only [hsub, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [pow_succ (S x) n]
  have hfac : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * S x ^ n := by positivity
  have hplus := mul_nonneg hfac (sq_nonneg (x 0 + x 1))
  have hminus := mul_nonneg hfac (sq_nonneg (x 0 - x 1))
  apply abs_le.mpr
  constructor <;> nlinarith only [hfac, hplus, hminus]

private theorem abs_first_cross_le {p w s r a b : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hr : r ^ 2 ≤ s) :
    |4 * p * r * w * a * b| ≤ 2 * p * (w * a ^ 2) + 2 * p * (w * s * b ^ 2) := by
  have hbase : |4 * r * a * b| ≤ 2 * a ^ 2 + 2 * r ^ 2 * b ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg (a - r * b), sq_nonneg (a + r * b)]
  have hmul := mul_le_mul_of_nonneg_left hbase (mul_nonneg hp hw)
  have hupper := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hr (sq_nonneg b)) (mul_nonneg hp hw)
  rw [show 4 * p * r * w * a * b = (p * w) * (4 * r * a * b) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hp hw)]
  nlinarith only [hmul, hupper]

/-- The mixed derivative of `S^p*u²` is dominated by three successive
weighted derivative levels. This pointwise estimate is independent of the measure;
its coefficients specialize to `5,3,1` and `13,5,1` at `p=1,2`. -/
theorem abs_mixed_pow_weighted_square_le
    {p : ℕ} (hp : 1 ≤ p) (u : ℝ^2 → ℝ) (hu : ContDiff ℝ 2 u) (x : ℝ^2) :
    |(∂[0] (∂[1] ((fun y ↦ S y ^ p * u y ^ 2) : ℝ^2 → ℝ))) x| ≤
      (2 * (p : ℝ) ^ 2 + 2 * p + 1) * (S x ^ (p - 1) * u x ^ 2) +
        (2 * p + 1) * (S x ^ p * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) +
          S x ^ (p + 1) * (∂[0] (∂[1] u)) x ^ 2 := by
  let w := S x ^ (p - 1)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hS : 0 ≤ S x := by positivity
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpow : S x ^ p = w * S x := by
    dsimp [w]
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hnext : S x ^ (p + 1) = w * S x ^ 2 := by rw [pow_succ, hpow]; ring
  have hdu := (hu.differentiable (by norm_num)).differentiableAt (x := x)
  have hformula : (∂[0] (∂[1] ((fun y ↦ S y ^ p * u y ^ 2) : ℝ^2 → ℝ))) x =
      (∂[0] (∂[1] ((fun y ↦ S y ^ p) : ℝ^2 → ℝ))) x * u x ^ 2 +
        4 * (p : ℝ) * x 0 * w * u x * (∂[1] u) x +
        4 * (p : ℝ) * x 1 * w * u x * (∂[0] u) x +
        2 * w * S x * (∂[0] u) x * (∂[1] u) x + 2 * w * S x * u x * (∂[0] (∂[1] u)) x := by
    rw [mixed_product_row (fun y ↦ S y ^ p) (fun y ↦ u y ^ 2)
      (by fun_prop) (hu.pow 2), partialDeriv_weight_pow, partialDeriv_weight_pow,
      partialDeriv_sq 0 hdu, partialDeriv_sq 1 hdu, mixed_square u hu, hpow]
    dsimp [w]
    ring
  have hzero : |(∂[0] (∂[1] ((fun y ↦ S y ^ p) : ℝ^2 → ℝ))) x * u x ^ 2| ≤
      (2 * (p : ℝ) ^ 2 - 2 * p) * (w * u x ^ 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (u x))]
    simpa only [mul_assoc, w] using
      mul_le_mul_of_nonneg_right (abs_mixed_weight_pow_le hp x) (sq_nonneg (u x))
  have hrS : x 0 ^ 2 ≤ S x := by dsimp; nlinarith only [sq_nonneg (x 1)]
  have hzS : x 1 ^ 2 ≤ S x := by dsimp; nlinarith only [sq_nonneg (x 0)]
  have hr := abs_first_cross_le hp0 hw hrS (a := u x) (b := (∂[1] u) x)
  have hz := abs_first_cross_le hp0 hw hzS (a := u x) (b := (∂[0] u) x)
  have hgrad : |2 * w * S x * (∂[0] u) x * (∂[1] u) x| ≤
      w * S x * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2) := by
    have hminus := mul_nonneg (mul_nonneg hw hS) (sq_nonneg ((∂[0] u) x - (∂[1] u) x))
    have hplus := mul_nonneg (mul_nonneg hw hS) (sq_nonneg ((∂[0] u) x + (∂[1] u) x))
    apply abs_le.mpr
    constructor <;> nlinarith only [hminus, hplus]
  have hlast : |2 * w * S x * u x * (∂[0] (∂[1] u)) x| ≤
      w * u x ^ 2 + w * S x ^ 2 * (∂[0] (∂[1] u)) x ^ 2 := by
    have hminus := mul_nonneg hw (sq_nonneg (u x - S x * (∂[0] (∂[1] u)) x))
    have hplus := mul_nonneg hw (sq_nonneg (u x + S x * (∂[0] (∂[1] u)) x))
    apply abs_le.mpr
    constructor <;> nlinarith only [hminus, hplus]
  rw [hformula, hpow, hnext]
  calc
    _ ≤ |(∂[0] (∂[1] ((fun y ↦ S y ^ p) : ℝ^2 → ℝ))) x * u x ^ 2| +
        |4 * (p : ℝ) * x 0 * w * u x * (∂[1] u) x| +
        |4 * (p : ℝ) * x 1 * w * u x * (∂[0] u) x| +
        |2 * w * S x * (∂[0] u) x * (∂[1] u) x| + |2 * w * S x * u x * (∂[0] (∂[1] u)) x| :=
      (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans
          (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by nlinarith only [hzero, hr, hz, hgrad, hlast]

private theorem compact_weighted_square_integrable
    {f : ℝ^2 → ℝ} (hf : Continuous f) (hcompact : HasCompactSupport f)
    {w : ℝ^2 → ℝ} (hw : Continuous w) :
    Integrable (fun x ↦ w x * f x ^ 2) := by
  have hsq : HasCompactSupport (fun x ↦ f x ^ 2) :=
    hcompact.comp_left (g := fun t : ℝ ↦ t ^ 2) (by norm_num)
  exact (hw.mul (hf.pow 2)).integrable_of_hasCompactSupport hsq.mul_left

private theorem compact_decay_density_integrable
    {u : ℝ^2 → ℝ} (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u)
    (p : ℕ) (a b c : ℝ) :
    Integrable (fun x ↦ a * (S x ^ (p - 1) * u x ^ 2) +
      b * (S x ^ p * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) +
        c * (S x ^ (p + 1) * (∂[0] (∂[1] u)) x ^ 2)) := by
  have hs : Continuous S := by fun_prop
  have hR : ContDiff ℝ 1 (∂[0] u) := contDiff_partialDeriv_of_succ (m := 1) hu
  have hZ : ContDiff ℝ 1 (∂[1] u) := contDiff_partialDeriv_of_succ (m := 1) hu
  have hRZ : Continuous (∂[0] (∂[1] u)) :=
    (contDiff_partialDeriv_of_succ (m := 0) hZ).continuous
  have hRc : HasCompactSupport (∂[0] u) :=
    hcompact.fderiv_apply ℝ (EuclideanSpace.single 0 1)
  have hZc : HasCompactSupport (∂[1] u) :=
    hcompact.fderiv_apply ℝ (EuclideanSpace.single 1 1)
  have hRZc : HasCompactSupport (∂[0] (∂[1] u)) :=
    hZc.fderiv_apply ℝ (EuclideanSpace.single 0 1)
  have h0 : Integrable (fun x ↦ S x ^ (p - 1) * u x ^ 2) :=
    compact_weighted_square_integrable hu.continuous hcompact
    (hs.pow (p - 1))
  have hR1 : Integrable (fun x ↦ S x ^ p * (∂[0] u) x ^ 2) :=
    compact_weighted_square_integrable hR.continuous hRc (hs.pow p)
  have hZ1 : Integrable (fun x ↦ S x ^ p * (∂[1] u) x ^ 2) :=
    compact_weighted_square_integrable hZ.continuous hZc (hs.pow p)
  have h1 : Integrable (fun x ↦ S x ^ p * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) := by
    have hsum : Integrable (fun x ↦ S x ^ p * (∂[0] u) x ^ 2 + S x ^ p * (∂[1] u) x ^ 2) :=
      Integrable.fun_add (ε' := ℝ) hR1 hZ1
    exact hsum.congr (Filter.Eventually.of_forall (fun x ↦ (mul_add _ _ _).symm))
  have h2 : Integrable (fun x ↦ S x ^ (p + 1) * (∂[0] (∂[1] u)) x ^ 2) :=
    compact_weighted_square_integrable hRZ hRZc (hs.pow (p + 1))
  have h01 : Integrable (fun x ↦ a * (S x ^ (p - 1) * u x ^ 2) +
      b * (S x ^ p * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2))) :=
    Integrable.fun_add (ε' := ℝ) (h0.const_mul a) (h1.const_mul b)
  exact Integrable.fun_add (ε' := ℝ) h01 (h2.const_mul c)

/-- The compact mixed-FTC bound respects the derivative hierarchy: each derivative
costs one power of `S`. The coefficients are `2p²+2p+1,2p+1,1`;
in particular `5,3,1` for `p=1`. -/
theorem pow_weighted_value_sq_le_integral_of_hasCompactSupport
    {p : ℕ} (hp : 1 ≤ p) {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hcompact : HasCompactSupport u) (x : ℝ^2) :
    S x ^ p * u x ^ 2 ≤
      ∫ y, (2 * (p : ℝ) ^ 2 + 2 * p + 1) * (S y ^ (p - 1) * u y ^ 2) +
        (2 * p + 1) * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
          S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2 := by
  let f : ℝ^2 → ℝ := fun y ↦ S y ^ p * u y ^ 2
  have hf : ContDiff ℝ 2 f :=
    ((show ContDiff ℝ 2 S by fun_prop).pow p).mul (hu.pow 2)
  have huSq : HasCompactSupport (fun y : ℝ^2 ↦ u y ^ 2) :=
    hcompact.comp_left (g := fun t : ℝ ↦ t ^ 2) (by norm_num)
  have hfc : HasCompactSupport f :=
    huSq.mul_left (f := fun y : ℝ^2 ↦ S y ^ p)
  have hZ : ContDiff ℝ 1 (∂[1] f) := contDiff_partialDeriv_of_succ (m := 1) hf
  have hRZ : Continuous (∂[0] (∂[1] f)) :=
    (contDiff_partialDeriv_of_succ (m := 0) hZ).continuous
  have hRZc : HasCompactSupport (∂[0] (∂[1] f)) :=
    (hfc.fderiv_apply ℝ (EuclideanSpace.single 1 1)).fderiv_apply ℝ
      (EuclideanSpace.single 0 1)
  have hmajorant : Integrable (fun y : ℝ^2 ↦
      (2 * (p : ℝ) ^ 2 + 2 * p + 1) * (S y ^ (p - 1) * u y ^ 2) +
        (2 * p + 1) * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
          S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) := by
    simpa only [one_mul] using
      (compact_decay_density_integrable hu hcompact p
        (2 * (p : ℝ) ^ 2 + 2 * p + 1) (2 * p + 1) 1)
  calc
    S x ^ p * u x ^ 2 = |f x| := (abs_of_nonneg (by dsimp [f]; positivity)).symm
    _ ≤ ∫ y, |(∂[0] (∂[1] f)) y| := norm_le_integral_abs_mixedPartialDeriv hf hfc x
    _ ≤ _ := integral_mono (hRZ.integrable_of_hasCompactSupport hRZc).abs hmajorant
      (abs_mixed_pow_weighted_square_le hp u hu)

private theorem exists_cutoff_derivative_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (x : ℝ^2),
        |(∂[0] (ballCutoff (0 : ℝ^2) hr).toFun) x| ≤ A * r⁻¹ ∧
        |(∂[1] (ballCutoff (0 : ℝ^2) hr).toFun) x| ≤ A * r⁻¹ ∧
        |(∂[0] (∂[1] (ballCutoff (0 : ℝ^2) hr).toFun)) x| ≤ B * r⁻¹ ^ 2 := by
  obtain ⟨A₀, hA₀, h₀⟩ := exists_abs_iteratedPartialDeriv_ballCutoff_le [(0 : Fin 2)]
  obtain ⟨A₁, hA₁, h₁⟩ := exists_abs_iteratedPartialDeriv_ballCutoff_le [(1 : Fin 2)]
  obtain ⟨B, hB, h₂⟩ := exists_abs_iteratedPartialDeriv_ballCutoff_le [(0 : Fin 2), 1]
  refine ⟨A₀ + A₁, B, add_nonneg hA₀ hA₁, hB, ?_⟩
  intro r hr x
  have hR : |(∂[0] (ballCutoff (0 : ℝ^2) hr).toFun) x| ≤ A₀ * r⁻¹ := by
    simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
      Nat.zero_add, pow_one] using h₀ 0 r hr x
  have hZ : |(∂[1] (ballCutoff (0 : ℝ^2) hr).toFun) x| ≤ A₁ * r⁻¹ := by
    simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
      Nat.zero_add, pow_one] using h₁ 0 r hr x
  refine ⟨hR.trans ?_, hZ.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₁) (inv_nonneg.mpr hr.le)
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA₀) (inv_nonneg.mpr hr.le)
  · simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.reduceAdd] using h₂ 0 r hr x

private theorem weight_le_five_radius_sq {r : ℝ} (hr : 1 ≤ r)
    {x : ℝ^2} (hx : x ∈ closedBall (0 : ℝ^2) (2 * r)) :
    S x ≤ 5 * r ^ 2 := by
  have hnorm : ‖x‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hnormSq : ‖x‖ ^ 2 ≤ (2 * r) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hnorm
  have heq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  dsimp
  nlinarith only [hnormSq, heq, hr]

private theorem first_cutoff_weighted_sq_le
    {f : ℝ^2 → ℝ} {r A : ℝ} (hr : 1 ≤ r) (hA : 0 ≤ A)
    (hsupport : tsupport f ⊆ closedBall (0 : ℝ^2) (2 * r))
    {x : ℝ^2} (hbound : |f x| ≤ A * r⁻¹) :
    S x * f x ^ 2 ≤ 5 * A ^ 2 := by
  by_cases hf : f x = 0
  · simp only [hf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    positivity
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hS := weight_le_five_radius_sq hr (hsupport (subset_tsupport f hf))
  have hfSq : f x ^ 2 ≤ (A * r⁻¹) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (f x)) (mul_nonneg hA (inv_nonneg.mpr hr0.le))).mpr hbound
  calc
    _ ≤ (5 * r ^ 2) * (A * r⁻¹) ^ 2 :=
      mul_le_mul hS hfSq (sq_nonneg _) (by positivity)
    _ = 5 * A ^ 2 := by cas using hr0.ne'

private theorem second_cutoff_weighted_sq_le
    {f : ℝ^2 → ℝ} {r B : ℝ} (hr : 1 ≤ r) (hB : 0 ≤ B)
    (hsupport : tsupport f ⊆ closedBall (0 : ℝ^2) (2 * r))
    {x : ℝ^2} (hbound : |f x| ≤ B * r⁻¹ ^ 2) :
    S x ^ 2 * f x ^ 2 ≤ 25 * B ^ 2 := by
  by_cases hf : f x = 0
  · simp only [hf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    positivity
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hS := weight_le_five_radius_sq hr (hsupport (subset_tsupport f hf))
  have hSSq : S x ^ 2 ≤ (5 * r ^ 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hS
  have hfSq : f x ^ 2 ≤ (B * r⁻¹ ^ 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (f x)) (mul_nonneg hB (sq_nonneg _))).mpr hbound
  calc
    _ ≤ (5 * r ^ 2) ^ 2 * (B * r⁻¹ ^ 2) ^ 2 :=
      mul_le_mul hSSq hfSq (sq_nonneg _) (sq_nonneg _)
    _ = 25 * B ^ 2 := by cas using hr0.ne'

private theorem cutoff_weighted_derivative_bounds
    {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 1 ≤ r)
    (hr0 : 0 < r) (x : ℝ^2)
    (hR : |(∂[0] (ballCutoff (0 : ℝ^2) hr0).toFun) x| ≤ A * r⁻¹)
    (hZ : |(∂[1] (ballCutoff (0 : ℝ^2) hr0).toFun) x| ≤ A * r⁻¹)
    (hRZ : |(∂[0] (∂[1] (ballCutoff (0 : ℝ^2) hr0).toFun)) x| ≤ B * r⁻¹ ^ 2) :
    S x * (∂[0] (ballCutoff (0 : ℝ^2) hr0).toFun) x ^ 2 ≤ 5 * A ^ 2 ∧
    S x * (∂[1] (ballCutoff (0 : ℝ^2) hr0).toFun) x ^ 2 ≤ 5 * A ^ 2 ∧
    S x ^ 2 * (∂[0] (∂[1] (ballCutoff (0 : ℝ^2) hr0).toFun)) x ^ 2 ≤ 25 * B ^ 2 := by
  let χ := ballCutoff (0 : ℝ^2) hr0
  have hsupport := tsupport_ballCutoff_subset (0 : ℝ^2) hr0
  have hRs : tsupport (∂[0] χ.toFun) ⊆ tsupport χ.toFun :=
    tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single 0 1)
  have hZs : tsupport (∂[1] χ.toFun) ⊆ tsupport χ.toFun :=
    tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single 1 1)
  have hRZs : tsupport (∂[0] (∂[1] χ.toFun)) ⊆ tsupport (∂[1] χ.toFun) :=
    tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single 0 1)
  exact ⟨first_cutoff_weighted_sq_le hr hA (hRs.trans hsupport) hR,
    first_cutoff_weighted_sq_le hr hA (hZs.trans hsupport) hZ,
    second_cutoff_weighted_sq_le hr hB ((hRZs.trans hZs).trans hsupport) hRZ⟩

private theorem cutoff_product_energy_bounds
    {u χ : ℝ^2 → ℝ} (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    {A B : ℝ} (x : ℝ^2) (hχsq : χ x ^ 2 ≤ 1)
    (hR : S x * (∂[0] χ) x ^ 2 ≤ 5 * A ^ 2)
    (hZ : S x * (∂[1] χ) x ^ 2 ≤ 5 * A ^ 2)
    (hRZ : S x ^ 2 * (∂[0] (∂[1] χ)) x ^ 2 ≤ 25 * B ^ 2) :
    (χ x * u x) ^ 2 ≤ u x ^ 2 ∧
    S x * ((∂[0] (fun y ↦ χ y * u y)) x ^ 2 + (∂[1] (fun y ↦ χ y * u y)) x ^ 2) ≤
      2 * (S x * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) + 20 * A ^ 2 * u x ^ 2 ∧
    S x ^ 2 * (∂[0] (∂[1] (fun y ↦ χ y * u y))) x ^ 2 ≤
      4 * (S x ^ 2 * (∂[0] (∂[1] u)) x ^ 2) +
        20 * A ^ 2 * (S x * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) + 100 * B ^ 2 * u x ^ 2 := by
  have hS : 0 ≤ S x := by positivity
  have h0 : (χ x * u x) ^ 2 ≤ u x ^ 2 := by
    simpa only [mul_pow, one_mul] using mul_le_mul_of_nonneg_right hχsq (sq_nonneg (u x))
  have hfirst (i : Fin 2) (hi : S x * (∂[i] χ) x ^ 2 ≤ 5 * A ^ 2) :
      S x * (∂[i] (fun y ↦ χ y * u y)) x ^ 2 ≤
        2 * (S x * (∂[i] u) x ^ 2) + 10 * A ^ 2 * u x ^ 2 := by
    rw [partialDeriv_mul (hχ.differentiable (by norm_num)).differentiableAt
      (hu.differentiable (by norm_num)).differentiableAt]
    have hadd := mul_le_mul_of_nonneg_left
      (add_sq_le (a := (∂[i] χ) x * u x) (b := χ x * (∂[i] u) x)) hS
    have hcut := mul_le_mul_of_nonneg_right hi (sq_nonneg (u x))
    have hfield := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hχsq (sq_nonneg ((∂[i] u) x))) hS
    nlinarith only [hadd, hcut, hfield]
  have h1 :
      S x * ((∂[0] (fun y ↦ χ y * u y)) x ^ 2 + (∂[1] (fun y ↦ χ y * u y)) x ^ 2) ≤
        2 * (S x * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) + 20 * A ^ 2 * u x ^ 2 := by
    nlinarith only [hfirst 0 hR, hfirst 1 hZ]
  refine ⟨h0, h1, ?_⟩
  rw [mixed_product_row χ u hχ hu]
  have hfour (a b c d : ℝ) :
      (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith only [sq_nonneg (a + b - c - d), sq_nonneg (a - b), sq_nonneg (c - d)]
  have hadd := mul_le_mul_of_nonneg_left
    (hfour (χ x * (∂[0] (∂[1] u)) x) ((∂[0] χ) x * (∂[1] u) x)
      ((∂[1] χ) x * (∂[0] u) x) ((∂[0] (∂[1] χ)) x * u x)) (sq_nonneg (S x))
  have hfield := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hχsq (sq_nonneg ((∂[0] (∂[1] u)) x))) (sq_nonneg (S x))
  have hcutR := mul_le_mul_of_nonneg_right hR (mul_nonneg hS (sq_nonneg ((∂[1] u) x)))
  have hcutZ := mul_le_mul_of_nonneg_right hZ (mul_nonneg hS (sq_nonneg ((∂[0] u) x)))
  have hcutRZ := mul_le_mul_of_nonneg_right hRZ (sq_nonneg (u x))
  nlinarith only [hadd, hfield, hcutR, hcutZ, hcutRZ]

private theorem cutoff_hierarchy_density_le
    {u χ : ℝ^2 → ℝ} (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    {A B a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w)
    (x : ℝ^2) (hχsq : χ x ^ 2 ≤ 1)
    (hR : S x * (∂[0] χ) x ^ 2 ≤ 5 * A ^ 2)
    (hZ : S x * (∂[1] χ) x ^ 2 ≤ 5 * A ^ 2)
    (hRZ : S x ^ 2 * (∂[0] (∂[1] χ)) x ^ 2 ≤ 25 * B ^ 2) :
    a * (w * (χ x * u x) ^ 2) +
        b * (w * S x * ((∂[0] (fun y ↦ χ y * u y)) x ^ 2 +
          (∂[1] (fun y ↦ χ y * u y)) x ^ 2)) +
        w * S x ^ 2 * (∂[0] (∂[1] (fun y ↦ χ y * u y))) x ^ 2 ≤
      (a + 20 * b * A ^ 2 + 100 * B ^ 2) * (w * u x ^ 2) +
        (2 * b + 20 * A ^ 2) * (w * S x * ((∂[0] u) x ^ 2 + (∂[1] u) x ^ 2)) +
          4 * (w * S x ^ 2 * (∂[0] (∂[1] u)) x ^ 2) := by
  obtain ⟨h0, h1, h2⟩ := cutoff_product_energy_bounds hu hχ x hχsq hR hZ hRZ
  have h0w := mul_le_mul_of_nonneg_left h0 (mul_nonneg ha hw)
  have h1w := mul_le_mul_of_nonneg_left h1 (mul_nonneg hb hw)
  have h2w := mul_le_mul_of_nonneg_left h2 hw
  nlinarith only [h0w, h1w, h2w]

/-- The canonical bump gives constants for every positive integer weight exponent.
The three input weights are `S^(p-1)`, `S^p`, and `S^(p+1)`; the output is `S^p*u²`.
In particular, `p=1` gives swirl decay, and `p=2,3,4` use successive derivative hierarchies.

The constants come from first and mixed second derivatives of the fixed bump.
Compact support and pointwise decay of the field are not hypotheses. -/
theorem exists_pow_weighted_value_sq_le_integrals :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (p : ℕ), 1 ≤ p →
      ∀ (u : ℝ^2 → ℝ), ContDiff ℝ 2 u →
        Integrable (fun y ↦ S y ^ (p - 1) * u y ^ 2) →
        Integrable (fun y ↦ S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) →
        Integrable (fun y ↦ S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) →
      ∀ x : ℝ^2, S x ^ p * u x ^ 2 ≤
        (2 * (p : ℝ) ^ 2 + 2 * p + 1 + 20 * (2 * p + 1) * A ^ 2 + 100 * B ^ 2) *
          (∫ y, S y ^ (p - 1) * u y ^ 2) +
        (2 * (2 * p + 1) + 20 * A ^ 2) *
          (∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
        4 * (∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) := by
  obtain ⟨A, B, hA, hB, hbounds⟩ := exists_cutoff_derivative_bounds
  refine ⟨A, B, hA, hB, ?_⟩
  intro p hp u hu h0 h1 h2 x
  let r := ‖x‖ + 1
  have hr : 1 ≤ r := by dsimp [r]; linarith [norm_nonneg x]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let χ := ballCutoff (0 : ℝ^2) hr0
  let v : ℝ^2 → ℝ := fun y ↦ χ y * u y
  have hχ : ContDiff ℝ 2 χ.toFun :=
    χ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv : ContDiff ℝ 2 v := hχ.mul hu
  have hvc : HasCompactSupport v := χ.hasCompactSupport.mul_right
  have hvalue : v x = u x := by
    have hχx : χ x = 1 := ballCutoff_eq_one (0 : ℝ^2) hr0
      (by simpa only [mem_closedBall, dist_zero_right] using
        (show ‖x‖ ≤ r by dsimp [r]; linarith))
    simp only [v, hχx, one_mul]
  let a : ℝ := 2 * (p : ℝ) ^ 2 + 2 * p + 1
  let b : ℝ := 2 * p + 1
  let C₀ : ℝ := a + 20 * b * A ^ 2 + 100 * B ^ 2
  let C₁ : ℝ := 2 * b + 20 * A ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hC₀ : Integrable (fun y ↦ C₀ * (S y ^ (p - 1) * u y ^ 2)) :=
    h0.const_mul C₀
  have hC₁ : Integrable (fun y ↦ C₁ * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2))) :=
    h1.const_mul C₁
  have hC₂ : Integrable (fun y ↦ 4 * (S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2)) :=
    h2.const_mul 4
  have hC₀₁ : Integrable (fun y ↦ C₀ * (S y ^ (p - 1) * u y ^ 2) +
      C₁ * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2))) :=
    Integrable.fun_add (ε' := ℝ) hC₀ hC₁
  have hmajor : Integrable (fun y ↦ C₀ * (S y ^ (p - 1) * u y ^ 2) +
      C₁ * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
        4 * (S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2)) :=
    Integrable.fun_add (ε' := ℝ) hC₀₁ hC₂
  have hpoint (y : ℝ^2) :
      a * (S y ^ (p - 1) * v y ^ 2) +
        b * (S y ^ p * ((∂[0] v) y ^ 2 + (∂[1] v) y ^ 2)) + S y ^ (p + 1) * (∂[0] (∂[1] v)) y ^ 2 ≤
      C₀ * (S y ^ (p - 1) * u y ^ 2) +
        C₁ * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
          4 * (S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) := by
    obtain ⟨hR, hZ, hRZ⟩ := hbounds r hr0 y
    obtain ⟨hRs, hZs, hRZs⟩ := cutoff_weighted_derivative_bounds hA hB hr hr0 y hR hZ hRZ
    have hχIcc := ballCutoff_mem_Icc (0 : ℝ^2) y hr0
    have hχsq : χ y ^ 2 ≤ 1 := by nlinarith only [hχIcc.1, hχIcc.2]
    have hpow₁ : S y ^ p = S y ^ (p - 1) * S y := by
      rw [← pow_succ, Nat.sub_add_cancel hp]
    have hpow₂ : S y ^ (p + 1) = S y ^ (p - 1) * S y ^ 2 := by
      rw [pow_succ, hpow₁]
      ring
    rw [hpow₁, hpow₂]
    exact cutoff_hierarchy_density_le hu hχ ha hb (by positivity) y hχsq hRs hZs hRZs
  change S x ^ p * u x ^ 2 ≤
    C₀ * (∫ y, S y ^ (p - 1) * u y ^ 2) +
      C₁ * (∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
        4 * (∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2)
  calc
    S x ^ p * u x ^ 2 = S x ^ p * v x ^ 2 := by rw [hvalue]
    _ ≤ ∫ y, a * (S y ^ (p - 1) * v y ^ 2) +
        b * (S y ^ p * ((∂[0] v) y ^ 2 + (∂[1] v) y ^ 2)) + S y ^ (p + 1) * (∂[0] (∂[1] v)) y ^ 2 :=
      pow_weighted_value_sq_le_integral_of_hasCompactSupport hp hv hvc x
    _ ≤ ∫ y, C₀ * (S y ^ (p - 1) * u y ^ 2) +
        C₁ * (S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
          4 * (S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) :=
      integral_mono (by simpa only [one_mul] using
        compact_decay_density_integrable hv hvc p a b 1) hmajor hpoint
    _ = _ := by
      rw [integral_add hC₀₁ hC₂, integral_add hC₀ hC₁]
      simp only [integral_const_mul]

/-- Taking the square root gives the decay estimate.
At `p=1` the left side is `√S*|u|`; at `p=2` it is `S*|u|`.
The same bump constants apply to every positive natural exponent. -/
theorem exists_sqrt_pow_mul_abs_le_integrals :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (p : ℕ), 1 ≤ p →
      ∀ (u : ℝ^2 → ℝ), ContDiff ℝ 2 u →
        Integrable (fun y ↦ S y ^ (p - 1) * u y ^ 2) →
        Integrable (fun y ↦ S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) →
        Integrable (fun y ↦ S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) →
      ∀ x : ℝ^2, √(S x ^ p) * |u x| ≤ √
        ((2 * (p : ℝ) ^ 2 + 2 * p + 1 + 20 * (2 * p + 1) * A ^ 2 + 100 * B ^ 2) *
          (∫ y, S y ^ (p - 1) * u y ^ 2) +
        (2 * (2 * p + 1) + 20 * A ^ 2) *
          (∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
        4 * (∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_pow_weighted_value_sq_le_integrals
  refine ⟨A, B, hA, hB, ?_⟩
  intro p hp u hu h0 h1 h2 x
  have h := Real.sqrt_le_sqrt (hbound p hp u hu h0 h1 h2 x)
  rw [Real.sqrt_mul (show 0 ≤ S x ^ p by positivity), Real.sqrt_sq_eq_abs] at h
  exact h

end PDE.Analysis

namespace PDE.Analysis

open MeasureTheory
open SobolevSpace.Weighted PDE.Common

local notation "S" => (fun x : ℝ^2 ↦ 1 + x 0 ^ 2 + x 1 ^ 2)
local notation "ν" => (volume.restrict (Set.ofPred (fun x : ℝ^2 ↦ 0 ≤ x 0)))

/-- The polynomial hierarchy is unchanged by the physical radial reflection. -/
private theorem polynomial_weight_reflection (x : ℝ^2) :
    S (PDE.Common.coordinateReflection 0 x) = S x := by
  simp only [PDE.Common.coordinateReflection_apply_same,
    PDE.Common.coordinateReflection_apply_of_ne (n := 2) 0 1 (by norm_num), neg_sq]

/-- Even and odd fields obey the same hierarchy on the physical half-plane.
Differentiating the reflection identity determines the signs of every row;
squaring removes them. The whole-plane cutoff estimate therefore costs exactly
the factor two from reflection, with no extra integrability or decay premise. -/
theorem exists_pow_weighted_value_sq_le_halfSpace_integrals :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (p : ℕ), 1 ≤ p →
      ∀ (u : ℝ^2 → ℝ), ContDiff ℝ 2 u →
      ∀ (ε : ℝ),
        IsReflectionEigenfunctionOn Set.univ 0 ε u →
        Integrable (fun y ↦ S y ^ (p - 1) * u y ^ 2) ν →
        Integrable (fun y ↦ S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) ν →
        Integrable (fun y ↦ S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) ν →
      ∀ x : ℝ^2, S x ^ p * u x ^ 2 ≤ 2 *
        ((2 * (p : ℝ) ^ 2 + 2 * p + 1 + 20 * (2 * p + 1) * A ^ 2 + 100 * B ^ 2) *
          (∫ y, S y ^ (p - 1) * u y ^ 2 ∂ν) +
        (2 * (2 * p + 1) + 20 * A ^ 2) *
          (∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2) ∂ν) +
        4 * (∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2 ∂ν)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_pow_weighted_value_sq_le_integrals
  refine ⟨A, B, hA, hB, ?_⟩
  intro p hp u hu ε hparity h0 h1 h2 x
  -- Reflecting twice gives `u = ε² u`, so either `ε² = 1` or `u` vanishes identically.
  by_cases hε : ε ^ 2 = 1
  swap
  · have hzero (y : ℝ^2) : u y = 0 := by
      have hy := hparity y (Set.mem_univ y)
      have hRy := hparity (coordinateReflection 0 y) (Set.mem_univ _)
      rw [coordinateReflection_involutive 0 y, hy] at hRy
      have hmul : (1 - ε ^ 2) * u y = 0 := by linear_combination hRy
      exact (mul_eq_zero.mp hmul).resolve_left fun h ↦ hε (by linarith)
    obtain rfl : u = fun _ ↦ 0 := funext hzero
    have hd (i : Fin 2) : ∂[i] (fun _ : ℝ^2 ↦ (0 : ℝ)) = fun _ ↦ 0 :=
      funext fun _ ↦ partialDeriv_const 0
    simp [hd]
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hR : ContDiff ℝ 1 (∂[0] u) := contDiff_partialDeriv_of_succ (m := 1) hu
  have hZ : ContDiff ℝ 1 (∂[1] u) := contDiff_partialDeriv_of_succ (m := 1) hu
  have hRZ : Continuous (∂[0] (∂[1] u)) :=
    (contDiff_partialDeriv_of_succ (m := 0) hZ).continuous
  have hinv : ∀ y ∈ (Set.univ : Set (ℝ^2)), coordinateReflection 0 y ∈ Set.univ :=
    fun _ _ ↦ Set.mem_univ _
  have hRparity := hparity.partialDeriv_same isOpen_univ hinv
    (hu1.differentiable one_ne_zero).differentiableOn
  have hZparity := hparity.partialDeriv_of_ne isOpen_univ hinv
    (hu1.differentiable one_ne_zero).differentiableOn (by norm_num : (1 : Fin 2) ≠ 0)
  have hRZparity := hZparity.partialDeriv_same isOpen_univ hinv
    (hZ.differentiable one_ne_zero).differentiableOn
  have hS : Continuous S := by fun_prop
  have heven0 : PDE.Common.IsEvenUnderCoordinateReflection 0
      (fun y ↦ S y ^ (p - 1) * u y ^ 2) := by
    intro y
    simp only [polynomial_weight_reflection, hparity y (Set.mem_univ y),
      mul_pow, hε, one_mul]
  have heven1 : PDE.Common.IsEvenUnderCoordinateReflection 0
      (fun y ↦ S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) := by
    intro y
    simp only [polynomial_weight_reflection, hRparity y (Set.mem_univ y),
      hZparity y (Set.mem_univ y), mul_pow, neg_sq, hε, one_mul]
  have heven2 : PDE.Common.IsEvenUnderCoordinateReflection 0
      (fun y ↦ S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) := by
    intro y
    simp only [polynomial_weight_reflection, hRZparity y (Set.mem_univ y),
      mul_pow, neg_sq, hε, one_mul]
  have h0full := integrable_integral_le_twice_of_nonneg_even 0
    ((hS.pow (p - 1)).mul (hu.continuous.pow 2))
    (fun y ↦ by change 0 ≤ S y ^ (p - 1) * u y ^ 2; positivity) heven0 h0
  have h1full := integrable_integral_le_twice_of_nonneg_even 0
    ((hS.pow p).mul ((hR.continuous.pow 2).add (hZ.continuous.pow 2)))
    (fun y ↦ by change 0 ≤ S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2); positivity) heven1 h1
  have h2full := integrable_integral_le_twice_of_nonneg_even 0
    ((hS.pow (p + 1)).mul (hRZ.pow 2))
    (fun y ↦ by change 0 ≤ S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2; positivity) heven2 h2
  let C₀ : ℝ :=
    2 * (p : ℝ) ^ 2 + 2 * p + 1 + 20 * (2 * p + 1) * A ^ 2 + 100 * B ^ 2
  let C₁ : ℝ := 2 * (2 * p + 1) + 20 * A ^ 2
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  calc
    S x ^ p * u x ^ 2 ≤
        C₀ * (∫ y, S y ^ (p - 1) * u y ^ 2) +
          C₁ * (∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) +
            4 * (∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) :=
      hbound p hp u hu h0full.1 h1full.1 h2full.1 x
    _ ≤ C₀ * (2 * ∫ y, S y ^ (p - 1) * u y ^ 2 ∂ν) +
          C₁ * (2 * ∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2) ∂ν) +
            4 * (2 * ∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2 ∂ν) :=
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left h0full.2 hC₀)
          (mul_le_mul_of_nonneg_left h1full.2 hC₁))
        (mul_le_mul_of_nonneg_left h2full.2 (by norm_num))
    _ = _ := by dsimp [C₀, C₁]; ring

/-- The half-plane hierarchy gives pointwise decay after taking a square
root. The same cutoff constants work for `p=1,2,3,4`, and for every larger
natural exponent for which the three physical energy integrals are finite. -/
theorem exists_sqrt_pow_mul_abs_le_halfSpace_integrals :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (p : ℕ), 1 ≤ p →
      ∀ (u : ℝ^2 → ℝ), ContDiff ℝ 2 u →
      ∀ (ε : ℝ), ε ^ 2 = 1 →
        IsReflectionEigenfunctionOn Set.univ 0 ε u →
        Integrable (fun y ↦ S y ^ (p - 1) * u y ^ 2) ν →
        Integrable (fun y ↦ S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2)) ν →
        Integrable (fun y ↦ S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2) ν →
      ∀ x : ℝ^2, √(S x ^ p) * |u x| ≤ √(2 *
        ((2 * (p : ℝ) ^ 2 + 2 * p + 1 + 20 * (2 * p + 1) * A ^ 2 + 100 * B ^ 2) *
          (∫ y, S y ^ (p - 1) * u y ^ 2 ∂ν) +
        (2 * (2 * p + 1) + 20 * A ^ 2) *
          (∫ y, S y ^ p * ((∂[0] u) y ^ 2 + (∂[1] u) y ^ 2) ∂ν) +
        4 * (∫ y, S y ^ (p + 1) * (∂[0] (∂[1] u)) y ^ 2 ∂ν))) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_pow_weighted_value_sq_le_halfSpace_integrals
  refine ⟨A, B, hA, hB, ?_⟩
  intro p hp u hu ε hε hparity h0 h1 h2 x
  have h := Real.sqrt_le_sqrt (hbound p hp u hu ε hparity h0 h1 h2 x)
  rw [Real.sqrt_mul (show 0 ≤ S x ^ p by positivity), Real.sqrt_sq_eq_abs] at h
  exact h

end PDE.Analysis
