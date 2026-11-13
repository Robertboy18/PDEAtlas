/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.IteratedDerivativeEstimates
public import PDE.FDeriv.PartialDeriv.Norm

/-!
# Interior derivative bounds with L¹ data

The mean-value formula turns an integral bound into a uniform bound on a smaller
ball. The supremum estimate then controls every derivative order.
For an open ball, we first work on smaller closed balls and let their radii
increase to the given radius. The result is Evans's Theorem 7 of §2.2.3 with his constants
(`interiorDerivativeConstant`), stated for the operator norm of `D^k u(x)`; the coordinate
versions are `IsHarmonicPDE.norm_iteratedPartialDeriv_le_integral_abs` and
`IsHarmonicPDE.enorm_iteratedPartialDeriv_le_eLpNorm_one`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 7 (Estimates on derivatives), (18)-(19),
  p. 29.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Metric Set
open PDE.Analysis
open scoped Topology

namespace LaplacianEquation

/-- The dimension and order factor in the harmonic interior L¹ estimate.
Order zero is the mean-value bound; positive orders use the constants of
Evans, §2.2.3, Theorem 7. -/
noncomputable def interiorDerivativeConstant (n k : ℕ) : ℝ :=
  if k = 0 then (unitBallVolume n)⁻¹
  else ((2 : ℝ) ^ (n + 1) * (n : ℝ) * (k : ℝ)) ^ k / unitBallVolume n

/-- The constant in the interior estimate is strictly positive. -/
theorem interiorDerivativeConstant_pos (n k : ℕ) [Fact (0 < n)] :
    0 < interiorDerivativeConstant n k := by
  have hα : 0 < unitBallVolume n := unitBallVolume_pos n
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Fact.out : 0 < n)
  unfold interiorDerivativeConstant
  split_ifs with hk
  · exact inv_pos.mpr hα
  · have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity

/-- Every derivative at the center is controlled by the L¹ norm on a closed
admissible ball. Only the original `C²` harmonicity hypothesis is needed:
interior smoothness and the higher derivative estimates are reused below. -/
theorem IsHarmonicPDE.norm_iteratedFDeriv_le_integral_abs_of_closedBall
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ U) :
    ‖iteratedFDeriv ℝ k u x‖ ≤
      interiorDerivativeConstant n k / r ^ (n + k) *
        ∫ y in ball x r, |u y| := by
  classical
  have hα : 0 < unitBallVolume n := unitBallVolume_pos n
  have hint : IntegrableOn u (ball x r) volume :=
    ((hu.contDiffOn.mono hball).continuousOn.integrableOn_compact
      (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  obtain rfl | hk := k.eq_zero_or_pos
  · have hmean := hu.hasSphereMeanValueProperty.abs_le_integral_abs hr hball hint
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    refine hmean.trans_eq ?_
    simp only [interiorDerivativeConstant, ↓reduceIte, Nat.add_zero]
    field_simp [hα.ne', hr.ne']
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  let I : ℝ := ∫ y in ball x r, |u y|
  let M : ℝ := I / (unitBallVolume n * (r / 2) ^ n)
  let ρ : ℝ := r / (2 * (k : ℝ))
  have hI : 0 ≤ I := integral_nonneg fun y ↦ abs_nonneg (u y)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hbudget : (k : ℝ) * ρ = r / 2 := by
    dsimp [ρ]
    field_simp [hk'.ne']
  have hM (y : ℝ^n) (hy : y ∈ closedBall x (r / 2)) : |u y| ≤ M :=
    hu.hasSphereMeanValueProperty.abs_le_integral_abs_of_subset (half_pos hr)
      ((closedBall_subset_closedBall' (by linarith [mem_closedBall.mp hy])).trans hball)
      (ball_subset_ball' (by linarith [mem_closedBall.mp hy])) hint
  have hderiv :
      ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M / ρ ^ k :=
    (hu.on_ball (ball_subset_closedBall.trans hball)).norm_iteratedFDeriv_le
      isOpen_ball hρ
      (by rw [hbudget]; exact closedBall_subset_ball (half_lt_self hr))
      (by rw [hbudget]; exact hM)
  have hconstant : (2 : ℝ) ^ (n + k) * ((n : ℝ) * (k : ℝ)) ^ k ≤
      ((2 : ℝ) ^ (n + 1) * (n : ℝ) * (k : ℝ)) ^ k := by
    rw [mul_assoc, mul_pow ((2 : ℝ) ^ (n + 1)), ← pow_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num)
      (by nlinarith [Nat.mul_le_mul_left n (show 1 ≤ k from hk)])) (by positivity)
  calc
    ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M / ρ ^ k := hderiv
    _ = ((2 : ℝ) ^ (n + k) * ((n : ℝ) * (k : ℝ)) ^ k /
          (unitBallVolume n * r ^ (n + k))) * I := by
      dsimp [M, ρ]
      simp only [div_pow, mul_pow, pow_add]
      field_simp [hα.ne', hr.ne', hk'.ne']
    _ ≤ (((2 : ℝ) ^ (n + 1) * (n : ℝ) * (k : ℝ)) ^ k /
          (unitBallVolume n * r ^ (n + k))) * I :=
      mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right (by positivity)).2 hconstant) hI
    _ = interiorDerivativeConstant n k / r ^ (n + k) *
          ∫ y in ball x r, |u y| := by
      simp only [interiorDerivativeConstant, ite_eq_right hk.ne', div_div, I]

/-- Interior derivative estimate on the open ball appearing in Evans's statement.
An integrable function may grow near the boundary; no closed-ball regularity
or boundary bound is assumed. -/
theorem IsHarmonicPDE.norm_iteratedFDeriv_le_integral_abs
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : ball x r ⊆ U)
    (hint : IntegrableOn u (ball x r) volume) :
    ‖iteratedFDeriv ℝ k u x‖ ≤
      interiorDerivativeConstant n k / r ^ (n + k) *
        ∫ y in ball x r, |u y| := by
  let I : ℝ := ∫ y in ball x r, |u y|
  have hlimit :
      Tendsto (fun q : ℝ ↦ interiorDerivativeConstant n k / q ^ (n + k) * I)
        (𝓝[<] r) (𝓝 (interiorDerivativeConstant n k / r ^ (n + k) * I)) :=
    ((continuousAt_const.div (continuousAt_id.pow (n + k))
      (pow_ne_zero _ hr.ne')).mul continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds
  apply ge_of_tendsto hlimit
  filter_upwards [(eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with q hq hqr
  have hsmall_closed : closedBall x q ⊆ U :=
    (closedBall_subset_ball hqr).trans hball
  have hsmall_open : ball x q ⊆ ball x r :=
    ball_subset_ball hqr.le
  refine (hu.norm_iteratedFDeriv_le_integral_abs_of_closedBall hq hsmall_closed).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by
    exact div_nonneg (interiorDerivativeConstant_pos n k).le (pow_pos hq _).le)
  exact setIntegral_mono_set hint.abs
    (Eventually.of_forall fun y ↦ abs_nonneg (u y))
    (Eventually.of_forall fun y hy ↦ hsmall_open hy)

/-- The harmonic interior estimate on an open ball, including an infinite L¹ norm.
The coefficient is strictly positive, so the infinite-norm case is automatic.
For finite norm, Mathlib identifies the norm with the integral of `|u|`. -/
theorem IsHarmonicPDE.enorm_iteratedFDeriv_le_eLpNorm_one
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : ball x r ⊆ U) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ k u x‖ ≤
      ENNReal.ofReal (interiorDerivativeConstant n k / r ^ (n + k)) *
        eLpNorm u 1 (volume.restrict (ball x r)) := by
  have hC : 0 < interiorDerivativeConstant n k / r ^ (n + k) :=
    div_pos (interiorDerivativeConstant_pos n k) (pow_pos hr _)
  by_cases htop : eLpNorm u 1 (volume.restrict (ball x r)) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC)]
    exact le_top
  · have hint : IntegrableOn u (ball x r) volume :=
      memLp_one_iff_integrable.mp
        (show MemLp u 1 (volume.restrict (ball x r)) from lt_top_iff_ne_top.mpr htop)
    have hnorm : ENNReal.ofReal (∫ y in ball x r, |u y|) =
        eLpNorm u 1 (volume.restrict (ball x r)) := by
      rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable]
      simpa only [Real.norm_eq_abs] using
        ofReal_integral_norm_eq_lintegral_enorm hint
    rw [← hnorm, ← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal
      (hu.norm_iteratedFDeriv_le_integral_abs hr hball hint)

/-- The same L¹ bound controls every ordered coordinate derivative. Smoothness
on the open ball follows from the original harmonicity hypothesis. -/
theorem IsHarmonicPDE.norm_iteratedPartialDeriv_le_integral_abs
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (indices : List (Fin n)) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : ball x r ⊆ U)
    (hint : IntegrableOn u (ball x r) volume) :
    ‖iteratedPartialDeriv indices u x‖ ≤
      interiorDerivativeConstant n indices.length / r ^ (n + indices.length) *
        ∫ y in ball x r, |u y| := by
  have hsmooth : ContDiffAt ℝ indices.length u x :=
    ((hu.on_ball hball).contDiffOn_of_isOpen (m := indices.length) isOpen_ball
      x (mem_ball_self hr)).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  exact (PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv indices hsmooth).trans
    (hu.norm_iteratedFDeriv_le_integral_abs hr hball hint)

/-- Every ordered coordinate derivative satisfies the open-ball estimate,
without a finiteness assumption on the L¹ norm. -/
theorem IsHarmonicPDE.enorm_iteratedPartialDeriv_le_eLpNorm_one
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (indices : List (Fin n)) {x : ℝ^n} {r : ℝ}
    (hr : 0 < r) (hball : ball x r ⊆ U) :
    ENNReal.ofReal ‖iteratedPartialDeriv indices u x‖ ≤
      ENNReal.ofReal
        (interiorDerivativeConstant n indices.length / r ^ (n + indices.length)) *
        eLpNorm u 1 (volume.restrict (ball x r)) := by
  have hsmooth : ContDiffAt ℝ indices.length u x :=
    ((hu.on_ball hball).contDiffOn_of_isOpen (m := indices.length) isOpen_ball
      x (mem_ball_self hr)).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  exact (ENNReal.ofReal_le_ofReal
    (PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv indices hsmooth)).trans
      (hu.enorm_iteratedFDeriv_le_eLpNorm_one hr hball)

end LaplacianEquation
