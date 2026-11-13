/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.WeightedExpansion
import CAS.ExactTactic

/-!
# Expanding polynomial bumps activated at time zero

The squared support radius grows affinely in time. Multiplication by time
gives zero initial data, while exponential damping controls the later growth.
The positive-part cube makes the function jointly C² across the expanding
sphere. Spatial derivative formulas reuse the stationary ball bump.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A time-activated bump with affine squared radius and exponential damping. -/
def expandingPolynomialBump (z : E) (r v δ : ℝ) (x : E) (t : ℝ) : ℝ :=
  t * Real.exp (-δ * t) * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 3

/-- Joint C² regularity holds even across the support boundary and at time zero. -/
theorem contDiff_expandingPolynomialBump (z : E) (r v δ : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (expandingPolynomialBump z r v δ)) := by
  have hgap : ContDiff ℝ 2 (fun p : E × ℝ ↦ r ^ 2 + v * p.2 - ‖p.1 - z‖ ^ 2) :=
    (contDiff_const.add (contDiff_const.mul contDiff_snd)).sub
      ((contDiff_fst.sub contDiff_const).norm_sq ℝ)
  exact (contDiff_snd.mul (contDiff_const.mul contDiff_snd).exp).mul
    (contDiff_two_posPart_cube.comp hgap)

omit [InnerProductSpace ℝ E] in
/-- At a time with nonnegative squared radius, the spatial profile is the
stationary bump times its scalar amplitude. -/
theorem expandingPolynomialBump_eq_ballBump
    (z : E) {r v δ t : ℝ} (hradius : 0 ≤ r ^ 2 + v * t) :
    (fun x ↦ expandingPolynomialBump z r v δ x t) =
      fun x ↦ t * Real.exp (-δ * t) * polynomialBallBump z (√(r ^ 2 + v * t)) x := by
  exact weightedPolynomialBallBump_eq_ballBump z hradius

omit [InnerProductSpace ℝ E] in
/-- The time derivative includes activation, exponential damping, and expansion
of the squared radius. All terms vanish outside the support. -/
theorem hasDerivAt_expandingPolynomialBump
    (z : E) (r v δ : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (expandingPolynomialBump z r v δ x)
      (Real.exp (-δ * t) *
        ((1 - δ * t) * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 3 +
          3 * v * t * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 2)) t := by
  have hradius : HasDerivAt (fun s : ℝ ↦ r ^ 2 + v * s) v t := by
    cas
  have hfactor : HasDerivAt (fun s : ℝ ↦ s * Real.exp (-δ * s))
      ((1 - δ * t) * Real.exp (-δ * t)) t := by
    cas
  convert! hasDerivAt_weightedPolynomialBallBump z x hradius hfactor using 1
  cas

/-- The spatial differential comes from the stationary ball-bump differential. -/
theorem fderiv_expandingPolynomialBump_apply
    (z : E) {r v δ t : ℝ} (hradius : 0 ≤ r ^ 2 + v * t) (x d : E) :
    fderiv ℝ (fun y ↦ expandingPolynomialBump z r v δ y t) x d =
      t * Real.exp (-δ * t) *
        (-6 * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 2 * ⟪x - z, d⟫) := by
  rw [expandingPolynomialBump_eq_ballBump z hradius,
    fderiv_const_mul ((contDiff_polynomialBallBump _ _).differentiable (by norm_num) x),
    smul_apply, smul_eq_mul, fderiv_polynomialBallBump_apply, Real.sq_sqrt hradius]

/-- The spatial curvature also reuses the stationary profile, including on the
expanding sphere. -/
theorem secondDirectionalDerivative_expandingPolynomialBump
    (z : E) {r v δ t : ℝ} (hradius : 0 ≤ r ^ 2 + v * t) (x d : E) :
    secondDirectionalDerivative (fun y ↦ expandingPolynomialBump z r v δ y t) x d =
      t * Real.exp (-δ * t) *
        (24 * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ * ⟪x - z, d⟫ ^ 2 -
          6 * (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 2 * ‖d‖ ^ 2) := by
  rw [expandingPolynomialBump_eq_ballBump z hradius, secondDirectionalDerivative_const_mul,
    secondDirectionalDerivative_polynomialBallBump, Real.sq_sqrt hradius]

omit [InnerProductSpace ℝ E] in
/-- The activated profile is nonnegative at nonnegative time. -/
theorem expandingPolynomialBump_nonneg (z : E) (r v δ : ℝ) (x : E) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ expandingPolynomialBump z r v δ x t := by
  unfold expandingPolynomialBump
  positivity

omit [InnerProductSpace ℝ E] in
/-- The profile vanishes whenever the squared distance reaches its squared
support radius. -/
theorem expandingPolynomialBump_eq_zero (z : E) {r v δ t : ℝ} (x : E)
    (houtside : r ^ 2 + v * t ≤ ‖x - z‖ ^ 2) :
    expandingPolynomialBump z r v δ x t = 0 := by
  simp [expandingPolynomialBump, posPart_eq_zero.mpr (sub_nonpos.mpr houtside)]

omit [InnerProductSpace ℝ E] in
/-- A bound on time and the squared support radius bounds the whole activated
profile, independently of the spatial point. -/
theorem expandingPolynomialBump_le (z : E) {r R v δ t s : ℝ} (x : E)
    (hδ : 0 ≤ δ) (ht : 0 ≤ t) (hts : t ≤ s)
    (hradius : r ^ 2 + v * t ≤ R ^ 2) :
    expandingPolynomialBump z r v δ x t ≤ s * R ^ 6 := by
  have hgap : (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ≤ R ^ 2 :=
    sup_le ((sub_le_self _ (sq_nonneg _)).trans hradius) (sq_nonneg R)
  have hcube : (r ^ 2 + v * t - ‖x - z‖ ^ 2)⁺ ^ 3 ≤ R ^ 6 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (posPart_nonneg _) hgap 3
  have hexp : Real.exp (-δ * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) ht)
  have hfactor : t * Real.exp (-δ * t) ≤ s := by
    exact (mul_le_mul_of_nonneg_left hexp ht).trans (by simpa using hts)
  exact mul_le_mul hfactor hcube (pow_nonneg (posPart_nonneg _) _) (ht.trans hts)

end PDE.Analysis
