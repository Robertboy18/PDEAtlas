/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import CAS.ExactTactic

/-!
# H¹ control of the coupled H² production

For the coupled equation, the differentiated Hilbert pair contains the output
vorticity itself. The highest velocity derivative is therefore controlled by
the H² energy, while its coefficient needs only H¹. Equal spatial and amplitude
rescaling rates contribute a separate linear term.

The jet estimate `norm_integral_coupled_rescaled_jet_production_le` uses continuous lower
derivatives and L² highest derivatives, and the classical version
`norm_integral_coupled_rescaled_sobolev_production_le` follows from it. For smooth
trajectories, `CoupledEvolution` identifies this production with the time derivative of
the H² energy.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory PDE.Analysis
open scoped ENNReal

namespace DeGregorio

private theorem coupled_production_scalar_bound
    {d a b c : ℝ} (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    3 * ((d + a + b) * a * a) + (d + a + b) * b * b +
        (d + a + b) * c * c + 2 * ((a + b) * b * b) +
        2 * ((a + b) * c * c) + 2 * ((b + c) * b * c) ≤
      (3 * d + 8 * (a + b)) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h₀ : 3 * ((d + a + b) * a * a) + (d + a + b) * b * b +
      (d + a + b) * c * c ≤ 3 * (d + a + b) * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := add_nonneg (add_nonneg hd ha) hb
    cas using h
  have h₁ : 2 * ((a + b) * b * b) + 2 * ((a + b) * c * c) ≤
      2 * (a + b) * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := add_nonneg ha hb
    cas using h
  have h₂ : 2 * (b + c) * c ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    have h := two_mul_le_add_sq b c
    cas using h
  have hmajor := add_le_add (add_le_add h₀ h₁) (mul_le_mul_of_nonneg_left h₂ hb)
  have hcoef : 3 * (d + a + b) + 2 * (a + b) + 3 * b ≤ 3 * d + 8 * (a + b) := by
    cas using ha
  have hfinal := mul_le_mul_of_nonneg_right hcoef
    (add_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c))
  calc
    _ ≤ (3 * (d + a + b) + 2 * (a + b) + 3 * b) * (a ^ 2 + b ^ 2 + c ^ 2) := by
      cas using hmajor
    _ ≤ _ := hfinal

/-- The coupled production estimate depends only on the Hilbert pairs and
the three one-dimensional Sobolev bounds. In particular, the highest
derivatives `r` and `s` need only be L² functions. -/
theorem norm_integral_coupled_rescaled_jet_production_le
    {w q r h d s : ℝ → ℝ} (ρ : ℝ)
    (hw : Continuous w) (hq : Continuous q) (hh : Continuous h)
    (hpair : IsHilbertPair w h) (hpair₁ : IsHilbertPair q d) (hpair₂ : IsHilbertPair r s)
    (hW : ∀ x, ‖w x‖ ≤ lpNorm w 2 volume + lpNorm q 2 volume)
    (hQ : ∀ x, ‖q x‖ ≤ lpNorm q 2 volume + lpNorm r 2 volume)
    (hH : ∀ x, ‖h x‖ ≤ lpNorm w 2 volume + lpNorm q 2 volume) :
    ‖∫ x,
      3 * (ρ + h x) * w x ^ 2 + (ρ + h x) * q x ^ 2 -
        (ρ + h x) * r x ^ 2 + 2 * d x * w x * q x +
        2 * s x * w x * r x + 2 * d x * q x * r x‖ ≤
      (3 * |ρ| + 8 * (lpNorm w 2 volume + lpNorm q 2 volume)) *
        ((∫ x, w x ^ 2) + (∫ x, q x ^ 2) + ∫ x, r x ^ 2) := by
  let k := fun x ↦ ρ + h x
  have hwLp := hpair.memLp_left
  have hqLp := hpair₁.memLp_left
  have hrLp := hpair₂.memLp_left
  let a := lpNorm w 2 volume
  let b := lpNorm q 2 volume
  let c := lpNorm r 2 volume
  have hk : Continuous k := continuous_const.add hh
  have hK (x : ℝ) : ‖k x‖ ≤ |ρ| + a + b := by
    apply (norm_add_le ρ (h x)).trans
    simpa only [Real.norm_eq_abs, add_assoc, add_comm, add_left_comm] using
      add_le_add_left (hH x) |ρ|
  have hAB : 0 ≤ |ρ| + a + b :=
    add_nonneg (add_nonneg (abs_nonneg ρ) lpNorm_nonneg) lpNorm_nonneg
  have hab : 0 ≤ a + b := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have hbc : 0 ≤ b + c := add_nonneg lpNorm_nonneg lpNorm_nonneg
  have h₀ := abs_integral_triple_mul_le_of_bound hk.aestronglyMeasurable hAB hK hwLp hwLp
  have h₁ := abs_integral_triple_mul_le_of_bound hk.aestronglyMeasurable hAB hK hqLp hqLp
  have h₂ := abs_integral_triple_mul_le_of_bound hk.aestronglyMeasurable hAB hK hrLp hrLp
  have h₃ := abs_integral_triple_mul_le_of_bound hw.aestronglyMeasurable hab hW
    hpair₁.memLp_right hqLp
  have h₄ := abs_integral_triple_mul_le_of_bound hw.aestronglyMeasurable hab hW
    hpair₂.memLp_right hrLp
  have h₅ := abs_integral_triple_mul_le_of_bound hq.aestronglyMeasurable hbc hQ
    hpair₁.memLp_right hrLp
  change |∫ x, k x * w x * w x| ≤ (|ρ| + a + b) * a * a at h₀
  change |∫ x, k x * q x * q x| ≤ (|ρ| + a + b) * b * b at h₁
  change |∫ x, k x * r x * r x| ≤ (|ρ| + a + b) * c * c at h₂
  rw [show lpNorm d 2 volume = b from congrArg ENNReal.toReal hpair₁.eLpNorm_eq] at h₃ h₅
  rw [show lpNorm s 2 volume = c from congrArg ENNReal.toReal hpair₂.eLpNorm_eq] at h₄
  have hHtop := memLp_top_of_bound (μ := volume) hk.aestronglyMeasurable (|ρ| + a + b)
    (Eventually.of_forall hK)
  have hWtop := memLp_top_of_bound (μ := volume) hw.aestronglyMeasurable (a + b)
    (Eventually.of_forall hW)
  have hQtop := memLp_top_of_bound (μ := volume) hq.aestronglyMeasurable (b + c)
    (Eventually.of_forall hQ)
  have hI₀ := (hHtop.mul (r := 2) hwLp).integrable_mul hwLp
  have hI₁ := (hHtop.mul (r := 2) hqLp).integrable_mul hqLp
  have hI₂ := (hHtop.mul (r := 2) hrLp).integrable_mul hrLp
  have hI₃ := (hWtop.mul (r := 2) hpair₁.memLp_right).integrable_mul hqLp
  have hI₄ := (hWtop.mul (r := 2) hpair₂.memLp_right).integrable_mul hrLp
  have hI₅ := (hQtop.mul (r := 2) hpair₁.memLp_right).integrable_mul hrLp
  have halgebra : (fun x ↦
      3 * (ρ + h x) * w x ^ 2 + (ρ + h x) * q x ^ 2 -
        (ρ + h x) * r x ^ 2 + 2 * d x * w x * q x +
        2 * s x * w x * r x + 2 * d x * q x * r x) =
      fun x ↦ 3 * (k x * w x * w x) + k x * q x * q x - k x * r x * r x +
        2 * (w x * d x * q x) + 2 * (w x * s x * r x) +
        2 * (q x * d x * r x) := by
    funext x
    dsimp [k]
    cas
  simp only [Pi.mul_def] at hI₀ hI₁ hI₂ hI₃ hI₄ hI₅
  have hsplit : ∫ x, (3 * (k x * w x * w x) + k x * q x * q x - k x * r x * r x +
        2 * (w x * d x * q x) + 2 * (w x * s x * r x) + 2 * (q x * d x * r x)) =
      3 * (∫ x, k x * w x * w x) + (∫ x, k x * q x * q x) - (∫ x, k x * r x * r x) +
        2 * (∫ x, w x * d x * q x) + 2 * (∫ x, w x * s x * r x) +
        2 * ∫ x, q x * d x * r x := by
    rw [integral_add, integral_add, integral_add, integral_sub, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul] <;> fun_prop
  have hsq : (∫ x, w x ^ 2) + (∫ x, q x ^ 2) + ∫ x, r x ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
    rw [integral_sq_eq_eLpNorm_toReal_sq hwLp, integral_sq_eq_eLpNorm_toReal_sq hqLp,
      integral_sq_eq_eLpNorm_toReal_sq hrLp]
    rfl
  rw [halgebra, hsplit, hsq, Real.norm_eq_abs]
  -- the triangle inequality for the six terms, then the six bounds and the scalar estimate
  refine ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _)
      le_rfl)) le_rfl)) le_rfl)) le_rfl)).trans (le_trans ?_ (coupled_production_scalar_bound
        (d := |ρ|) (a := a) (b := b) (c := c) (abs_nonneg ρ) lpNorm_nonneg lpNorm_nonneg))
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  gcongr

/-- In the classical coupled equation, H¹ controls the H² production.
A common spatial and amplitude rescaling rate contributes at most three
times its magnitude. -/
theorem norm_integral_coupled_rescaled_sobolev_production_le {w u : ℝ → ℝ} (ρ : ℝ)
    (hw : ContDiff ℝ 3 w) (hsuppw : HasCompactSupport w)
    (hu : ContDiff ℝ 3 u) (hpair : IsHilbertPair w (deriv u)) :
    ‖∫ x,
      3 * (ρ + deriv u x) * w x ^ 2 + (ρ + deriv u x) * deriv w x ^ 2 -
        (ρ + deriv u x) * deriv (deriv w) x ^ 2 +
        2 * deriv (deriv u) x * w x * deriv w x +
        2 * deriv (deriv (deriv u)) x * w x * deriv (deriv w) x +
        2 * deriv (deriv u) x * deriv w x * deriv (deriv w) x‖ ≤
      (3 * |ρ| + 8 * (lpNorm w 2 volume + lpNorm (deriv w) 2 volume)) *
        ((∫ x, w x ^ 2) + (∫ x, deriv w x ^ 2) + ∫ x, deriv (deriv w) x ^ 2) := by
  have hh : ContDiff ℝ 2 (deriv u) := hu.deriv'
  have hq : ContDiff ℝ 1 (deriv w) := (hw.deriv' (n := 2)).of_le (by norm_num)
  have hpair₁ := hpair.deriv_of_contDiff_two hh.continuous
    (hw.of_le (by norm_num)) hsuppw
  have hpair₂ := hpair₁.deriv_of_contDiff_two (hh.continuous_deriv (by norm_num))
    (hw.deriv' (n := 2)) hsuppw.deriv
  exact norm_integral_coupled_rescaled_jet_production_le ρ hw.continuous hq.continuous
    hh.continuous hpair hpair₁ hpair₂
    (SobolevSpace.norm_apply_le_eLpNorm_toReal_add_deriv
      (hw.of_le (by norm_num)) (by norm_num) hpair.memLp_left hpair₁.memLp_left)
    (SobolevSpace.norm_apply_le_eLpNorm_toReal_add_deriv
      hq (by norm_num) hpair₁.memLp_left hpair₂.memLp_left)
    (hpair.norm_le_eLpNorm_add_deriv hh.continuous (hw.of_le (by norm_num)) hsuppw)

end DeGregorio
