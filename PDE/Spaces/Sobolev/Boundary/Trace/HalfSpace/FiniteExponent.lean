/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Spaces.Sobolev.Boundary.Trace.HalfLine.FiniteExponent
import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral

/-!
# Finite-exponent trace estimate on the upper half-space

We integrate the one-dimensional finite-exponent endpoint estimate over
tangential slices. For a compactly supported `C¹` function on `ℝ^(n+1)`, we
prove

`∫_{ℝ^n} |γf|^p ≤ (p - 1) ∫_{ℝ^(n+1)₊} |f|^p +
  ∫_{ℝ^(n+1)₊} |∂ₙf|^p`

for every real exponent `p ≥ 1`. This is the flat-boundary estimate (1) in step 1 of the proof
of Evans §5.5, Theorem 1, with explicit constants and with only the normal derivative on the
right; compact support takes the place of Evans's cutoff `ζ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, proof of Theorem 1, step 1, estimate (1), p. 272.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.HalfSpace

open MeasureTheory Set

variable {n : ℕ}

private theorem integral_boundary_rpow_le_of_slice_bounds
    (F G : ℝ^n × ℝ → ℝ) {p : ℝ}
    (hBoundary : Integrable (fun y : ℝ^n ↦ |F (y, 0)| ^ p))
    (hF : Integrable (fun z ↦ |F z| ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure))
    (hG : Integrable (fun z ↦ |G z| ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure))
    (hSlice : ∀ y : ℝ^n,
      |F (y, 0)| ^ p ≤
        (p - 1) * (∫ t, |F (y, t)| ^ p ∂positiveNormalMeasure) +
          (∫ t, |G (y, t)| ^ p ∂positiveNormalMeasure)) :
    (∫ y : ℝ^n, |F (y, 0)| ^ p) ≤
      (p - 1) * (∫ z, |F z| ^ p
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) +
        (∫ z, |G z| ^ p
          ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) := by
  have hFinner : Integrable
      (fun y : ℝ^n ↦ ∫ t, |F (y, t)| ^ p ∂positiveNormalMeasure) :=
    hF.integral_prod_left
  have hGinner : Integrable
      (fun y : ℝ^n ↦ ∫ t, |G (y, t)| ^ p ∂positiveNormalMeasure) :=
    hG.integral_prod_left
  calc
    (∫ y : ℝ^n, |F (y, 0)| ^ p) ≤
        ∫ y : ℝ^n,
          ((p - 1) * (∫ t, |F (y, t)| ^ p ∂positiveNormalMeasure) +
            (∫ t, |G (y, t)| ^ p ∂positiveNormalMeasure)) :=
      integral_mono hBoundary (hFinner.const_mul (p - 1) |>.add hGinner) hSlice
    _ = (p - 1) *
          (∫ y : ℝ^n, ∫ t, |F (y, t)| ^ p ∂positiveNormalMeasure) +
          (∫ y : ℝ^n, ∫ t, |G (y, t)| ^ p ∂positiveNormalMeasure) := by
      rw [integral_add (hFinner.const_mul (p - 1)) hGinner,
        integral_const_mul]
    _ = (p - 1) * (∫ z, |F z| ^ p
          ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) +
          (∫ z, |G z| ^ p
            ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) := by
      rw [integral_prod _ hF, integral_prod _ hG]

private theorem smoothBoundaryValue_rpow_le_slice_energy
    {f : ℝ^(n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 1 ≤ p) (y : ℝ^n) :
    |smoothBoundaryValue f y| ^ p ≤
      (p - 1) *
        (∫ t, |normalSlice f y t| ^ p ∂positiveNormalMeasure) +
        (∫ t, |normalDerivativeInSplit f (y, t)| ^ p
          ∂positiveNormalMeasure) := by
  have h := Trace.HalfLine.endpoint_abs_rpow_le_integral_add_integral
    (normalSlice_contDiff hf y) (normalSlice_hasCompactSupport hfc y) hp
  simp_rw [deriv_normalSlice hf y] at h
  simpa [smoothBoundaryValue, positiveNormalMeasure] using h

/--
Finite-exponent trace estimate: for a compactly supported `C¹` function `f` on `ℝ^(n+1)` and
real `p ≥ 1`, the integral over `ℝ^n` of `|smoothBoundaryValue f|^p` is at most
`(p - 1) ∫ |f|^p + ∫ |∂ₙf|^p`, both integrals over the upper half-space.
-/
theorem smooth_boundary_integral_abs_rpow_le_upper_energy
    {f : ℝ^(n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 1 ≤ p) :
    (∫ y : ℝ^n, |smoothBoundaryValue f y| ^ p) ≤
      (p - 1) *
        (∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
          |f x| ^ p) +
        (∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
          |(∂[Fin.last n] f) x| ^ p) := by
  have hp_ne : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hBoundary : Integrable
      (fun y : ℝ^n ↦ |smoothBoundaryValue f y| ^ p) :=
    (smoothBoundaryValue_continuous (n := n) hf.continuous).abs.rpow_const
      (fun _ ↦ Or.inr (le_trans (by norm_num) hp))
      |>.integrable_of_hasCompactSupport
        ((smoothBoundaryValue_hasCompactSupport (n := n) hfc).abs.rpow_const hp_ne)
  have hF : Integrable
      (fun z : ℝ^n × ℝ ↦ |normalSlice f z.1 z.2| ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalSlice_product_continuous (n := n) hf.continuous).abs.rpow_const
      (fun _ ↦ Or.inr (le_trans (by norm_num) hp))
      |>.integrable_of_hasCompactSupport
        ((normalSlice_product_hasCompactSupport (n := n) hfc).abs.rpow_const hp_ne)
  have hG : Integrable
      (fun z : ℝ^n × ℝ ↦ |normalDerivativeInSplit f z| ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalDerivativeInSplit_continuous (n := n) hf).abs.rpow_const
      (fun _ ↦ Or.inr (le_trans (by norm_num) hp))
      |>.integrable_of_hasCompactSupport
        ((normalDerivativeInSplit_hasCompactSupport (n := n) hfc).abs.rpow_const hp_ne)
  have hproduct := integral_boundary_rpow_le_of_slice_bounds
    (n := n)
    (fun z ↦ normalSlice f z.1 z.2)
    (normalDerivativeInSplit f)
    hBoundary hF hG
    (smoothBoundaryValue_rpow_le_slice_energy hf hfc hp)
  have hF_eq :
      (∫ z : ℝ^n × ℝ, |normalSlice f z.1 z.2| ^ p
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) =
        ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
          |f x| ^ p := by
    simpa [normalSlice] using
      (integral_joinTangentialNormal_eq_integral_upper
        (n := n) (g := fun x ↦ |f x| ^ p))
  have hG_eq :
      (∫ z : ℝ^n × ℝ, |normalDerivativeInSplit f z| ^ p
        ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) =
        ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩),
          |(∂[Fin.last n] f) x| ^ p := by
    simpa [normalDerivativeInSplit] using
      (integral_joinTangentialNormal_eq_integral_upper
        (n := n) (g := fun x ↦ |(∂[Fin.last n] f) x| ^ p))
  rw [hF_eq, hG_eq] at hproduct
  exact hproduct

end Trace.HalfSpace
end SobolevSpace
