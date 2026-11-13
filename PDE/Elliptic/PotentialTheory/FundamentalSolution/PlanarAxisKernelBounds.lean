/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarAxisKernel
public import PDE.Numerics.Certificates.PlanarKernelBalls
public import CAS.CEGA
public meta import PDE.Numerics.Certificates.PlanarKernelBalls

/-!
# Certified values of `J₁` and `J₂`

The integrals `J₁(B) = axisStripIntegral (1/B)` and `J₂(B) = axisSquareIntegral (1/B)` of Chen and
Hou II, Supplementary material II, Section 6.2, are differences of corner sums of the gradient
kernel `π ∂₂Φ` (`integral_rectangle_axisKernel`), each enclosed by the balls of
`integral_rectangle_gradientKernel_one_mem`. The two ball checks behind `J₂(50/369) ≥ 2` are
decided by `cega [fast]`, the certified evaluation tactic of SymLean (our verified computer
algebra system); the balls are built from FloatLib's rational arctangent and logarithm
enclosures. With `antitoneOn_axisSquareIntegral_div_sqrt` this bound makes `√B J₂(B)` increasing
on `(0, 50/369]`; since `e² > 7.38`, the supplement's condition `z ≤ h e^{-2}` lies inside.

## Main results

* `axisStripIntegral_mem_of_check`, `axisSquareIntegral_mem_of_check`: enclosures of `J₁` and `J₂`
  at a rational side `L ≥ 0` from two ball checks.
* `two_le_axisSquareIntegral`: `J₂(50/369) ≥ 2` (value `2.0283259`), from one check.
* `sqrt_mul_axisSquareIntegral_le_of_le`: for `0 < t ≤ z` and `7.38 z ≤ h`,
  `√t J₂(t/h) ≤ √z J₂(z/h)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II, Section 6.2.
  <https://arxiv.org/abs/2305.05660v3>
* R. J. George, W. Adkisson and A. Anandkumar, "FloatLib: Verified Floating-Point Arithmetic in
  Lean", arXiv:2609.19352, 2026.
  <https://arxiv.org/abs/2609.19352>, code: <https://github.com/lean-dojo/FloatLib>
-/

@[expose] public section

noncomputable section

open PDE.Analysis CAS.Numerics CAS.Numerics.PlanarKernel

namespace PotentialTheory.Planar

/-- `∫_{[a,b] × [c,d]} π ∂₂Φ` is the corner sum of `gradientOneCorner`. -/
theorem cornerSum_gradientOneCorner_mem {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d)
    {P bits : ℕ} {lo hi : ℚ}
    (h : IntervalBalls.checkBoundsCertain P (lo, hi) (gradientZeroBall P bits c d a b) = true) :
    (lo : ℝ) ≤ cornerSum gradientOneCorner a b c d ∧ cornerSum gradientOneCorner a b c d ≤ hi := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
  have e := integral_rectangle_gradientKernel_one_eq_cornerSum hab' hcd'
  have := integral_rectangle_gradientKernel_one_mem hab hcd h
  rw [e] at this
  exact this

/-- **`J₁` at a rational side** from two ball checks:
`J₁ = Σ_{[1,2] × [0,L]} - Σ_{[-1,0] × [0,L]}` of `gradientOneCorner`. -/
theorem axisStripIntegral_mem_of_check {L : ℚ} (hL : 0 ≤ L) {P bits : ℕ} {lo₁ hi₁ lo₂ hi₂ : ℚ}
    (h₁ : IntervalBalls.checkBoundsCertain P (lo₁, hi₁) (gradientZeroBall P bits 0 L 1 2) = true)
    (h₂ : IntervalBalls.checkBoundsCertain P (lo₂, hi₂) (gradientZeroBall P bits 0 L (-1) 0) =
      true) :
    ((lo₁ - hi₂ : ℚ) : ℝ) ≤ axisStripIntegral L ∧
      axisStripIntegral L ≤ ((hi₁ - lo₂ : ℚ) : ℝ) := by
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have e := integral_rectangle_axisKernel (a := -1) (b := 0) (c := 0) (d := L) (by norm_num) hL'
  have b₁ := cornerSum_gradientOneCorner_mem (a := 1) (b := 2) (by norm_num) hL h₁
  have b₂ := cornerSum_gradientOneCorner_mem (a := -1) (b := 0) (by norm_num) hL h₂
  rw [axisStripIntegral, e]
  push_cast at b₁ b₂ ⊢
  norm_num at b₁ b₂ ⊢
  constructor <;> linarith [b₁.1, b₁.2, b₂.1, b₂.2]

/-- **`J₂` at a rational side** from two ball checks:
`J₂ = Σ_{[2,L+2] × [0,L]} - Σ_{[0,L]²}` of `gradientOneCorner`. -/
theorem axisSquareIntegral_mem_of_check {L : ℚ} (hL : 0 ≤ L) {P bits : ℕ} {lo₁ hi₁ lo₂ hi₂ : ℚ}
    (h₁ : IntervalBalls.checkBoundsCertain P (lo₁, hi₁)
      (gradientZeroBall P bits 0 L 2 (L + 2)) = true)
    (h₂ : IntervalBalls.checkBoundsCertain P (lo₂, hi₂) (gradientZeroBall P bits 0 L 0 L) =
      true) :
    ((lo₁ - hi₂ : ℚ) : ℝ) ≤ axisSquareIntegral L ∧
      axisSquareIntegral L ≤ ((hi₁ - lo₂ : ℚ) : ℝ) := by
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have e := integral_rectangle_axisKernel (a := 0) (b := L) (c := 0) (d := L) hL' hL'
  have b₁ := cornerSum_gradientOneCorner_mem (a := 2) (b := L + 2) (by linarith) hL h₁
  have b₂ := cornerSum_gradientOneCorner_mem (a := 0) (b := L) hL hL h₂
  rw [axisSquareIntegral, e]
  push_cast at b₁ b₂ ⊢
  norm_num at b₁ b₂ ⊢
  constructor <;> linarith [b₁.1, b₁.2, b₂.1, b₂.2]

/-- The ball checks behind `two_le_axisSquareIntegral`, at the side `L₀ = 369/50`. -/
def axisSquareThresholdCheck : Bool :=
  IntervalBalls.checkBoundsCertain 200 (-214864988 / 10 ^ 8, -214864986 / 10 ^ 8)
      (gradientZeroBall 200 200 0 (369 / 50) 2 (369 / 50 + 2)) &&
    IntervalBalls.checkBoundsCertain 200 (-417697578 / 10 ^ 8, -417697576 / 10 ^ 8)
      (gradientZeroBall 200 200 0 (369 / 50) 0 (369 / 50))

/-- The two ball checks enclosing the corner sums of `J₂` at the side `L₀ = 369/50` succeed. -/
theorem axisSquareThresholdCheck_eq : axisSquareThresholdCheck = true := by
  cega [fast]

/-- **`J₂(50/369) ≥ 2`** (value `2.0283259`). -/
theorem two_le_axisSquareIntegral : 2 ≤ axisSquareIntegral (369 / 50) := by
  have h := axisSquareThresholdCheck_eq
  simp only [axisSquareThresholdCheck, Bool.and_eq_true] at h
  have := (axisSquareIntegral_mem_of_check (L := 369 / 50) (by norm_num) h.1 h.2).1
  push_cast at this
  norm_num at this ⊢
  linarith

/-- **The supremum of `x₁^{1/2} J₂(x₁/h)` over a cell `(0, z]`**, Supp. 6.2: for `0 < t ≤ z`
and `7.38 z ≤ h`, `√t J₂(t/h) ≤ √z J₂(z/h)`. -/
theorem sqrt_mul_axisSquareIntegral_le_of_le {h t z : ℝ} (ht : 0 < t)
    (htz : t ≤ z) (hz : z * (369 / 50) ≤ h) :
    √t * axisSquareIntegral (h / t) ≤ √z * axisSquareIntegral (h / z) :=
  have hh : 0 < h := by linarith
  sqrt_mul_axisSquareIntegral_le (by norm_num) (by exact_mod_cast two_le_axisSquareIntegral) hh ht
    htz hz

end PotentialTheory.Planar
