/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.PlanarKernelBalls

/-!
# A rational bound of the velocity kernel on a box about its pole

`velocityBoxUpper A B` is a rational upper bound of
`A log(1 + B²/A²) + 2 B arctan(A/B)` (the closed form `velocityBoxIntegral A B` of
`PotentialTheory.Planar`) for positive rationals `A`, `B`, from FloatLib's logarithm and arctangent
enclosures at rational points (`logAt`, `atanAt`) with an accuracy of about `2⁻⁶⁴`
(`log_mul_add_arctan_le_velocityBoxUpper`). With `lintegral_velocityBox_le` it bounds the integral
of `|s₂| / (2|s|²)` over the box `[-A, A] × [-B, B]`, and with the arguments exchanged that of
`|s₁| / (2|s|²)`.

## Main definitions

* `velocityBoxUpper`: the rational upper bound of `A log(1 + B²/A²) + 2 B arctan(A/B)` from the
  upper endpoints of FloatLib's enclosures at `64` bits.

## Main results

* `log_mul_add_arctan_le_velocityBoxUpper`: for positive rationals `A`, `B`,
  `A log(1 + B²/A²) + 2 B arctan(A/B) ≤ velocityBoxUpper A B`.

## References

* R. J. George, W. Adkisson and A. Anandkumar, "FloatLib: Verified Floating-Point Arithmetic in
  Lean", arXiv:2609.19352, 2026.
  <https://arxiv.org/abs/2609.19352>
  <https://github.com/lean-dojo/FloatLib>
-/

@[expose] public section

namespace CAS.Numerics.PlanarKernel

/-- A rational upper bound of `A log(1 + B²/A²) + 2 B arctan(A/B)` for positive `A`, `B`, from the
upper endpoints of FloatLib's enclosures at `64` bits. -/
def velocityBoxUpper (A B : ℚ) : ℚ :=
  A * (logAt 64 (1 + B ^ 2 / A ^ 2)).hi + 2 * B * (atanAt 64 (A / B)).hi

/-- `velocityBoxUpper` bounds `A log(1 + B²/A²) + 2 B arctan(A/B)` from above. -/
theorem log_mul_add_arctan_le_velocityBoxUpper {A B : ℚ} (hA : 0 < A) (hB : 0 < B) :
    (A : ℝ) * Real.log (1 + (B : ℝ) ^ 2 / (A : ℝ) ^ 2) + 2 * B * Real.arctan ((A : ℝ) / B) ≤
      velocityBoxUpper A B := by
  have hq : (0 : ℚ) ≤ 1 + B ^ 2 / A ^ 2 := by positivity
  have hlog := (logAt_sound 64 hq).2
  have hatan := (atanAt_sound 64 (A / B)).2
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  push_cast at hlog hatan
  unfold velocityBoxUpper
  push_cast
  have h1 := mul_le_mul_of_nonneg_left hlog hA'.le
  have h2 := mul_le_mul_of_nonneg_left hatan (by positivity : (0 : ℝ) ≤ 2 * B)
  linarith

end CAS.Numerics.PlanarKernel
