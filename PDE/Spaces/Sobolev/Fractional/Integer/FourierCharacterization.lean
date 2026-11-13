/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.Complex
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight

/-!
# Fourier characterization of complex integer Sobolev spaces

For every nonnegative integer `k`, a complex `L²` function has square-integrable weak
derivatives through order `k` exactly when `(1 + ‖ξ‖^k) 𝓕u` belongs to `L²`.
One positive constant gives both norm bounds. The Sobolev norm is the Hilbert
sum of the complex weak-derivative norms.

This is Evans §5.8.5, Theorem 8, in Mathlib's unitary Fourier convention with phase
`exp (-2π i ⟪x, ξ⟫)`. No integrability beyond `L²`, real-valuedness, or classical smoothness is
assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, pp. 297-298, with the Fourier transform of
  §4.3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory SobolevSpace.GraphSpace
open scoped FourierTransform

namespace SobolevSpace.Fractional

variable {n k : ℕ}

/-- Evans §5.8.5, Theorem 8(i): a complex `u ∈ L²(ℝ^n)` is the base function of an element of
complex `H^k(ℝ^n)` if and only if `(1 + ‖ξ‖^k) 𝓕u` lies in `L²`. -/
theorem exists_complexWkSpace_iff_memLp_integerWeightedFourier
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    (∃ U : ComplexWkSpaceOn n k Set.univ, U.1 (baseIndex n k) =ᵐ[volume] u) ↔
      MemLp (integerWeightedFourier k u) 2 volume :=
  (exists_complexWkSpace_iff_memSobolev u).trans
    (memSobolev_iff_memLp_integerWeightedFourier k u)

end SobolevSpace.Fractional

namespace SobolevSpace.GraphSpace.ComplexWkSpaceOn

open SobolevSpace.Fractional

variable {n k : ℕ}

/-- The literal weighted Fourier transform of the base function of a complex Sobolev graph. -/
def weightedFourier (U : ComplexWkSpaceOn n k Set.univ) :
    Lp ℂ 2 (volume : Measure (ℝ^n)) :=
  integerWeightedFourierLp (ofComplexWkSpace U)

/-- The weighted transform represents `(1 + ‖ξ‖^k) 𝓕u` for the base function. -/
theorem coeFn_weightedFourier (U : ComplexWkSpaceOn n k Set.univ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hu : U.1 (baseIndex n k) =ᵐ[volume] u) :
    (U.weightedFourier : ℝ^n → ℂ) =ᵐ[volume] integerWeightedFourier k u := by
  have heq : toL2Fun (Nat.cast_nonneg k) (ofComplexWkSpace U) = u :=
    Lp.ext ((coeFn_toL2Fun_ofComplexWkSpace U).trans hu)
  simpa only [weightedFourier, heq] using coeFn_integerWeightedFourierLp (ofComplexWkSpace U)

/-- The weighted Fourier norm is controlled by the complex weak-derivative norm. -/
theorem norm_weightedFourier_le (U : ComplexWkSpaceOn n k Set.univ) :
    ‖U.weightedFourier‖ ≤ (2 * ofComplexWkSpaceNormBound n k) * ‖U‖ := by
  calc
    _ ≤ 2 * ‖ofComplexWkSpace U‖ := norm_integerWeightedFourierLp_le _
    _ ≤ 2 * (ofComplexWkSpaceNormBound n k * ‖U‖) :=
      mul_le_mul_of_nonneg_left (norm_ofComplexWkSpace_le U) (by norm_num)
    _ = _ := by ring

/-- The complex weak-derivative norm is controlled by the literal weighted Fourier norm. -/
theorem norm_le_weightedFourier (U : ComplexWkSpaceOn n k Set.univ) :
    ‖U‖ ≤ (2 * toWkpSpaceNormBound n k * 2 ^ k) * ‖U.weightedFourier‖ := by
  calc
    ‖U‖ = ‖toComplexWkSpace (ofComplexWkSpace U)‖ := by
      rw [toComplexWkSpace_ofComplexWkSpace]
    _ ≤ 2 * toWkpSpaceNormBound n k * ‖ofComplexWkSpace U‖ :=
      norm_toComplexWkSpace_le _
    _ ≤ 2 * toWkpSpaceNormBound n k * (2 ^ k * ‖U.weightedFourier‖) :=
      mul_le_mul_of_nonneg_left (norm_le_integerWeightedFourierLp _) (by
        exact mul_nonneg (by norm_num) toWkpSpaceNormBound_nonneg)
    _ = _ := by ring

end SobolevSpace.GraphSpace.ComplexWkSpaceOn

namespace SobolevSpace.Fractional

/-- Evans §5.8.5, Theorem 8(ii): there is `C > 0` such that
`C⁻¹ ‖U‖ ≤ ‖(1 + ‖ξ‖^k) 𝓕u‖ ≤ C ‖U‖` for every `U` in complex `H^k(ℝ^n)` with base function `u`. -/
theorem exists_complex_fourier_norm_comparison (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ComplexWkSpaceOn n k Set.univ,
      C⁻¹ * ‖U‖ ≤ ‖U.weightedFourier‖ ∧ ‖U.weightedFourier‖ ≤ C * ‖U‖ := by
  let A := 2 * toWkpSpaceNormBound n k * 2 ^ k
  let B := 2 * ofComplexWkSpaceNormBound n k
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num)
    toWkpSpaceNormBound_nonneg) (by positivity)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (ofComplexWkSpaceNormBound_nonneg n k)
  refine ⟨1 + A + B, by positivity, fun U ↦ ⟨?_, ?_⟩⟩
  · apply (inv_mul_le_iff₀ (by positivity : 0 < 1 + A + B)).mpr
    exact U.norm_le_weightedFourier.trans
      (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A + B) (norm_nonneg _))
  · exact U.norm_weightedFourier_le.trans
      (mul_le_mul_of_nonneg_right (by linarith : B ≤ 1 + A + B) (norm_nonneg _))

end SobolevSpace.Fractional
