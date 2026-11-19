/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.SpaceTime.Blocks
public import PDE.Numerics.Certificates.TensorSplineNodes.Field

/-!
# Block fields with tensor B-spline coefficients

The spatial coefficients of a block field can be multilevel tensor B-spline fields of the node
engine (`TensorSpline.field`) that share their knots and modes and differ in their coefficient
tensors. The field is linear in the coefficient tensor (`TensorSpline.field_withCoeff_sum`), so
every rational combination of the coefficients of a block, in particular the time-derivative
coefficients `dₘⱼ = kₘ⁻¹ ∑ᵢ D i j cₘᵢ` for a rational time scale `kₘ`
(`BlockField.derivCoeff_eq_splineField`) and the end values `∑ᵢ bᵢ(hi) cₘᵢ` used by the
continuity check, is again a field of the engine with an exact rational coefficient tensor. The
engine then certifies its corner jets; the time layer needs no evaluation of its own.

## Main definitions

* `TensorSpline.Level.withCoeff`: the level with the knots and modes of `lv` and the coefficient
  tensor `a`.
* `SpaceTime.splineField`: the tensor B-spline field with the knots and modes of `lv` and given
  coefficient tensors of its levels.

## Main results

* `TensorSpline.field_withCoeff_sum`: a rational combination of fields with common knots and
  modes is the field of the combined coefficient tensors.
* `SpaceTime.BlockField.derivCoeff_eq_splineField`: if the coefficients of a block are spline
  fields and the time scale is rational, the derivative coefficient `dₘⱼ = k⁻¹ ∑ᵢ D i j cₘᵢ` is
  the spline field with the combined rational coefficient tensor.
-/

@[expose] public section

namespace CAS.Numerics

open Finset

namespace TensorSpline

/-- The level with the knots and modes of `lv` and the coefficient tensor `a`. -/
def Level.withCoeff (lv : Level) (a : ℕ → ℕ → ℚ) : Level :=
  { lv with coeff := a }

/-- **Linearity in the coefficients.** A rational combination of fields with common knots and
modes is the field of the combined coefficient tensors. -/
theorem field_withCoeff_sum {ι : Type*} (s : Finset ι) (q : ι → ℚ) (n L : ℕ) (lv : ℕ → Level)
    (a : ι → ℕ → ℕ → ℕ → ℚ) (wt : ℝ → ℝ) (x y : ℝ) :
    field n L (fun m ↦ (lv m).withCoeff fun i j ↦ ∑ k ∈ s, q k * a k m i j) wt x y =
      ∑ k ∈ s, (q k : ℝ) * field n L (fun m ↦ (lv m).withCoeff (a k m)) wt x y := by
  simp only [field, Level.withCoeff, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ m ∈ range L, ∑ i ∈ range (lv m).rows, ∑ k ∈ s, ∑ j ∈ range (lv m).cols,
        (q k : ℝ) * ((a k m i j : ℝ) * mode n (lv m).xKnots ((lv m).xModes i) x *
          (wt y * mode n (lv m).yKnots ((lv m).yModes j) y)) := by
        refine sum_congr rfl fun m _ ↦ sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_comm]
        refine sum_congr rfl fun k _ ↦ sum_congr rfl fun j _ ↦ ?_
        ring
    _ = ∑ m ∈ range L, ∑ k ∈ s, ∑ i ∈ range (lv m).rows, ∑ j ∈ range (lv m).cols,
        (q k : ℝ) * ((a k m i j : ℝ) * mode n (lv m).xKnots ((lv m).xModes i) x *
          (wt y * mode n (lv m).yKnots ((lv m).yModes j) y)) :=
        sum_congr rfl fun m _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

end TensorSpline

namespace SpaceTime

open TensorSpline

variable {n : ℕ} {B : TimeBasis n}

/-- The tensor B-spline field with the knots and modes of `lv` and the coefficient tensors
`a m i j` of its levels. -/
noncomputable def splineField (N L : ℕ) (lv : ℕ → Level) (wt : ℝ → ℝ)
    (a : ℕ → ℕ → ℕ → ℚ) : ℝ → ℝ → ℝ :=
  fun x y ↦ field N L (fun m ↦ (lv m).withCoeff (a m)) wt x y

/-- **Time-derivative coefficients of spline blocks.** If the coefficients of block `m` are
spline fields with coefficient tensors `a i` and the time scale is the rational `k`, the
derivative coefficient `dₘⱼ = k⁻¹ ∑ᵢ D i j cₘᵢ` is the spline field with the rational tensor
`∑ᵢ (k⁻¹ D i j) aᵢ`. -/
theorem BlockField.derivCoeff_eq_splineField (F : BlockField B (ℝ → ℝ → ℝ)) {N L : ℕ}
    {lv : ℕ → Level} {wt : ℝ → ℝ} {m : ℕ} (a : Fin n → ℕ → ℕ → ℕ → ℚ)
    (ha : ∀ i, F.coeff m i = splineField N L lv wt (a i)) {k : ℚ} (hk : F.scale m = k)
    (j : Fin n) :
    F.derivCoeff m j =
      splineField N L lv wt fun l r c ↦ ∑ i, k⁻¹ * B.derivMatrix i j * a i l r c := by
  funext x y
  simp only [BlockField.derivCoeff, hk, ha, splineField]
  have := field_withCoeff_sum Finset.univ (fun i ↦ k⁻¹ * B.derivMatrix i j) N L lv
    (fun i ↦ a i) wt x y
  simp only [mul_assoc] at this ⊢
  rw [this]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum, Rat.cast_mul,
    Rat.cast_inv]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [splineField]
  ring

end SpaceTime

end CAS.Numerics
