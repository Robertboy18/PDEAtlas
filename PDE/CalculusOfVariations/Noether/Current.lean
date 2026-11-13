/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.Coordinates
public import PDE.CalculusOfVariations.NullLagrangian.Basic
public import PDE.Analysis.Calculus.Divergence
public import PDE.Analysis.Calculus.Jacobian.SecondJet

/-!
# The current associated with a field and space variation

If `v` is the variation of a field at fixed spatial coordinates and `X` is the spatial
velocity, the Noether current has components `Σₖ L_{Pₖᵢ} vₖ + L Xᵢ`. Its divergence is
computed by the product rule and the first-variation coordinate formula.
The resulting identity holds before imposing either invariance or the Euler–Lagrange
equations.

For a transformation whose field velocity along a moving point is `η`, the fixed-coordinate
variation is `v = η - Du X`. Evans, §8.6.2, Theorem 1, writes the current of a scalar field
as `m L_p - L v`, with multiplier `m` and domain velocity `v`; it is our current with field
variation `m` and spatial velocity `-v`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1 and §8.6.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ}

/-- The density evaluated on the first jet of a field. -/
def fieldDensity (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (u : ℝ^n → ℝ^m) (x : ℝ^n) : ℝ :=
  L (jacobianMatrix u x) (u x) x

/-- The momentum conjugate to the gradient entry in row `k`, column `i`. -/
def momentum (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (u : ℝ^n → ℝ^m) (k : Fin m) (i : Fin n) (x : ℝ^n) : ℝ :=
  fderiv ℝ (fun P ↦ L P (u x) x) (jacobianMatrix u x) (Matrix.single k i 1)

/-- The pointwise first variation, using the full differential of the density. -/
def firstVariationDensity (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (u v : ℝ^n → ℝ^m) (x : ℝ^n) : ℝ :=
  fderiv ℝ
    (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
    (jacobianMatrix u x, (u x, x)) (jacobianMatrix v x, (v x, 0))

/-- The Noether current for a fixed-coordinate field variation `v` and spatial velocity `X`.
For a moving-coordinate field generator `η`, substitute `v = η - Du X`. -/
def noetherCurrent (L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ)
    (u v : ℝ^n → ℝ^m) (X : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 (fun i ↦ ∑ k, momentum L u k i x * v x k) + fieldDensity L u x • X x

variable {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {u v : ℝ^n → ℝ^m} {X : ℝ^n → ℝ^n} {x : ℝ^n}

/-- A `C²` density germ evaluated on a `C²` field germ has a `C¹` density germ. -/
theorem contDiffAt_fieldDensity
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x) : ContDiffAt ℝ 1 (fieldDensity L u) x := by
  unfold fieldDensity
  exact (hL.of_le (by norm_num)).comp x
    ((contDiffAt_jacobianMatrix hu).prodMk
      ((hu.of_le (by norm_num)).prodMk contDiffAt_id))

/-- The momentum of a `C²` density germ along a `C²` field germ is `C¹`. -/
theorem contDiffAt_momentum
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x) (k : Fin m) (i : Fin n) :
    ContDiffAt ℝ 1 (momentum L u k i) x := by
  have hjet := (contDiffAt_jacobianMatrix hu).prodMk
    ((hu.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).prodMk contDiffAt_id)
  have hnear : momentum L u k i =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ
        (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
        (jacobianMatrix u y, (u y, y)) (Matrix.single k i 1, (0, 0))) := by
    filter_upwards [hjet.continuousAt.eventually (hL.eventually (by norm_num))] with y hy
    exact fderiv_lagrangian_matrix_apply (hy.differentiableAt (by norm_num)) _
  apply ContDiffAt.congr_of_eventuallyEq _ hnear
  exact ((hL.fderiv_right (m := 1) (by norm_num)).comp x hjet).clm_apply
    contDiffAt_const

/-- The divergence of the Noether current equals the density variation plus transport,
minus the Euler–Lagrange expression paired with the fixed-coordinate field variation. -/
theorem divergence_noetherCurrent
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x) (hv : DifferentiableAt ℝ v x)
    (hX : DifferentiableAt ℝ X x) :
    ∇· (noetherCurrent L u v X) x =
      firstVariationDensity L u v x +
        fderiv ℝ (fieldDensity L u) x (X x) +
        fieldDensity L u x * ∇· X x -
        ∑ k, classicalEulerLagrange L u x k * v x k := by
  have hA (k : Fin m) (i : Fin n) :=
    (contDiffAt_momentum hL hu k i).differentiableAt (by norm_num)
  have hV (k : Fin m) : DifferentiableAt ℝ (fun y ↦ v y k) x :=
    (EuclideanSpace.proj k : ℝ^m →L[ℝ] ℝ).differentiableAt.comp x hv
  have hd := (contDiffAt_fieldDensity hL hu).differentiableAt (by norm_num)
  have hXi (i : Fin n) : DifferentiableAt ℝ (fun y ↦ X y i) x :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).differentiableAt.comp x hX
  have hsplit :
      ∇· (noetherCurrent L u v X) x =
        (∑ i, ∑ k, ((∂[i] (momentum L u k i)) x * v x k +
          momentum L u k i x * (∂[i] (fun y ↦ v y k)) x)) +
        ∇· (fun y ↦ fieldDensity L u y • X y) x := by
    unfold divergence noetherCurrent
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    change (∑ i, (∂[i] (fun y ↦ (∑ k, momentum L u k i y * v y k) +
      fieldDensity L u y * X y i)) x) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hsum : DifferentiableAt ℝ (fun y ↦ ∑ k, momentum L u k i y * v y k) x :=
      DifferentiableAt.fun_sum (fun k _ ↦ (hA k i).mul (hV k))
    have hadd :
        (∂[i] (fun y ↦ (∑ k, momentum L u k i y * v y k) +
          fieldDensity L u y * X y i)) x =
        (∂[i] (fun y ↦ ∑ k, momentum L u k i y * v y k)) x +
          (∂[i] (fun y ↦ fieldDensity L u y * X y i)) x :=
      partialDeriv_add hsum (hd.fun_mul (hXi i))
    rw [hadd]
    congr 1
    rw [partialDeriv_sum Finset.univ
      (f := fun k y ↦ momentum L u k i y * v y k)
      (fun k _ ↦ (hA k i).fun_mul (hV k)) i]
    apply Finset.sum_congr rfl
    intro k _
    exact partialDeriv_mul (hA k i) (hV k)
  rw [hsplit, divergence_smul hd hX]
  unfold firstVariationDensity
  rw [fderiv_lagrangian_apply_matrix_value (hL.differentiableAt (by norm_num))]
  rw [Finset.sum_comm]
  unfold momentum
  simp only [Finset.sum_add_distrib, classicalEulerLagrange,
    jacobianMatrix, jacobianColumn, Matrix.of_apply, add_mul, neg_mul,
    Finset.sum_mul, Finset.sum_neg_distrib]
  simp only [mul_comm]
  abel

end PDE.CalculusOfVariations.Noether
