/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Parabolic.Heat.Kernel.Basic
import Mathlib.Analysis.Calculus.FDeriv.Partial
import PDE.Parabolic.Heat.Kernel.TimeDerivative
import CAS.ExactTactic

/-!
# Spatial derivatives of the Euclidean heat kernel

At a fixed time `t > 0` the heat kernel `Φ(x, t) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` is a smooth
Gaussian in `x`, and its derivatives are polynomials in `x` times `Φ` itself:

* gradient: `∇Φ = -(x / (2t)) Φ`, so `∂ᵢΦ = -(xᵢ / (2t)) Φ`;
* Hessian: `D²Φ(h, k) = ((x·h)(x·k) / (4t²) - (h·k) / (2t)) Φ`;
* Laplacian: `ΔΦ = (‖x‖² / (4t²) - n / (2t)) Φ`.

These formulas are proved as Fréchet-derivative statements. The gradient is written
basis-free as a multiple of `innerSL ℝ x`, the Hessian is packaged as the continuous bilinear
map `fundamentalSolutionHeatHessian`, and the coordinate second derivatives and the Laplacian
are read off by evaluating the Hessian on standard basis vectors and summing. The Laplacian
formula is the spatial half of the verification that `Φ` solves the heat equation
(Evans, PDE, §2.3.1), completed in `PDE.Parabolic.Heat.Kernel.Equation`.

## Main results

* `differentiableAt_fundamentalSolutionHeat`, `hasFDerivAt_fundamentalSolutionHeat_space`:
  spatial differentiability and the gradient at positive time.
* `hasFDerivAt_fundamentalSolutionHeat_timeSpace`: joint differentiability in `(t, x)`, with
  derivative the coproduct of the time derivative and the spatial gradient.
* `fundamentalSolutionHeatHessian`, `hasFDerivAt_fundamentalSolutionHeat_gradient`: the
  closed-form Hessian and the proof that it is the derivative of the gradient.
* `norm_fundamentalSolutionHeatHessian_le`: the operator-norm bound
  `‖D²Φ‖ ≤ Φ · (1 / (2t) + ‖x‖² / (4t²))`, the domination estimate used when differentiating
  heat convolutions twice under the integral sign.
* `fundamentalSolutionHeat_partialDeriv`, `fundamentalSolutionHeat_deriv2_x`: first and pure
  second coordinate derivatives.
* `laplacian_fundamentalSolutionHeat`, `trace_fundamentalSolutionHeatHessian_eq_laplacian`:
  the Laplacian, and its identification with the trace of the Hessian.

## Implementation notes

`fundamentalSolutionHeat` is zero for `t ≤ 0`, and `fundamentalSolutionHeatHessian x t` is
defined by the algebraic formula for every `t` (it involves `1 / (2t)`, which Lean totalizes
at `t = 0`). Every derivative statement therefore carries the hypothesis `0 < t`; the purely
algebraic evaluation lemmas `fundamentalSolutionHeatHessian_apply_apply` and
`fundamentalSolutionHeatHessian_diagonal` do not need it, and neither does the continuity
statement `continuous_fundamentalSolutionHeatHessian_apply`, since for `t ≤ 0` the kernel and
its Hessian vanish.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, definition of the fundamental solution.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-! ## First derivatives and the Hessian -/

section SpatialDerivatives

variable {t : ℝ}

/-- At any fixed positive time the heat kernel is differentiable in the spatial variable. For
`t > 0` the kernel is the Gaussian `(4πt)^(-n/2) exp(-‖z‖² / (4t))`, a composition of `exp`
with a multiple of the squared norm. -/
theorem differentiableAt_fundamentalSolutionHeat (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
    DifferentiableAt ℝ
      (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t) x := by
  have h : (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t) =
      fun z ↦ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp ((-1 / (4 * t)) * ‖z‖ ^ 2) := by
    funext z
    simp [fundamentalSolutionHeat, not_le_of_gt ht, div_eq_mul_inv, mul_comm]
  rw [h]
  exact (((differentiableAt_id.norm_sq ℝ).const_mul _).exp).const_mul _

/-- Fréchet derivative of the heat kernel in the spatial variable for `t > 0`. -/
theorem hasFDerivAt_fundamentalSolutionHeat_space (t : ℝ) (ht : 0 < t)
    (x : ℝ^n) :
    HasFDerivAt (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t)
      ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) x t) • innerSL ℝ x) x := by
  have hbranch : (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t) =
      fun z ↦ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp ((-1 / (4 * t)) * ‖z‖ ^ 2) := by
    funext z
    simp [fundamentalSolutionHeat, not_le_of_gt ht, div_eq_mul_inv, mul_comm]
  rw [hbranch]
  convert (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-1 / (4 * t))).exp.const_mul
    ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))) using 1
  ext v
  simp [fundamentalSolutionHeat, not_le_of_gt ht, div_eq_mul_inv, mul_comm, smul_smul]
  field_simp
  ring

/-- The positive-time heat kernel is jointly Fréchet differentiable in time and space.

The derivative adds the response to a time increment and the response to a spatial
increment. The latter is expressed by the inner product with the spatial gradient. -/
theorem hasFDerivAt_fundamentalSolutionHeat_timeSpace
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    HasFDerivAt
      (fun p : ℝ × ℝ^n ↦
        fundamentalSolutionHeat (n := n) p.2 p.1)
      (ContinuousLinearMap.coprod
        (((‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
              fundamentalSolutionHeat (n := n) x t) •
            (1 : ℝ →L[ℝ] ℝ))
        ((-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) x t) •
            innerSL ℝ x))
      (t, x) := by
  let T : ℝ × ℝ^n → ℝ := fun p ↦
    (‖p.2‖ ^ 2 / (4 * p.1 ^ 2) - (n : ℝ) / (2 * p.1)) * fundamentalSolutionHeat (n := n) p.2 p.1
  let G : ℝ × ℝ^n → (ℝ^n) →L[ℝ] ℝ := fun p ↦
    (-(1 / (2 * p.1)) * fundamentalSolutionHeat (n := n) p.2 p.1) • innerSL ℝ p.2
  have hpos : ∀ᶠ p in nhds (t, x), 0 < p.1 := continuousAt_fst.eventually (eventually_gt_nhds ht)
  have htime : ∀ᶠ p in nhds (t, x), HasFDerivAt
      (fun s : ℝ ↦ fundamentalSolutionHeat (n := n) p.2 s) (T p • (1 : ℝ →L[ℝ] ℝ)) p.1 := by
    filter_upwards [hpos] with p hp
    convert ((differentiableAt_fundamentalSolutionHeat_time p.2 p.1 hp).hasDerivAt.congr_deriv
      (fundamentalSolutionHeat_deriv_t p.2 p.1 hp)).hasFDerivAt using 1
    ext
    simp [T, mul_comm]
  have hspace : ∀ᶠ p in nhds (t, x), HasFDerivAt
      (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z p.1) (G p) p.2 := by
    filter_upwards [hpos] with p hp
    exact hasFDerivAt_fundamentalSolutionHeat_space p.1 hp p.2
  have hkernel :
      ContinuousAt (fun p : ℝ × ℝ^n ↦ fundamentalSolutionHeat (n := n) p.2 p.1) (t, x) := by
    have hK : ContinuousAt (fun p : ℝ × ℝ^n ↦
        (4 * Real.pi * p.1) ^ (-(n : ℝ) / 2) * Real.exp (-(‖p.2‖ ^ 2 / (4 * p.1)))) (t, x) := by
      fun_prop (disch := first | positivity | exact Or.inl (by positivity))
    refine hK.congr ?_
    filter_upwards [hpos] with p hp
    simp [fundamentalSolutionHeat, not_le_of_gt hp]
  have hT : ContinuousAt (fun p ↦ T p • (1 : ℝ →L[ℝ] ℝ)) (t, x) := by
    simp only [T]
    fun_prop (disch := positivity)
  have hG : ContinuousAt G (t, x) := by
    simp only [G]
    fun_prop (disch := positivity)
  exact (hasStrictFDerivAt_uncurry_coprod (f := fun s (z : ℝ^n) ↦ fundamentalSolutionHeat z s)
    (f₁ := fun s z ↦ T (s, z) • (1 : ℝ →L[ℝ] ℝ)) (f₂ := fun s z ↦ G (s, z))
    htime hspace hT hG).hasFDerivAt

/-- The algebraic formula for the spatial Hessian of the Gaussian heat kernel.

Applied to directions `h` and `k`, this is
`((x·h)(x·k)/(4t²) - (h·k)/(2t)) Γ(x,t)`. The basis-free operator is used below
to differentiate the heat-kernel convolution twice before taking its trace. The formula makes
sense for every `t`, but `hasFDerivAt_fundamentalSolutionHeat_gradient` identifies it with the
Hessian only for `0 < t`. -/
noncomputable def fundamentalSolutionHeatHessian
    (x : ℝ^n) (t : ℝ) :
    ℝ^n →L[ℝ]
      (ℝ^n →L[ℝ] ℝ) :=
  let a : ℝ := -(1 / (2 * t))
  (a * fundamentalSolutionHeat (n := n) x t) •
      ((innerSL ℝ).toLinearMap.toContinuousLinearMap : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ) +
    (a • ((a * fundamentalSolutionHeat (n := n) x t) • innerSL ℝ x)).smulRight
      (innerSL ℝ x)

/-- The derivative of the spatial heat-kernel gradient is its basis-free Hessian. -/
theorem hasFDerivAt_fundamentalSolutionHeat_gradient
    (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
    HasFDerivAt
      (fun y : ℝ^n ↦
        (-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) y t) • innerSL ℝ y)
      (fundamentalSolutionHeatHessian (n := n) x t) x := by
  exact ((hasFDerivAt_fundamentalSolutionHeat_space t ht x).const_mul (-(1 / (2 * t)))).smul
    ((innerSL ℝ).toLinearMap.toContinuousLinearMap : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ).hasFDerivAt

/-- Evaluating one output slot of the Gaussian Hessian gives a continuously varying covector
(for `t ≤ 0` the kernel and its Hessian vanish). Stating it one slot at a time avoids choosing
a topology on the nested space of continuous linear maps. -/
theorem continuous_fundamentalSolutionHeatHessian_apply
    (t : ℝ) (v : ℝ^n) :
    Continuous fun x : ℝ^n ↦
      ((ContinuousLinearMap.apply ℝ ℝ) v).comp
        (fundamentalSolutionHeatHessian (n := n) x t) := by
  have hK : Continuous fun x : ℝ^n ↦ fundamentalSolutionHeat (n := n) x t := by
    rcases le_or_gt t 0 with ht | ht
    · have h0 : (fun x : ℝ^n ↦ fundamentalSolutionHeat (n := n) x t) = fun _ ↦ 0 := by
        funext x
        simp [fundamentalSolutionHeat, ht]
      rw [h0]
      exact continuous_const
    · exact continuous_iff_continuousAt.mpr fun x ↦
        (hasFDerivAt_fundamentalSolutionHeat_space t ht x).continuousAt
  convert (by fun_prop : Continuous fun x : ℝ^n ↦
    (-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) x t) • innerSL ℝ v +
      ((1 / (4 * t ^ 2) * fundamentalSolutionHeat (n := n) x t) * inner ℝ x v) • innerSL ℝ x)
    using 1
  ext x h
  simp [fundamentalSolutionHeatHessian, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
  ring

/-- Evaluation of the heat-kernel Hessian on two spatial directions. -/
theorem fundamentalSolutionHeatHessian_apply_apply
    (x h k : ℝ^n) (t : ℝ) :
    fundamentalSolutionHeatHessian (n := n) x t h k =
      (-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) x t) * inner ℝ h k +
        (1 / (4 * t ^ 2) * fundamentalSolutionHeat (n := n) x t) *
          (inner ℝ x h * inner ℝ x k) := by
  simp [fundamentalSolutionHeatHessian, innerSL_apply_apply, smul_eq_mul]
  ring

/-- Operator-norm bound for the spatial heat-kernel Hessian.

The right-hand side is a quadratic polynomial times the Gaussian. This is the domination
estimate used when differentiating bounded-data heat convolutions a second time. -/
theorem norm_fundamentalSolutionHeatHessian_le
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    ‖fundamentalSolutionHeatHessian (n := n) x t‖ ≤
      fundamentalSolutionHeat (n := n) x t *
        (1 / (2 * t) + (1 / (4 * t ^ 2)) * ‖x‖ ^ 2) := by
  have hK := (fundamentalSolutionHeat_pos (n := n) x t ht).le
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k ↦ ?_
  rw [fundamentalSolutionHeatHessian_apply_apply, Real.norm_eq_abs]
  have h1 : (0 : ℝ) < 1 / (2 * t) := by positivity
  have h2 : (0 : ℝ) < 1 / (4 * t ^ 2) := by positivity
  calc _ ≤ _ := abs_add_le _ _
    _ = 1 / (2 * t) * fundamentalSolutionHeat (n := n) x t * |inner ℝ h k| +
          1 / (4 * t ^ 2) * fundamentalSolutionHeat (n := n) x t *
            (|inner ℝ x h| * |inner ℝ x k|) := by
      simp only [abs_mul, abs_neg, abs_of_pos h1, abs_of_pos h2, abs_of_nonneg hK]
    _ ≤ 1 / (2 * t) * fundamentalSolutionHeat (n := n) x t * (‖h‖ * ‖k‖) +
          1 / (4 * t ^ 2) * fundamentalSolutionHeat (n := n) x t *
            ((‖x‖ * ‖h‖) * (‖x‖ * ‖k‖)) := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = _ := by ring

/-- The algebraic formula for a diagonal entry of `fundamentalSolutionHeatHessian`.

For positive time, `hasFDerivAt_fundamentalSolutionHeat_gradient` identifies this bilinear map
with the analytic second spatial derivative of the Gaussian heat kernel. -/
theorem fundamentalSolutionHeatHessian_diagonal
    (x : ℝ^n) (t : ℝ) (i : Fin n) :
    fundamentalSolutionHeatHessian (n := n) x t
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) =
      ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
        fundamentalSolutionHeat (n := n) x t := by
  rw [fundamentalSolutionHeatHessian_apply_apply (n := n)]
  have hxi : inner ℝ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
    simp [EuclideanSpace.single, PiLp.inner_apply, PiLp.single_apply]
  have hii :
      inner ℝ (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) = 1 := by
    simp [EuclideanSpace.single]
  rw [hxi, hii]
  ring

/-- First spatial derivatives of the heat kernel for `t > 0`. -/
theorem fundamentalSolutionHeat_partialDeriv
    (t : ℝ) (ht : 0 < t) (x : ℝ^n) (i : Fin n) :
    (∂[i]
        (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t)) x =
      (-(x i) / (2 * t)) * fundamentalSolutionHeat (n := n) x t := by
  rw [partialDeriv, (hasFDerivAt_fundamentalSolutionHeat_space t ht x).fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  have hinner : inner ℝ x (EuclideanSpace.single i (1 : ℝ)) = x i := by
    simp [EuclideanSpace.single, PiLp.inner_apply, PiLp.single_apply]
  rw [hinner]
  cas

end SpatialDerivatives

/-! ## Coordinate second derivatives and trace -/

/-- Second spatial derivatives of the heat kernel for `t > 0`. -/
theorem fundamentalSolutionHeat_deriv2_x
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) (i : Fin n) :
    (∂[i]
        (fun y : ℝ^n ↦
          (∂[i]
            (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z t)) y)) x =
      ((x i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * fundamentalSolutionHeat (n := n) x t := by
  let e : ℝ^n := EuclideanSpace.single i 1
  have hpartial :
      (fun y : ℝ^n ↦ (∂[i] (fun z : ℝ^n ↦ fundamentalSolutionHeat z t)) y) =
        (fun y ↦ ((-(1 / (2 * t)) * fundamentalSolutionHeat y t) • innerSL ℝ y) e) := by
    funext y
    rw [partialDeriv, (hasFDerivAt_fundamentalSolutionHeat_space t ht y).fderiv]
  rw [hpartial, partialDeriv]
  have hd := ((ContinuousLinearMap.apply ℝ ℝ) e).hasFDerivAt.comp x
    (hasFDerivAt_fundamentalSolutionHeat_gradient t ht x)
  have hdf := hd.fderiv
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hdf
  rw [hdf]
  change fundamentalSolutionHeatHessian x t e e = _
  exact fundamentalSolutionHeatHessian_diagonal x t i

/-- Laplacian of the heat kernel (spatial variables) for `t > 0`. -/
theorem laplacian_fundamentalSolutionHeat (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    laplacian (n := n)
        (fun y : ℝ^n ↦ fundamentalSolutionHeat (n := n) y t) x =
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * fundamentalSolutionHeat (n := n) x t := by
  simp only [laplacian, fundamentalSolutionHeat_deriv2_x x t ht, ← Finset.sum_mul,
    Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← EuclideanSpace.real_norm_sq_eq]
  cas

/-- The trace of the basis-free heat-kernel Hessian is the Laplacian. -/
theorem trace_fundamentalSolutionHeatHessian_eq_laplacian
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    (∑ i : Fin n,
      fundamentalSolutionHeatHessian (n := n) x t
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) =
      laplacian (n := n)
        (fun y : ℝ^n ↦
          fundamentalSolutionHeat (n := n) y t) x := by
  unfold laplacian
  refine Finset.sum_congr rfl (fun i _hi ↦ ?_)
  rw [fundamentalSolutionHeatHessian_diagonal (n := n)]
  symm
  simpa [partialDeriv] using
    fundamentalSolutionHeat_deriv2_x (n := n) x t ht i

end HeatEquation
