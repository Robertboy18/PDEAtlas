/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Smooth

/-!
# Coordinate derivatives of transport terms and of gradients

To differentiate an equation such as `-½ u - ½ x·∇u + W·∇W + ∇P - Δu = F` in a coordinate
direction, one needs the coordinate derivative of each term. For the Laplacian this is
`PDE.partialDeriv_laplacian`. This module gives the derivatives of the transport terms `x·∇f`
and `g·∇f`, of a gradient, and of a scalar function times a fixed vector, each at the regularity
it needs: `C²` at the point for the transported function, and differentiability at the point
for the transporting field.

## Main results

* `partialDeriv_fderiv` (all maps `f` that are `C²` at the point): `∂ₖ(Df) = D(∂ₖf)`, with the
  bound `norm_fderiv_partialDeriv_le`: `|D(∂ₖf)| ≤ |D²f|`.
* `partialDeriv_fderiv_apply` (all `f` that are `C²` at the point, all `g` differentiable
  there): `∂ₖ(g·∇f) = g·∇(∂ₖf) + (∂ₖg)·∇f`.
* `partialDeriv_fderiv_apply_self` (all `f` that are `C²` at the point):
  `∂ₖ(x·∇f) = x·∇(∂ₖf) + ∂ₖf`; `iteratedPartialDeriv_fderiv_apply_self` (all smooth `f`, all
  words `α` of coordinate derivatives): `∂^α(x·∇f) = x·∇(∂^αf) + |α| ∂^αf`.
* `partialDeriv_gradient` (all scalars `P` that are `C²` at the point): `∂ₖ∇P = ∇(∂ₖP)`.
* `sum_partialDeriv_partialDeriv_eq_zero` (all smooth fields with zero divergence):
  `∑ᵢ ∂ᵢ∂ⱼφᵢ = 0`.
* `abs_partialDeriv_mul_component_le` (all vector fields `W` differentiable at the point):
  `|∂ₗ(WᵢWⱼ)| ≤ 2 |W| |DW|`.
* `partialDeriv_smul_const`, `laplacian_smul_const`, `divergence_smul_single` (all scalar
  functions `ψ`): the derivatives of `ψ e` for a fixed vector `e`, and `div(ψ eᵢ) = ∂ᵢψ`.

## How it works

`y ↦ Df(y) (g y)` is bilinear in `Df` and `g`, so its derivative in the direction `eₖ` is
`D²f(x) eₖ (g x) + Df(x) (∂ₖg x)`. The second derivative is symmetric at a point where `f` is
`C²`, so the first term is `D(∂ₖf)(x) (g x)`. With `g` the identity this gives
`∂ₖ(x·∇f) = x·∇(∂ₖf) + ∂ₖf`, and induction on the word gives the formula for `∂^α`. The same
symmetry, read in coordinates, gives `∂ₖ∇P = ∇(∂ₖP)` for a gradient and
`∑ᵢ ∂ᵢ∂ⱼφᵢ = ∂ⱼ(div φ)` for a field. The scalar statements
`PDE.partialDeriv_advectiveDerivative` and
`NavierStokes.Stationary.partialDeriv_sum_coord_mul_partialDeriv` are coordinate forms of
`partialDeriv_fderiv_apply` and `partialDeriv_fderiv_apply_self`, and
`NavierStokes.Stationary.divergence_partialDeriv_eq_zero` is `div(∂ⱼφ) = 0` for a smooth
divergence-free `φ`.
-/

@[expose] public section

open scoped Gradient

namespace PDE

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate derivative of the total derivative is the total derivative of the coordinate
derivative, `∂ₖ(Df) = D(∂ₖf)`, for `f` of class `C²` at the point. -/
theorem partialDeriv_fderiv {f : ℝ^n → F} {x : ℝ^n} (k : Fin n) (hf : ContDiffAt ℝ 2 f x) :
    ∂[k] (fderiv ℝ f) x = fderiv ℝ (∂[k] f) x := by
  have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hk : HasFDerivAt (∂[k] f)
      ((ContinuousLinearMap.apply ℝ F (EuclideanSpace.single k (1 : ℝ))).comp
        (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single k (1 : ℝ))).hasFDerivAt.comp x hA
  ext y
  rw [hk.fderiv]
  change fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single k 1) y = _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact (hf.isSymmSndFDerivAt (by simp)).eq (EuclideanSpace.single k (1 : ℝ)) y

/-- The derivative of a coordinate derivative is bounded by the second derivative:
`|D(∂ₖf)| ≤ |D²f|` at a point where `f` is of class `C²`. -/
theorem norm_fderiv_partialDeriv_le {f : ℝ^n → F} {x : ℝ^n} (k : Fin n)
    (hf : ContDiffAt ℝ 2 f x) : ‖fderiv ℝ (∂[k] f) x‖ ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← partialDeriv_fderiv k hf]
  calc ‖∂[k] (fderiv ℝ f) x‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ :=
        norm_partialDeriv_le_norm_fderiv k _ x
    _ = ‖iteratedFDeriv ℝ 2 f x‖ := by
        rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- The coordinate derivative of a transport term: `∂ₖ(g·∇f) = g·∇(∂ₖf) + (∂ₖg)·∇f`, for `f` of
class `C²` at the point and `g` differentiable there. -/
theorem partialDeriv_fderiv_apply {f : ℝ^n → F} {g : ℝ^n → ℝ^n} {x : ℝ^n} (k : Fin n)
    (hf : ContDiffAt ℝ 2 f x) (hg : DifferentiableAt ℝ g x) :
    ∂[k] (fun y ↦ fderiv ℝ f y (g y)) x =
      fderiv ℝ (∂[k] f) x (g x) + fderiv ℝ f x (∂[k] g x) := by
  have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hprod := hA.clm_apply hg.hasFDerivAt
  have hk : HasFDerivAt (∂[k] f)
      ((ContinuousLinearMap.apply ℝ F (EuclideanSpace.single k (1 : ℝ))).comp
        (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single k (1 : ℝ))).hasFDerivAt.comp x hA
  have hsymm := (hf.isSymmSndFDerivAt (by simp)).eq (EuclideanSpace.single k (1 : ℝ)) (g x)
  change fderiv ℝ (fun y ↦ fderiv ℝ f y (g y)) x (EuclideanSpace.single k 1) =
    fderiv ℝ (∂[k] f) x (g x) + fderiv ℝ f x (fderiv ℝ g x (EuclideanSpace.single k 1))
  rw [hprod.fderiv, hk.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply]
  rw [hsymm, add_comm]

/-- The coordinate derivative of the dilation term: `∂ₖ(x·∇f) = x·∇(∂ₖf) + ∂ₖf`, for `f` of
class `C²` at the point. -/
theorem partialDeriv_fderiv_apply_self {f : ℝ^n → F} {x : ℝ^n} (k : Fin n)
    (hf : ContDiffAt ℝ 2 f x) :
    ∂[k] (fun y ↦ fderiv ℝ f y y) x = fderiv ℝ (∂[k] f) x x + ∂[k] f x := by
  have h := partialDeriv_fderiv_apply (g := fun y ↦ y) k hf differentiableAt_fun_id
  have hid : ∂[k] (fun y : ℝ^n ↦ y) x = EuclideanSpace.single k (1 : ℝ) := by
    change fderiv ℝ (fun y : ℝ^n ↦ y) x (EuclideanSpace.single k 1) = _
    rw [fderiv_fun_id]
    rfl
  rw [h, hid]
  rfl

/-- The dilation term under a word of coordinate derivatives:
`∂^α(x·∇f) = x·∇(∂^αf) + |α| ∂^αf`, for a smooth `f`. Each derivative that passes the factor
`x` leaves one more copy of the derivative of `f`. -/
theorem iteratedPartialDeriv_fderiv_apply_self {f : ℝ^n → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin n)) (x : ℝ^n) :
    iteratedPartialDeriv α (fun y ↦ fderiv ℝ f y y) x =
      fderiv ℝ (iteratedPartialDeriv α f) x x + (α.length : ℝ) • iteratedPartialDeriv α f x := by
  induction α generalizing x with
  | nil =>
    change fderiv ℝ f x x = fderiv ℝ f x x + ((0 : ℕ) : ℝ) • f x
    rw [Nat.cast_zero, zero_smul, add_zero]
  | cons k rest ih =>
    have h2 : ContDiff ℝ 2 (iteratedPartialDeriv rest f) :=
      (contDiff_top_iteratedPartialDeriv hf rest).of_le (by simp)
    have hfun : (fun y ↦ iteratedPartialDeriv rest (fun y ↦ fderiv ℝ f y y) y) =
        fun y ↦ fderiv ℝ (iteratedPartialDeriv rest f) y y +
          (rest.length : ℝ) • iteratedPartialDeriv rest f y := funext ih
    have hd1 : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (iteratedPartialDeriv rest f) y y) x :=
      ((h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).clm_apply
        differentiableAt_fun_id
    have hd2 : DifferentiableAt ℝ
        (fun y ↦ (rest.length : ℝ) • iteratedPartialDeriv rest f y) x :=
      (h2.differentiable (by norm_num) x).fun_const_smul _
    change ∂[k] (fun y ↦ iteratedPartialDeriv rest (fun y ↦ fderiv ℝ f y y) y) x =
      fderiv ℝ (∂[k] (iteratedPartialDeriv rest f)) x x +
        ((rest.length + 1 : ℕ) : ℝ) • ∂[k] (iteratedPartialDeriv rest f) x
    rw [hfun, partialDeriv_add hd1 hd2, partialDeriv_const_smul,
      partialDeriv_fderiv_apply_self k h2.contDiffAt, Nat.cast_add, Nat.cast_one, add_smul,
      one_smul]
    abel

/-- The coordinate derivative of a gradient is the gradient of the coordinate derivative,
`∂ₖ∇P = ∇(∂ₖP)`, for a scalar `P` of class `C²` at the point. -/
theorem partialDeriv_gradient {P : ℝ^n → ℝ} {x : ℝ^n} (k : Fin n) (hP : ContDiffAt ℝ 2 P x) :
    ∂[k] (∇ P) x = ∇ (∂[k] P) x := by
  have hgrad : DifferentiableAt ℝ (∇ P) x :=
    ((InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ).differentiableAt.comp x
      ((hP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  ext i
  rw [partialDeriv_apply k i hgrad, gradient_apply_eq_partialDeriv]
  have hfun : (fun y ↦ ∇ P y i) = fun y ↦ ∂[i] P y :=
    funext fun y ↦ gradient_apply_eq_partialDeriv P y i
  rw [hfun]
  exact partialDeriv_partialDeriv_comm_at k i hP

/-- For a smooth field `φ` on `ℝⁿ` whose divergence vanishes at every point,
`∑ᵢ ∂ᵢ∂ⱼφᵢ = ∂ⱼ(div φ) = 0` at every point, because second derivatives commute. -/
theorem sum_partialDeriv_partialDeriv_eq_zero {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hdiv : ∀ x, PDE.divergence φ x = 0) (j : Fin n) (x : ℝ^n) :
    ∑ i, PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x = 0 := by
  have hφi (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ φ z i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hφ
  have hcomm (i : Fin n) :
      PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x =
        PDE.partialDeriv j (fun y ↦ PDE.partialDeriv i (fun z ↦ φ z i) y) x :=
    PDE.partialDeriv_partialDeriv_comm i j ((hφi i).of_le (by simp)) x
  have hsum : PDE.partialDeriv j (fun y ↦ ∑ i, PDE.partialDeriv i (fun z ↦ φ z i) y) x =
      ∑ i, PDE.partialDeriv j (fun y ↦ PDE.partialDeriv i (fun z ↦ φ z i) y) x :=
    PDE.partialDeriv_sum (f := fun i y ↦ PDE.partialDeriv i (fun z ↦ φ z i) y) Finset.univ
      (fun i _ ↦ ((PDE.contDiff_top_partialDeriv (i := i) (hφi i)).differentiable
        (by simp)).differentiableAt) j
  have hzero : (fun y ↦ ∑ i, PDE.partialDeriv i (fun z ↦ φ z i) y) = fun _ ↦ (0 : ℝ) :=
    funext fun y ↦ (PDE.divergence_eq_sum φ y).symm.trans (hdiv y)
  calc ∑ i, PDE.partialDeriv i (fun y ↦ PDE.partialDeriv j (fun z ↦ φ z i) y) x
      = ∑ i, PDE.partialDeriv j (fun y ↦ PDE.partialDeriv i (fun z ↦ φ z i) y) x :=
        Finset.sum_congr rfl fun i _ ↦ hcomm i
    _ = PDE.partialDeriv j (fun y ↦ ∑ i, PDE.partialDeriv i (fun z ↦ φ z i) y) x := hsum.symm
    _ = PDE.partialDeriv j (fun _ ↦ (0 : ℝ)) x := by rw [hzero]
    _ = 0 := PDE.partialDeriv_const 0

/-- The coordinate derivative of a product of two components of a vector field `W` is bounded
by `2 |W| |DW|`. -/
theorem abs_partialDeriv_mul_component_le {m : ℕ} {W : ℝ^n → ℝ^m} {x : ℝ^n}
    (hW : DifferentiableAt ℝ W x) (i j : Fin m) (l : Fin n) :
    |∂[l] (fun y ↦ W y i * W y j) x| ≤ 2 * (‖W x‖ * ‖fderiv ℝ W x‖) := by
  have hi : DifferentiableAt ℝ (fun y ↦ W y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x hW
  have hj : DifferentiableAt ℝ (fun y ↦ W y j) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.comp x hW
  have hc : ∀ k : Fin m, |W x k| ≤ ‖W x‖ := fun k ↦ by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (W x) k
  have hd : ∀ k : Fin m, |∂[l] (fun y ↦ W y k) x| ≤ ‖fderiv ℝ W x‖ := fun k ↦ by
    rw [← partialDeriv_apply l k hW]
    have h := PiLp.norm_apply_le (∂[l] W x) k
    rw [Real.norm_eq_abs] at h
    exact h.trans (norm_partialDeriv_le_norm_fderiv l W x)
  rw [partialDeriv_mul hi hj]
  calc |∂[l] (fun y ↦ W y i) x * W x j + W x i * ∂[l] (fun y ↦ W y j) x|
      ≤ |∂[l] (fun y ↦ W y i) x * W x j| + |W x i * ∂[l] (fun y ↦ W y j) x| := abs_add_le _ _
    _ = |∂[l] (fun y ↦ W y i) x| * |W x j| + |W x i| * |∂[l] (fun y ↦ W y j) x| := by
        rw [abs_mul, abs_mul]
    _ ≤ ‖fderiv ℝ W x‖ * ‖W x‖ + ‖W x‖ * ‖fderiv ℝ W x‖ :=
        add_le_add (mul_le_mul (hd i) (hc j) (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul (hc i) (hd j) (abs_nonneg _) (norm_nonneg _))
    _ = 2 * (‖W x‖ * ‖fderiv ℝ W x‖) := by ring

/-- The coordinate derivative of a scalar function times a fixed vector,
`∂ᵢ(ψ e) = (∂ᵢψ) e`: the case of a constant factor in `partialDeriv_smul`. -/
theorem partialDeriv_smul_const {ψ : ℝ^n → ℝ} {x : ℝ^n} (i : Fin n)
    (hψ : DifferentiableAt ℝ ψ x) (e : F) : ∂[i] (fun y ↦ ψ y • e) x = ∂[i] ψ x • e := by
  rw [partialDeriv_smul hψ (differentiableAt_const e), partialDeriv_const, smul_zero, zero_add]

/-- The Laplacian of a scalar function times a fixed vector. -/
theorem laplacian_smul_const {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ 2 ψ) (e : F) (x : ℝ^n) :
    laplacian (fun y ↦ ψ y • e) x = laplacian ψ x • e := by
  have h1 : ∀ i : Fin n, ∂[i] (fun y ↦ ψ y • e) = fun y ↦ ∂[i] ψ y • e := fun i ↦
    funext fun y ↦ partialDeriv_smul_const i (hψ.differentiable (by norm_num) y) e
  unfold laplacian
  simp only [h1]
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ ↦ partialDeriv_smul_const i
    ((ContDiff.partialDeriv (k := 1) hψ i).differentiable one_ne_zero x) e

/-- The divergence of a scalar function times a coordinate vector is a coordinate derivative of
the function. -/
theorem divergence_smul_single (ψ : ℝ^n → ℝ) (x : ℝ^n) (i : Fin n) :
    ∇· (fun y ↦ ψ y • EuclideanSpace.single i (1 : ℝ)) x = ∂[i] ψ x := by
  rw [divergence_eq_sum, Finset.sum_eq_single i]
  · have h : (fun y ↦ (ψ y • EuclideanSpace.single i (1 : ℝ)) i) = ψ := funext fun y ↦ by simp
    rw [h]
  · intro k _ hk
    have h : (fun y ↦ (ψ y • EuclideanSpace.single i (1 : ℝ)) k) = fun _ ↦ 0 :=
      funext fun y ↦ by simp [hk]
    rw [h]
    exact partialDeriv_const 0
  · intro h
    exact absurd (Finset.mem_univ i) h

end PDE
