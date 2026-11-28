/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

import PDE.Analysis.Operator.FiniteRankDeterminant
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The finite-rank determinant criterion: the embedded form and a family of instances

## Motivation

Does the determinant criterion `Analysis.Operator.exists_eigenvalue_of_det_neg` cover a space
that is embedded in `L²`, with the `L²` pairing on the right of the eigenvalue equation, and can
all of its hypotheses hold at once, also in infinite dimension?

## The idea

A bounded linear map `ι : X → H` into a real inner product space defines the bounded form
`J h g = ⟪ι h, ι g⟫`. For this form the third inequality of the criterion reads
`‖ℓ h‖² ≤ c_F ‖ι h‖²`, and the eigenvalue equation `L⋆ h = λ J h` reads
`⟪L⋆ h, g⟫ = λ ⟪ι h, ι g⟫` for every `g` in `X`. With `H = L²` and `ι` the embedding, this is
the weak eigenvalue equation with the `L²` pairing on the right.

For the instances let `e` be a unit vector of a real Hilbert space `H` and let `P` be the
orthogonal projection onto its line. Take `D = H`, `m = 1`, `ℓ h = 2 ⟪e, h⟫`, `Φ q = -q e`,
`L⋆ = 1 - 4 P` and the inner product as `J`. Then `L⋆ + ℓ† ℓ` is the Riesz map `h ↦ ⟪h, ·⟫`,
which is onto, `⟪L⋆ h, h⟫ + ‖ℓ h‖² = ‖h‖²`, `⟪L⋆ (h + Φ ℓ h), h⟫ = ‖h‖² + 2 ⟪e, h⟫²`,
`‖ℓ h‖² = 4 ⟪e, h⟫² ≤ 4 ‖h‖²`, and `det (1 + ℓ Φ) = -1`.

## Main results

* The first example holds for all real normed spaces `X`, real inner product spaces `H` and
  bounded linear maps `ι : X → H`: the criterion with the pairing of `H` on the right.
* The second example is a family of instances: in every real Hilbert space with a unit vector
  `e`, the hypotheses of the criterion hold for the data above with `a = 1` and `c_F = 4`. The
  criterion gives an eigenvalue of `1 - 4 P` in `(-4, 0)`, in agreement with
  `(1 - 4 P) e = -3 e`.
* The third example holds for all data of `Analysis.Operator.exists_kernel_of_det_neg` whose
  coordinate map `ℓ` vanishes at a nonzero vector: then `t_G ≥ 1` and `δ ≥ 0`, so the constant
  `min (1 - θ - ε) (1 - θ - δ - ε t_G)` is `1 - θ - δ - ε t_G`.

## Relations

The first two examples apply `Analysis.Operator.exists_eigenvalue_of_det_neg`. The third
concerns the constant `a` with which `Analysis.Operator.exists_kernel_of_det_neg` follows from
the criterion.

## What stays open

In the instances the domain `D` is the whole space and `L⋆` is bounded. The hypotheses for the
self-similar Navier–Stokes linearization, where `L⋆` is unbounded, are not checked in this
library.
-/

set_option linter.privateModule false

open Set
open scoped RealInnerProductSpace

namespace PDE.Examples

open Analysis.Operator

/-- The criterion for a space `X` with a bounded linear map `ι` into a real inner product space
`H`, with the pairing of `H` on the right of the eigenvalue equation. -/
example {X H : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {m : ℕ} (ι : X →L[ℝ] H) (D : Submodule ℝ X)
    (Lstar : D →ₗ[ℝ] StrongDual ℝ X) (ℓ : X →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] D) {a cF : ℝ} (ha : 0 < a) (hcF : 0 < cF)
    (hsurj : ∀ f : StrongDual ℝ X, ∃ h : D, Lstar h + coordTranspose ℓ (ℓ h) = f)
    (hcoer : ∀ h : D, a * ‖(h : X)‖ ^ 2 ≤ Lstar h h + ‖ℓ h‖ ^ 2)
    (hcoerΦ : ∀ h : D, a * ‖(h : X)‖ ^ 2 ≤ Lstar (h + Φ (ℓ h)) h)
    (hℓ : ∀ h : X, ‖ℓ h‖ ^ 2 ≤ cF * ‖ι h‖ ^ 2)
    (hdet : LinearMap.det (1 + ℓ.toLinearMap ∘ₗ D.subtype ∘ₗ Φ) < 0) :
    ∃ lambda ∈ Ioo (-cF) 0, ∃ h : D, h ≠ 0 ∧ ∀ g : X, Lstar h g = lambda * ⟪ι h, ι g⟫ := by
  obtain ⟨lambda, hlambda, h, hh0, hh⟩ := exists_eigenvalue_of_det_neg D Lstar
    ((innerSL ℝ).bilinearComp ι ι) ℓ Φ ha hcF hsurj hcoer hcoerΦ
    (fun h ↦ by simpa using hℓ h) hdet
  exact ⟨lambda, hlambda, h, hh0, fun g ↦ by rw [hh]; simp⟩

/-- A family of instances of every hypothesis of the criterion. In a real Hilbert space `H` with
a unit vector `e`, take `D = H`, `m = 1`, `ℓ h = 2 ⟪e, h⟫`, `Φ q = -q e`, the inner product as
`J` and `L⋆ = 1 - 4 P`, where `P` is the orthogonal projection onto the line of `e`. The
hypotheses hold with `a = 1` and `c_F = 4`, and the criterion gives `λ` in `(-4, 0)` and `h ≠ 0`
with `(1 - 4 P) h = λ h` in the weak form. -/
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (e : H)
    (he : ‖e‖ = 1) :
    ∃ lambda ∈ Ioo (-4 : ℝ) 0, ∃ h : H, h ≠ 0 ∧
      ∀ g : H, ⟪h, g⟫ - 4 * (⟪e, h⟫ * ⟪e, g⟫) = lambda * ⟪h, g⟫ := by
  -- The data: `J` is the inner product, `L⋆ = 1 - 4 P`, `ℓ h = 2 ⟪e, h⟫` and `Φ q = -q e`.
  let J : H →L[ℝ] StrongDual ℝ H :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ H) (ContinuousLinearMap.id ℝ H)
  let Lstar : (⊤ : Submodule ℝ H) →ₗ[ℝ] StrongDual ℝ H :=
    (J - (4 : ℝ) • (innerSL ℝ e).smulRight (innerSL ℝ e)).toLinearMap ∘ₗ
      (⊤ : Submodule ℝ H).subtype
  let ℓ : H →L[ℝ] EuclideanSpace ℝ (Fin 1) := coordinateMap fun _ ↦ (2 : ℝ) • innerSL ℝ e
  let Φ : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] (⊤ : Submodule ℝ H) :=
    (reconstruction fun _ ↦ -e).toLinearMap.codRestrict ⊤ fun _ ↦ Submodule.mem_top
  have hJ : ∀ h g : H, J h g = ⟪h, g⟫ := fun h g ↦ by simp [J]
  have hL : ∀ (h : (⊤ : Submodule ℝ H)) (g : H),
      Lstar h g = ⟪(h : H), g⟫ - 4 * (⟪e, (h : H)⟫ * ⟪e, g⟫) := fun h g ↦ by
    simp [Lstar, hJ]
  have hℓ0 : ∀ h : H, ℓ h 0 = 2 * ⟪e, h⟫ := fun h ↦ by simp [ℓ]
  have hℓ : ∀ h : H, ‖ℓ h‖ ^ 2 = 4 * ⟪e, h⟫ ^ 2 := fun h ↦ by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, hℓ0, Real.norm_eq_abs, sq_abs]
    ring
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hΦ : ∀ h : H, ((Φ (ℓ h) : (⊤ : Submodule ℝ H)) : H) = -(2 * ⟪e, h⟫) • e := fun h ↦ by
    simp [Φ, reconstruction_apply, hℓ0]
  -- `L⋆ + ℓ† ℓ` is the Riesz map, which is onto.
  have hsurj : ∀ f : StrongDual ℝ H, ∃ h : (⊤ : Submodule ℝ H),
      Lstar h + coordTranspose ℓ (ℓ h) = f := fun f ↦ by
    refine ⟨⟨(InnerProductSpace.toDual ℝ H).symm f, Submodule.mem_top⟩, ?_⟩
    ext g
    rw [add_apply, hL, coordTranspose_coordinateMap_apply, Fin.sum_univ_one, hℓ0,
      InnerProductSpace.toDual_symm_apply]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  -- `⟪L⋆ h, h⟫ + ‖ℓ h‖² = ‖h‖²`.
  have hcoer : ∀ h : (⊤ : Submodule ℝ H), 1 * ‖(h : H)‖ ^ 2 ≤ Lstar h h + ‖ℓ h‖ ^ 2 := fun h ↦ by
    rw [hL, hℓ, real_inner_self_eq_norm_sq]
    exact le_of_eq (by ring)
  -- `⟪L⋆ (h + Φ ℓ h), h⟫ = ‖h‖² + 2 ⟪e, h⟫²`.
  have hcoerΦ : ∀ h : (⊤ : Submodule ℝ H), 1 * ‖(h : H)‖ ^ 2 ≤ Lstar (h + Φ (ℓ h)) h := fun h ↦ by
    rw [hL, Submodule.coe_add, hΦ, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hee, real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ⟪e, (h : H)⟫]
  -- `‖ℓ h‖² = 4 ⟪e, h⟫² ≤ 4 ‖h‖²` by the Cauchy–Schwarz inequality.
  have hJℓ : ∀ h : H, ‖ℓ h‖ ^ 2 ≤ 4 * J h h := fun h ↦ by
    rw [hℓ, hJ, real_inner_self_eq_norm_sq]
    have := abs_real_inner_le_norm e h
    rw [he, one_mul] at this
    nlinarith [sq_abs ⟪e, h⟫, abs_nonneg ⟪e, h⟫, norm_nonneg h]
  -- `ℓ Φ = -2`, so `det (1 + ℓ Φ) = -1`.
  have hdet : LinearMap.det (1 + ℓ.toLinearMap ∘ₗ (⊤ : Submodule ℝ H).subtype ∘ₗ Φ) < 0 := by
    rw [det_one_add_eq_det_of_apply_single (Λ := Matrix.of fun _ _ ↦ (-2 : ℝ)) _
      (fun i j ↦ by simp [ℓ, Φ, he])]
    simp [Matrix.det_unique]
  obtain ⟨lambda, hlambda, h, hh0, hh⟩ := exists_eigenvalue_of_det_neg ⊤ Lstar J ℓ Φ one_pos
    (by norm_num) hsurj hcoer hcoerΦ hJℓ hdet
  refine ⟨lambda, hlambda, h, fun h0 ↦ hh0 (Subtype.ext h0), fun g ↦ ?_⟩
  have := congrArg (fun F : StrongDual ℝ H ↦ F g) hh
  simpa [hL, hJ] using this

/-- The constant of the perturbative form. If the coordinate map `ℓ` vanishes at a nonzero
vector, for example when the dimension of `E` exceeds `m`, the amplification bound forces
`t_G ≥ 1` and the residual bound forces `δ ≥ 0`. For `ε ≥ 0` the constant
`min (1 - θ - ε) (1 - θ - δ - ε t_G)`, with which `exists_kernel_of_det_neg` follows from
`exists_eigenvalue_of_det_neg`, is then `1 - θ - δ - ε t_G`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ} {D : Submodule ℝ E}
    (L : D →ₗ[ℝ] StrongDual ℝ E) (ℓ : E →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Φ : EuclideanSpace ℝ (Fin m) →L[ℝ] E) (hΦ : ∀ q, Φ q ∈ D) {θ δ ε tG : ℝ}
    (hres : ∀ h, ‖L ⟨Φ (ℓ h), hΦ (ℓ h)⟩ - coordTranspose ℓ (ℓ h)‖ ≤ δ * ‖h‖)
    (htG : ∀ h, ‖h + Φ (ℓ h)‖ ≤ tG * ‖h‖) (hε : 0 ≤ ε) {h : E} (hh : h ≠ 0) (hℓ : ℓ h = 0) :
    min (1 - θ - ε) (1 - θ - δ - ε * tG) = 1 - θ - δ - ε * tG := by
  have hpos : 0 < ‖h‖ := norm_pos_iff.2 hh
  have h1 : 1 ≤ tG := by
    have := htG h
    rw [hℓ, map_zero, add_zero] at this
    exact le_of_mul_le_mul_right (by linarith) hpos
  have h2 : 0 ≤ δ := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hres h)) hpos
  exact min_eq_right (by nlinarith [mul_nonneg hε (sub_nonneg.2 h1)])

end PDE.Examples
