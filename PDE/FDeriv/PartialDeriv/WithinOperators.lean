/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.FDeriv.PartialDeriv.Within
import PDE.FDeriv.Calculus

/-!
# Advection and the Laplacian within a set

For fields given on a closed set `s` (a closed half-space, say), the transport term and the
Laplacian are taken with the derivatives within `s`. At a point of `s` they depend only on the
values of `f` on `s`, and on an open subset of `s` they are the ordinary `advectiveDerivative`
and `laplacian`, with no regularity hypothesis.

## Main definitions

* `PDE.advectiveDerivativeWithin`: `D_s f(x) (u x)`, the derivative of `f` within `s` in the
  direction of the velocity `u x`.
* `PDE.laplacianWithin`: `∑ᵢ ∂ᵢ^s ∂ᵢ^s f(x)`, with both derivatives within `s`.

## Main results

* `eqOn_advectiveDerivativeWithin`: on an open subset of `s`, advection within `s` is ordinary
  advection.
* `advectiveDerivativeWithin_congr`: at a point of `s`, advection within `s` depends only on the
  values of the field on `s`.
* `advectiveDerivativeWithin_eq_sum`: the coordinate formula for scalar advection within a set.
* `eqOn_laplacianWithin`: on an open subset of `s`, the Laplacian within `s` is the ordinary
  Laplacian.
* `laplacianWithin_congr`: at a point of `s`, the Laplacian within `s` depends only on the values
  of `f` on `s`.
* `laplacianWithin_eq_laplacian`: for a function `C²` at a point of a set with unique
  derivatives, the Laplacian within the set is the ordinary Laplacian.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : ℝ^n → E} {s U : Set (ℝ^n)} {x : ℝ^n}

/-! ### Agreement with the ordinary derivatives on open subsets -/

/-- On an open subset of `s`, the partial derivative within `s` is the ordinary one. -/
theorem eqOn_partialDerivWithin (hU : IsOpen U) (hUs : U ⊆ s) (i : Fin n) :
    EqOn (partialDerivWithin i f s) (∂[i] f) U := fun _ hx ↦
  partialDerivWithin_of_mem_nhds i (mem_of_superset (hU.mem_nhds hx) hUs)

/-- On an open subset of `s`, the ordinary derivative of a partial derivative within `s` is the
ordinary second derivative. -/
theorem eqOn_partialDeriv_partialDerivWithin (hU : IsOpen U) (hUs : U ⊆ s) (i j : Fin n) :
    EqOn (∂[j] (partialDerivWithin i f s)) (∂[j] (∂[i] f)) U := by
  intro y hy
  have hloc : partialDerivWithin i f s =ᶠ[𝓝 y] ∂[i] f :=
    eventuallyEq_of_mem (hU.mem_nhds hy) (eqOn_partialDerivWithin hU hUs i)
  exact (hloc.partialDeriv j).eq_of_nhds

/-- On an open subset of `s`, a second partial derivative within `s` is the ordinary one. -/
theorem eqOn_partialDerivWithin_partialDerivWithin (hU : IsOpen U) (hUs : U ⊆ s) (i j : Fin n) :
    EqOn (partialDerivWithin j (partialDerivWithin i f s) s) (∂[j] (∂[i] f)) U := fun y hy ↦ by
  rw [eqOn_partialDerivWithin hU hUs j hy]
  exact eqOn_partialDeriv_partialDerivWithin hU hUs i j hy

/-! ### Algebra of partial derivatives within a set -/

/-- The partial derivative within `s` of a sum. -/
theorem partialDerivWithin_fun_add (i : Fin n) (hs : UniqueDiffWithinAt ℝ s x)
    (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x) :
    partialDerivWithin i (fun y ↦ f y + g y) s x =
      partialDerivWithin i f s x + partialDerivWithin i g s x := by
  simp only [partialDerivWithin, fderivWithin_fun_add hs hf hg, add_apply]

/-- The partial derivative within `s` of a difference. -/
theorem partialDerivWithin_fun_sub (i : Fin n) (hs : UniqueDiffWithinAt ℝ s x)
    (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x) :
    partialDerivWithin i (fun y ↦ f y - g y) s x =
      partialDerivWithin i f s x - partialDerivWithin i g s x := by
  simp only [partialDerivWithin, fderivWithin_fun_sub hs hf hg, sub_apply]

/-- The partial derivative within `s` of a negative. -/
theorem partialDerivWithin_fun_neg (i : Fin n) (hs : UniqueDiffWithinAt ℝ s x) :
    partialDerivWithin i (fun y ↦ -f y) s x = -partialDerivWithin i f s x := by
  simp only [partialDerivWithin, fderivWithin_fun_neg hs, neg_apply]

/-- Two partial derivatives within a set with unique derivatives of a sum of functions `C²` within
it. -/
theorem partialDerivWithin_partialDerivWithin_fun_add (i j : Fin n) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s) :
    partialDerivWithin j (partialDerivWithin i (fun y ↦ f y + g y) s) s x =
      partialDerivWithin j (partialDerivWithin i f s) s x +
        partialDerivWithin j (partialDerivWithin i g s) s x := by
  have h1 : EqOn (partialDerivWithin i (fun y ↦ f y + g y) s)
      (fun y ↦ partialDerivWithin i f s y + partialDerivWithin i g s y) s := fun y hy ↦
    partialDerivWithin_fun_add i (hs y hy) ((hf.differentiableOn (by norm_num)) y hy)
      ((hg.differentiableOn (by norm_num)) y hy)
  rw [partialDerivWithin_congr j h1 hx]
  exact partialDerivWithin_fun_add j (hs x hx)
    (((hf.partialDerivWithin (m := 1) i hs (by norm_num)).differentiableOn one_ne_zero) x hx)
    (((hg.partialDerivWithin (m := 1) i hs (by norm_num)).differentiableOn one_ne_zero) x hx)

/-- Two partial derivatives within a set with unique derivatives of a difference of functions `C²`
within it. -/
theorem partialDerivWithin_partialDerivWithin_fun_sub (i j : Fin n) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s) :
    partialDerivWithin j (partialDerivWithin i (fun y ↦ f y - g y) s) s x =
      partialDerivWithin j (partialDerivWithin i f s) s x -
        partialDerivWithin j (partialDerivWithin i g s) s x := by
  have h1 : EqOn (partialDerivWithin i (fun y ↦ f y - g y) s)
      (fun y ↦ partialDerivWithin i f s y - partialDerivWithin i g s y) s := fun y hy ↦
    partialDerivWithin_fun_sub i (hs y hy) ((hf.differentiableOn (by norm_num)) y hy)
      ((hg.differentiableOn (by norm_num)) y hy)
  rw [partialDerivWithin_congr j h1 hx]
  exact partialDerivWithin_fun_sub j (hs x hx)
    (((hf.partialDerivWithin (m := 1) i hs (by norm_num)).differentiableOn one_ne_zero) x hx)
    (((hg.partialDerivWithin (m := 1) i hs (by norm_num)).differentiableOn one_ne_zero) x hx)

/-- For a function `C²` on the whole space, two partial derivatives within a set with unique
derivatives are the ordinary ones at points of the set. -/
theorem partialDerivWithin_partialDerivWithin_of_contDiff (i j : Fin n) (hf : ContDiff ℝ 2 f)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    partialDerivWithin j (partialDerivWithin i f s) s x = (∂[j] (∂[i] f)) x := by
  have h1 : EqOn (partialDerivWithin i f s) (∂[i] f) s := fun y hy ↦
    (hf.differentiable (by norm_num) y).partialDerivWithin_eq i (hs y hy)
  rw [partialDerivWithin_congr j h1 hx]
  exact ((((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
    one_ne_zero) x).partialDerivWithin_eq j (hs x hx)

/-! ### Advection within a set -/

/-- The advective derivative of `f` along `u` within `s`: the derivative of `f` within `s` at `x`
applied to `u x`. -/
def advectiveDerivativeWithin (u : ℝ^n → ℝ^n) (f : ℝ^n → E) (s : Set (ℝ^n)) (x : ℝ^n) : E :=
  fderivWithin ℝ f s x (u x)

/-- Coordinate formula for scalar advection within a set. -/
theorem advectiveDerivativeWithin_eq_sum (u : ℝ^n → ℝ^n) (f : ℝ^n → ℝ) (s : Set (ℝ^n))
    (x : ℝ^n) :
    advectiveDerivativeWithin u f s x = ∑ i : Fin n, u x i * partialDerivWithin i f s x := by
  rw [advectiveDerivativeWithin]
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (u x)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  simp [partialDerivWithin]

/-- Within a neighbourhood of the point, advection within `s` is ordinary advection. -/
theorem advectiveDerivativeWithin_of_mem_nhds (u : ℝ^n → ℝ^n) (h : s ∈ 𝓝 x) :
    advectiveDerivativeWithin u f s x = advectiveDerivative u f x := by
  rw [advectiveDerivativeWithin, fderivWithin_of_mem_nhds h]
  rfl

/-- On an open subset of `s`, advection within `s` is ordinary advection. -/
theorem eqOn_advectiveDerivativeWithin (u : ℝ^n → ℝ^n) (hU : IsOpen U) (hUs : U ⊆ s) :
    EqOn (advectiveDerivativeWithin u f s) (advectiveDerivative u f) U := fun _ hx ↦
  advectiveDerivativeWithin_of_mem_nhds u (mem_of_superset (hU.mem_nhds hx) hUs)

/-- At a point of `s`, advection within `s` depends only on the values of the field on `s`. -/
theorem advectiveDerivativeWithin_congr (u : ℝ^n → ℝ^n) (h : EqOn f g s) (hx : x ∈ s) :
    advectiveDerivativeWithin u f s x = advectiveDerivativeWithin u g s x := by
  rw [advectiveDerivativeWithin, advectiveDerivativeWithin, fderivWithin_congr' h hx]

/-- Advection within `s` is additive in the field. -/
theorem advectiveDerivativeWithin_add (u : ℝ^n → ℝ^n) (hs : UniqueDiffWithinAt ℝ s x)
    (hf : DifferentiableWithinAt ℝ f s x) (hg : DifferentiableWithinAt ℝ g s x) :
    advectiveDerivativeWithin u (f + g) s x =
      advectiveDerivativeWithin u f s x + advectiveDerivativeWithin u g s x := by
  simp only [advectiveDerivativeWithin, fderivWithin_add hs hf hg, add_apply]

/-- Scalar advection within a closed set with unique derivatives is linear on fields
differentiable within it, at every point. -/
theorem advectiveDerivativeWithin_sum_smul {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (u : ℝ^n → ℝ^n) (f : ι → ℝ^n → ℝ) (hs : IsClosed s) (hu : UniqueDiffOn ℝ s)
    (hd : ∀ k ∈ t, DifferentiableOn ℝ (f k) s) (x : ℝ^n) :
    advectiveDerivativeWithin u (∑ k ∈ t, c k • f k) s x =
      ∑ k ∈ t, c k * advectiveDerivativeWithin u (f k) s x := by
  simp only [advectiveDerivativeWithin_eq_sum, partialDerivWithin_sum_smul t c f _ hs hu hd x,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

/-- Advection within `s` is additive in the velocity. -/
theorem advectiveDerivativeWithin_add_velocity (u v : ℝ^n → ℝ^n) :
    advectiveDerivativeWithin (u + v) f s x =
      advectiveDerivativeWithin u f s x + advectiveDerivativeWithin v f s x := by
  simp only [advectiveDerivativeWithin, Pi.add_apply, map_add]

/-! ### The Laplacian within a set -/

/-- The Laplacian within `s`, `∑ᵢ ∂ᵢ^s (∂ᵢ^s f)`, with both derivatives within `s`. -/
def laplacianWithin (f : ℝ^n → E) (s : Set (ℝ^n)) (x : ℝ^n) : E :=
  ∑ i : Fin n, partialDerivWithin i (partialDerivWithin i f s) s x

/-- On an open subset of `s`, the Laplacian within `s` is the ordinary Laplacian. -/
theorem eqOn_laplacianWithin (hU : IsOpen U) (hUs : U ⊆ s) :
    EqOn (laplacianWithin f s) (laplacian f) U := fun _ hy ↦
  Finset.sum_congr rfl fun i _ ↦ eqOn_partialDerivWithin_partialDerivWithin hU hUs i i hy

/-- At a point of `s`, the Laplacian within `s` depends only on the values of `f` on `s`. -/
theorem laplacianWithin_congr (h : EqOn f g s) (hx : x ∈ s) :
    laplacianWithin f s x = laplacianWithin g s x :=
  Finset.sum_congr rfl fun i _ ↦ partialDerivWithin_congr i (partialDerivWithin_eqOn i h) hx

/-- Partial derivatives within `s` of functions with the same germ at `x` have the same germ. -/
theorem partialDerivWithin_eventuallyEq (i : Fin n) (h : f =ᶠ[𝓝 x] g) :
    partialDerivWithin i f s =ᶠ[𝓝 x] partialDerivWithin i g s := by
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.1 h
  filter_upwards [hUo.mem_nhds hxU] with y hy
  have hy' : f =ᶠ[𝓝[s] y] g := nhdsWithin_le_nhds (eventuallyEq_of_mem (hUo.mem_nhds hy) hU)
  rw [partialDerivWithin, partialDerivWithin, hy'.fderivWithin_eq (hU hy)]

/-- The Laplacian within `s` at `x` depends only on the germ of the function at `x`. -/
theorem laplacianWithin_congr_nhds (h : f =ᶠ[𝓝 x] g) :
    laplacianWithin f s x = laplacianWithin g s x := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 := partialDerivWithin_eventuallyEq (s := s) i h
  have h2 : partialDerivWithin i f s =ᶠ[𝓝[s] x] partialDerivWithin i g s :=
    nhdsWithin_le_nhds h1
  rw [partialDerivWithin, partialDerivWithin, h2.fderivWithin_eq h1.eq_of_nhds]

/-- For a function `C²` at a point of a set with unique derivatives, the Laplacian within the set
is the ordinary Laplacian. -/
theorem laplacianWithin_eq_laplacian (hf : ContDiffAt ℝ 2 f x) (hs : UniqueDiffOn ℝ s)
    (hx : x ∈ s) : laplacianWithin f s x = laplacian f x := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hev : partialDerivWithin i f s =ᶠ[𝓝[s] x] ∂[i] f := by
    filter_upwards [nhdsWithin_le_nhds (hf.eventually (by simp)), self_mem_nhdsWithin]
      with y hy hys
    exact (hy.differentiableAt (by norm_num)).partialDerivWithin_eq i (hs y hys)
  have hd : DifferentiableAt ℝ (∂[i] f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [partialDerivWithin, hev.fderivWithin_eq (hev.eq_of_nhdsWithin hx)]
  exact hd.partialDerivWithin_eq i (hs x hx)

end PDE
