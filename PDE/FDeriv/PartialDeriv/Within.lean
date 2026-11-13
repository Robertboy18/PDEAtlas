/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# Partial derivatives within a set

`partialDerivWithin i f s x = fderivWithin ℝ f s x eᵢ` is the coordinate derivative of `f` within
the set `s`. For a function given on a closed half-space it is the derivative up to the boundary:
it depends only on the values of `f` on `s`, it is the ordinary partial derivative where `s` is a
neighbourhood of the point or where `f` is differentiable and `s` has unique derivatives, and it
vanishes off the closure of `s`.

## Main definitions

* `partialDerivWithin`: the derivative of `f` within `s` at `x` in the coordinate direction
  `eᵢ`.

## Main results

* `partialDerivWithin_congr`: at a point of `s` the derivative within `s` depends only on the
  values on `s`.
* `partialDerivWithin_of_mem_nhds`: within a neighbourhood of the point it is the ordinary
  partial derivative.
* `DifferentiableAt.partialDerivWithin_eq`: where `f` is differentiable and `s` has unique
  derivatives it is the ordinary partial derivative.
* `partialDerivWithin_of_notMem_closure`: off the closure of `s` it is zero.
* `ContDiffOn.partialDerivWithin`: a function `C^k` within a set with unique derivatives has
  partial derivatives within it that are `C^m` within it, `m + 1 ≤ k`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : ℝ^n → E} {s : Set (ℝ^n)} {x : ℝ^n}

/-- The partial derivative `∂ᵢ f(x)` within the set `s`: the derivative of `f` within `s` at `x`
in the coordinate direction `eᵢ`. -/
def partialDerivWithin (i : Fin n) (f : ℝ^n → E) (s : Set (ℝ^n)) (x : ℝ^n) : E :=
  fderivWithin ℝ f s x (EuclideanSpace.single i (1 : ℝ))

/-- Within a neighbourhood of the point, the derivative is the ordinary partial derivative. -/
theorem partialDerivWithin_of_mem_nhds (i : Fin n) (h : s ∈ 𝓝 x) :
    partialDerivWithin i f s x = (∂[i] f) x := by
  rw [partialDerivWithin, fderivWithin_of_mem_nhds h]
  rfl

/-- On an open set, the derivative within it is the ordinary partial derivative. -/
theorem partialDerivWithin_of_isOpen (i : Fin n) (hs : IsOpen s) (hx : x ∈ s) :
    partialDerivWithin i f s x = (∂[i] f) x :=
  partialDerivWithin_of_mem_nhds i (hs.mem_nhds hx)

/-- The derivative within the whole space is the ordinary partial derivative. -/
@[simp]
theorem partialDerivWithin_univ (i : Fin n) : partialDerivWithin i f univ = ∂[i] f := by
  funext x
  exact partialDerivWithin_of_mem_nhds i univ_mem

/-- A derivative within `s` gives the partial derivative within `s` where `s` has unique
derivatives. -/
theorem _root_.HasFDerivWithinAt.partialDerivWithin_eq (i : Fin n) {f' : ℝ^n →L[ℝ] E}
    (h : HasFDerivWithinAt f f' s x) (hs : UniqueDiffWithinAt ℝ s x) :
    PDE.partialDerivWithin i f s x = f' (EuclideanSpace.single i (1 : ℝ)) := by
  rw [PDE.partialDerivWithin, h.fderivWithin hs]

/-- Where `f` is differentiable and `s` has unique derivatives, the derivative within `s` is the
ordinary partial derivative. -/
theorem _root_.DifferentiableAt.partialDerivWithin_eq (i : Fin n) (h : DifferentiableAt ℝ f x)
    (hs : UniqueDiffWithinAt ℝ s x) : PDE.partialDerivWithin i f s x = (∂[i] f) x := by
  rw [PDE.partialDerivWithin, fderivWithin_eq_fderiv hs h]
  rfl

/-- The derivative within `s` at a point of `s` depends only on the values on `s`. -/
theorem partialDerivWithin_congr (i : Fin n) (h : EqOn f g s) (hx : x ∈ s) :
    partialDerivWithin i f s x = partialDerivWithin i g s x := by
  rw [partialDerivWithin, partialDerivWithin, fderivWithin_congr' h hx]

/-- The derivative within `s` depends only on the values on `s`, as functions on `s`. -/
theorem partialDerivWithin_eqOn (i : Fin n) (h : EqOn f g s) :
    EqOn (partialDerivWithin i f s) (partialDerivWithin i g s) s :=
  fun _ hx ↦ partialDerivWithin_congr i h hx

/-- Off the closure of `s` the derivative within `s` is zero. -/
theorem partialDerivWithin_of_notMem_closure (i : Fin n) (hx : x ∉ closure s) :
    partialDerivWithin i f s x = 0 := by
  rw [partialDerivWithin, fderivWithin_zero_of_notMem_closure hx]
  rfl

/-- The derivative within a closed set with unique derivatives is linear on functions
differentiable within it, at every point. -/
theorem partialDerivWithin_sum_smul {ι : Type*} (t : Finset ι) (c : ι → ℝ) (u : ι → ℝ^n → E)
    (i : Fin n) (hs : IsClosed s) (hu : UniqueDiffOn ℝ s)
    (hd : ∀ k ∈ t, DifferentiableOn ℝ (u k) s) (x : ℝ^n) :
    partialDerivWithin i (∑ k ∈ t, c k • u k) s x =
      ∑ k ∈ t, c k • partialDerivWithin i (u k) s x := by
  by_cases hx : x ∈ s
  · have hd' : ∀ k ∈ t, DifferentiableWithinAt ℝ (c k • u k) s x :=
      fun k hk ↦ ((hd k hk) x hx).const_smul (c k)
    rw [partialDerivWithin, fderivWithin_sum (hu x hx) hd', sum_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [fderivWithin_const_smul (hu x hx) ((hd k hk) x hx)]
    rfl
  · have hx' : x ∉ closure s := by rwa [hs.closure_eq]
    rw [partialDerivWithin_of_notMem_closure i hx']
    simp [partialDerivWithin_of_notMem_closure i hx']

/-- A function `C^k` within a set with unique derivatives has partial derivatives within it that
are `C^m` within it, `m + 1 ≤ k`. -/
theorem _root_.ContDiffOn.partialDerivWithin {m k : WithTop ℕ∞} (i : Fin n)
    (hf : ContDiffOn ℝ k f s) (hs : UniqueDiffOn ℝ s) (hmk : m + 1 ≤ k) :
    ContDiffOn ℝ m (PDE.partialDerivWithin i f s) s :=
  (hf.fderivWithin hs hmk).clm_apply contDiffOn_const

end PDE
