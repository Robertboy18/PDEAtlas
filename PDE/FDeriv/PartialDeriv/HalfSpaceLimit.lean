/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.Within
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Iterated partial derivatives within a set and their limits from an open subset

For a function that is `C^k` within a set `s` with unique derivatives (a closed half-space, say),
the iterated coordinate derivatives within `s` are `C^{k - j}` within `s`, and on an open subset
`U ⊆ s` they coincide with the ordinary iterated partial derivatives. Hence the ordinary iterated
partial derivatives of order at most `k` have limits at every point of `s` from `U`: the values of
the derivatives within `s` there. On a closed coordinate half-space, a function vanishing on the
boundary hyperplane has derivatives within the half-space in the tangential directions that
vanish on the hyperplane.

## Main results

* `PDE.iteratedPartialDerivWithin`: the iterated partial derivative within `s` along a word.
* `PDE.eqOn_iteratedPartialDeriv`: agreement with `iteratedPartialDeriv` on `U` and regularity.
* `PDE.tendsto_iteratedPartialDeriv`: the limit from `U`.
* `PDE.partialDerivWithin_eq_zero_of_eqOn_hyperplane`,
  `PDE.iteratedPartialDerivWithin_replicate_eq_zero`: tangential derivatives of a zero trace.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The iterated partial derivative within `s` along a word of coordinate directions; the head of
the word is the outermost derivative, as for `iteratedPartialDeriv`. -/
def iteratedPartialDerivWithin (indices : List (Fin n)) (f : ℝ^n → E) (s : Set (ℝ^n)) :
    ℝ^n → E :=
  match indices with
  | [] => f
  | i :: rest => partialDerivWithin i (iteratedPartialDerivWithin rest f s) s

/-- Along the empty word the iterated partial derivative within `s` is `f` itself. -/
@[simp] theorem iteratedPartialDerivWithin_nil (f : ℝ^n → E) (s : Set (ℝ^n)) :
    iteratedPartialDerivWithin [] f s = f := rfl

/-- Along `i :: rest` the iterated partial derivative within `s` is the partial derivative `∂ᵢ`
within `s` of the one along `rest`. -/
@[simp] theorem iteratedPartialDerivWithin_cons (i : Fin n) (rest : List (Fin n))
    (f : ℝ^n → E) (s : Set (ℝ^n)) :
    iteratedPartialDerivWithin (i :: rest) f s =
      partialDerivWithin i (iteratedPartialDerivWithin rest f s) s := rfl

variable {f : ℝ^n → E} {s U : Set (ℝ^n)}

/-- On an open subset `U` of a set `s` with unique derivatives, the iterated partial derivatives
of a function `C^{j + m}` within `s` along a word of length `j` agree with those within `s`, which
are `C^m` within `s`. -/
theorem eqOn_iteratedPartialDeriv (hU : IsOpen U) (hUs : U ⊆ s) (hs : UniqueDiffOn ℝ s)
    (indices : List (Fin n)) {m : ℕ}
    (hf : ContDiffOn ℝ ((indices.length + m : ℕ) : WithTop ℕ∞) f s) :
    EqOn (iteratedPartialDeriv indices f) (iteratedPartialDerivWithin indices f s) U ∧
      ContDiffOn ℝ m (iteratedPartialDerivWithin indices f s) s := by
  induction indices generalizing m with
  | nil => exact ⟨fun x _ ↦ rfl, by simpa using hf⟩
  | cons i rest ih =>
    have hf' : ContDiffOn ℝ ((rest.length + (m + 1) : ℕ) : WithTop ℕ∞) f s := by
      have : (i :: rest).length + m = rest.length + (m + 1) := by simp; omega
      rwa [this] at hf
    obtain ⟨heq, hreg⟩ := ih hf'
    refine ⟨fun x hx ↦ ?_, hreg.partialDerivWithin i hs (by norm_cast)⟩
    have hloc : iteratedPartialDeriv rest f =ᶠ[𝓝 x] iteratedPartialDerivWithin rest f s :=
      eventuallyEq_of_mem (hU.mem_nhds hx) heq
    have hsx : s ∈ 𝓝 x := mem_of_superset (hU.mem_nhds hx) hUs
    have hdiff : DifferentiableAt ℝ (iteratedPartialDerivWithin rest f s) x :=
      ((hreg.differentiableOn (by norm_num)) x (hUs hx)).differentiableAt hsx
    change partialDeriv i (fun y ↦ iteratedPartialDeriv rest f y) x = _
    rw [iteratedPartialDerivWithin_cons, partialDerivWithin_of_mem_nhds i hsx]
    exact partialDeriv_eq_of_fderiv_eq (hloc.fderiv_eq (𝕜 := ℝ)) i

/-- The iterated partial derivatives of order at most `k` of a function `C^k` within `s` have
limits from an open subset `U ⊆ s` at every point of `s`. -/
theorem tendsto_iteratedPartialDeriv (hU : IsOpen U) (hUs : U ⊆ s) (hs : UniqueDiffOn ℝ s)
    (indices : List (Fin n)) (hf : ContDiffOn ℝ indices.length f s) {p : ℝ^n} (hp : p ∈ s) :
    Tendsto (iteratedPartialDeriv indices f) (𝓝[U] p)
      (𝓝 (iteratedPartialDerivWithin indices f s p)) := by
  obtain ⟨heq, hreg⟩ := eqOn_iteratedPartialDeriv hU hUs hs indices (m := 0) (by simpa using hf)
  refine ((hreg.continuousOn p hp).mono hUs).tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (heq hx).symm

/-- On the closed half-space `{0 ≤ x c}`, the derivative within the half-space in a tangential
direction of a function vanishing on the boundary hyperplane vanishes there. -/
theorem partialDerivWithin_eq_zero_of_eqOn_hyperplane {c j : Fin n} (hjc : j ≠ c)
    (hf : ∀ x : ℝ^n, x c = 0 → f x = 0) {x : ℝ^n} (hx : x c = 0)
    (hd : DifferentiableWithinAt ℝ f {y : ℝ^n | 0 ≤ y c} x) :
    partialDerivWithin j f {y : ℝ^n | 0 ≤ y c} x = 0 := by
  set γ : ℝ → ℝ^n := fun t ↦ x + t • EuclideanSpace.single j (1 : ℝ)
  have hγ : ∀ t, γ t c = 0 := fun t ↦ by simp [γ, hx, Ne.symm hjc]
  have hmaps : MapsTo γ univ {y : ℝ^n | 0 ≤ y c} := fun t _ ↦ by
    simp only [mem_ofPred_eq, hγ t, le_refl]
  have hγd : HasDerivWithinAt γ (EuclideanSpace.single j (1 : ℝ)) univ 0 := by
    have h : HasDerivAt γ ((1 : ℝ) • EuclideanSpace.single j (1 : ℝ)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add x
    rw [one_smul] at h
    exact h.hasDerivWithinAt
  have hγ0 : γ 0 = x := by simp [γ]
  have hcomp := (hγ0 ▸ hd.hasFDerivWithinAt).comp_hasDerivWithinAt (0 : ℝ) hγd hmaps
  have hzero : HasDerivWithinAt (f ∘ γ) 0 univ 0 := by
    have : f ∘ γ = fun _ ↦ 0 := funext fun t ↦ hf _ (hγ t)
    rw [this]
    exact hasDerivWithinAt_const _ _ _
  have h1 := hcomp.derivWithin uniqueDiffWithinAt_univ
  rw [hzero.derivWithin uniqueDiffWithinAt_univ] at h1
  rw [hγ0] at h1
  simpa [partialDerivWithin] using h1.symm

/-- Iterated tangential derivatives within the closed half-space of a function `C^k` within it
and vanishing on the boundary hyperplane vanish on the hyperplane. -/
theorem iteratedPartialDerivWithin_replicate_eq_zero {c j : Fin n} (hjc : j ≠ c) {k : ℕ}
    (hf : ContDiffOn ℝ k f {y : ℝ^n | 0 ≤ y c}) (hzero : ∀ x : ℝ^n, x c = 0 → f x = 0) :
    ∀ x : ℝ^n, x c = 0 →
      iteratedPartialDerivWithin (List.replicate k j) f {y : ℝ^n | 0 ≤ y c} x = 0 := by
  have hs : UniqueDiffOn ℝ {y : ℝ^n | 0 ≤ y c} := by
    apply uniqueDiffOn_convex (convex_halfSpace_ge (EuclideanSpace.proj c).isLinear 0)
    refine ⟨EuclideanSpace.single c 1, mem_interior_iff_mem_nhds.mpr ?_⟩
    apply Filter.mem_of_superset
      ((isOpen_lt continuous_const (EuclideanSpace.proj c).continuous).mem_nhds
        (show (0 : ℝ) < (EuclideanSpace.single c 1 : ℝ^n) c by simp))
    intro x hx
    exact (show 0 < x c from hx).le
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    have hk : ContDiffOn ℝ k f {y : ℝ^n | 0 ≤ y c} := hf.of_le (by norm_cast; omega)
    intro x hx
    rw [List.replicate_succ, iteratedPartialDerivWithin_cons]
    have hreg := (eqOn_iteratedPartialDeriv (U := ∅) isOpen_empty (empty_subset _) hs
      (List.replicate k j) (m := 1) (by simpa using hf)).2
    refine partialDerivWithin_eq_zero_of_eqOn_hyperplane hjc (ih hk) hx ?_
    exact (hreg.differentiableOn (by norm_num)) x (show 0 ≤ x c by rw [hx])

end PDE
