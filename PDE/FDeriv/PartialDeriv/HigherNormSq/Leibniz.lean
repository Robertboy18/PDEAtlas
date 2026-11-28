/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.PartialDeriv.HigherNormSq

/-!
# The Leibniz rule for coordinate square norms

## Motivation

How large are the derivatives of a product, measured in the coordinate norm
`iteratedCoordinateNorm`?

## The idea

The answer has the same shape as for the operator norm of `iteratedFDeriv`: the norm of order
`k` of `B (f, g)` is at most `‖B‖ ∑ₗ (k choose l) |Dˡf| |D^{k-l}g|`. We prove it by induction on
`k`. One coordinate derivative of `B (f, g)` is `B (∂ᵢ f, g) + B (f, ∂ᵢ g)`, each part obeys the
bound of order `k`, and Minkowski's inequality in `ℝ^n` turns the sum over `i` of the squares
into coordinate norms of order one higher. Pascal's rule collects the binomial coefficients.

## Main results

* `iteratedCoordinateNorm_bilinear_le`: the Leibniz bound for all continuous bilinear maps `B`
  and all `f`, `g` that are `C^k` at the point.
* `iteratedCoordinateNorm_mul_le`, `iteratedCoordinateNorm_clm_apply_le`: the cases of a product
  of real functions and of a family of continuous linear maps applied to a vector function.

## Relations

This is the coordinate-norm form of Mathlib's
`ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`. It uses
`sqrt_sum_sq_le_sum_mul_sqrt` and `iteratedCoordinateNorm_add_le`. The two special cases are
one-line corollaries, and `iteratedCoordinateNorm_comp_le` in
`PDE.FDeriv.PartialDeriv.HigherNormSq.Composition` iterates the second one.

## What stays open

No exact Leibniz formula over words is stated, only the bound.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology

variable {n : ℕ} {F₁ F₂ G : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace PDE

/-- **Leibniz rule for the coordinate norm.** For a continuous bilinear map `B` and functions
`f`, `g` that are `C^k` at `x`, the coordinate norm of order `k` of `y ↦ B (f y) (g y)` at `x` is
at most `‖B‖ ∑ₗ (k choose l) |Dˡf(x)| |D^{k-l}g(x)|`. The proof is an induction on `k` with the
product rule and Minkowski's inequality. -/
theorem iteratedCoordinateNorm_bilinear_le (B : F₁ →L[ℝ] F₂ →L[ℝ] G) (k : ℕ) {f : ℝ^n → F₁}
    {g : ℝ^n → F₂} {x : ℝ^n} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    iteratedCoordinateNorm k (fun y ↦ B (f y) (g y)) x ≤
      ‖B‖ * ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * iteratedCoordinateNorm l f x *
        iteratedCoordinateNorm (k - l) g x := by
  induction k generalizing f g with
  | zero => simpa [mul_assoc] using B.le_opNorm₂ (f x) (g x)
  | succ k ih =>
    have hk : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left 1 k
    have hfk : ContDiffAt ℝ k f x := hf.of_le (by exact_mod_cast Nat.le_succ k)
    have hgk : ContDiffAt ℝ k g x := hg.of_le (by exact_mod_cast Nat.le_succ k)
    -- the product rule holds near `x`
    have hprod (i : Fin n) : ∂[i] (fun y ↦ B (f y) (g y)) =ᶠ[𝓝 x]
        fun y ↦ B ((∂[i] f) y) (g y) + B (f y) ((∂[i] g) y) := by
      filter_upwards [hf.eventually_differentiableAt hk, hg.eventually_differentiableAt hk]
        with y hfy hgy
      simp only [partialDeriv, B.fderiv_of_bilinear hfy hgy, add_apply,
        ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply]
      exact add_comm _ _
    have hbil {f' : ℝ^n → F₁} {g' : ℝ^n → F₂} (hf' : ContDiffAt ℝ k f' x)
        (hg' : ContDiffAt ℝ k g' x) : ContDiffAt ℝ k (fun y ↦ B (f' y) (g' y)) x :=
      B.isBoundedBilinearMap.contDiff.contDiffAt.comp x (hf'.prodMk hg')
    -- both parts of each coordinate derivative obey the bound of order `k`
    have hstep (i : Fin n) : iteratedCoordinateNorm k (∂[i] (fun y ↦ B (f y) (g y))) x ≤
        ∑ l ∈ (Finset.range (k + 1)).disjSum (Finset.range (k + 1)),
          Sum.elim (fun l ↦ ‖B‖ * (k.choose l : ℝ) * iteratedCoordinateNorm (k - l) g x)
            (fun l ↦ ‖B‖ * (k.choose l : ℝ) * iteratedCoordinateNorm l f x) l *
          Sum.elim (fun l ↦ iteratedCoordinateNorm l (∂[i] f) x)
            (fun l ↦ iteratedCoordinateNorm (k - l) (∂[i] g) x) l := by
      rw [(hprod i).iteratedCoordinateNorm k, Finset.sum_disjSum]
      refine (iteratedCoordinateNorm_add_le k (hbil (hf.partialDeriv i le_rfl) hgk)
        (hbil hfk (hg.partialDeriv i le_rfl))).trans ?_
      refine add_le_add ((ih (hf.partialDeriv i le_rfl) hgk).trans_eq ?_)
        ((ih hfk (hg.partialDeriv i le_rfl)).trans_eq ?_)
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ ↦ by simp only [Sum.elim_inl]; ring
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ ↦ by simp only [Sum.elim_inr]; ring
    -- Minkowski's inequality over `i`
    have h := sqrt_sum_sq_le_sum_mul_sqrt ((Finset.range (k + 1)).disjSum (Finset.range (k + 1)))
      (c := Sum.elim (fun l ↦ ‖B‖ * (k.choose l : ℝ) * iteratedCoordinateNorm (k - l) g x)
        (fun l ↦ ‖B‖ * (k.choose l : ℝ) * iteratedCoordinateNorm l f x))
      (u := fun l i ↦ Sum.elim (fun l ↦ iteratedCoordinateNorm l (∂[i] f) x)
        (fun l ↦ iteratedCoordinateNorm (k - l) (∂[i] g) x) l)
      (fun i ↦ iteratedCoordinateNorm_nonneg k _ x)
      (by
        rintro (l | l) _
        · exact mul_nonneg (mul_nonneg B.opNorm_nonneg (Nat.cast_nonneg _))
            (iteratedCoordinateNorm_nonneg _ _ _)
        · exact mul_nonneg (mul_nonneg B.opNorm_nonneg (Nat.cast_nonneg _))
            (iteratedCoordinateNorm_nonneg _ _ _)) hstep
    rw [Finset.sum_disjSum] at h
    simp only [Sum.elim_inl, Sum.elim_inr, ← iteratedCoordinateNorm_succ] at h
    -- Pascal's rule
    refine h.trans_eq ?_
    simp only [mul_assoc]
    rw [Finset.sum_choose_succ_mul
      (fun a b ↦ iteratedCoordinateNorm a f x * iteratedCoordinateNorm b g x) k, mul_add,
      Finset.mul_sum, Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun l hl ↦ ?_
      rw [show k - l + 1 = k + 1 - l by have := Finset.mem_range.mp hl; omega]
    · exact Finset.sum_congr rfl fun l _ ↦ by ring

/-- The Leibniz bound without the factor `‖B‖`, for all bilinear maps of norm at most one. -/
theorem iteratedCoordinateNorm_bilinear_le_of_le_one (B : F₁ →L[ℝ] F₂ →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    (k : ℕ) {f : ℝ^n → F₁} {g : ℝ^n → F₂} {x : ℝ^n} (hf : ContDiffAt ℝ k f x)
    (hg : ContDiffAt ℝ k g x) :
    iteratedCoordinateNorm k (fun y ↦ B (f y) (g y)) x ≤
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * iteratedCoordinateNorm l f x *
        iteratedCoordinateNorm (k - l) g x := by
  refine (iteratedCoordinateNorm_bilinear_le B k hf hg).trans ?_
  refine mul_le_of_le_one_left (Finset.sum_nonneg fun l _ ↦ ?_) hB
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (iteratedCoordinateNorm_nonneg _ _ _))
    (iteratedCoordinateNorm_nonneg _ _ _)

/-- **Leibniz rule for a product of real functions**, in the coordinate norm. -/
theorem iteratedCoordinateNorm_mul_le (k : ℕ) {f g : ℝ^n → ℝ} {x : ℝ^n}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    iteratedCoordinateNorm k (fun y ↦ f y * g y) x ≤
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * iteratedCoordinateNorm l f x *
        iteratedCoordinateNorm (k - l) g x :=
  iteratedCoordinateNorm_bilinear_le_of_le_one (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) k hf hg

/-- **Leibniz rule for a family of continuous linear maps applied to a vector function**, in the
coordinate norm. -/
theorem iteratedCoordinateNorm_clm_apply_le (k : ℕ) {T : ℝ^n → F₁ →L[ℝ] G} {g : ℝ^n → F₁}
    {x : ℝ^n} (hT : ContDiffAt ℝ k T x) (hg : ContDiffAt ℝ k g x) :
    iteratedCoordinateNorm k (fun y ↦ T y (g y)) x ≤
      ∑ l ∈ Finset.range (k + 1), (k.choose l : ℝ) * iteratedCoordinateNorm l T x *
        iteratedCoordinateNorm (k - l) g x :=
  iteratedCoordinateNorm_bilinear_le_of_le_one (ContinuousLinearMap.id ℝ (F₁ →L[ℝ] G))
    ContinuousLinearMap.norm_id_le k hT hg

end PDE
