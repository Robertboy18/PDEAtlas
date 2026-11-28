/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.FamilyNorm
public import PDE.Elliptic.Regularity.Analytic.FrozenOperator

/-!
# The autonomous diagonal system with its coefficients frozen at a point

## Motivation

What does the operator with the coefficients frozen at a point `x` do to a smooth solution
`v = (v_l)` of the system `∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ v_l - f_{l i}(v)) = 0`, and how large are the
derivatives of the result at `x`?

## The idea

Let `L = ∑ᵢⱼ aᵢⱼ(v(x)) ∂ᵢ∂ⱼ`. The frozen coefficients are constants and pass through `∂ᵢ`, so the
equation gives

`L v_l = ∑ᵢ ∂ᵢ (∑ⱼ (aᵢⱼ(v(x)) - aᵢⱼ(v)) ∂ⱼ v_l + f_{l i}(v))`

on the whole domain. The bracket is `frozenFlux a f v x l i`. Its first factor vanishes at `x`,
so in the Leibniz rule for the derivatives of order `k + 1` at `x` the term without a derivative
on the coefficient drops out, and what remains is a sum of products of derivatives of
`aᵢⱼ ∘ v` of order `r ≥ 1` with derivatives of `v` of order `k + 2 - r`.

## Main results

* `frozenOperator_eq_sum_partialDeriv_frozenFlux`: the identity above, at every point where the
  equation holds, `v` is `C²`, and the coefficients and the forcing are differentiable at the
  value of `v`.
* `iteratedCoordinateNorm_frozenOperator_le`: the bound on the coordinate norm of order `k` of
  `L v_l` at `x`, from bounds `α r` on the derivatives of `aᵢⱼ ∘ v` and `φ` on those of
  `f_{l i} ∘ v`.
* `sum_iteratedCoordinateNorm_mul_frozenOperator_le`: the sum over the family that the Bernstein
  inequality needs, in terms of family norms.

## Relations

The class of systems is the one of
`PDE.Elliptic.Regularity.Quasilinear.Bootstrap.contDiffOn_infty_of_autonomous_system`, written
pointwise for a smooth solution. The bounds use `PDE.iteratedCoordinateNorm_mul_le` and
`sum_iteratedCoordinateNorm_mul_le`; they feed
`PDE.Elliptic.Regularity.Analytic.Structure`.

## What stays open

The system has no zero-order source term outside the divergence. The two estimates are stated
for a solution that is smooth on an open set; for a fixed order `k`, finitely many derivatives
near the point would be enough.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ} {I : Type*} [Fintype I] {a : Fin n → Fin n → (I → ℝ) → ℝ}
  {f : I → Fin n → (I → ℝ) → ℝ} {v : ℝ^n → I → ℝ}

/-- The flux of the component `l` in the direction `i` of the autonomous diagonal system:
`∑ⱼ aᵢⱼ(v) ∂ⱼ v_l - f_{l i}(v)`. The system says that its divergence vanishes. -/
def flux (a : Fin n → Fin n → (I → ℝ) → ℝ) (f : I → Fin n → (I → ℝ) → ℝ) (v : ℝ^n → I → ℝ)
    (l : I) (i : Fin n) (y : ℝ^n) : ℝ :=
  ∑ j, a i j (v y) * (∂[j] (fun z ↦ v z l)) y - f l i (v y)

/-- The flux relative to the coefficients frozen at `x`:
`∑ⱼ (aᵢⱼ(v(x)) - aᵢⱼ(v)) ∂ⱼ v_l + f_{l i}(v)`. Its divergence is the frozen operator applied to
`v_l` (`frozenOperator_eq_sum_partialDeriv_frozenFlux`). -/
def frozenFlux (a : Fin n → Fin n → (I → ℝ) → ℝ) (f : I → Fin n → (I → ℝ) → ℝ)
    (v : ℝ^n → I → ℝ) (x : ℝ^n) (l : I) (i : Fin n) (y : ℝ^n) : ℝ :=
  ∑ j, (a i j (v x) - a i j (v y)) * (∂[j] (fun z ↦ v z l)) y + f l i (v y)

/-- **The frozen equation.** At a point `y` where the component `l` of the system holds, the
operator with coefficients frozen at `x` applied to `v_l` is the divergence of the frozen flux.
Here `v` is `C²` at `y` and the coefficients and the forcing are differentiable at `v y`. -/
theorem frozenOperator_eq_sum_partialDeriv_frozenFlux {x y : ℝ^n} (hv : ContDiffAt ℝ 2 v y)
    (ha : ∀ i j, DifferentiableAt ℝ (a i j) (v y))
    (hf : ∀ l i, DifferentiableAt ℝ (f l i) (v y)) (l : I)
    (heq : ∑ i, (∂[i] (flux a f v l i)) y = 0) :
    frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l) y =
      ∑ i, (∂[i] (frozenFlux a f v x l i)) y := by
  have hvd : DifferentiableAt ℝ v y := hv.differentiableAt (by norm_num)
  have hvl : ContDiffAt ℝ 2 (fun z ↦ v z l) y := contDiffAt_pi.mp hv l
  have hdj (j : Fin n) : DifferentiableAt ℝ (∂[j] (fun z ↦ v z l)) y :=
    (hvl.partialDeriv j (k := 1) (by norm_num)).differentiableAt (by norm_num)
  have hlin (i : Fin n) :
      DifferentiableAt ℝ (fun z ↦ ∑ j, a i j (v x) * (∂[j] (fun z ↦ v z l)) z) y :=
    DifferentiableAt.fun_sum fun j _ ↦ (hdj j).const_mul _
  have hflux (i : Fin n) : DifferentiableAt ℝ (flux a f v l i) y :=
    (DifferentiableAt.fun_sum fun j _ ↦ ((ha i j).comp y hvd).mul (hdj j)).sub
      ((hf l i).comp y hvd)
  -- the frozen flux is the frozen linear flux minus the flux of the system
  have hsplit (i : Fin n) : frozenFlux a f v x l i =
      fun z ↦ (∑ j, a i j (v x) * (∂[j] (fun z ↦ v z l)) z) - flux a f v l i z := by
    funext z
    simp only [frozenFlux, flux, sub_mul, Finset.sum_sub_distrib]
    ring
  have hi (i : Fin n) : (∂[i] (frozenFlux a f v x l i)) y =
      (∑ j, a i j (v x) * (∂[i] (∂[j] (fun z ↦ v z l))) y) - (∂[i] (flux a f v l i)) y := by
    rw [hsplit i, partialDeriv_sub (hlin i) (hflux i),
      partialDeriv_sum Finset.univ (fun j _ ↦ (hdj j).const_mul _) i]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ congrFun (partialDeriv_const_mul_fun _ i) y
  simp only [hi, Finset.sum_sub_distrib, heq, sub_zero, frozenOperator]

section Bounds

variable {U : Set (ℝ^n)} {x : ℝ^n} {k : ℕ} {α : ℕ → ℝ} {φ : ℝ}

/-- **Derivatives of the frozen operator applied to a solution.** Let `v` be smooth on an open
set `U` where the system holds, with coefficients and forcing smooth along `v`. If at `x ∈ U`
the coordinate norms of order `r + 1 ≤ k + 1` of every `aᵢⱼ ∘ v` are at most `α (r + 1)` and
those of order `k + 1` of every `f_{l i} ∘ v` are at most `φ`, then the coordinate norm of order
`k` of `∑ᵢⱼ aᵢⱼ(v(x)) ∂ᵢ∂ⱼ v_l` at `x` is at most
`n² ∑_{r ≤ k} (k+1 choose r+1) α(r+1) |D^{k+1-r} v_l(x)| + n φ`. -/
theorem iteratedCoordinateNorm_frozenOperator_le (hU : IsOpen U) (hxU : x ∈ U)
    (hv : ContDiffOn ℝ ∞ v U) (ha : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ∞ (a i j) (v y))
    (hf : ∀ y ∈ U, ∀ l i, ContDiffAt ℝ ∞ (f l i) (v y))
    (heq : ∀ y ∈ U, ∀ l, ∑ i, (∂[i] (flux a f v l i)) y = 0) (l : I)
    (hα : ∀ i j r, r ≤ k →
      iteratedCoordinateNorm (r + 1) (fun y ↦ a i j (v y)) x ≤ α (r + 1))
    (hφ : ∀ i, iteratedCoordinateNorm (k + 1) (fun y ↦ f l i (v y)) x ≤ φ) :
    iteratedCoordinateNorm k (frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l)) x ≤
      (n : ℝ) ^ 2 * ∑ r ∈ Finset.range (k + 1), ((k + 1).choose (r + 1) : ℝ) * α (r + 1) *
        iteratedCoordinateNorm (k + 1 - r) (fun z ↦ v z l) x + n * φ := by
  have hvx (y : ℝ^n) (hy : y ∈ U) : ContDiffAt ℝ ∞ v y := hv.contDiffAt (hU.mem_nhds hy)
  have hle (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  -- the frozen equation holds near `x`
  have hfrozen : frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l) =ᶠ[𝓝 x]
      fun y ↦ ∑ i, (∂[i] (frozenFlux a f v x l i)) y := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact frozenOperator_eq_sum_partialDeriv_frozenFlux ((hvx y hy).of_le (by norm_num))
      (fun i j ↦ (ha y hy i j).differentiableAt (by simp))
      (fun l i ↦ (hf y hy l i).differentiableAt (by simp)) l (heq y hy l)
  -- smoothness of the pieces of the frozen flux at `x`
  have hvl : ContDiffAt ℝ ∞ (fun z ↦ v z l) x := contDiffAt_pi.mp (hvx x hxU) l
  have hd (j : Fin n) : ContDiffAt ℝ ∞ (∂[j] (fun z ↦ v z l)) x :=
    hvl.partialDeriv j (by simp)
  have hav (i j : Fin n) : ContDiffAt ℝ ∞ (fun y ↦ a i j (v y)) x :=
    (ha x hxU i j).comp x (hvx x hxU)
  have hb (i j : Fin n) : ContDiffAt ℝ ∞ (fun y ↦ a i j (v x) - a i j (v y)) x :=
    contDiffAt_const.sub (hav i j)
  have he (i : Fin n) : ContDiffAt ℝ ∞ (fun y ↦ f l i (v y)) x :=
    (hf x hxU l i).comp x (hvx x hxU)
  have hprod (i j : Fin n) : ContDiffAt ℝ ∞
      (fun y ↦ (a i j (v x) - a i j (v y)) * (∂[j] (fun z ↦ v z l)) y) x :=
    (hb i j).mul (hd j)
  have hsumj (i : Fin n) : ContDiffAt ℝ ∞
      (fun y ↦ ∑ j, (a i j (v x) - a i j (v y)) * (∂[j] (fun z ↦ v z l)) y) x :=
    ContDiffAt.sum fun j _ ↦ hprod i j
  have hG (i : Fin n) : ContDiffAt ℝ ∞ (frozenFlux a f v x l i) x := (hsumj i).add (he i)
  -- the Leibniz rule for one product; the term without a derivative on the coefficient vanishes
  set S := ∑ r ∈ Finset.range (k + 1), ((k + 1).choose (r + 1) : ℝ) * α (r + 1) *
    iteratedCoordinateNorm (k + 1 - r) (fun z ↦ v z l) x with hS
  have hleib (i j : Fin n) : iteratedCoordinateNorm (k + 1)
      (fun y ↦ (a i j (v x) - a i j (v y)) * (∂[j] (fun z ↦ v z l)) y) x ≤ S := by
    refine (iteratedCoordinateNorm_mul_le (k + 1) ((hb i j).of_le (hle _))
      ((hd j).of_le (hle _))).trans ?_
    rw [Finset.sum_range_succ']
    have hzero : iteratedCoordinateNorm 0 (fun y ↦ a i j (v x) - a i j (v y)) x = 0 := by
      simp
    rw [hzero, mul_zero, zero_mul, add_zero]
    refine Finset.sum_le_sum fun r hr ↦ ?_
    have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have h1 : iteratedCoordinateNorm (r + 1) (fun y ↦ a i j (v x) - a i j (v y)) x ≤
        α (r + 1) := by
      rw [iteratedCoordinateNorm, iteratedCoordinateNormSq_const_sub (Nat.succ_ne_zero r)]
      exact hα i j r hrk
    have h2 : iteratedCoordinateNorm (k + 1 - (r + 1)) (∂[j] (fun z ↦ v z l)) x ≤
        iteratedCoordinateNorm (k + 1 - r) (fun z ↦ v z l) x := by
      rw [show k + 1 - r = (k + 1 - (r + 1)) + 1 by omega]
      exact iteratedCoordinateNorm_partialDeriv_le _ _ x j
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
      (iteratedCoordinateNorm_nonneg _ _ _)
      (mul_nonneg (Nat.cast_nonneg _) ((iteratedCoordinateNorm_nonneg _ _ _).trans h1))
  -- one component of the frozen flux
  have hflux (i : Fin n) : iteratedCoordinateNorm (k + 1) (frozenFlux a f v x l i) x ≤
      n * S + φ := by
    refine (iteratedCoordinateNorm_add_le (k + 1) ((hsumj i).of_le (hle _))
      ((he i).of_le (hle _))).trans (add_le_add ?_ (hφ i))
    refine (iteratedCoordinateNorm_sum_le Finset.univ (k + 1)
      fun j _ ↦ (hprod i j).of_le (hle _)).trans ?_
    calc ∑ j, iteratedCoordinateNorm (k + 1)
          (fun y ↦ (a i j (v x) - a i j (v y)) * (∂[j] (fun z ↦ v z l)) y) x
        ≤ ∑ _j : Fin n, S := Finset.sum_le_sum fun j _ ↦ hleib i j
      _ = n * S := by simp
  -- the divergence of the frozen flux
  rw [hfrozen.iteratedCoordinateNorm k]
  calc iteratedCoordinateNorm k (fun y ↦ ∑ i, (∂[i] (frozenFlux a f v x l i)) y) x
      ≤ ∑ i, iteratedCoordinateNorm k (∂[i] (frozenFlux a f v x l i)) x :=
        iteratedCoordinateNorm_sum_le Finset.univ k
          fun i _ ↦ ((hG i).partialDeriv i (by simp)).of_le (hle _)
    _ ≤ ∑ i, iteratedCoordinateNorm (k + 1) (frozenFlux a f v x l i) x :=
        Finset.sum_le_sum fun i _ ↦ iteratedCoordinateNorm_partialDeriv_le k _ x i
    _ ≤ ∑ _i : Fin n, (n * S + φ) := Finset.sum_le_sum fun i _ ↦ hflux i
    _ = (n : ℝ) ^ 2 * S + n * φ := by simp; ring

/-- **The cross term of the Bernstein inequality for a solution.** In the setting of
`iteratedCoordinateNorm_frozenOperator_le`, with nonnegative bounds `α` and `φ` valid for every
component, the sum over the family of `|Dᵏ v_l| |Dᵏ(L v_l)|` at `x` is at most
`|Dᵏ v| (n² ∑_{r ≤ k} (k+1 choose r+1) α(r+1) |D^{k+1-r} v| + n |I| φ)`, in family norms. -/
theorem sum_iteratedCoordinateNorm_mul_frozenOperator_le (hU : IsOpen U) (hxU : x ∈ U)
    (hv : ContDiffOn ℝ ∞ v U) (ha : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ∞ (a i j) (v y))
    (hf : ∀ y ∈ U, ∀ l i, ContDiffAt ℝ ∞ (f l i) (v y))
    (heq : ∀ y ∈ U, ∀ l, ∑ i, (∂[i] (flux a f v l i)) y = 0) (hα0 : ∀ r, 0 ≤ α r)
    (hφ0 : 0 ≤ φ)
    (hα : ∀ i j r, r ≤ k →
      iteratedCoordinateNorm (r + 1) (fun y ↦ a i j (v y)) x ≤ α (r + 1))
    (hφ : ∀ l i, iteratedCoordinateNorm (k + 1) (fun y ↦ f l i (v y)) x ≤ φ) :
    ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
        iteratedCoordinateNorm k (frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l)) x ≤
      familyNorm k v x * ((n : ℝ) ^ 2 * ∑ r ∈ Finset.range (k + 1),
        ((k + 1).choose (r + 1) : ℝ) * α (r + 1) * familyNorm (k + 1 - r) v x +
          n * Fintype.card I * φ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
        iteratedCoordinateNorm k (frozenOperator (fun i j ↦ a i j (v x)) (fun z ↦ v z l)) x
      ≤ ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
          ((n : ℝ) ^ 2 * ∑ r ∈ Finset.range (k + 1), ((k + 1).choose (r + 1) : ℝ) *
            α (r + 1) * iteratedCoordinateNorm (k + 1 - r) (fun z ↦ v z l) x + n * φ) :=
        Finset.sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_left
          (iteratedCoordinateNorm_frozenOperator_le hU hxU hv ha hf heq l hα (hφ l))
          (iteratedCoordinateNorm_nonneg _ _ _)
    _ = (n : ℝ) ^ 2 * ∑ r ∈ Finset.range (k + 1), ((k + 1).choose (r + 1) : ℝ) * α (r + 1) *
          ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
            iteratedCoordinateNorm (k + 1 - r) (fun z ↦ v z l) x +
          n * φ * ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
        · exact Finset.sum_congr rfl fun l _ ↦ by ring
    _ ≤ (n : ℝ) ^ 2 * ∑ r ∈ Finset.range (k + 1), ((k + 1).choose (r + 1) : ℝ) * α (r + 1) *
          (familyNorm k v x * familyNorm (k + 1 - r) v x) +
          n * φ * (Fintype.card I * familyNorm k v x) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ ↦ ?_)
          (sq_nonneg _)) (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hn hφ0))
        · exact mul_le_mul_of_nonneg_left (sum_iteratedCoordinateNorm_mul_le k (k + 1 - r) v x)
            (mul_nonneg (Nat.cast_nonneg _) (hα0 _))
        · calc ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x
              ≤ ∑ _l : I, familyNorm k v x :=
                Finset.sum_le_sum fun l _ ↦ iteratedCoordinateNorm_apply_le_familyNorm k v x l
            _ = Fintype.card I * familyNorm k v x := by simp
    _ = _ := by
        simp only [mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun r _ ↦ by ring
        · ring

end Bounds

end PDE.Elliptic.Regularity.Analytic
