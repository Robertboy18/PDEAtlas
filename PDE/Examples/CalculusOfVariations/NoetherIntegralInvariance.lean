/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.IntegralInvariance
public import PDE.CalculusOfVariations.Noether.Scalar
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Scalar Noether identity from invariance of the action

Let `w t` be a family of scalar fields and `Φ t` a family of injective `C²` maps with `Φ 0 = id`,
such that for small `t` the action of `w t` over every bounded open `V` equals the action of `w 0`
over `Φ t '' V`; this is the invariance (6) of Evans, §8.6.1. With `m = ∂ₜw` and `v = ∂ₜΦ` at
`t = 0`, the Noether current `m Lp − L v` has divergence `m (div Lp − Lz)`, as in Noether's theorem,
Evans, §8.6.2, Theorem 1(i), (7). This identity holds without an Euler–Lagrange equation. For a
solution of the Euler–Lagrange equation the current is divergence free, Theorem 1(ii), (8). The
example derives the scalar statement from `divergence_noetherCurrent_of_domain_invariance`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.1, (2), (5) and (6), p. 512, and §8.6.2,
  Theorem 1 (Noether's Theorem), (7)-(8), p. 513.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Elementwise Gradient Topology

namespace PDE.Examples.CalculusOfVariations

open PDE.CalculusOfVariations PDE.CalculusOfVariations.Noether

variable {n : ℕ} {L : ℝ^n → ℝ → ℝ^n → ℝ}
  {w : ℝ → ℝ^n → ℝ} {Φ : ℝ → ℝ^n → ℝ^n}
  (hL : ContDiff ℝ 2 (fun q : ℝ^n × (ℝ × ℝ^n) ↦ L q.1 q.2.1 q.2.2))
  (hw : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y,
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ w p.1 p.2) (t, y))
  (hΦ : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y,
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (t, y))
  (hΦ₀ : Φ 0 = id) (hinj : ∀ᶠ t in 𝓝 0, Function.Injective (Φ t))
  (hinvariant : ∀ᶠ t in 𝓝 0, ∀ V : Set (ℝ^n), IsOpen V → Bornology.IsBounded V →
    (∫ y in V, L (∇ (w t) y) (w t y) y) =
      ∫ y in Φ t '' V, L (∇ (w 0) y) (w 0 y) y)

include hL hw hΦ hΦ₀ hinj hinvariant in
/-- The scalar Noether identity for an invariant action, and the conservation law for
solutions of the Euler–Lagrange equation. -/
example (x : ℝ^n) :
    ∇· (fun y ↦ deriv (fun t ↦ w t y) 0 • ∇ (fun p ↦ L p (w 0 y) y) (∇ (w 0) y) -
      L (∇ (w 0) y) (w 0 y) y • deriv (fun t ↦ Φ t y) 0) x =
    deriv (fun t ↦ w t x) 0 *
      (∇· (fun y ↦ ∇ (fun p ↦ L p (w 0 y) y) (∇ (w 0) y)) x -
        deriv (fun z ↦ L (∇ (w 0) x) z x) (w 0 x)) ∧
    (-∇· (fun y ↦ ∇ (fun p ↦ L p (w 0 y) y) (∇ (w 0) y)) x +
        deriv (fun z ↦ L (∇ (w 0) x) z x) (w 0 x) = 0 →
      ∇· (fun y ↦ deriv (fun t ↦ w t y) 0 • ∇ (fun p ↦ L p (w 0 y) y) (∇ (w 0) y) -
        L (∇ (w 0) y) (w 0 y) y • deriv (fun t ↦ Φ t y) 0) x = 0) := by
  let U (t : ℝ) (y : ℝ^n) : ℝ^1 := WithLp.toLp 2 (fun _ ↦ w t y)
  have hU : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y,
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (t, y) := by
    filter_upwards [hw] with t ht
    exact fun y ↦ contDiffAt_euclidean.mpr (fun _ ↦ ht y)
  have hI : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ V : Set (ℝ^n), IsOpen V → Bornology.IsBounded V →
      (∫ y in V, fieldDensity (scalarLagrangian L) (U t) y) =
        ∫ y in Φ t '' V, fieldDensity (scalarLagrangian L) (U 0) y := by
    simpa only [fieldDensity_scalarLagrangian, U] using hinvariant
  have hvel (y : ℝ^n) : deriv (fun t ↦ U t y) 0 0 = deriv (fun t ↦ w t y) 0 := by
    have hd : DifferentiableAt ℝ (fun t ↦ U t y) 0 :=
      ((hU.self_of_nhds y).comp 0 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
        (by norm_num)
    have hp := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt.comp_hasDerivAt
      0 hd.hasDerivAt
    exact hp.deriv.symm
  have hfinite := fieldDensity_eventually_eq_of_integral_invariance
    (contDiff_scalarLagrangian hL) hU hΦ hΦ₀ hinj hI x
  have hid := divergence_noetherCurrent_of_domain_invariance
    (contDiff_scalarLagrangian hL).contDiffAt (hU.self_of_nhds x) (hΦ.self_of_nhds x)
    (Eventually.of_forall (congrFun hΦ₀)) hfinite
  have hcur : noetherCurrent (scalarLagrangian L) (U 0)
      (fun y ↦ deriv (fun t ↦ U t y) 0) (fun y ↦ -deriv (fun t ↦ Φ t y) 0) =
      (fun y ↦ deriv (fun t ↦ w t y) 0 • ∇ (fun p ↦ L p (w 0 y) y) (∇ (w 0) y) -
        L (∇ (w 0) y) (w 0 y) y • deriv (fun t ↦ Φ t y) 0) := by
    funext y
    rw [noetherCurrent_scalarLagrangian _ _ _ _
      (hL.differentiable (by norm_num) _), hvel]
    simp only [U, smul_neg, sub_eq_add_neg]
  rw [hcur] at hid
  simp only [Fin.sum_univ_one, classicalEulerLagrange_scalarLagrangian (U 0) x
    (Eventually.of_forall (fun _ ↦ hL.differentiable (by norm_num) _)), hvel] at hid
  constructor
  · rw [hid]
    ring
  · intro hEL
    rw [hid]
    change -((-∇· (fun y ↦ ∇ (fun p ↦ L p (w 0 y) y) (∇ (w 0) y)) x +
      deriv (fun z ↦ L (∇ (w 0) x) z x) (w 0 x)) * _) = 0
    rw [hEL, zero_mul, neg_zero]

end PDE.Examples.CalculusOfVariations
