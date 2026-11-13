/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.TensorOperatorSemantics

/-!
# Symbolic weak-form integrands

Pointwise symbolic integrands for the standard weak formulations: the Dirichlet form
`∇u · ∇v`, the `L²` mass form `u v`, the Poisson residual `∇u · ∇v - f v`, the heat residual
`u_t v + ∇ₓu · ∇ₓv - f v` and wave residual `u_tt v + ∇ₓu · ∇ₓv - f v` with an explicit time
coordinate and an explicit list of spatial coordinates, the modified Helmholtz residual
`∇u · ∇v + κ u v - f v`, and the small-strain energy `ε(u) : ε(v)` built from symmetric
gradients. Each is a `Verified.Expr` obtained from `closedPartial` and the checked normalizer,
so it can be manipulated by the symbolic layer and integrated by the quadrature layer.

The accompanying theorems identify each integrand, evaluated at a point where the differentiated
expressions are valid, with its analytic coordinate formula in terms of `partialDeriv`. They are
pointwise statements; integration over a domain and the integration by parts that produces
these integrands from the strong form are separate steps.

## Main results

* `dirichletIntegrand`, `dirichletIntegrand_eval_eq_sum_partialDeriv_mul`.
* `massIntegrand`, `massIntegrand_eval_eq_mul`.
* `poissonWeakResidualIntegrand`,
  `poissonWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_sub`.
* `spatialDirichletIntegrand`,
  `spatialDirichletIntegrand_eval_eq_list_sum_partialDeriv_mul`: the Dirichlet form over an
  explicit list of spatial coordinates, so that the time coordinate is never differentiated
  by accident in the time-dependent residuals.
* `heatWeakResidualIntegrand`, `waveWeakResidualIntegrand`,
  `modifiedHelmholtzWeakResidualIntegrand` and their evaluation theorems.
* `symmetricGradientEnergyIntegrand`,
  `symmetricGradientEnergyIntegrand_eval_eq_sum_partialDeriv_average_mul_average`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1(b), (8), p. 373, and (9) and the definition of a
  weak solution, p. 374.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace CAS

open scoped BigOperators

/-- Symbolic Dirichlet weak-form integrand `∇u · ∇v`. -/
def dirichletIntegrand {n : Nat} (u v : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  dotProduct (Verified.Expr.closedGradient u) (Verified.Expr.closedGradient v)

/-- The symbolic Dirichlet integrand evaluates to the sum of analytic coordinate-partial
products. -/
theorem dirichletIntegrand_eval_eq_sum_partialDeriv_mul {n : Nat}
    (u v : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) (hv : v.ValidAt x) :
    (dirichletIntegrand u v).eval x =
      ∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x := by
  unfold dirichletIntegrand Verified.Expr.closedGradient
  rw [dotProduct_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.closedPartial i u) *
        Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.closedPartial i v) =
      (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
        (∂[i] (fun y : ℝ^n ↦ v.eval y)) x
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u) (x := x) (i := i) hu]
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := v) (x := x) (i := i) hv]

/-- Symbolic `L²` mass-form integrand `u v`. -/
def massIntegrand {n : Nat} (u v : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize (u * v)

/-- The symbolic `L²` integrand evaluates to the product of the denoted functions. -/
theorem massIntegrand_eval_eq_mul {n : Nat}
    (u v : Verified.Expr (Fin n)) (x : ℝ^n) :
    (massIntegrand u v).eval x = u.eval x * v.eval x := by
  unfold massIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k) (Verified.Expr.Alg.normalize (u * v)) =
      u.eval x * v.eval x
  rw [Verified.Expr.Alg.eval_normalize]
  simp [Verified.Expr.eval]

/-- Symbolic Poisson weak-form residual integrand `∇u · ∇v - f v`.

This is the pointwise integrand before domain integration against the test function `v`. -/
def poissonWeakResidualIntegrand {n : Nat}
    (u f v : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize (dirichletIntegrand u v - f * v)

/-- The symbolic Poisson weak residual evaluates to the coordinate Dirichlet sum minus the
source-test product. -/
theorem poissonWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_sub {n : Nat}
    (u f v : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) (hv : v.ValidAt x) :
    (poissonWeakResidualIntegrand u f v).eval x =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x) -
        f.eval x * v.eval x := by
  unfold poissonWeakResidualIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize (dirichletIntegrand u v - f * v)) =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x) -
        f.eval x * v.eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (dirichletIntegrand u v).eval x - f.eval x * v.eval x =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x) -
        f.eval x * v.eval x
  rw [dirichletIntegrand_eval_eq_sum_partialDeriv_mul
    (u := u) (v := v) (x := x) hu hv]

/-- Symbolic spatial Dirichlet integrand over an explicit coordinate list.

This is the space-time form of `dirichletIntegrand`: the caller names exactly the
spatial coordinates that appear in `∇ₓu · ∇ₓv`, so the time coordinate is excluded from
the weak heat and wave integrands.
-/
def spatialDirichletRaw {n : Nat} (spatial : List (Verified.Expr.SymVar n))
    (u v : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  spatial.foldr
    (fun coord acc ↦
      Verified.Expr.closedPartial coord.idx u *
        Verified.Expr.closedPartial coord.idx v + acc)
    0

/-- Normalized symbolic spatial Dirichlet integrand over an explicit coordinate list. -/
def spatialDirichletIntegrand {n : Nat} (spatial : List (Verified.Expr.SymVar n))
    (u v : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize (spatialDirichletRaw spatial u v)

/-- The spatial Dirichlet integrand evaluates to the sum over exactly the selected coordinate
partials. -/
theorem spatialDirichletIntegrand_eval_eq_list_sum_partialDeriv_mul {n : Nat}
    (spatial : List (Verified.Expr.SymVar n)) (u v : Verified.Expr (Fin n))
    (p : ℝ^n) (hu : u.ValidAt p) (hv : v.ValidAt p) :
    (spatialDirichletIntegrand spatial u v).eval p =
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum := by
  unfold spatialDirichletIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ p k)
        (Verified.Expr.Alg.normalize (spatialDirichletRaw spatial u v)) =
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum
  rw [Verified.Expr.Alg.eval_normalize]
  induction spatial with
  | nil =>
      simp [spatialDirichletRaw]
  | cons coord rest ih =>
      change
        (Verified.Expr.closedPartial coord.idx u).eval p *
              (Verified.Expr.closedPartial coord.idx v).eval p +
            (spatialDirichletRaw rest u v).eval p =
          (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
              (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p +
            (rest.map fun next ↦
              (∂[next.idx] (fun q : ℝ^n ↦ u.eval q)) p *
                (∂[next.idx]
                  (fun q : ℝ^n ↦ v.eval q)) p).sum
      rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
        (expr := u) (x := p) (i := coord.idx) hu]
      rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
        (expr := v) (x := p) (i := coord.idx) hv]
      change Verified.Expr.eval p (spatialDirichletRaw rest u v) = _ at ih
      rw [ih]

/-- Symbolic weak heat-equation residual integrand
`u_t v + ∇ₓu · ∇ₓv - f v`.

The time coordinate and the spatial coordinates are explicit arguments. For `L = -Δ` the
bilinear form (8) of Evans, §7.1.1(b), is `B[u, v; t] = ∫ ∇u · ∇v`, so the integral of this
residual over `U` is the left side of (9) there minus its right side. The spatial gradient is
taken over the named coordinates only.
-/
def heatWeakResidualIntegrand {n : Nat} (t : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (u f v : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize
    (Verified.Expr.closedPartial t.idx u * v +
      spatialDirichletIntegrand spatial u v - f * v)

/-- The symbolic weak heat residual evaluates to its analytic coordinate-partial formula. -/
theorem heatWeakResidualIntegrand_eval_eq_time_mul_add_spatial_sum_sub {n : Nat}
    (t : Verified.Expr.SymVar n) (spatial : List (Verified.Expr.SymVar n))
    (u f v : Verified.Expr (Fin n)) (p : ℝ^n)
    (hu : u.ValidAt p) (hv : v.ValidAt p) :
    (heatWeakResidualIntegrand t spatial u f v).eval p =
      (∂[t.idx] (fun q : ℝ^n ↦ u.eval q)) p *
        v.eval p +
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum -
      f.eval p * v.eval p := by
  unfold heatWeakResidualIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ p k)
        (Verified.Expr.Alg.normalize
          (Verified.Expr.closedPartial t.idx u * v +
            spatialDirichletIntegrand spatial u v - f * v)) =
      (∂[t.idx] (fun q : ℝ^n ↦ u.eval q)) p *
        v.eval p +
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum -
      f.eval p * v.eval p
  rw [Verified.Expr.Alg.eval_normalize]
  change
    Verified.Expr.eval (fun k : Fin n ↦ p k) (Verified.Expr.closedPartial t.idx u) *
        v.eval p +
      (spatialDirichletIntegrand spatial u v).eval p - f.eval p * v.eval p =
      (∂[t.idx] (fun q : ℝ^n ↦ u.eval q)) p *
        v.eval p +
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum -
      f.eval p * v.eval p
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u) (x := p) (i := t.idx) hu]
  rw [spatialDirichletIntegrand_eval_eq_list_sum_partialDeriv_mul
    (spatial := spatial) (u := u) (v := v) (p := p) hu hv]

/-- Symbolic weak wave-equation residual integrand
`u_tt v + ∇ₓu · ∇ₓv - f v`.

As with the heat weak-form construction, the time coordinate and spatial-coordinate
list are explicit. The second time derivative is represented by differentiating
the checked first time derivative once more.
-/
def waveWeakResidualIntegrand {n : Nat} (t : Verified.Expr.SymVar n)
    (spatial : List (Verified.Expr.SymVar n)) (u f v : Verified.Expr (Fin n)) :
    Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize
    (Verified.Expr.closedPartial t.idx (Verified.Expr.closedPartial t.idx u) * v +
      spatialDirichletIntegrand spatial u v - f * v)

/-- The symbolic weak wave residual evaluates to its analytic coordinate formula, with the second
time derivative written as `∂t` applied to the checked first derivative. -/
theorem waveWeakResidualIntegrand_eval_eq_time2_mul_add_spatial_sum_sub {n : Nat}
    (t : Verified.Expr.SymVar n) (spatial : List (Verified.Expr.SymVar n))
    (u f v : Verified.Expr (Fin n)) (p : ℝ^n)
    (hdt : (Verified.Expr.closedPartial t.idx u).ValidAt p)
    (hu : u.ValidAt p) (hv : v.ValidAt p) :
    (waveWeakResidualIntegrand t spatial u f v).eval p =
      (∂[t.idx]
          (fun q : ℝ^n ↦ (Verified.Expr.closedPartial t.idx u).eval q)) p *
        v.eval p +
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum -
      f.eval p * v.eval p := by
  unfold waveWeakResidualIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ p k)
        (Verified.Expr.Alg.normalize
          (Verified.Expr.closedPartial t.idx (Verified.Expr.closedPartial t.idx u) * v +
            spatialDirichletIntegrand spatial u v - f * v)) =
      (∂[t.idx]
          (fun q : ℝ^n ↦ (Verified.Expr.closedPartial t.idx u).eval q)) p *
        v.eval p +
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum -
      f.eval p * v.eval p
  rw [Verified.Expr.Alg.eval_normalize]
  change
    Verified.Expr.eval (fun k : Fin n ↦ p k)
        (Verified.Expr.closedPartial t.idx (Verified.Expr.closedPartial t.idx u)) *
        v.eval p +
      (spatialDirichletIntegrand spatial u v).eval p - f.eval p * v.eval p =
      (∂[t.idx]
          (fun q : ℝ^n ↦ (Verified.Expr.closedPartial t.idx u).eval q)) p *
        v.eval p +
      (spatial.map fun coord ↦
        (∂[coord.idx] (fun q : ℝ^n ↦ u.eval q)) p *
          (∂[coord.idx] (fun q : ℝ^n ↦ v.eval q)) p).sum -
      f.eval p * v.eval p
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := Verified.Expr.closedPartial t.idx u) (x := p) (i := t.idx) hdt]
  rw [spatialDirichletIntegrand_eval_eq_list_sum_partialDeriv_mul
    (spatial := spatial) (u := u) (v := v) (p := p) hu hv]

/-- Symbolic modified Helmholtz weak-form residual integrand `∇u · ∇v + κ u v - f v`.

This is the integrand of the shifted coercive bilinear form minus a load term, before
integration over the domain. -/
def modifiedHelmholtzWeakResidualIntegrand {n : Nat}
    (κ u f v : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  Verified.Expr.Alg.normalize (dirichletIntegrand u v + κ * u * v - f * v)

/-- The symbolic modified Helmholtz residual evaluates to the Dirichlet, mass, and source terms. -/
theorem modifiedHelmholtzWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_add_sub {n : Nat}
    (κ u f v : Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : u.ValidAt x) (hv : v.ValidAt x) :
    (modifiedHelmholtzWeakResidualIntegrand κ u f v).eval x =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x) +
        κ.eval x * u.eval x * v.eval x -
        f.eval x * v.eval x := by
  unfold modifiedHelmholtzWeakResidualIntegrand
  change
    Verified.Expr.eval (fun k : Fin n ↦ x k)
        (Verified.Expr.Alg.normalize (dirichletIntegrand u v + κ * u * v - f * v)) =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x) +
        κ.eval x * u.eval x * v.eval x -
        f.eval x * v.eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (dirichletIntegrand u v).eval x + κ.eval x * u.eval x * v.eval x -
        f.eval x * v.eval x =
      (∑ i : Fin n,
        (∂[i] (fun y : ℝ^n ↦ u.eval y)) x *
          (∂[i] (fun y : ℝ^n ↦ v.eval y)) x) +
        κ.eval x * u.eval x * v.eval x -
        f.eval x * v.eval x
  rw [dirichletIntegrand_eval_eq_sum_partialDeriv_mul
    (u := u) (v := v) (x := x) hu hv]

/-- Symbolic small-strain bilinear-form integrand, using the Frobenius pairing of symmetric
gradients. -/
def symmetricGradientEnergyIntegrand {n : Nat}
    (u v : Fin n → Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  frobeniusInnerProduct (symmetricGradient u) (symmetricGradient v)

/-- The symbolic small-strain integrand evaluates to the Frobenius product of the analytic
symmetric-gradient entries. -/
theorem symmetricGradientEnergyIntegrand_eval_eq_sum_partialDeriv_average_mul_average
    {n : Nat}
    (u v : Fin n → Verified.Expr (Fin n)) (x : ℝ^n)
    (hu : ∀ k : Fin n, (u k).ValidAt x)
    (hv : ∀ k : Fin n, (v k).ValidAt x) :
    (symmetricGradientEnergyIntegrand u v).eval x =
      ∑ i : Fin n, ∑ j : Fin n,
        (((∂[j] (fun y : ℝ^n ↦ (u i).eval y)) x +
            (∂[i] (fun y : ℝ^n ↦ (u j).eval y)) x) / 2) *
          (((∂[j] (fun y : ℝ^n ↦ (v i).eval y)) x +
              (∂[i] (fun y : ℝ^n ↦ (v j).eval y)) x) / 2) := by
  unfold symmetricGradientEnergyIntegrand
  rw [frobeniusInnerProduct_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [symmetricGradient_eval_eq_partialDeriv_average (field := u) (x := x) (i := i) (j := j) hu]
  rw [symmetricGradient_eval_eq_partialDeriv_average (field := v) (x := x) (i := i) (j := j) hv]

end CAS
