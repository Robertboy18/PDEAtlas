/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.ModelHierarchy
public import PDE.FDeriv.Calculus
public import CAS.ClosedForm.Expression.FiniteSeries
public import CAS.ClosedForm.Expression.Polynomial.Normalization
public import PDE.Symbolic.Calculus.EuclideanOperators

/-!
# Symbolic spacetime Navier-Stokes operators

Symbolic counterparts of the analytic incompressible-flow operators, acting on reflected
expressions `Verified.Expr (Fin (n + 1))` in spacetime coordinates: spatial divergence, vorticity
components, the material derivative `∂ₜv + (u · ∇)v`, the spatial pressure gradient, the spatial
vector Laplacian, and the Euler and Navier-Stokes momentum residuals assembled from them. The
reflected expressions, their partial derivatives `Verified.Expr.closedPartial` and the
normalization `Verified.Expr.Alg.normalize` come from SymLean, our computer algebra system for
Lean.

The semantic bridge is the family of `eval_*` theorems: each states that evaluating
a symbolic operator at a point where the expressions are valid gives the corresponding analytic
operator from `PDE.Fluid.Incompressible.Operators` and `PDE.Fluid.NavierStokes.Operators`,
applied to the interpreted fields `fun y => WithLp.toLp 2 fun j => (u j).eval y`. This lets a
closed-form residual check by SymLean discharge the analytic momentum equation of an explicit
solution.

## Main declarations

* `spacetimeDivergence`, `spacetimeMaterialDerivative`, `spacetimePressureGradient`,
  `spacetimeVectorLaplacian`: the symbolic operators.
* `spacetimeEulerMomentumResidual`, `spacetimeNavierStokesMomentumResidual`: the symbolic
  residuals `∂ₜu + (u · ∇)u + ∇p - f` and `∂ₜu + (u · ∇)u + ∇p - ν Δu - f`.
* `eval_spacetimeEulerMomentumResidual_eq_modelResidual_component`,
  `eval_spacetimeNavierStokesMomentumResidual_eq_modelResidual_component`: the evaluated symbolic
  residuals agree componentwise with the named analytic residuals of the model hierarchy.
* `navierStokesMomentumComponent_eq_of_spacetimeResidual_eval_zero`,
  `divergenceFreeAt_of_spacetimeDivergence_eval_zero`: a vanishing symbolic residual yields the
  analytic momentum equation, respectively `IncompressibleFlow.DivergenceFreeAt`.

## Implementation notes

Coordinate `0` is time and `i.succ` is the `i`th spatial coordinate, matching the analytic
operators. The `ValidAt` hypotheses are what the reflected differentiation needs in order to agree
with `partialDeriv`; second derivatives additionally need validity of the first symbolic
derivative expression. The viscosity in the symbolic Navier-Stokes residual is a pointwise
multiplier and is not differentiated.
-/

@[expose] public section

open PDE (spatialGradient)

namespace NavierStokes.Symbolic

open CAS
open CAS.Euclid2

noncomputable section

/-- Constant unit viscosity in two spatial dimensions. -/
def unitViscosity2 : Verified.Expr (Fin 2) := 1

/-! ## Spacetime residual operators

The analytic Navier-Stokes operators in `PDE.Fluid.NavierStokes.Operators`
use spacetime coordinates with coordinate `0` as time and `i.succ` as the
`i`th spatial coordinate.  These symbolic operators mirror that convention,
so CAS checks can be used as the closed-form residual step before a larger
ordinary Lean proof consumes the analytic PDE interface.
-/

/-- Symbolic spatial divergence in spacetime coordinates. -/
def spacetimeDivergence {n : Nat} (u : Fin n → Verified.Expr (Fin (n + 1))) :
    Verified.Expr (Fin (n + 1)) :=
  Verified.Expr.Alg.normalize <|
    Verified.Expr.sum (m := n) fun i ↦
      Verified.Expr.closedPartial i.succ (u i)

/-- Symbolic vorticity component `∂ⱼuᵢ - ∂ᵢuⱼ` in spacetime coordinates. -/
def spacetimeVorticityComponent {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (i j : Fin n) :
    Verified.Expr (Fin (n + 1)) :=
  Verified.Expr.Alg.normalize <|
    Verified.Expr.closedPartial j.succ (u i) -
      Verified.Expr.closedPartial i.succ (u j)

/-- Symbolic scalar vorticity `∂ₓu₂ - ∂ᵧu₁` for a planar spacetime flow. -/
def spacetimePlanarVorticity
    (u : Fin 2 → Verified.Expr (Fin 3)) : Verified.Expr (Fin 3) :=
  spacetimeVorticityComponent u (1 : Fin 2) (0 : Fin 2)

/-- Symbolic spacetime material derivative `∂ₜv + (u · ∇)v`. -/
def spacetimeMaterialDerivative {n : Nat}
    (u v : Fin n → Verified.Expr (Fin (n + 1))) : Fin n → Verified.Expr (Fin (n + 1)) :=
  fun i ↦
    Verified.Expr.Alg.normalize <|
      Verified.Expr.closedPartial (0 : Fin (n + 1)) (v i) +
        Verified.Expr.sum (m := n) fun j ↦
          u j * Verified.Expr.closedPartial j.succ (v i)

/-- Symbolic spatial pressure gradient in spacetime coordinates. -/
def spacetimePressureGradient {n : Nat} (p : Verified.Expr (Fin (n + 1))) :
    Fin n → Verified.Expr (Fin (n + 1)) :=
  fun i ↦ Verified.Expr.closedPartial i.succ p

/-- Symbolic spatial vector Laplacian in spacetime coordinates. -/
def spacetimeVectorLaplacian {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) : Fin n → Verified.Expr (Fin (n + 1)) :=
  fun i ↦
    Verified.Expr.Alg.normalize <|
      Verified.Expr.sum (m := n) fun j ↦
        Verified.Expr.closedPartial j.succ
          (Verified.Expr.closedPartial j.succ (u i))

/-- Symbolic spacetime Euler momentum residual
`∂ₜu + (u · ∇)u + ∇p - f`. -/
def spacetimeEulerMomentumResidual {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (p : Verified.Expr (Fin (n + 1)))
    (f : Fin n → Verified.Expr (Fin (n + 1))) : Fin n → Verified.Expr (Fin (n + 1)) :=
  fun i ↦
    Verified.Expr.Alg.normalize
      (spacetimeMaterialDerivative u u i + spacetimePressureGradient p i - f i)

/-- Symbolic spacetime Navier-Stokes momentum residual
`∂ₜu + (u · ∇)u + ∇p - ν Δu - f`.

The expression `ν` is a pointwise multiplier and is not differentiated. A variable-viscosity
stress divergence generally has additional coefficient-gradient terms. The physical problem
interface specializes the multiplier to a positive constant. -/
def spacetimeNavierStokesMomentumResidual {n : Nat}
    (ν : Verified.Expr (Fin (n + 1))) (u : Fin n → Verified.Expr (Fin (n + 1)))
    (p : Verified.Expr (Fin (n + 1))) (f : Fin n → Verified.Expr (Fin (n + 1))) :
    Fin n → Verified.Expr (Fin (n + 1)) :=
  fun i ↦
    Verified.Expr.Alg.normalize
      (spacetimeMaterialDerivative u u i + spacetimePressureGradient p i -
        ν * spacetimeVectorLaplacian u i - f i)

/-! ### Semantic bridge to analytic Navier-Stokes operators -/

/--
Evaluating symbolic spacetime divergence gives the analytic spatial-divergence
sum used by `IncompressibleFlow.DivergenceFreeAt`.
-/
theorem eval_spacetimeDivergence_eq_sum {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1))
    (hvalid : ∀ i : Fin n, (u i).ValidAt x) :
    (spacetimeDivergence u).eval x =
      ∑ i : Fin n,
        (∂[i.succ] (fun y : ℝ^(n + 1) ↦ (u i).eval y)) x := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  unfold spacetimeDivergence
  change
    (Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
      (Verified.Expr.Alg.normalize
        (Verified.Expr.sum (m := n) fun i : Fin n ↦
          Verified.Expr.closedPartial i.succ (u i)))) =
      ∑ i : Fin n,
        (∂[i.succ] (fun y : ℝ^(n + 1) ↦ (u i).eval y)) x
  rw [Verified.Expr.Alg.eval_normalize]
  have hsum :
      Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
        (Verified.Expr.sum (m := n) fun i : Fin n ↦
          Verified.Expr.closedPartial i.succ (u i)) =
        ((List.finRange n).map fun i ↦
          Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
            (Verified.Expr.closedPartial i.succ (u i))).sum := by
    simp [Verified.Expr.eval_sum]
  rw [hsum]
  rw [← List.sum_toFinset
    (f := fun i : Fin n ↦ (Verified.Expr.closedPartial i.succ (u i)).eval x)
    (List.nodup_finRange n)]
  rw [List.toFinset_finRange]
  apply Finset.sum_congr rfl
  intro i _
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u i) (x := x) (i := i.succ) (hvalid i)]

/-- Symbolic vorticity evaluation agrees with the corresponding analytic tensor entry. -/
theorem eval_spacetimeVorticityComponent_eq {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1))
    (i j : Fin n) (hvalidI : (u i).ValidAt x)
    (hvalidJ : (u j).ValidAt x) :
    (spacetimeVorticityComponent u i j).eval x =
      IncompressibleFlow.vorticityTensor n
        (fun y ↦ WithLp.toLp 2 fun k : Fin n ↦ (u k).eval y) x (i, j) := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  unfold spacetimeVorticityComponent
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (Verified.Expr.closedPartial j.succ (u i)).eval x -
        (Verified.Expr.closedPartial i.succ (u j)).eval x =
      IncompressibleFlow.vorticityTensor n
        (fun y ↦ WithLp.toLp 2 fun k : Fin n ↦ (u k).eval y) x (i, j)
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u i) (x := x) (i := j.succ) hvalidI]
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u j) (x := x) (i := i.succ) hvalidJ]
  simp

/-- The symbolic planar curl agrees with analytic planar vorticity. -/
theorem eval_spacetimePlanarVorticity_eq
    (u : Fin 2 → Verified.Expr (Fin 3)) (x : ℝ^3)
    (hvalid : ∀ i : Fin 2, (u i).ValidAt x) :
    (spacetimePlanarVorticity u).eval x =
      IncompressibleFlow.spacetimePlanarVorticity
        (fun y ↦ WithLp.toLp 2 fun i : Fin 2 ↦ (u i).eval y) x := by
  simpa [spacetimePlanarVorticity,
    IncompressibleFlow.spacetimePlanarVorticity] using
    eval_spacetimeVorticityComponent_eq u x
      (1 : Fin 2) (0 : Fin 2) (hvalid 1) (hvalid 0)

/--
Componentwise semantic bridge for the symbolic material derivative
`∂ₜv + (u · ∇)v`.
-/
theorem eval_spacetimeMaterialDerivative_eq_sum {n : Nat}
    (u v : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1))
    (i : Fin n)
    (hvalidVTime : (v i).ValidAt x)
    (hvalidVSpatial : ∀ _j : Fin n, (v i).ValidAt x) :
    (spacetimeMaterialDerivative u v i).eval x =
      (∂[(0 : Fin (n + 1))]
          (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x +
        ∑ j : Fin n,
          (u j).eval x *
            (∂[j.succ]
              (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  unfold spacetimeMaterialDerivative
  change
    (Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
      (Verified.Expr.Alg.normalize
        (Verified.Expr.closedPartial (0 : Fin (n + 1)) (v i) +
          Verified.Expr.sum (m := n) fun j : Fin n ↦
            u j * Verified.Expr.closedPartial j.succ (v i)))) =
      (∂[(0 : Fin (n + 1))]
          (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x +
        ∑ j : Fin n,
          (u j).eval x *
            (∂[j.succ]
              (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
        (Verified.Expr.closedPartial (0 : Fin (n + 1)) (v i)) +
      Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
        (Verified.Expr.sum (m := n) fun j : Fin n ↦
          u j * Verified.Expr.closedPartial j.succ (v i)) =
      (∂[(0 : Fin (n + 1))]
          (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x +
        ∑ j : Fin n,
          (u j).eval x *
            (∂[j.succ]
              (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := v i) (x := x) (i := (0 : Fin (n + 1))) hvalidVTime]
  have hsum :
      Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
        (Verified.Expr.sum (m := n) fun j : Fin n ↦
          u j * Verified.Expr.closedPartial j.succ (v i)) =
        ((List.finRange n).map fun j ↦
          Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
            (u j * Verified.Expr.closedPartial j.succ (v i))).sum := by
    simp [Verified.Expr.eval_sum]
  rw [hsum]
  rw [← List.sum_toFinset
    (f := fun j : Fin n ↦ (u j * Verified.Expr.closedPartial j.succ (v i)).eval x)
    (List.nodup_finRange n)]
  rw [List.toFinset_finRange]
  apply congrArg (fun s ↦
    (∂[(0 : Fin (n + 1))]
      (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x + s)
  apply Finset.sum_congr rfl
  intro j _
  change
    Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k) (u j) *
      Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
        (Verified.Expr.closedPartial j.succ (v i)) =
    (u j).eval x *
      (∂[j.succ]
        (fun y : ℝ^(n + 1) ↦ (v i).eval y)) x
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := v i) (x := x) (i := j.succ) (hvalidVSpatial j)]

/-- Symbolic pressure-gradient evaluation agrees with the analytic pressure-gradient component. -/
theorem eval_spacetimePressureGradient_eq {n : Nat}
    (p : Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1)) (i : Fin n)
    (hvalid : p.ValidAt x) :
    (spacetimePressureGradient p i).eval x =
      (∂[i.succ] (fun y : ℝ^(n + 1) ↦ p.eval y)) x := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  simpa [spacetimePressureGradient] using
    (Verified.Expr.closedPartial_eval_eq_partialDeriv
      (expr := p) (x := x) (i := i.succ) hvalid)

/--
Componentwise semantic bridge for the symbolic spatial vector Laplacian.

Validity at the evaluation point persists on a neighborhood, where the first symbolic
derivative agrees with the analytic derivative. This local equality suffices inside the second
`partialDeriv`; validity of the first derivative expression remains a separate hypothesis.
-/
theorem eval_spacetimeVectorLaplacian_eq_sum {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1)) (i : Fin n)
    (hvalid : (u i).ValidAt x)
    (hvalidPartial : ∀ j : Fin n, (Verified.Expr.closedPartial j.succ (u i)).ValidAt x) :
    (spacetimeVectorLaplacian u i).eval x =
      ∑ j : Fin n,
        (∂[j.succ]
          (fun y : ℝ^(n + 1) ↦
            (∂[j.succ]
              (fun z : ℝ^(n + 1) ↦ (u i).eval z)) y)) x := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  unfold spacetimeVectorLaplacian
  change
    (Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
      (Verified.Expr.Alg.normalize
        (Verified.Expr.sum (m := n) fun j : Fin n ↦
          Verified.Expr.closedPartial j.succ
            (Verified.Expr.closedPartial j.succ (u i))))) =
      ∑ j : Fin n,
        (∂[j.succ]
          (fun y : ℝ^(n + 1) ↦
            (∂[j.succ]
              (fun z : ℝ^(n + 1) ↦ (u i).eval z)) y)) x
  rw [Verified.Expr.Alg.eval_normalize]
  have hsum :
      Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
        (Verified.Expr.sum (m := n) fun j : Fin n ↦
          Verified.Expr.closedPartial j.succ
            (Verified.Expr.closedPartial j.succ (u i))) =
        ((List.finRange n).map fun j ↦
          Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
            (Verified.Expr.closedPartial j.succ
              (Verified.Expr.closedPartial j.succ (u i)))).sum := by
    simp [Verified.Expr.eval_sum]
  rw [hsum]
  rw [← List.sum_toFinset
    (f := fun j : Fin n ↦
      (Verified.Expr.closedPartial j.succ
        (Verified.Expr.closedPartial j.succ (u i))).eval x)
    (List.nodup_finRange n)]
  rw [List.toFinset_finRange]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := Verified.Expr.closedPartial j.succ (u i)) (x := x) (i := j.succ)
    (hvalidPartial j)]
  apply PDE.partialDeriv_congr_nhds
  filter_upwards [Verified.Expr.eventually_validAt (u i) x hvalid] with y hy
  exact (Verified.Expr.closedPartial_eval_eq_partialDeriv
    (expr := u i) (x := y) (i := j.succ) hy)

/--
The symbolic material derivative agrees componentwise with
`IncompressibleFlow.materialDerivative` for expression-defined velocity fields.
-/
theorem eval_spacetimeMaterialDerivative_eq_analytic_component {n : Nat}
    (u v : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1))
    (i : Fin n)
    (hvalidVTime : (v i).ValidAt x)
    (hvalidVSpatial : ∀ _j : Fin n, (v i).ValidAt x) :
    (spacetimeMaterialDerivative u v i).eval x =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (v j).eval y)
        x) i := by
  rw [eval_spacetimeMaterialDerivative_eq_sum
    (u := u) (v := v) (x := x) (i := i) hvalidVTime hvalidVSpatial]
  simp only [IncompressibleFlow.materialDerivative_apply]

/-- The symbolic pressure gradient agrees componentwise with the analytic
`spatialGradient`. -/
theorem eval_spacetimePressureGradient_eq_analytic_component {n : Nat}
    (p : Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1)) (i : Fin n)
    (hvalid : p.ValidAt x) :
    (spacetimePressureGradient p i).eval x =
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i := by
  rw [eval_spacetimePressureGradient_eq (p := p) (x := x) (i := i) hvalid]
  simp

/--
Semantic bridge for the symbolic spacetime Euler momentum residual.

This is the inviscid version of
`eval_spacetimeNavierStokesMomentumResidual_eq_analytic_component`: the evaluated
symbolic residual is the componentwise analytic quantity
`Dₜu + ∇p - f`.
-/
theorem eval_spacetimeEulerMomentumResidual_eq_analytic_component {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (p : Verified.Expr (Fin (n + 1)))
    (f : Fin n → Verified.Expr (Fin (n + 1)))
    (x : ℝ^(n + 1)) (i : Fin n)
    (hvalidUTime : (u i).ValidAt x)
    (hvalidUSpatial : ∀ _j : Fin n, (u i).ValidAt x)
    (hvalidP : p.ValidAt x) :
    (spacetimeEulerMomentumResidual u p f i).eval x =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i +
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i -
      (f i).eval x := by
  unfold spacetimeEulerMomentumResidual
  change
    (Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
      (Verified.Expr.Alg.normalize
        (spacetimeMaterialDerivative u u i + spacetimePressureGradient p i - f i))) =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i +
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i -
      (f i).eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (spacetimeMaterialDerivative u u i).eval x +
        (spacetimePressureGradient p i).eval x -
      (f i).eval x =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i +
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i -
      (f i).eval x
  rw [eval_spacetimeMaterialDerivative_eq_analytic_component
    (u := u) (v := u) (x := x) (i := i) hvalidUTime hvalidUSpatial]
  rw [eval_spacetimePressureGradient_eq_analytic_component
    (p := p) (x := x) (i := i) hvalidP]

/--
The symbolic Euler residual agrees componentwise with the named analytic
Euler residual from the incompressible model hierarchy.
-/
theorem eval_spacetimeEulerMomentumResidual_eq_modelResidual_component {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1)))
    (p : Verified.Expr (Fin (n + 1)))
    (f : Fin n → Verified.Expr (Fin (n + 1)))
    (x : ℝ^(n + 1)) (i : Fin n)
    (hvalidUTime : (u i).ValidAt x)
    (hvalidUSpatial : ∀ _j : Fin n, (u i).ValidAt x)
    (hvalidP : p.ValidAt x) :
    (spacetimeEulerMomentumResidual u p f i).eval x =
      (IncompressibleFlow.eulerMomentumResidual n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ p.eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (f j).eval y)
        x) i := by
  rw [eval_spacetimeEulerMomentumResidual_eq_analytic_component
    (u := u) (p := p) (f := f) (x := x) (i := i)
    hvalidUTime hvalidUSpatial hvalidP]
  simp [IncompressibleFlow.eulerMomentumResidual]

/-- The symbolic spatial vector Laplacian agrees with the component inside `viscousTerm`. -/
theorem eval_spacetimeViscousTerm_eq_analytic_component {n : Nat}
    (ν : ℝ) (u : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1)) (i : Fin n)
    (hvalid : (u i).ValidAt x)
    (hvalidPartial : ∀ j : Fin n, (Verified.Expr.closedPartial j.succ (u i)).ValidAt x) :
    ν * (spacetimeVectorLaplacian u i).eval x =
      (NavierStokes.viscousTerm n ν
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i := by
  rw [eval_spacetimeVectorLaplacian_eq_sum
    (u := u) (x := x) (i := i) hvalid hvalidPartial]
  simp [NavierStokes.viscousTerm,
    IncompressibleFlow.spatialVectorLaplacian, IncompressibleFlow.spatialLaplacian]

/--
Semantic bridge for the symbolic spacetime Navier-Stokes momentum residual.

The right side is the componentwise residual of the analytic Navier-Stokes
operators for expression-defined velocity, pressure, and force fields.
-/
theorem eval_spacetimeNavierStokesMomentumResidual_eq_analytic_component {n : Nat}
    (ν : Verified.Expr (Fin (n + 1))) (u : Fin n → Verified.Expr (Fin (n + 1)))
    (p : Verified.Expr (Fin (n + 1))) (f : Fin n → Verified.Expr (Fin (n + 1)))
    (x : ℝ^(n + 1)) (i : Fin n)
    (hvalidUTime : (u i).ValidAt x)
    (hvalidUSpatial : ∀ _j : Fin n, (u i).ValidAt x)
    (hvalidP : p.ValidAt x)
    (hvalidPartial : ∀ j : Fin n, (Verified.Expr.closedPartial j.succ (u i)).ValidAt x) :
    (spacetimeNavierStokesMomentumResidual ν u p f i).eval x =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i +
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i -
      (NavierStokes.viscousTerm n (ν.eval x)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i -
      (f i).eval x := by
  unfold spacetimeNavierStokesMomentumResidual
  change
    (Verified.Expr.eval (fun k : Fin (n + 1) ↦ x k)
      (Verified.Expr.Alg.normalize
        (spacetimeMaterialDerivative u u i + spacetimePressureGradient p i -
          ν * spacetimeVectorLaplacian u i - f i))) =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i +
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i -
      (NavierStokes.viscousTerm n (ν.eval x)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i -
      (f i).eval x
  rw [Verified.Expr.Alg.eval_normalize]
  change
    (spacetimeMaterialDerivative u u i).eval x +
        (spacetimePressureGradient p i).eval x -
      (ν.eval x * (spacetimeVectorLaplacian u i).eval x) -
      (f i).eval x =
      (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i +
      (spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i -
      (NavierStokes.viscousTerm n (ν.eval x)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x) i -
      (f i).eval x
  rw [eval_spacetimeMaterialDerivative_eq_analytic_component
    (u := u) (v := u) (x := x) (i := i) hvalidUTime hvalidUSpatial]
  rw [eval_spacetimePressureGradient_eq_analytic_component
    (p := p) (x := x) (i := i) hvalidP]
  rw [← eval_spacetimeViscousTerm_eq_analytic_component
    (ν := ν.eval x) (u := u) (x := x) (i := i) hvalidUTime hvalidPartial]

/--
The symbolic Navier–Stokes residual agrees componentwise with the named
analytic residual from the incompressible model hierarchy.
-/
theorem eval_spacetimeNavierStokesMomentumResidual_eq_modelResidual_component
    {n : Nat}
    (ν : Verified.Expr (Fin (n + 1)))
    (u : Fin n → Verified.Expr (Fin (n + 1)))
    (p : Verified.Expr (Fin (n + 1)))
    (f : Fin n → Verified.Expr (Fin (n + 1)))
    (x : ℝ^(n + 1)) (i : Fin n)
    (hvalidUTime : (u i).ValidAt x)
    (hvalidUSpatial : ∀ _j : Fin n, (u i).ValidAt x)
    (hvalidP : p.ValidAt x)
    (hvalidPartial :
      ∀ j : Fin n, (Verified.Expr.closedPartial j.succ (u i)).ValidAt x) :
    (spacetimeNavierStokesMomentumResidual ν u p f i).eval x =
      (IncompressibleFlow.navierStokesMomentumResidual n (ν.eval x)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ p.eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (f j).eval y)
        x) i := by
  rw [eval_spacetimeNavierStokesMomentumResidual_eq_analytic_component
    (ν := ν) (u := u) (p := p) (f := f) (x := x) (i := i)
    hvalidUTime hvalidUSpatial hvalidP hvalidPartial]
  simp [IncompressibleFlow.navierStokesMomentumResidual]

/--
If the symbolic spacetime Navier-Stokes residual evaluates to zero, the
ordinary analytic component momentum equation follows.
-/
theorem navierStokesMomentumComponent_eq_of_spacetimeResidual_eval_zero {n : Nat}
    (ν : Verified.Expr (Fin (n + 1))) (u : Fin n → Verified.Expr (Fin (n + 1)))
    (p : Verified.Expr (Fin (n + 1))) (f : Fin n → Verified.Expr (Fin (n + 1)))
    (x : ℝ^(n + 1)) (i : Fin n)
    (hvalidUTime : (u i).ValidAt x)
    (hvalidUSpatial : ∀ _j : Fin n, (u i).ValidAt x)
    (hvalidP : p.ValidAt x)
    (hvalidPartial : ∀ j : Fin n, (Verified.Expr.closedPartial j.succ (u i)).ValidAt x)
    (hzero : (spacetimeNavierStokesMomentumResidual ν u p f i).eval x = 0) :
    (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x +
      spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i =
      (NavierStokes.viscousTerm n (ν.eval x)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x +
      WithLp.toLp 2 (fun j : Fin n ↦ (f j).eval x)) i := by
  have hres := eval_spacetimeNavierStokesMomentumResidual_eq_analytic_component
    (ν := ν) (u := u) (p := p) (f := f) (x := x) (i := i)
    hvalidUTime hvalidUSpatial hvalidP hvalidPartial
  rw [hzero] at hres
  simp at hres ⊢
  linarith

/--
If the symbolic spacetime Euler residual evaluates to zero, the ordinary
componentwise inviscid momentum equation follows.
-/
theorem eulerMomentumComponent_eq_of_spacetimeResidual_eval_zero {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (p : Verified.Expr (Fin (n + 1)))
    (f : Fin n → Verified.Expr (Fin (n + 1)))
    (x : ℝ^(n + 1)) (i : Fin n)
    (hvalidUTime : (u i).ValidAt x)
    (hvalidUSpatial : ∀ _j : Fin n, (u i).ValidAt x)
    (hvalidP : p.ValidAt x)
    (hzero : (spacetimeEulerMomentumResidual u p f i).eval x = 0) :
    (IncompressibleFlow.materialDerivative n
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        (fun y ↦ WithLp.toLp 2 fun j : Fin n ↦ (u j).eval y)
        x +
      spatialGradient
        (fun y : ℝ^(n + 1) ↦ p.eval y) x) i =
      (WithLp.toLp 2 (fun j : Fin n ↦ (f j).eval x)) i := by
  have hres := eval_spacetimeEulerMomentumResidual_eq_analytic_component
    (u := u) (p := p) (f := f) (x := x) (i := i)
    hvalidUTime hvalidUSpatial hvalidP
  rw [hzero] at hres
  simp at hres ⊢
  linarith

/-- The symbolic divergence bridge in `IncompressibleFlow.DivergenceFreeAt` form. -/
theorem divergenceFreeAt_of_spacetimeDivergence_eval_zero {n : Nat}
    (u : Fin n → Verified.Expr (Fin (n + 1))) (x : ℝ^(n + 1))
    (hvalid : ∀ i : Fin n, (u i).ValidAt x)
    (hzero : (spacetimeDivergence u).eval x = 0) :
    IncompressibleFlow.DivergenceFreeAt
      (fun y ↦ WithLp.toLp 2 fun i : Fin n ↦ (u i).eval y) x := by
  change
    (∑ i : Fin n,
      (∂[i.succ] (fun y : ℝ^(n + 1) ↦ (u i).eval y)) x) = 0
  rw [← eval_spacetimeDivergence_eq_sum (u := u) (x := x) hvalid]
  exact hzero


end

end NavierStokes.Symbolic
