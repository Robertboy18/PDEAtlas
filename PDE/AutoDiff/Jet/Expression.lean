/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Jet.Composition
public import PDE.AutoDiff.Jet.Analytic
public import CAS.Calculus.IteratedDifferentiation
public import PDE.Symbolic.Calculus.EuclideanOperators

/-!
# Compiling verified expressions to multivariate formal jets

We evaluate the verified symbolic expression language over order-indexed,
arbitrary-index multivariate jets. Arithmetic nodes use the formal power-series operations
directly. A unary elementary function is compiled by composing its argument jet with the
normalized derivatives of the corresponding one-variable symbolic primitive.

The compiler is algebraically total, as is `Verified.Expr.eval`. Analytic derivative
statements retain the expression's explicit `ValidAt` hypotheses; in particular, division,
logarithm, square root, and real powers do not hide their domain conditions. A real power with a
positive base is compiled through `exp (log a * b)`; with a nonpositive base only its value and
total symbolic first derivative are recorded. Analytic correctness is proved for the value
and first coefficients; higher coefficients are formal data.

For a unary node `g(a)`, the outer coefficients handed to `Jet.compose` are
`normalizedCoefficient g (a.eval x) k = g^{(k)}(a.eval x) / k!`, computed by the symbolic
iterated derivative of the one-variable primitive `g(var 0)` and evaluated as a total real
number. The value and first-coefficient theorems then follow from `Jet.value_compose` and the
chain rule `Jet.firstCoefficient_compose` together with the symbolic derivative rules.

## Main results

* `toJet expr x`: the compiled jet of `expr` at the base point `x`.
* `value_toJet`: its value is `expr.eval x`.
* `firstCoefficient_toJet`: at order `≥ 1`, its first coefficient in direction `i` is the
  (totalized) symbolic derivative `(expr.diff i).eval x`; this holds with no validity
  hypothesis because both sides use the same total conventions.
* `firstCoefficient_toJet_eq_partialDeriv`, `toJet_representsFirstOrderAt`: under `ValidAt x`,
  the first coefficients are the partial derivatives of `y ↦ expr.eval y` at `x`.
-/

@[expose] public section

namespace CAS.Verified.Expr

open PDE.AutoDiff

noncomputable section

/-- The normalized `k`th formal symbolic derivative evaluated at `x`.

This total quantity becomes an analytic Taylor coefficient only under the corresponding
`ValidAt` and iterated differentiability hypotheses. -/
def normalizedCoefficient
    (outer : Verified.Expr (Fin 1)) (x : ℝ) (k : ℕ) : ℝ :=
  (outer.iteratedDiff (0 : Fin 1) k).eval (fun _ ↦ x) /
    (Nat.factorial k : ℝ)

/-- The one-variable expression used to lift a sine node to jets. -/
def sinePrimitive : Verified.Expr (Fin 1) :=
  .sin (.var 0)

/-- The one-variable expression used to lift a cosine node to jets. -/
def cosinePrimitive : Verified.Expr (Fin 1) :=
  .cos (.var 0)

/-- The one-variable expression used to lift an inverse-tangent node to jets. -/
def arctangentPrimitive : Verified.Expr (Fin 1) :=
  .atan (.var 0)

/-- The one-variable expression used to lift an inverse-sine node to jets. -/
def arcsinePrimitive : Verified.Expr (Fin 1) :=
  .asin (.var 0)

/-- The one-variable expression used to lift an inverse-cosine node to jets. -/
def arccosinePrimitive : Verified.Expr (Fin 1) :=
  .acos (.var 0)

/-- The one-variable expression used to lift an exponential node to jets. -/
def exponentialPrimitive : Verified.Expr (Fin 1) :=
  .exp (.var 0)

/-- The one-variable expression used to lift a logarithm node to jets. -/
def logarithmPrimitive : Verified.Expr (Fin 1) :=
  .log (.var 0)

/-- The one-variable expression used to lift a square-root node to jets. -/
def squareRootPrimitive : Verified.Expr (Fin 1) :=
  .sqrt (.var 0)

open scoped Classical in
/-- The formal jet with value `c`, first-order coefficient `d i` in direction `i`, and no
higher-order terms.

This is the fallback used for a real power whose base is not positive. There the expression is
outside the analytic domain of `Verified.Expr.ValidAt`, and the compiled jet certifies only the
value and the (totalized) symbolic first derivative, exactly as `value_toJet` and
`firstCoefficient_toJet` require. -/
def firstOrderJet {ι : Type} {order : ℕ} (c : ℝ) (d : ι → ℝ) : Jet ι ℝ order :=
  fun m ↦ if m = 0 then c else if h : ∃ i, m = Finsupp.single i 1 then d h.choose else 0

/-- The value of the first-order fallback jet is its constant coefficient. -/
@[simp]
theorem value_firstOrderJet {ι : Type} {order : ℕ} (c : ℝ) (d : ι → ℝ) :
    Jet.value (firstOrderJet (order := order) c d) = c := by
  rw [Jet.value, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
  simp [firstOrderJet]

/-- The first-order coefficients of the fallback jet are the supplied directional data. -/
@[simp]
theorem firstCoefficient_firstOrderJet {ι : Type} {order : ℕ} (c : ℝ) (d : ι → ℝ)
    (i : ι) :
    Jet.firstCoefficient i (firstOrderJet (order := order) c d) = d i := by
  classical
  rw [Jet.firstCoefficient, Jet.coefficient, MvPowerSeries.coeff_apply]
  have hne : (Finsupp.single i 1 : ι →₀ ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
  have hex : ∃ j, (Finsupp.single i 1 : ι →₀ ℕ) = Finsupp.single j 1 := ⟨i, rfl⟩
  have hchoose : i = hex.choose :=
    (Finsupp.single_left_inj one_ne_zero).mp hex.choose_spec
  simp only [firstOrderJet, ite_eq_right hne, dite_eq_left hex]
  rw [← hchoose]

/--
Compile a verified expression at `x` into a multivariate formal jet.

This is a proof-only model over `ℝ`. Symbolic coefficients can be enclosed by FloatLib;
their analytic interpretation requires the separate derivative theorems.
The variable type `ι` is arbitrary. The erased order index selects finite extraction
and composition policies and provides no typing invariant.
-/
def toJet {ι : Type} [DecidableEq ι] {order : ℕ}
    (expr : Verified.Expr ι) (x : ι → ℝ) :
    Jet ι ℝ order :=
  match expr with
  | .nat n => Jet.constant n
  | .int n => Jet.constant n
  | .rat num den => Jet.constant ((num : ℝ) / (den : ℝ))
  | .pi => Jet.constant Real.pi
  | .e => Jet.constant (Real.exp 1)
  | .var i => Jet.coordinate x i
  | .add a b => toJet (order := order) a x + toJet (order := order) b x
  | .mul a b => toJet (order := order) a x * toJet (order := order) b x
  | .sub a b => toJet (order := order) a x - toJet (order := order) b x
  | .div a b =>
      toJet (order := order) a x * (toJet (order := order) b x)⁻¹
  | .neg a => -toJet (order := order) a x
  | .pow a n => toJet (order := order) a x ^ n
  | .sin a =>
      Jet.compose
        (normalizedCoefficient sinePrimitive (a.eval x))
        (toJet (order := order) a x)
  | .cos a =>
      Jet.compose
        (normalizedCoefficient cosinePrimitive (a.eval x))
        (toJet (order := order) a x)
  | .atan a =>
      Jet.compose
        (normalizedCoefficient arctangentPrimitive (a.eval x))
        (toJet (order := order) a x)
  | .asin a =>
      Jet.compose
        (normalizedCoefficient arcsinePrimitive (a.eval x))
        (toJet (order := order) a x)
  | .acos a =>
      Jet.compose
        (normalizedCoefficient arccosinePrimitive (a.eval x))
        (toJet (order := order) a x)
  | .exp a =>
      Jet.compose
        (normalizedCoefficient exponentialPrimitive (a.eval x))
        (toJet (order := order) a x)
  | .log a =>
      Jet.compose
        (normalizedCoefficient logarithmPrimitive (a.eval x))
        (toJet (order := order) a x)
  | .sqrt a =>
      Jet.compose
        (normalizedCoefficient squareRootPrimitive (a.eval x))
        (toJet (order := order) a x)
  | .rpow a b =>
      -- On a positive base, `a ^ b = exp (log a * b)`, so the jet is the composition of the
      -- exponential and logarithm primitives with the product of the operand jets. Elsewhere the
      -- expression is outside the analytic domain and only the value and the total symbolic first
      -- derivative are recorded.
      if 0 < a.eval x then
        Jet.compose
          (normalizedCoefficient exponentialPrimitive (Real.log (a.eval x) * b.eval x))
          (Jet.compose
            (normalizedCoefficient logarithmPrimitive (a.eval x))
            (toJet (order := order) a x) *
            toJet (order := order) b x)
      else
        firstOrderJet (a.eval x ^ b.eval x)
          fun i ↦ ((Verified.Expr.rpow a b).diff i).eval x

/-- The zeroth normalized coefficient is the evaluation of the expression itself. -/
@[simp]
theorem normalizedCoefficient_zero
    (outer : Verified.Expr (Fin 1)) (x : ℝ) :
    normalizedCoefficient outer x 0 = outer.eval (fun _ ↦ x) := by
  simp [normalizedCoefficient]

/-- The first normalized coefficient is the evaluation of the symbolic first derivative
(`1! = 1`). -/
@[simp]
theorem normalizedCoefficient_one
    (outer : Verified.Expr (Fin 1)) (x : ℝ) :
    normalizedCoefficient outer x 1 =
      (outer.diff (0 : Fin 1)).eval (fun _ ↦ x) := by
  simp [normalizedCoefficient]

/-- The constant coefficient of the compiled jet is ordinary expression evaluation. -/
@[simp]
theorem value_toJet {ι : Type} [DecidableEq ι] {order : ℕ}
    (expr : Verified.Expr ι) (x : ι → ℝ) :
    Jet.value (expr.toJet (order := order) x) = expr.eval x := by
  induction expr with
  | nat n => simp [toJet]
  | int n => simp [toJet]
  | rat num den => simp [toJet]
  | pi => simp [toJet]
  | e => simp [toJet]
  | var i => simp [toJet]
  | add a b ha hb => simp [toJet, ha, hb]
  | mul a b ha hb => simp [toJet, ha, hb]
  | sub a b ha hb => simp [toJet, ha, hb]
  | div a b ha hb => simp [toJet, ha, hb, div_eq_mul_inv]
  | neg a ha => simp [toJet, ha]
  | pow a n ha => simp [toJet, ha]
  | sin a ha => simp [toJet, sinePrimitive]
  | cos a ha => simp [toJet, cosinePrimitive]
  | atan a ha => simp [toJet, arctangentPrimitive]
  | asin a ha => simp [toJet, arcsinePrimitive]
  | acos a ha => simp [toJet, arccosinePrimitive]
  | exp a ha => simp [toJet, exponentialPrimitive]
  | log a ha => simp [toJet, logarithmPrimitive]
  | sqrt a ha => simp [toJet, squareRootPrimitive]
  | rpow a b ha hb =>
      rw [toJet]
      split
      · rename_i hpos
        simp [exponentialPrimitive, Real.rpow_def_of_pos hpos]
      · simp

/--
At positive jet order, every first coefficient agrees with the checked symbolic derivative.

Gradient and Jacobian extraction rely on this compiler-correctness theorem.
-/
theorem firstCoefficient_toJet {ι : Type} [DecidableEq ι] {order : ℕ}
    (expr : Verified.Expr ι) (x : ι → ℝ) (i : ι)
    (horder : 1 ≤ order) :
    Jet.firstCoefficient i (expr.toJet (order := order) x) =
      (expr.diff i).eval x := by
  induction expr with
  | nat n => simp [toJet]
  | int n => simp [toJet]
  | rat num den => simp [toJet]
  | pi => simp [toJet]
  | e => simp [toJet]
  | var j =>
      by_cases h : i = j
      · subst j
        simp [toJet]
      · simp [toJet, h, Ne.symm h]
  | add a b ha hb => simp [toJet, ha, hb]
  | mul a b ha hb =>
      simp [toJet, Jet.firstCoefficient_mul, ha, hb]
      ring
  | sub a b ha hb => simp [toJet, ha, hb]
  | div a b ha hb =>
      rw [toJet, Jet.firstCoefficient_mul_inv, ha, hb]
      simp only [Jet.value_inv, value_toJet]
      change
        a.eval x * (-(b.eval x)⁻¹ ^ 2 * (b.diff i).eval x) +
            (b.eval x)⁻¹ * (a.diff i).eval x =
          ((a.diff i).eval x * b.eval x - a.eval x * (b.diff i).eval x) /
            b.eval x ^ 2
      by_cases hzero : b.eval x = 0
      · simp [hzero]
      · field_simp
        ring
  | neg a ha => simp [toJet, ha]
  | pow a n ha =>
      simp [toJet, Jet.firstCoefficient_pow, ha]
  | sin a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [sinePrimitive]
  | cos a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [cosinePrimitive]
  | atan a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [arctangentPrimitive, div_eq_mul_inv, mul_comm]
  | asin a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [arcsinePrimitive, div_eq_mul_inv, mul_comm]
  | acos a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [arccosinePrimitive, div_eq_mul_inv, mul_comm]
  | exp a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [exponentialPrimitive]
  | log a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [logarithmPrimitive, div_eq_mul_inv, mul_comm]
  | sqrt a ha =>
      rw [toJet, Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one, ha]
      simp [squareRootPrimitive, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_assoc]
  | rpow a b ha hb =>
      rw [toJet]
      split
      · rename_i hpos
        rw [Jet.firstCoefficient_compose _ _ _ horder, normalizedCoefficient_one,
          Jet.firstCoefficient_mul, Jet.firstCoefficient_compose _ _ _ horder,
          normalizedCoefficient_one, Jet.value_compose, normalizedCoefficient_zero, ha, hb,
          value_toJet]
        have hne : a.eval x ≠ 0 := ne_of_gt hpos
        simp only [exponentialPrimitive, logarithmPrimitive, Verified.Expr.diff,
          Verified.Expr.eval, Nat.cast_one, ↓reduceIte, mul_one]
        rw [← Real.rpow_def_of_pos hpos, Real.rpow_sub_one hne]
        field_simp
        ring
      · simp

/--
For a Euclidean expression valid at `x`, a compiled first coefficient is the partial
derivative at `x`.
-/
theorem firstCoefficient_toJet_eq_partialDeriv
    {n order : ℕ} (expr : Verified.Expr (Fin n)) (x : ℝ^n) (i : Fin n)
    (horder : 1 ≤ order) (hvalid : expr.ValidAt x) :
    Jet.firstCoefficient i (expr.toJet (order := order) x) =
      (∂[i] (fun y : ℝ^n ↦ expr.eval y)) x := by
  rw [firstCoefficient_toJet expr x i horder]
  exact (Verified.Expr.partialDeriv_eval_eq expr x i hvalid).symm

/--
At positive order, compiling an expression valid at `x` produces a formal jet with first-order
calculus semantics for expression evaluation.

The certificate includes differentiability on a neighborhood of `x`. It does not identify higher
coefficients with mixed derivatives or assert convergence of the formal series.
-/
theorem toJet_representsFirstOrderAt
    {n order : ℕ} (expr : Verified.Expr (Fin n)) (x : ℝ^n)
    (horder : 1 ≤ order) (hvalid : expr.ValidAt x) :
    Jet.RepresentsFirstOrderAt
      (expr.toJet (order := order) x) (fun y : ℝ^n ↦ expr.eval y) x := by
  refine ⟨(expr.eventually_validAt x hvalid).mono ?_, value_toJet expr x, ?_⟩
  · intro y hy
    exact (expr.hasFDerivAt_eval y hy).differentiableAt
  · intro i
    exact firstCoefficient_toJet_eq_partialDeriv expr x i horder hvalid

end

end CAS.Verified.Expr
