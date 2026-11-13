/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.InitialTrace

/-!
# Sobolev compatibility values for higher-order wave regularity

Higher regularity for the wave equation `u_tt + L u = f` with homogeneous
Dirichlet data requires compatibility conditions on the initial data: the
formal initial time derivatives

`q₀ = g`, `q₁ = h`, `q_{k+2} = ∂_t^k f(0) - L q_k`

must all have zero trace, with `q_k ∈ H^{m+1-k}(Ω)`. `WaveCompatibilityValues`
stores these values at their exact Sobolev orders. Each value has homogeneous
Dirichlet trace, and `Realizes` ties the recurrence to both the Sobolev-scale
spatial operators and the weak operator in the wave equation.

## Main results

* `WaveCompatibilityValues`: the typed list `q₀, …, q_m` with
  `q_k ∈ H^{m+1-k}(Ω)` and `HasDirichletTraceZero`.
* `head`, `tail`, `baseList`, `baseAt`: access to the values and to their
  `L²(Ω)` representatives.
* `Realizes`: `q₀ = g`, the weak operator `A` applied to `q₀` is the load
  functional of `L q₀`, and the tail realizes the time-differentiated data
  starting from `h` and `f(0) - L q₀`.
* `Realizes.timeDerivative`: the family for the time-differentiated equation
  is the tail of the original family.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, compatibility conditions (62), and the
  Remark after it, equations (65)-(66).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
A higher-order Sobolev value has homogeneous Dirichlet trace zero when its
canonical restriction to `H¹(Omega)` lies in `H¹₀(Omega)`.
-/
def HasDirichletTraceZero
    {r : ℕ} (hr : 1 ≤ r) (u : W^{r,2}(Omega)) : Prop :=
  lowerOrderCLM (n := n) (p := 2) (Ω := Omega) hr u ∈
    (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule

/--
The concrete values `q₀, q₁, ..., q_m` in Evans's compatibility recurrence.
The `k`-th value has Sobolev regularity `H^{m+1-k}(Omega)` and homogeneous
Dirichlet trace.
-/
inductive WaveCompatibilityValues
    (n : ℕ) (Omega : Set (ℝ^n)) : ℕ → Type
  | zero
      (q0 : W^{1,2}(Omega))
      (q0_zero :
        HasDirichletTraceZero
          (n := n) (Omega := Omega) (le_rfl : 1 ≤ 1) q0) :
      WaveCompatibilityValues n Omega 0
  | succ {m : ℕ}
      (q0 : W^{(m + 2),2}(Omega))
      (q0_zero :
        HasDirichletTraceZero
          (n := n) (Omega := Omega)
          (by omega : 1 ≤ m + 2) q0)
      (tail : WaveCompatibilityValues n Omega m) :
      WaveCompatibilityValues n Omega (m + 1)

namespace WaveCompatibilityValues

/-- The leading compatibility value `q₀ ∈ H^{m+1}(Omega)`. -/
def head :
    {m : ℕ} →
      WaveCompatibilityValues n Omega m →
      W^{(m + 1),2}(Omega)
  | 0, .zero q0 _ => q0
  | _ + 1, .succ q0 _ _ => q0

/-- Drop `q₀` from a successor-order compatibility family. -/
def tail
    (Q : WaveCompatibilityValues n Omega (m + 1)) :
    WaveCompatibilityValues n Omega m := by
  cases Q with
  | succ _ _ tail =>
      exact tail

/--
The compatibility values as their underlying `L²(Omega)` representatives,
in the order `q₀, q₁, ..., q_m`.
-/
def baseList :
    {m : ℕ} →
      WaveCompatibilityValues n Omega m →
      List (DerivLp n 2 Omega)
  | 0, .zero q0 _ =>
      [wkpBaseCoordinateCLM (n := n) (p := 2) (Ω := Omega) q0]
  | _ + 1, .succ q0 _ tail =>
      wkpBaseCoordinateCLM (n := n) (p := 2) (Ω := Omega) q0 ::
        baseList tail

/-- A compatibility family of order `m` lists the `m + 1` values
`q₀, …, q_m`. -/
@[simp]
theorem length_baseList (Q : WaveCompatibilityValues n Omega m) :
    Q.baseList.length = m + 1 := by
  induction Q with
  | zero =>
      rfl
  | succ _ _ tail ih =>
      simp only [baseList, List.length_cons, ih]

/-- The `k`-th compatibility value as an `L²(Omega)` class. -/
def baseAt
    (Q : WaveCompatibilityValues n Omega m)
    (k : Fin (m + 1)) : DerivLp n 2 Omega :=
  Q.baseList.get
    ⟨k.1, by simpa only [length_baseList] using k.2⟩

/-- The zeroth listed value is the `L²` representative of the leading value
`q₀`. -/
@[simp]
theorem baseAt_zero (Q : WaveCompatibilityValues n Omega m) :
    Q.baseAt 0 = wkpBaseCoordinateCLM (n := n) (p := 2) (Ω := Omega) Q.head := by
  cases Q with
  | zero =>
      rfl
  | succ =>
      rfl

/-- Indexing the tail at `k` is indexing the original family at `k + 1`. -/
@[simp]
theorem baseAt_tail_succ
    (Q : WaveCompatibilityValues n Omega (m + 1))
    (k : Fin (m + 1)) :
    Q.tail.baseAt k =
      Q.baseAt ⟨k.1 + 1, by omega⟩ := by
  cases Q with
  | succ =>
      rfl

/--
The typed compatibility values realize Evans's algebraic recurrence.

At Sobolev order `r`, `spatialOperator r` maps `H^{r+2}(Omega)` to
`H^r(Omega)`. The weak-operator equality certifies that each such application
represents the same stationary operator used in the wave equation.
-/
def Realizes :
    {m : ℕ} →
      (Q : WaveCompatibilityValues n Omega m) →
      (A :
        H¹₀(Omega) →L[ℝ]
          StrongDual ℝ (H¹₀(Omega))) →
      (spatialOperator :
        ∀ r : ℕ,
          W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega)) →
      {F : SobolevTimeJet n m Omega t0 t1} →
      (forcingTraces : InitialTraceData (F := F)) →
      (g : W^{(m + 1),2}(Omega)) →
      (h : W^{m,2}(Omega)) → Prop
  | 0, .zero q0 _, _, _, _, .zero _, g, _ =>
      q0 = g
  | m + 1, .succ q0 q0_zero tail, A, spatialOperator, _,
      .succ _ _ _ initial _ traceTail, g, h =>
      q0 = g ∧
        A
            (⟨lowerOrderCLM
                (n := n) (p := 2) (Ω := Omega)
                (by omega : 1 ≤ m + 2) q0,
              q0_zero⟩ :
              H¹₀(Omega)) =
          loadFunctional (n := n) (Ω := Omega)
            (wkpBaseCoordinateCLM
              (n := n) (m := m) (p := 2) (Ω := Omega)
              (spatialOperator m q0)) ∧
        Realizes tail A spatialOperator traceTail h
          (initial - spatialOperator m q0)

/--
The compatibility family for the time-differentiated equation is the tail
of the original family.
-/
theorem Realizes.timeDerivative {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    {Q : WaveCompatibilityValues n Omega (m + 1)} {A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega))}
    {spatialOperator : ∀ r : ℕ, W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega)}
    {forcingTraces : InitialTraceData (F := F)} {g : W^{(m + 2),2}(Omega)}
    {h : W^{(m + 1),2}(Omega)} (hQ : Q.Realizes A spatialOperator forcingTraces g h) :
    Q.tail.Realizes A spatialOperator forcingTraces.timeDerivative h
      (forcingTraces.head - spatialOperator m g) := by
  cases Q with
  | succ q0 q0_zero tail =>
      cases forcingTraces with
      | succ f dF hderiv initial isTrace traceTail =>
          rw [← hQ.1]
          exact hQ.2.2

end WaveCompatibilityValues

end Hyperbolic.HigherRegularity
