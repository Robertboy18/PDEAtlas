/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus

/-!
# Classical harmonicity

`IsHarmonicPDE n u U` records that `u` is `C²` on `U` and has vanishing Euclidean Laplacian
there. The definition does not require `U` to be open; openness enters only when relative
regularity is promoted to pointwise regularity. Restriction and linear closure lemmas for the
predicate follow.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2, Laplace's equation (1) and the definition of a harmonic
  function, p. 20.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace LaplacianEquation


/-- Harmonicity in the PDE sense: a `C²` function with vanishing Laplacian on `U`. -/
def IsHarmonicPDE (n : ℕ) (u : ℝ^n → ℝ)
    (U : Set (ℝ^n)) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ∀ x ∈ U, laplacian u x = 0

/-- A harmonic function in the PDE sense is `C²` on the domain. -/
theorem IsHarmonicPDE.contDiffOn {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) :
    ContDiffOn ℝ 2 u U :=
  hu.1

/-- A harmonic function in the PDE sense has zero Euclidean Laplacian on the domain. -/
theorem IsHarmonicPDE.laplacian_eq_zero {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U)
    {x : ℝ^n} (hx : x ∈ U) :
    laplacian u x = 0 :=
  hu.2 x hx

/-- On an open domain, PDE-harmonicity gives ordinary pointwise `C²` regularity at each point.

This is the local form used in Evans-style arguments; without openness, `ContDiffOn` only gives
regularity relative to the set. -/
theorem IsHarmonicPDE.contDiffAt_of_isOpen {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    {x : ℝ^n} (hx : x ∈ U) :
    ContDiffAt ℝ 2 u x :=
  (hu.contDiffOn x hx).contDiffAt (hU.mem_nhds hx)

/-- On an open domain, the vanishing-Laplacian clause of `IsHarmonicPDE` holds throughout a
neighborhood of each point. -/
theorem IsHarmonicPDE.eventually_laplacian_eq_zero_of_isOpen {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    {x : ℝ^n} (hx : x ∈ U) :
    ∀ᶠ y in nhds x, laplacian u y = 0 :=
  Filter.eventually_of_mem (hU.mem_nhds hx) fun _ hy ↦ hu.laplacian_eq_zero hy

/-- Constructor for PDE harmonicity from `C²` regularity and vanishing Laplacian. -/
theorem IsHarmonicPDE.mk {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu_reg : ContDiffOn ℝ 2 u U)
    (hu_lap : ∀ x ∈ U, laplacian u x = 0) :
    IsHarmonicPDE n u U :=
  ⟨hu_reg, hu_lap⟩

/-- PDE-harmonicity restricts to smaller domains. -/
theorem IsHarmonicPDE.mono {n : ℕ}
    {u : ℝ^n → ℝ}
    {V U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hVU : V ⊆ U) :
    IsHarmonicPDE n u V :=
  ⟨hu.contDiffOn.mono hVU, fun x hx ↦ hu.laplacian_eq_zero (x := x) (hVU hx)⟩

/-- PDE-harmonicity restricts to any open Metric.ball contained in the original domain. -/
theorem IsHarmonicPDE.on_ball {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r : ℝ}
    (hball : Metric.ball x r ⊆ U) :
    IsHarmonicPDE n u (Metric.ball x r) :=
  hu.mono hball

/-- PDE-harmonicity restricts to any closed Metric.ball contained in the original domain. -/
theorem IsHarmonicPDE.on_closedBall {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) {x : ℝ^n} {r : ℝ}
    (hball : Metric.closedBall x r ⊆ U) :
    IsHarmonicPDE n u (Metric.closedBall x r) :=
  hu.mono hball

/-- The sum of two PDE-harmonic functions is PDE-harmonic on an open domain. -/
theorem IsHarmonicPDE.add {n : ℕ}
    {u v : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hv : IsHarmonicPDE n v U) (hU : IsOpen U) :
    IsHarmonicPDE n (fun x ↦ u x + v x) U := by
  constructor
  · exact hu.contDiffOn.add hv.contDiffOn
  · intro x hx
    have hu_x := hu.contDiffAt_of_isOpen hU hx
    have hv_x := hv.contDiffAt_of_isOpen hU hx
    rw [PDE.laplacian_add u v x hu_x hv_x, hu.laplacian_eq_zero hx,
      hv.laplacian_eq_zero hx, add_zero]

/-- A scalar multiple of a PDE-harmonic function is PDE-harmonic. -/
theorem IsHarmonicPDE.const_mul {n : ℕ}
    (c : ℝ) {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) :
    IsHarmonicPDE n (fun x ↦ c * u x) U := by
  constructor
  · exact contDiffOn_const.mul hu.contDiffOn
  · intro x hx
    rw [PDE.laplacian_const_smul c u x, hu.laplacian_eq_zero hx, mul_zero]

/-- The negative of a PDE-harmonic function is PDE-harmonic. -/
theorem IsHarmonicPDE.neg {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) :
    IsHarmonicPDE n (-u) U := by
  constructor
  · exact hu.contDiffOn.neg
  · intro x hx
    rw [PDE.laplacian_neg, hu.laplacian_eq_zero hx, neg_zero]

/-- The difference of two PDE-harmonic functions is PDE-harmonic on an open domain. -/
theorem IsHarmonicPDE.sub {n : ℕ}
    {u v : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hv : IsHarmonicPDE n v U) (hU : IsOpen U) :
    IsHarmonicPDE n (u - v) U := by
  constructor
  · exact hu.contDiffOn.sub hv.contDiffOn
  · intro x hx
    have hu_x := hu.contDiffAt_of_isOpen hU hx
    have hv_x := hv.contDiffAt_of_isOpen hU hx
    have hneg_x : ContDiffAt ℝ 2 (-v) x := hv_x.neg
    have hadd := PDE.laplacian_add u (-v) x hu_x hneg_x
    change laplacian (fun y ↦ u y + (-v) y) x = 0
    rw [hadd, PDE.laplacian_neg, hu.laplacian_eq_zero hx,
      hv.laplacian_eq_zero hx]
    simp

/-- Linear combinations of PDE-harmonic functions are PDE-harmonic on an open domain. -/
theorem IsHarmonicPDE.linear_combination {n : ℕ}
    (a b : ℝ) {u v : ℝ^n → ℝ}
    {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hv : IsHarmonicPDE n v U) (hU : IsOpen U) :
    IsHarmonicPDE n (fun x ↦ a * u x + b * v x) U :=
  (hu.const_mul a).add (hv.const_mul b) hU

end LaplacianEquation
