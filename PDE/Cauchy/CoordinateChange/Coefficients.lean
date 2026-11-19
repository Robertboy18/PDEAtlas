/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.CoordinateChange.Arguments
public import PDE.Cauchy.CoordinateChange.Principal

/-!
# Transformed quasilinear coefficients

The principal matrix transports every highest mixed derivative. The
remaining terms depend analytically on position and all lower jets, so the
transformed equation is again quasilinear of the same order. Evans, §4.6.1, proof of
Theorem 1, step 1, leaves this form (10) of the transformed equation to the reader.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1(b), Theorem 1 (Cauchy data and
  noncharacteristic surfaces) and its proof, (9)-(12), pp. 235-236.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {n k : ℕ}

/-- Coefficient of each highest mixed derivative in chart coordinates. -/
def transformedCoefficients
    (a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    (c ψ : ℝ^n → ℝ^n) (β : Sym (Fin n) k)
    (z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)) : ℝ :=
  ∑ α, a α (coordinateArguments k c ψ z) * principalMatrix c (ψ z.1) α β

/-- The forcing after moving the lower-jet part of the highest derivatives
to the right side of the equation. -/
def transformedForcing
    (a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    (c ψ : ℝ^n → ℝ^n)
    (z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)) : ℝ :=
  b (coordinateArguments k c ψ z) -
    ∑ α, a α (coordinateArguments k c ψ z) * highestRemainder c (ψ z.1) z.2 α

/-- Analyticity of the original coefficients gives analyticity of every
transformed principal coefficient at every lower-jet array. -/
theorem analyticAt_transformedCoefficients
    {a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ}
    {c ψ : ℝ^n → ℝ^n} {y : ℝ^n}
    (hc : AnalyticAt ℝ c (ψ y)) (hψ : AnalyticAt ℝ ψ y)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)
    (ha : ∀ α, AnalyticAt ℝ (a α) (coordinateArguments k c ψ (y, q)))
    (β : Sym (Fin n) k) :
    AnalyticAt ℝ (transformedCoefficients a c ψ β) (y, q) := by
  have harg := analyticAt_coordinateArguments hc hψ q
  have hp := hψ.comp
    (show AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ z.1) (y, q) from
        analyticAt_fst)
  exact Finset.univ.analyticAt_fun_sum fun α _ ↦
    ((ha α).comp_of_eq harg rfl).mul
      ((analyticAt_principalMatrix hc α β).comp_of_eq hp rfl)

private theorem analyticAt_weighted_remainder
    {a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ}
    {c ψ : ℝ^n → ℝ^n} {y : ℝ^n}
    (hc : AnalyticAt ℝ c (ψ y)) (hψ : AnalyticAt ℝ ψ y)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)
    (α : Sym (Fin n) k)
    (ha : AnalyticAt ℝ (a α) (coordinateArguments k c ψ (y, q))) :
    AnalyticAt ℝ (fun z ↦ a α (coordinateArguments k c ψ z) *
      highestRemainder c (ψ z.1) z.2 α) (y, q) := by
  have harg := analyticAt_coordinateArguments hc hψ q
  have hf : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ z.1) (y, q) :=
    analyticAt_fst
  have hq : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ z.2) (y, q) :=
    analyticAt_snd
  have hp : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ (ψ z.1, z.2))
      (y, q) := (hψ.comp_of_eq hf rfl).prod hq
  have hl : AnalyticAt ℝ (fun z ↦ a α (coordinateArguments k c ψ z)) (y, q) :=
    ha.comp_of_eq harg rfl
  have hr : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦
        highestRemainder c (ψ z.1) z.2 α) (y, q) :=
    (analyticAt_highestRemainder hc q α).comp_of_eq
      (g := fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦
        highestRemainder c z.1 z.2 α)
      (f := fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ (ψ z.1, z.2))
      (x := (y, q)) (y := (ψ y, q)) hp rfl
  exact hl.mul hr

/-- The transformed forcing is analytic on the same full lower-jet domain. -/
theorem analyticAt_transformedForcing
    {a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ}
    {b : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ}
    {c ψ : ℝ^n → ℝ^n} {y : ℝ^n}
    (hc : AnalyticAt ℝ c (ψ y)) (hψ : AnalyticAt ℝ ψ y)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)
    (ha : ∀ α, AnalyticAt ℝ (a α) (coordinateArguments k c ψ (y, q)))
    (hb : AnalyticAt ℝ b (coordinateArguments k c ψ (y, q))) :
    AnalyticAt ℝ (transformedForcing a b c ψ) (y, q) :=
  (hb.comp_of_eq (analyticAt_coordinateArguments hc hψ q) rfl).sub
    (Finset.univ.analyticAt_fun_sum fun α _ ↦
      analyticAt_weighted_remainder hc hψ q α (ha α))

end PDE.Cauchy.Quasilinear.Analytic
