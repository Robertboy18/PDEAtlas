/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Cauchy.CoordinateChange.Coefficients

/-!
# The quasilinear equation after an analytic change of coordinates

A function `u` satisfies the transformed equation at `y` exactly when `u ∘ c`
satisfies the original equation at `ψ y`. The pure transverse coefficient is the
original principal symbol times a nonzero power of the gradient norm.

These are steps 1 and 2 of the proof of Evans, §4.6.1, Theorem 1: after the change of
variables (9) the equation keeps the quasilinear form (10) (`equation_comp_iff`), and its
pure transverse coefficient is a nonzero multiple of the symbol, as in (11)
(`transformedCoefficients_replicate_ne_zero`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1, proof of Theorem 1, (9)-(11).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Analysis.MultiIndex

open scoped Gradient

namespace PDE.Cauchy.Quasilinear.Analytic

variable {n k : ℕ}

/-- Pullback by an analytic chart converts the original scalar equation
exactly into the equation with the transformed coefficients and forcing. -/
theorem equation_comp_iff
    (a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    {c ψ : ℝ^n → ℝ^n} {u : ℝ^n → ℝ} {y : ℝ^n}
    (hk : 0 < k) (hc : AnalyticAt ℝ c (ψ y)) (hu : AnalyticAt ℝ u y)
    (hcy : c (ψ y) = y) :
    (∑ α, a α (ψ y, coordinateJetLT k (u ∘ c) (ψ y)) *
        coordinateDeriv α (u ∘ c) (ψ y)) =
      b (ψ y, coordinateJetLT k (u ∘ c) (ψ y)) ↔
    (∑ β, transformedCoefficients a c ψ β (y, coordinateJetLT k u y) *
        coordinateDeriv β u y) =
      transformedForcing a b c ψ (y, coordinateJetLT k u y) := by
  classical
  let z := (y, coordinateJetLT k u y)
  have harg : coordinateArguments k c ψ z =
      (ψ y, coordinateJetLT k (u ∘ c) (ψ y)) :=
    coordinateArguments_coordinateJetLT hc hu hcy
  have hd (α : Sym (Fin n) k) :
      coordinateDeriv α (u ∘ c) (ψ y) =
        highestRemainder c (ψ y) (coordinateJetLT k u y) α +
          ∑ β, principalMatrix c (ψ y) α β * coordinateDeriv β u y := by
    simpa only [hcy] using coordinateDeriv_comp_eq hk hc (hcy.symm ▸ hu) α
  have hsum :
      (∑ α, a α (coordinateArguments k c ψ z) * coordinateDeriv α (u ∘ c) (ψ y)) =
        (∑ α, a α (coordinateArguments k c ψ z) *
          highestRemainder c (ψ y) (coordinateJetLT k u y) α) +
        ∑ β, transformedCoefficients a c ψ β z * coordinateDeriv β u y := by
    simp only [hd, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      transformedCoefficients, Finset.sum_mul, z]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro α _
    exact (mul_assoc _ _ _).symm
  rw [← harg, hsum]
  change _ + _ = _ ↔ _ = _ - _
  constructor <;> intro h <;> linarith

/-- The pure transverse coefficient is the original principal symbol at the unit
level normal, times the gradient norm to the power of the equation order. -/
theorem transformedCoefficients_replicate
    (a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    {c ψ : ℝ^n → ℝ^n} {φ : ℝ^n → ℝ} {y : ℝ^n}
    (hc : AnalyticAt ℝ c (ψ y)) (i : Fin n)
    (hlevel : (fun x ↦ c x i) =ᶠ[nhds (ψ y)] φ)
    (hreg : fderiv ℝ φ (ψ y) ≠ 0)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) :
    transformedCoefficients a c ψ (Sym.replicate k i) (y, q) =
      ‖∇ φ (ψ y)‖ ^ k *
        ∑ α, a α (coordinateArguments k c ψ (y, q)) *
          monomial α (PDE.Analysis.Hypersurface.levelNormal φ (ψ y)) := by
  simp only [transformedCoefficients, principalMatrix_replicate hc i hlevel]
  exact sum_monomial_gradient hreg _

/-- A noncharacteristic symbol at the original lower jet gives a nonzero
pure transverse coefficient at the chart-coordinate lower jet. -/
theorem transformedCoefficients_replicate_ne_zero
    (a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    {c ψ : ℝ^n → ℝ^n} {φ : ℝ^n → ℝ} {y : ℝ^n}
    (hc : AnalyticAt ℝ c (ψ y)) (i : Fin n)
    (hlevel : (fun x ↦ c x i) =ᶠ[nhds (ψ y)] φ)
    (hreg : fderiv ℝ φ (ψ y) ≠ 0)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)
    (hsymbol : ∑ α, a α (coordinateArguments k c ψ (y, q)) *
      monomial α (PDE.Analysis.Hypersurface.levelNormal φ (ψ y)) ≠ 0) :
    transformedCoefficients a c ψ (Sym.replicate k i) (y, q) ≠ 0 := by
  rw [transformedCoefficients_replicate a hc i hlevel hreg q]
  exact mul_ne_zero (pow_ne_zero _
    (norm_ne_zero_iff.mpr (PDE.Analysis.Hypersurface.gradient_ne_zero hreg))) hsymbol

/-- An analytic level chart preserves coefficient and forcing analyticity and
noncharacteristicity at the lower jet of an analytic function. The function can
be a solution germ or an analytic extension of prescribed normal data. Only
its lower jet at the base point enters the coefficient hypotheses. -/
theorem analyticAt_transformed_of_level_chart
    (a : Sym (Fin n) k → ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) → ℝ)
    {p y : ℝ^n} {u : ℝ^n → ℝ}
    (c : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hps : p ∈ c.source) (hcp : c p = y)
    (hc : AnalyticAt ℝ c p) (hψ : AnalyticAt ℝ c.symm y)
    {φ : ℝ^n → ℝ} (hreg : fderiv ℝ φ p ≠ 0) (i : Fin n)
    (hlevel : (fun x ↦ c x i) =ᶠ[nhds p] φ)
    (hu : AnalyticAt ℝ u p)
    (ha : ∀ α, AnalyticAt ℝ (a α) (p, coordinateJetLT k u p))
    (hb : AnalyticAt ℝ b (p, coordinateJetLT k u p))
    (hsymbol : ∑ α, a α (p, coordinateJetLT k u p) *
      monomial α (PDE.Analysis.Hypersurface.levelNormal φ p) ≠ 0) :
    (∀ α, AnalyticAt ℝ (transformedCoefficients a c c.symm α)
      (y, coordinateJetLT k (u ∘ c.symm) y)) ∧
    AnalyticAt ℝ (transformedForcing a b c c.symm)
      (y, coordinateJetLT k (u ∘ c.symm) y) ∧
    transformedCoefficients a c c.symm (Sym.replicate k i)
      (y, coordinateJetLT k (u ∘ c.symm) y) ≠ 0 := by
  have hip : c.symm y = p := by
    rw [← hcp]
    exact c.left_inv hps
  have hU : AnalyticAt ℝ (u ∘ c.symm) y := hu.comp_of_eq hψ hip
  have hcomp : (u ∘ c.symm) ∘ c =ᶠ[nhds p] u :=
    Filter.Eventually.mono (c.eventually_left_inverse hps) (fun x hx ↦ congrArg u hx)
  have hjet : coordinateJetLT k ((u ∘ c.symm) ∘ c) p = coordinateJetLT k u p := by
    funext j α
    exact congrArg (fun D ↦ D (directions α))
      ((hcomp.iteratedFDeriv ℝ j).self_of_nhds)
  let q := coordinateJetLT k (u ∘ c.symm) y
  have hc' : AnalyticAt ℝ c (c.symm y) := hip ▸ hc
  have harg : coordinateArguments k c c.symm (y, q) = (p, coordinateJetLT k u p) := by
    rw [coordinateArguments_coordinateJetLT hc' hU (by rw [hip, hcp]), hip, hjet]
  have ha' (α : Sym (Fin n) k) :
      AnalyticAt ℝ (a α) (coordinateArguments k c c.symm (y, q)) := by
    rw [harg]
    exact ha α
  refine ⟨fun α ↦ analyticAt_transformedCoefficients hc' hψ q ha' α,
    analyticAt_transformedForcing hc' hψ q ha' ?_, ?_⟩
  · rw [harg]
    exact hb
  · apply transformedCoefficients_replicate_ne_zero a hc' i (hip ▸ hlevel) (hip ▸ hreg) q
    simpa only [harg, hip] using hsymbol

end PDE.Cauchy.Quasilinear.Analytic
