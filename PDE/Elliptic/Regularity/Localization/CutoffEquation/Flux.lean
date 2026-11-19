/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation

/-!
# Cutoff fluxes for divergence-form equations

Localizing a weak solution `u` of `-∂ᵢ(aᵢⱼ ∂ⱼ u) = f` by a smooth cutoff `ρ`
produces the equation for `ρ u` with the commutator forcing

`ρ f - ∑ᵢⱼ aᵢⱼ ∂ⱼ u ∂ᵢ ρ - ∑ᵢ ∂ᵢ(u ∑ⱼ aᵢⱼ ∂ⱼ ρ)`.

The last group is the divergence of the cutoff flux `qᵢ = u ∑ⱼ aᵢⱼ ∂ⱼ ρ`. For
this forcing to be an `L²` function rather than a distribution, `qᵢ` must
have an `L²` weak `i`-derivative. We prove that it does as soon as
`u ∈ L²` has an `L²` weak `i`-derivative (so in particular for `u ∈ H¹`),
`aᵢⱼ ∈ W^{1,∞}`, and `ρ` is smooth, and record the full weak Leibniz
expansion of `∂ᵢ qᵢ`. Evans handles solutions that need not vanish on the
boundary by putting the cutoff inside the test function (§6.3.1, proof of
Theorem 1); we put it on the solution instead, which turns a local solution
into a zero-trace one at the cost of this forcing.

## Main results

* `exists_weakDerivative_cutoffFluxTerm`: the single term `qᵢⱼ = (∂ⱼρ) aᵢⱼ u`
  has the `L²` weak `i`-derivative
  `(∂ⱼρ)(aᵢⱼ ∂ᵢu + (∂ᵢaᵢⱼ) u) + (∂ᵢ∂ⱼρ) aᵢⱼ u`.
* `exists_weakDerivative_cutoffFluxRow`,
  `exists_weakDerivative_cutoffFluxRowLp`: the sum over `j`, as a function
  and as an `L²` class.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1 and remark (i) after it (the solution
  need not vanish on the boundary).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open SobolevSpace.CompactSupportLocalization
open scoped BigOperators Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- One summand of the cutoff flux,
`qᵢⱼ = (∂ⱼρ) aᵢⱼ u`, has an `L²` weak `i`-derivative.  The returned
representatives record the full weak Leibniz expansion, including the weak
derivative of `aᵢⱼ`. -/
theorem exists_weakDerivative_cutoffFluxTerm
    (hΩopen : IsOpen Ω) (A : W^{1,∞}(Ω))
    (u du : DerivLp n 2 Ω) (i j : Fin n)
    (hu : HasWeakDerivativeOn (n := n) Ω [i]
      (u : ℝ^n → ℝ) (du : ℝ^n → ℝ))
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ q dq : DerivLp n 2 Ω,
      ((q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        iteratedPartialDeriv (n := n) [j] ρ.toFun x *
          ((((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
            DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)) ∧
      ((dq : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        iteratedPartialDeriv (n := n) [j] ρ.toFun x *
            (((((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x * du x) +
              ((((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)) +
          iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
            ((((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
              DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)) ∧
      HasWeakDerivativeOn (n := n) Ω [i]
        (q : ℝ^n → ℝ) (dq : ℝ^n → ℝ) := by
  let a : ℝ^n → ℝ := ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)
  let da : ℝ^n → ℝ := ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) : DerivLp n ∞ Ω)
  let dρ : ℝ^n → ℝ := fun x ↦ iteratedPartialDeriv (n := n) [j] ρ.toFun x
  let ddρ : ℝ^n → ℝ := fun x ↦ iteratedPartialDeriv (n := n) [i, j] ρ.toFun x
  have hρ (l : List (Fin n)) :
      MemLp (fun x ↦ iteratedPartialDeriv (n := n) l ρ.toFun x) ∞ (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) ρ.contDiff l).continuous
      |>.memLp_top_of_hasCompactSupport (iteratedPartialDeriv_hasCompactSupport (n := n) ρ l) _
  have hauLp : MemLp (fun x ↦ a x * u x) 2 (domainMeasure n Ω) :=
    (Lp.memLp ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).fun_mul (Lp.memLp u)
  have hdauLp : MemLp (fun x ↦ a x * du x + da x * u x) 2 (domainMeasure n Ω) :=
    ((Lp.memLp ((A : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).fun_mul (Lp.memLp du)).add
      ((Lp.memLp ((A : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i))).fun_mul (Lp.memLp u))
  have hqLp : MemLp (fun x ↦ dρ x * (a x * u x)) 2 (domainMeasure n Ω) :=
    (hρ [j]).fun_mul hauLp
  have hdqLp : MemLp (fun x ↦ dρ x * (a x * du x + da x * u x) + ddρ x * (a x * u x)) 2
      (domainMeasure n Ω) :=
    ((hρ [j]).fun_mul hdauLp).add ((hρ [i, j]).fun_mul hauLp)
  let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) ρ
  have hψ : (ψ : ℝ^n → ℝ) = fun x ↦ (∂[j] ρ.toFun) x := by
    funext x
    change (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) ρ :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = (∂[j] ρ.toFun) x
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp),
      (ρ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hqWeak : HasWeakDerivativeOn (n := n) Ω [i] (fun x ↦ dρ x * (a x * u x))
      (fun x ↦ dρ x * (a x * du x + da x * u x) + ddρ x * (a x * u x)) := by
    simpa [dρ, ddρ, hψ, iteratedPartialDeriv] using hasWeakDerivativeOn_mul_testFunction_first
      hauLp hdauLp (A.hasWeakDerivativeOn_mul_W1Top_first hΩopen i u du hu) ψ
  exact ⟨hqLp.toLp _, hdqLp.toLp _, hqLp.coeFn_toLp, hdqLp.coeFn_toLp,
    hqWeak.congr_ae hqLp.coeFn_toLp.symm hdqLp.coeFn_toLp.symm⟩

/-- Summing the preceding identity over the column index gives the cutoff
flux row

`qᵢ = u ∑ⱼ aᵢⱼ ∂ⱼρ`

and its `L²` weak divergence component `∂ᵢqᵢ`. -/
theorem exists_weakDerivative_cutoffFluxRow
    (hΩopen : IsOpen Ω) (Arow : Fin n → W^{1,∞}(Ω))
    (u du : DerivLp n 2 Ω) (i : Fin n)
    (hu : HasWeakDerivativeOn (n := n) Ω [i]
      (u : ℝ^n → ℝ) (du : ℝ^n → ℝ))
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ q dq : DerivLp n 2 Ω,
      ((q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ∑ j : Fin n,
          iteratedPartialDeriv (n := n) [j] ρ.toFun x *
            (((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
              DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x))) ∧
      ((dq : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ∑ j : Fin n,
          (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
              (((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x * du x) +
                ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)) +
            iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
              ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x))) ∧
      HasWeakDerivativeOn (n := n) Ω [i]
        (q : ℝ^n → ℝ) (dq : ℝ^n → ℝ) := by
  classical
  choose q dq hq hdq hweak using fun j ↦
    exists_weakDerivative_cutoffFluxTerm hΩopen (Arow j) u du i j hu ρ
  have hsumWeak := hasWeakDerivativeOn_finsetSum Finset.univ _ _ [i] fun j _ ↦
    (hweak j).congr_ae (hq j) (hdq j)
  have hqLp := memLp_finsetSum Finset.univ fun j _ ↦ (Lp.memLp (q j)).ae_eq (hq j)
  have hdqLp := memLp_finsetSum Finset.univ fun j _ ↦ (Lp.memLp (dq j)).ae_eq (hdq j)
  refine ⟨hqLp.toLp _, hdqLp.toLp _, ?_, ?_,
    hsumWeak.congr_ae hqLp.coeFn_toLp.symm hdqLp.coeFn_toLp.symm⟩
  · simpa using hqLp.coeFn_toLp
  · simpa using hdqLp.coeFn_toLp

/-- The row cutoff flux in its natural `L²` algebraic form has an `L²` weak
coordinate divergence, with the complete weak Leibniz expansion. -/
theorem exists_weakDerivative_cutoffFluxRowLp
    (hΩopen : IsOpen Ω) (Arow : Fin n → W^{1,∞}(Ω))
    (u du : DerivLp n 2 Ω) (i : Fin n)
    (hu : HasWeakDerivativeOn (n := n) Ω [i]
      (u : ℝ^n → ℝ) (du : ℝ^n → ℝ))
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ dq : DerivLp n 2 Ω,
      HasWeakDerivativeOn (n := n) Ω [i]
        ((∑ j : Fin n,
          partialTestFunctionLpTop (n := n) (Ω := Ω) ρ j •
            ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
              DerivLp n ∞ Ω)) • u) : DerivLp n 2 Ω) : ℝ^n → ℝ)
        (dq : ℝ^n → ℝ) ∧
      ((dq : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ∑ j : Fin n,
          (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
              (((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x * du x) +
                ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x)) +
            iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
              ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                DerivLp n ∞ Ω) : ℝ^n → ℝ) x * u x))) := by
  classical
  obtain ⟨q, dq, hq, hdq, hweak⟩ := exists_weakDerivative_cutoffFluxRow hΩopen Arow u du i hu ρ
  refine ⟨dq, hweak.congr_ae (hq.trans ?_) .rfl, hdq⟩
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun j ↦
      partialTestFunctionLpTop (n := n) (Ω := Ω) ρ j •
        ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)) • u),
    ae_all_iff.2 fun j ↦ partialTestFunctionLpTop_apply_ae (n := n) (Ω := Ω) ρ j,
    ae_all_iff.2 fun j ↦ Lp.coeFn_lpSMul (r := (2 : ENNReal))
      (((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)) u,
    ae_all_iff.2 fun j ↦ Lp.coeFn_lpSMul (r := (2 : ENNReal))
      (partialTestFunctionLpTop (n := n) (Ω := Ω) ρ j)
      ((((Arow j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)) • u)]
    with x hx hd hinner hout
  rw [hx]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hout j, Pi.smul_apply', smul_eq_mul, hd j, hinner j, Pi.smul_apply', smul_eq_mul]

end SobolevSpace.GraphSpace
