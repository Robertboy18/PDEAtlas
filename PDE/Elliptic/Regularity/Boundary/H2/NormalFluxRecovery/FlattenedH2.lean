/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.NormalNormal
import PDE.Elliptic.Regularity.Boundary.H2.TangentialEstimate
import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives

/-!
# Flattened-boundary `H²` assembly

For a weak solution `u ∈ H¹₀` of `-∂ᵢ(aⁱʲ ∂ⱼ u) = f` on the upper half-space with Lipschitz,
uniformly elliptic coefficients, we assemble an `H²` representative of `u` on the half-space and
keep the componentwise estimate from each recovery step. This is the flattened part of Evans's proof
of §6.3.2, Theorem 4, steps 1-5.

The statement is local and flattened: it is the estimate on the half-space obtained after a boundary
chart. The global `H²(Ω)` theorem for a `C²` domain, `exists_global_h2_of_isWeakDivergenceSolution`,
is assembled from these local pieces.

## Main results

* `flattenedH2Regularity.secondDerivativeBound`: the bound assigned to each Hessian entry, the
  common tangential bound for entries with a tangential index and the reciprocal-flux bound for the
  normal-normal entry.
* `exists_flattened_h2_with_bounds`: existence of an `H²` representative of `u` on the half-space
  with `‖∂ᵢ∂ⱼ u‖ ≤ secondDerivativeBound i j` for all `i, j`.
* `exists_flattened_h2`: the qualitative form.

## How it works

Evans bounds the tangential difference quotients of `Du` near the flat boundary, which gives every
second derivative with a tangential index, (51), and then solves the nondivergence form (52)-(53) of
the equation for `∂ₙ∂ₙ u`, using `aⁿⁿ ≥ θ` (54). The first half is the same in our proof:
`tangentialSecondWeakDerivative.exists_with_norm` and
`tangentialGradientComponent.exists_normalDerivative_with_norm` give the entries with a tangential
index. For the normal-normal entry we never pass to the nondivergence form, which needs `Lu = f`
almost everywhere. The flux rows have tangential weak derivatives
(`divergenceFluxL2.exists_tangentialWeakDerivative`), the weak divergence identity then gives the
normal derivative of the normal flux (`divergenceFluxL2.exists_normalDerivative`), and
`normalNormalWeakDerivative.exists_with_norm` subtracts the cross terms and divides by the normal
coefficient.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 1-5 of the proof of Theorem 4, (43)-(56),
  pp. 335-337.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Componentwise bound for the Hessian recovered by the flattened-boundary
argument. Tangential and mixed entries obey the common difference-quotient
bound; the normal-normal entry obeys the reciprocal-flux bound. -/
noncomputable def flattenedH2Regularity.secondDerivativeBound
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (i j : Fin n) : ℝ :=
  if j = PDE.Common.lastIndex (n := n) then
    if i = PDE.Common.lastIndex (n := n) then
      normalNormalWeakDerivative.bound A a C haLip haRep halpha f u
    else
      tangentialSecondWeakDerivative.bound C f u alpha
  else
    tangentialSecondWeakDerivative.bound C f u alpha

/-- Quantitative local flattened-boundary `H²` regularity. The
tangential, mixed, and normal-normal weak derivatives assemble into an `H²`
representative, and each Hessian row retains the estimate proved in the
corresponding recovery step. -/
theorem exists_flattened_h2_with_bounds
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑((((u : H¹(HalfSpace.upper n)) :
              WkpAmbientOn n 1 2 (HalfSpace.upper n))
            (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))) x) ∧
      (∀ i,
        ⇑((W : WkpAmbientOn n 2 2 (HalfSpace.upper n))
            (firstDerivIndex n 2 (by norm_num) i) :
              DerivLp n 2 (HalfSpace.upper n))
          =ᵐ[domainMeasure n (HalfSpace.upper n)]
            ⇑(((u : H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (singleDerivIndex n i) : DerivLp n 2 (HalfSpace.upper n))) ∧
      ∀ b : DerivIndex n 2, ∀ i j : Fin n, b.toList = [i, j] →
        ‖((W : WkpAmbientOn n 2 2 (HalfSpace.upper n)) b :
            DerivLp n 2 (HalfSpace.upper n))‖ ≤
          flattenedH2Regularity.secondDerivativeBound
            A a C haLip haRep halpha f u i j := by
  let normal := PDE.Common.lastIndex (n := n)
  have hsecondExist (i j : Fin n) :
      ∃ g : DerivLp n 2 (HalfSpace.upper n),
        ‖g‖ ≤ flattenedH2Regularity.secondDerivativeBound A a C haLip haRep halpha f u i j ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [j]
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u : ℝ^n → ℝ)
          (g : ℝ^n → ℝ) := by
    by_cases hj : j ≠ normal
    · obtain ⟨g, hgNorm, hg⟩ := tangentialSecondWeakDerivative.exists_with_norm
        A a C haLip haRep hA halpha f u hu j (by simpa [normal] using hj) i
      refine ⟨g, ?_, hg⟩
      simpa [flattenedH2Regularity.secondDerivativeBound, normal, hj,
        tangentialSecondWeakDerivative.bound] using hgNorm
    · have hjEq : j = normal := not_ne_iff.mp hj
      subst j
      by_cases hi : i ≠ normal
      · obtain ⟨g, hgNorm, hg⟩ :=
          tangentialGradientComponent.exists_normalDerivative_with_norm
            A a C haLip haRep hA halpha f u hu i (by simpa [normal] using hi)
        refine ⟨g, ?_, hg⟩
        simpa [flattenedH2Regularity.secondDerivativeBound, normal, hi,
          tangentialSecondWeakDerivative.bound] using hgNorm
      · have hiEq : i = normal := not_ne_iff.mp hi
        subst i
        obtain ⟨g, hgNorm, hg⟩ := normalNormalWeakDerivative.exists_with_norm
          A a C haLip haRep hA halpha f u hu
        exact ⟨g, by simpa [flattenedH2Regularity.secondDerivativeBound, normal] using hgNorm, hg⟩
  choose g hgNorm hg using hsecondExist
  let U : H¹(HalfSpace.upper n) := u
  let rows : Fin n → Fin n → ℝ^n → ℝ := fun i j ↦ (g i j : ℝ^n → ℝ)
  have hrowsMem (i j : Fin n) : MemLp (rows i j) 2
      (domainMeasure n (HalfSpace.upper n)) := MeasureTheory.Lp.memLp (g i j)
  have hrowsWeak (i j : Fin n) :
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [j]
        ((((U : WkpAmbientOn n 1 2 (HalfSpace.upper n))
          (singleDerivIndex n i) : DerivLp n 2 (HalfSpace.upper n)) :
            ℝ^n → ℝ))
        (rows i j) := by
    simpa only [U, rows, derivCoordCLM_apply] using hg i j
  obtain ⟨W, hWbase, hWfirst, hWsecond, _hWnorm⟩ :=
    exists_H2_of_firstDerivatives_haveWeakDerivatives
      U rows hrowsMem hrowsWeak
  refine ⟨W, hWbase, hWfirst, ?_⟩
  intro b i j hb
  have heq :
      ((W : WkpAmbientOn n 2 2 (HalfSpace.upper n)) b :
        DerivLp n 2 (HalfSpace.upper n)) = g i j := by
    apply MeasureTheory.Lp.ext
    simpa [rows] using hWsecond b i j hb
  rw [heq]
  exact hgNorm i j

/-- Qualitative form of local flattened-boundary `H²` regularity. -/
theorem exists_flattened_h2
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      ((((W : WkpAmbientOn n 2 2 (HalfSpace.upper n)) (baseIndex n 2) :
          DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ((((u : H¹(HalfSpace.upper n)) :
              WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) :
            DerivLp n 2 (HalfSpace.upper n)) : ℝ^n → ℝ)) := by
  obtain ⟨W, hW, _, _⟩ :=
    exists_flattened_h2_with_bounds
      A a C haLip haRep hA halpha f u hu
  exact ⟨W, hW⟩

end GraphSpace.BoundaryRegularity
end SobolevSpace
