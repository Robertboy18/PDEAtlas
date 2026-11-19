/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.TangentialDerivatives

/-!
# Normal derivative of the normal flux

The weak-divergence identity `∑ᵢ ∫ qᵢ ∂ᵢ φ = ∫ f φ` determines the normal derivative of the
normal flux row once the tangential rows are known to have tangential derivatives:

`∂ₙ qₙ = -f - ∑_{i ≠ n} ∂ᵢ qᵢ` in the weak sense on the half-space.

This step uses the equation itself to recover the one second derivative that the tangential
difference-quotient estimate cannot reach. It replaces step 5 of Evans's proof of §6.3.2,
Theorem 4, which solves the nondivergence form (52)-(53) of the equation for `∂ₙ∂ₙ u`. The
shared weak-divergence calculation gives the missing derivative; we
represent it as an `L²` element with the triangle-inequality bound
`‖∂ₙ qₙ‖ ≤ ‖f‖ + ∑_{i ≠ n} ‖∂ᵢ qᵢ‖`, and apply it to the divergence-form flux
`qᵢ = ∑ⱼ aⁱʲ ∂ⱼ u` of a weak solution, using the tangential flux derivatives from
`TangentialDerivatives`.

## Main results

* `normalFlux.exists_weakDerivative_of_weakDivergence_with_norm`: abstract `L²`
  recovery of `∂ₙ qₙ` from the divergence identity and tangential derivatives `dqᵢ`, with the norm
  bound `‖f‖ + ∑_{i ≠ n} ‖dqᵢ‖`.
* `normalFlux.derivativeBound`: the explicit bound for the divergence-form flux.
* `divergenceFluxL2.exists_normalDerivative_with_norm`,
  `divergenceFluxL2.exists_normalDerivative`: for a weak solution with Lipschitz uniformly
  elliptic coefficients, the normal flux `∑ⱼ aⁿʲ ∂ⱼ u` has an `L²` normal weak derivative bounded
  by `normalFlux.derivativeBound`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 5 of the proof of Theorem 4, (52)-(55),
  pp. 336-337.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Quantitative `L²` form of normal-flux recovery.  The normal
derivative is represented by `-f` minus the sum of the tangential flux
derivatives, so its norm is bounded by the corresponding triangle
inequality. -/
theorem normalFlux.exists_weakDerivative_of_weakDivergence_with_norm
    [Fact (0 < n)]
    (q dq : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      tsupport φ.toFun ⊆ HalfSpace.upper n →
        (∑ i : Fin n,
          ∫ x, (q i : ℝ^n → ℝ) x *
            iteratedPartialDeriv (n := n) [i] φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n)) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n))
    (htangential : ∀ i : Fin n, i ≠ PDE.Common.lastIndex (n := n) →
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i]
        (q i : ℝ^n → ℝ) (dq i : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ ‖f‖ +
          ∑ i ∈ Finset.univ.erase (PDE.Common.lastIndex (n := n)), ‖dq i‖ ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (q (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  exact exists_component_weakDerivative_of_weakDivergence_with_norm
    (PDE.Common.lastIndex (n := n)) q dq f hdiv htangential

/-- Qualitative `L²` form of normal-flux recovery. -/
theorem normalFlux.exists_weakDerivative_of_weakDivergence
    [Fact (0 < n)]
    (q dq : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      tsupport φ.toFun ⊆ HalfSpace.upper n →
        (∑ i : Fin n,
          ∫ x, (q i : ℝ^n → ℝ) x *
            iteratedPartialDeriv (n := n) [i] φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n)) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n))
    (htangential : ∀ i : Fin n, i ≠ PDE.Common.lastIndex (n := n) →
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i]
        (q i : ℝ^n → ℝ) (dq i : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (q (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ :=
    normalFlux.exists_weakDerivative_of_weakDivergence_with_norm q dq f hdiv htangential
  exact ⟨g, hg⟩

/-- Bound for the normal derivative of the normal flux obtained from the weak
divergence equation. -/
noncomputable def normalFlux.derivativeBound
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (C : Fin n → Fin n → NNReal)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n)) (alpha : ℝ) : ℝ :=
  ‖f‖ + ∑ i ∈ Finset.univ.erase (PDE.Common.lastIndex (n := n)),
    divergenceFluxL2.tangentialDerivativeBound A C f u alpha i

/-- Quantitative normal-flux conclusion for the flattened equation. Under the
same ellipticity and Lipschitz hypotheses used in the tangential estimate,
the normal flux `Σⱼ Aₙⱼ ∂ⱼu` has an `L²` normal weak derivative with
the bound dictated by the weak divergence equation. -/
theorem divergenceFluxL2.exists_normalDerivative_with_norm
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
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ normalFlux.derivativeBound A C f u alpha ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (divergenceFluxL2 A u (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  classical
  let normal := PDE.Common.lastIndex (n := n)
  have hexists (i : {i : Fin n // i ≠ normal}) :
      ∃ g : DerivLp n 2 (HalfSpace.upper n),
        ‖g‖ ≤ divergenceFluxL2.tangentialDerivativeBound A C f u alpha i.1 ∧
          HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i.1]
          (divergenceFluxL2 A u i.1 : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
    exact divergenceFluxL2.exists_tangentialWeakDerivative_with_norm
      A a C haLip haRep hA halpha f u hu i.1 i.1
        (by simpa [normal] using i.2)
  choose d hdNorm hd using hexists
  let dq : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun i ↦
    if hi : i ≠ normal then d ⟨i, hi⟩ else 0
  have hdq (i : Fin n) (hi : i ≠ normal) :
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i]
        (divergenceFluxL2 A u i : ℝ^n → ℝ) (dq i : ℝ^n → ℝ) := by
    simpa [dq, hi] using hd ⟨i, hi⟩
  obtain ⟨g, hgNorm, hg⟩ :=
    normalFlux.exists_weakDerivative_of_weakDivergence_with_norm
      (fun i ↦ divergenceFluxL2 A u i) dq f
      (divergenceFluxL2.weakDivergence A f u hu) (by
        intro i hi
        exact hdq i (by simpa [normal] using hi))
  refine ⟨g, hgNorm.trans ?_, hg⟩
  unfold normalFlux.derivativeBound
  apply add_le_add (le_refl ‖f‖)
  apply Finset.sum_le_sum
  intro i hi
  have hine : i ≠ normal := (Finset.mem_erase.mp hi).1
  simpa [dq, hine] using hdNorm ⟨i, hine⟩

/-- Qualitative normal-flux conclusion for the flattened equation. -/
theorem divergenceFluxL2.exists_normalDerivative
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
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (divergenceFluxL2 A u (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ := divergenceFluxL2.exists_normalDerivative_with_norm
    A a C haLip haRep hA halpha f u hu
  exact ⟨g, hg⟩

end GraphSpace.BoundaryRegularity
end SobolevSpace
