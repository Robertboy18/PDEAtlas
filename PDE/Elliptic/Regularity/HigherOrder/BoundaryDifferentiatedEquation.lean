/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.FlattenedH2
import PDE.Elliptic.Regularity.HigherOrder.DifferentiatedEquation

/-!
# Boundary differentiated equations

A tangential first derivative of a weak solution on the upper half-space gains an `H²`
representative (`exists_flattened_h2_tangentialCoordinateDerivative_upper`). The differentiated
equation supplies its `L²` forcing, the tangential trace theorem makes it an admissible `H¹₀`
solution, and the flattened-boundary `H²` theorem gives its second weak derivatives. This is the
case `|α| = 1` of step 3 of Evans's proof of §6.3.2, Theorem 5, which gives boundary `H³`
regularity. The domain-independent differentiated equation and the interior assembly results are in
`DifferentiatedEquation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 3 of the proof of Theorem 5, (85)-(90),
  pp. 341-342.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {n : ℕ} [Fact (0 < n)]

/--
A tangential first derivative on the upper half-space gains an `H²`
representative.  The differentiated equation supplies its `L²` forcing, the
tangential trace theorem makes it an admissible `H¹₀` solution, and the
flattened-boundary regularity theorem supplies all of its second
weak derivatives.
-/
theorem exists_flattened_h2_tangentialCoordinateDerivative_upper
    (A : Fin n → Fin n →
      W^{2,∞}(HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n)))
      alpha)
    (halpha : 0 < alpha)
    (F : W^{1,2}(HalfSpace.upper n))
    (U : W^{2,2}(HalfSpace.upper n))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2)
          (Ω := HalfSpace.upper n) (by norm_num) U ∈
        (h10SubmoduleOn
          (n := n) (Ω := HalfSpace.upper n)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦
        ((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n)))
      ((F : WkpAmbientOn n 1 2 (HalfSpace.upper n))
        (baseIndex n 1) : DerivLp n 2 (HalfSpace.upper n))
      ⟨lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2)
          (Ω := HalfSpace.upper n) (by norm_num) U,
        htrace0⟩) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      ⇑((W : WkpAmbientOn n 2 2 (HalfSpace.upper n))
          (baseIndex n 2) : DerivLp n 2 (HalfSpace.upper n))
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          ⇑((derivativeWordCLM
            (n := n) (m := 2) (r := 1) (p := 2)
            (Ω := HalfSpace.upper n) [k] (by simp) U :
              W^{1,2}(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
            (baseIndex n 1) := by
  let coeff : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n) :=
    fun i j ↦
      ((A i j : WkpAmbientOn n 2 ∞ (HalfSpace.upper n))
        (baseIndex n 2) : DerivLp n ∞ (HalfSpace.upper n))
  have htracek := tangentialDerivative_mem_H10 U htrace0 k hk
  let w : H¹₀(HalfSpace.upper n) :=
    ⟨derivativeWordCLM
        (n := n) (m := 2) (r := 1) (p := 2)
        (Ω := HalfSpace.upper n) [k] (by simp) U,
      htracek⟩
  obtain ⟨g, hg⟩ :=
    exists_coordinateDerivative_l2_weakEquation_solution
      (HalfSpace.isOpen_upper (n := n)) A F U k htrace0 htracek hu
  have hg' : IsWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n) coeff g w := by
    simpa [coeff, w] using hg
  -- `variableCoeffForm` uses the normed-space structure inherited from the
  -- defining closed submodule, so use that same instance here.
  have hgWeak : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) coeff))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n)
        g) w :=
    (isWeakSolution_iff_isWeakDivergenceSolution
      (n := n) (Ω := HalfSpace.upper n)
      (HalfSpace.isOpen_upper (n := n)) coeff g w).2 hg'
  obtain ⟨W, hW⟩ :=
    exists_flattened_h2 coeff a C haLip
      (by simpa [coeff] using haRep) (by simpa [coeff] using hA)
      halpha g w hgWeak
  refine ⟨W, ?_⟩
  simpa [w] using hW

end SobolevSpace.GraphSpace.BoundaryRegularity
