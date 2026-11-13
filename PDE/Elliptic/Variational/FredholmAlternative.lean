/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fredholm.MassPullback
public import PDE.Elliptic.Variational.LowerOrderForm
import PDE.Analysis.Fredholm.WeakForm.Alternative
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# Fredholm alternative for elliptic variational problems

Let `B` be the full divergence-form bilinear form on `H¹₀(Ω)`, with operator coefficients `A`
(principal part), `b` (first order), and `c` (zeroth order). Evans's Second Existence Theorem
for weak solutions (§6.2.3, Theorem 4 (i)) is a dichotomy: either the homogeneous problem
`B[u, ·] = 0` has a nonzero solution, or `B[u, ·] = (f, ·)` has exactly one solution for every
`f ∈ L²(Ω)`. We prove it with every forcing `ℓ` in the dual of `H¹₀(Ω)` in place of `(f, ·)`.
The proof shifts `B` by a multiple `lambda` of the mass form `M[u,v] = ⟪u, v⟫_{L²}` to reach a
coercive form, inverts that form by Lax–Milgram, and observes that the inverse composed with
`M` is compact, because the embedding `H¹₀(Ω) → L²(Ω)` is compact on a bounded domain
(Rellich–Kondrachov).

We do that reduction for the concrete Sobolev forms. The operator-level dichotomy is
`PDE.Analysis.fredholmAlternative_weak_solution_exactlyOne`. Here the mass form is identified
with the pullback of the `L²` inner product along `baseCoordCLM`
(`massFormCLM_eq_innerPullbackOperator`), its compactness comes from
`baseCoordCLM.isCompactOperator_of_bounded`, and the alternative is stated for
`fullDivergenceForm`. The compactness hypothesis appears in three grades: `hcompactMass`
on the mass operator, `hcompactBase` on the embedding `H¹₀(Ω) → L²(Ω)`, and finally
`hΩbounded`, where Rellich discharges it. The first grade is the abstract core of Evans's
proof. The last needs only a bounded measurable `Ω`, as in his statement, but keeps the shifted
coercivity `hcoercive` as a hypothesis, which Evans derives from his energy estimates (§6.2.2,
Theorem 2).

## Main results

* `massFormCLM_eq_innerPullbackOperator`, `isCompactOperator_massFormCLM`,
  `isCompactOperator_massFormCLM_of_bounded`: compactness of the mass operator on `H¹₀(Ω)`.
* `fullDivergenceForm.fredholmAlternative`: the dichotomy under shifted coercivity and
  compactness of the mass operator.
* `fullDivergenceForm.fredholmAlternative_of_compactEmbedding`: compactness assumed at its
  source, the embedding `H¹₀(Ω) → L²(Ω)`.
* `fullDivergenceForm.fredholmAlternative_of_bounded`: the dichotomy on a bounded measurable
  domain, with compactness discharged internally.

The statement is the exclusive dichotomy, clause (i) of Evans's theorem; the clauses on the
adjoint nullspace and its orthogonality condition are at the operator level in
`PDE.Analysis.Fredholm`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, Theorem 4 (Second Existence Theorem for weak
  solutions) and its proof, pp. 321-323; §5.7, Theorem 1 (Rellich–Kondrachov Compactness
  Theorem) and the Remark after it, pp. 286-289; §D.5, Theorem 5 (Fredholm alternative),
  p. 725.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function Filter ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

section


/-- The concrete Sobolev mass form is the pullback of the `L²` inner product
along the base-coordinate embedding. -/
theorem massFormCLM_eq_innerPullbackOperator :
    massFormCLM (n := n) (Ω := Ω) =
      PDE.Analysis.innerPullbackOperator
        (V := H¹₀(Ω)) (W := DerivLp n 2 Ω)
        (baseCoordCLM (n := n) (Ω := Ω)) := by
  ext u v
  rw [massFormCLM_apply]
  exact (PDE.Analysis.innerPullbackOperator_apply
    (V := H¹₀(Ω)) (W := DerivLp n 2 Ω)
    (baseCoordCLM (n := n) (Ω := Ω)) u v).symm

/-- Compactness of `H¹₀(Ω) → L²(Ω)` implies compactness of the mass operator
used in the Fredholm reduction. -/
theorem isCompactOperator_massFormCLM
    (hcompactBase :
      IsCompactOperator (baseCoordCLM (n := n) (Ω := Ω))) :
    IsCompactOperator (massFormCLM (n := n) (Ω := Ω)) := by
  rw [massFormCLM_eq_innerPullbackOperator (n := n) (Ω := Ω)]
  exact PDE.Analysis.isCompactOperator_innerPullbackOperator _ hcompactBase

/-- On a bounded domain, Rellich compactness discharges the compactness
hypothesis on the Sobolev mass form used in Evans's Fredholm reduction. -/
theorem isCompactOperator_massFormCLM_of_bounded
    (hΩmeas : MeasurableSet Ω)
    (hΩbounded : Bornology.IsBounded Ω) :
    IsCompactOperator (massFormCLM (n := n) (Ω := Ω)) :=
  isCompactOperator_massFormCLM
    (baseCoordCLM.isCompactOperator_of_bounded hΩmeas hΩbounded)

/-- Evans §6.2.3, Theorem 4 (i), for LeanPDE's full divergence-form weak problem: if the form
shifted by `lambda` times the mass form is coercive and the mass operator is compact, then
exactly one of two statements holds. Either the homogeneous Dirichlet problem has a nonzero weak
solution, or every `H⁻¹` forcing has a unique weak solution.

The compactness hypothesis is exposed: its bounded-domain
discharge is exactly the Rellich–Kondrachov step in Evans' proof. -/
theorem fullDivergenceForm.fredholmAlternative
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (lambda : ℝ)
    (hcoercive : IsCoercive
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c lambda))
    (hcompactMass :
      IsCompactOperator (massFormCLM (n := n) (Ω := Ω))) :
    Xor
      (∃ u : H¹₀(Ω), u ≠ 0 ∧
        IsWeakSolution
          (fullDivergenceForm (n := n) (Ω := Ω) A b c) 0 u)
      (∀ ell : StrongDual ℝ (H¹₀(Ω)),
        ∃! u : H¹₀(Ω),
          IsWeakSolution
            (fullDivergenceForm (n := n) (Ω := Ω) A b c) ell u) := by
  let form : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
    fullDivergenceForm (n := n) (Ω := Ω) A b c
  let shiftedForm : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
    shiftedDivergenceForm (n := n) (Ω := Ω) A b c lambda
  let massForm : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
    massFormCLM (n := n) (Ω := Ω)
  have hcoercive' : IsCoercive shiftedForm :=
    hcoercive
  have hcompactMass' : IsCompactOperator massForm := hcompactMass
  have hshift : ∀ u v : H¹₀(Ω),
      shiftedForm u v = form u v + lambda * massForm u v := by
    intro u v
    simpa only [shiftedForm, form, massForm, massFormCLM_apply] using
      shiftedDivergenceForm_apply (n := n) (Ω := Ω) A b c lambda u v
  change Xor
    (∃ u : H¹₀(Ω), u ≠ 0 ∧
      IsWeakSolution
        form 0 u)
    (∀ ell : StrongDual ℝ H¹₀(Ω), ∃! u : H¹₀(Ω),
      IsWeakSolution
        form ell u)
  exact @PDE.Analysis.fredholmAlternative_weak_solution_exactlyOne H¹₀(Ω)
    inferInstance inferInstance inferInstance form shiftedForm massForm
    hcoercive' lambda hshift hcompactMass'

/-- The alternative of `fullDivergenceForm.fredholmAlternative`, with compactness assumed for
the embedding `H¹₀(Ω) → L²(Ω)` (`baseCoordCLM`) instead of the mass operator. -/
theorem fullDivergenceForm.fredholmAlternative_of_compactEmbedding
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (lambda : ℝ)
    (hcoercive : IsCoercive
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c lambda))
    (hcompactBase :
      IsCompactOperator (baseCoordCLM (n := n) (Ω := Ω))) :
    Xor
      (∃ u : H¹₀(Ω), u ≠ 0 ∧
        IsWeakSolution
          (fullDivergenceForm (n := n) (Ω := Ω) A b c) 0 u)
      (∀ ell : StrongDual ℝ (H¹₀(Ω)),
        ∃! u : H¹₀(Ω),
          IsWeakSolution
            (fullDivergenceForm (n := n) (Ω := Ω) A b c) ell u) :=
  fullDivergenceForm.fredholmAlternative A b c lambda hcoercive
    (isCompactOperator_massFormCLM hcompactBase)

/-- Evans §6.2.3, Theorem 4(i), bounded-domain weak Fredholm
alternative.  For the full divergence-form weak problem, shifted
coercivity suffices: compactness of the mass term follows from the bounded-domain
Rellich theorem through `isCompactOperator_massFormCLM_of_bounded`.

The statement is the mutually exclusive dichotomy of clause (i). -/
theorem fullDivergenceForm.fredholmAlternative_of_bounded
    (hΩmeas : MeasurableSet Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (lambda : ℝ)
    (hcoercive : IsCoercive
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c lambda)) :
    Xor
      (∃ u : H¹₀(Ω), u ≠ 0 ∧
        IsWeakSolution
          (fullDivergenceForm (n := n) (Ω := Ω) A b c) 0 u)
      (∀ ell : StrongDual ℝ (H¹₀(Ω)),
        ∃! u : H¹₀(Ω),
          IsWeakSolution
            (fullDivergenceForm (n := n) (Ω := Ω) A b c) ell u) :=
  fullDivergenceForm.fredholmAlternative A b c lambda hcoercive
    (isCompactOperator_massFormCLM_of_bounded hΩmeas hΩbounded)

end

end GraphSpace

end SobolevSpace
