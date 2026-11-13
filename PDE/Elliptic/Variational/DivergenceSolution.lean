/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.QuadraticEnergy
public import PDE.Analysis.Variational.LaxMilgram
import PDE.Analysis.Operator.Coercivity
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Divergence-form solution theory

For a uniformly elliptic operator-coefficient matrix `A` on a bounded domain `Ω ⊆ ℝ^n`, the
variable-coefficient form `Bₐ` of `PDE.Elliptic.Variational.DivergenceForm` is bounded and
coercive on `H¹₀(Ω)`, so the Lax–Milgram theorem produces, for every `f ∈ L²(Ω)`, a unique weak
solution of the homogeneous Dirichlet problem `-∂ᵢ(aᵢⱼ ∂ⱼu) = f`. We name that
solution, realize the solution map as a bounded operator `L²(Ω) →L[ℝ] H¹₀(Ω)`, and prove the
stability estimates and the energy-minimization characterization that go with it. The
measurable-coefficient case (`aᵢⱼ ∈ L∞(Ω)`, elliptic almost everywhere) is obtained by
specializing to multiplication operators.

## Main results

* `variableCoeffSolveCLM`, `variableCoeffSolve`: the Lax–Milgram solution operator and the
  named weak solution for operator coefficients.
* `weakDivergenceSolveCLM`, `weakDivergenceSolve`: the same for measurable `L∞` coefficients.
* `existsUnique_variableCoeff_weakSolution`, `IsWeakDivergenceSolution.existsUnique_of_ae`:
  existence and uniqueness of weak solutions.
* `weakDivergenceSolve_integral_equation`: the weak equation written with integrals.
* `variableCoeffSolve_norm_le`, `variableCoeffSolve_sub_variableCoeffSolve_norm_le`:
  continuous dependence of the solution on the `L²` datum.
* `variableCoeffEnergy_minimizer_iff_weakSolution`,
  `variableCoeffSolve_unique_energyMinimizer`: for symmetric coefficients, weak solutions are
  exactly the minimizers of `J(v) = ½ Bₐ(v,v) - ⟪f, v⟫`, and the minimizer is unique.

## Implementation notes

The solution operator is linear and continuous rather than defined pointwise by choice.
`exists_global_h2_of_isWeakDivergenceSolution` shows that, under Evans's `C¹`
coefficient and `C²` boundary hypotheses, each value has an `H²` representative; linearity and
continuity of the operator are what allow a closed-graph upgrade of that qualitative statement
to a uniform `H²` estimate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, Definitions (8)-(9), p. 314; §6.2.1, Theorem 1
  (Lax–Milgram Theorem), pp. 315-317; §6.2.2, Theorems 2 and 3, pp. 318-319, and the Examples
  on p. 320 (`γ = 0` without lower-order terms); §6.3.2, Theorem 4 (Boundary
  `H²`-regularity), p. 334; §8.1.2, Example 2 (Generalized Dirichlet's principle), p. 456.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


section LaxMilgram

local notation "L2" => DerivLp n 2 Ω

-- Cache the inherited additive and Hilbert structures at this abstraction
-- boundary.  Opening `SobolevSpace.GraphSpace` activates the inherited caches. Without
-- them, elaborating the generic
-- Lax–Milgram theorem repeatedly unfolds the nested `W^{1,2}_0` subtype.
/-- The inherited normed additive structure on the `H¹₀(Ω)` space. -/
scoped instance h10NormedAddCommGroup : NormedAddCommGroup H¹₀(Ω) := inferInstance
/-- The inherited real Hilbert-space structure on the `H¹₀(Ω)` space. -/
scoped instance h10InnerProductSpace : InnerProductSpace ℝ H¹₀(Ω) := inferInstance

/-- The Lax–Milgram solution of the variable-coefficient problem as a
bounded linear operator `L²(Ω) → H¹₀(Ω)`.

The theorem `exists_global_h2_of_isWeakDivergenceSolution` later
shows that, for `C¹` coefficients and a `C²` boundary (Evans §6.3.2), every
value of this map has an `H²` representative.  Keeping the
present operator linear and continuous is what permits a closed-graph
upgrade of that qualitative regularity statement to a uniform `H²`
estimate. -/
noncomputable def variableCoeffSolveCLM
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha) :
    L2 →L[ℝ] H¹₀(Ω) := by
  have hB : IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) :=
    variableCoeffForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded A hA
  let S : StrongDual ℝ H¹₀(Ω) →L[ℝ] H¹₀(Ω) :=
    solveCLM (V := H¹₀(Ω))
      (variableCoeffForm (n := n) (Ω := Ω) A) hB
  let L : L2 →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
    loadFunctionalCLM (n := n) (Ω := Ω)
  exact S.comp L

/-- The unique weak solution of the uniformly elliptic divergence-form problem. -/
noncomputable def variableCoeffSolve
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (f : L2) : H¹₀(Ω) :=
  variableCoeffSolveCLM (n := n) (Ω := Ω)
    hn hΩbounded A hA f

/-- Evaluating the bounded solution operator at `f` gives the named weak solution
`variableCoeffSolve f`. -/
@[simp]
theorem variableCoeffSolveCLM_apply
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (f : L2) :
    variableCoeffSolveCLM (n := n) (Ω := Ω)
        hn hΩbounded A hA f =
      variableCoeffSolve (n := n) (Ω := Ω)
        hn hΩbounded A hA f :=
  rfl

/-- The named solver satisfies the variational equation. -/
theorem variableCoeffSolve_isWeakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (f : L2) :
    IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω) A)
      (loadFunctional (n := n) (Ω := Ω) f)
      (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hA f) := by
  have hB : IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) :=
    variableCoeffForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded A hA
  unfold variableCoeffSolve variableCoeffSolveCLM
  rw [ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply]
  exact solveCLM.isWeakSolution _ hB _

/-- The variable-coefficient problem has exactly one `H¹₀` weak solution. -/
theorem existsUnique_variableCoeff_weakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (f : L2) :
    ∃! u : H¹₀(Ω),
      IsWeakSolution
        (variableCoeffForm (n := n) (Ω := Ω) A)
        (loadFunctional (n := n) (Ω := Ω) f) u := by
  let u := variableCoeffSolve (n := n) (Ω := Ω)
    hn hΩbounded A hA f
  have hu : IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω) A)
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    exact variableCoeffSolve_isWeakSolution
      (n := n) (Ω := Ω) hn hΩbounded A hA f
  have hB : IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) :=
    variableCoeffForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded A hA
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact @IsWeakSolution.unique H¹₀(Ω) inferInstance
    inferInstance
    (variableCoeffForm (n := n) (Ω := Ω) A) hB
    (loadFunctional (n := n) (Ω := Ω) f) v u hv hu

/-- Existence and uniqueness for the distributional divergence-form equation
with a measurable `L∞` coefficient matrix. -/
theorem IsWeakDivergenceSolution.existsUnique
    (hΩopen : IsOpen Ω) (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (f : L2) :
    ∃! u : H¹₀(Ω),
      IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_variableCoeff_weakSolution
    (n := n) (Ω := Ω) hn hΩbounded
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) ha f
  refine ⟨u, ?_, ?_⟩
  · exact (isWeakSolution_iff_isWeakDivergenceSolution
      (n := n) (Ω := Ω) hΩopen a f u).1 hu
  · intro v hv
    exact huniq v ((isWeakSolution_iff_isWeakDivergenceSolution
      (n := n) (Ω := Ω) hΩopen a f v).2 hv)

/-- Evans' usual almost-everywhere pointwise ellipticity hypothesis gives existence and
uniqueness for the homogeneous-Dirichlet divergence-form weak problem. -/
theorem IsWeakDivergenceSolution.existsUnique_of_ae
    (hΩopen : IsOpen Ω) (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (f : L2) :
    ∃! u : H¹₀(Ω),
      IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u :=
  IsWeakDivergenceSolution.existsUnique
    (n := n) (Ω := Ω) hΩopen hn hΩbounded a
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a ha)
    f

/-- The named weak solution of the measurable divergence-form problem under Evans'
almost-everywhere uniform ellipticity hypothesis. -/
noncomputable def weakDivergenceSolve
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (f : L2) : H¹₀(Ω) :=
  variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a ha)
    f

/-- The measurable-coefficient divergence-form weak solver as a bounded
linear map `L²(Ω) → H¹₀(Ω)`. -/
noncomputable def weakDivergenceSolveCLM
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha) :
    L2 →L[ℝ] H¹₀(Ω) :=
  variableCoeffSolveCLM (n := n) (Ω := Ω) hn hΩbounded
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a ha)

/-- Evaluating the measurable-coefficient solution operator at `f` gives the named weak
solution `weakDivergenceSolve f`. -/
@[simp]
theorem weakDivergenceSolveCLM_apply
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (f : L2) :
    weakDivergenceSolveCLM (n := n) (Ω := Ω)
        hn hΩbounded a ha f =
      weakDivergenceSolve (n := n) (Ω := Ω)
        hn hΩbounded a ha f :=
  rfl

/-- The named variable-coefficient solver satisfies the standard
distributional divergence-form identity. -/
theorem variableCoeffSolve_isWeakDivergenceSolution
    (hΩopen : IsOpen Ω) (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : IntegratedElliptic (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) alpha)
    (f : L2) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a f
      (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) ha f) :=
  (isWeakSolution_iff_isWeakDivergenceSolution
    (n := n) (Ω := Ω) hΩopen a f
    (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) ha f)).1
      (variableCoeffSolve_isWeakSolution
        (n := n) (Ω := Ω) hn hΩbounded
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) ha f)

/-- The named AE-elliptic measurable-coefficient solver satisfies Evans' distributional
divergence-form weak equation. -/
theorem weakDivergenceSolve_isWeakDivergenceSolution
    (hΩopen : IsOpen Ω) (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (f : L2) :
    IsWeakDivergenceSolution (n := n) (Ω := Ω) a f
      (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a ha f) := by
  simpa [weakDivergenceSolve] using
    variableCoeffSolve_isWeakDivergenceSolution
      (n := n) (Ω := Ω) hΩopen hn hΩbounded a
        (integratedElliptic_multiplication_of_ae
          (n := n) (Ω := Ω) a ha)
      f

/-- Evans-readable weak equation for the AE-elliptic measurable-coefficient solver,
tested against an arbitrary `H¹₀` function. -/
theorem weakDivergenceSolve_integral_equation
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (f : L2) (v : H¹₀(Ω)) :
    (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, a i j x *
          (derivCoordCLM (n := n) (Ω := Ω) j
            (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a ha f) :
              ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := Ω) i v : ℝ^n → ℝ) x
        ∂domainMeasure n Ω) =
      ∫ x, (f : ℝ^n → ℝ) x *
          (baseCoordCLM (n := n) (Ω := Ω) v : ℝ^n → ℝ) x
        ∂domainMeasure n Ω := by
  have hweak :
      IsWeakSolution
        (variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
        (loadFunctional (n := n) (Ω := Ω) f)
        (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a ha f) := by
    simpa [weakDivergenceSolve] using
      variableCoeffSolve_isWeakSolution
        (n := n) (Ω := Ω) hn hΩbounded
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
        (integratedElliptic_multiplication_of_ae
          (n := n) (Ω := Ω) a ha)
        f
  exact weakSolution_eq_integral
    (n := n) (Ω := Ω) a f
    (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a ha f)
    hweak v

/-- Evans-readable weak equation for the variable-coefficient solver. -/
theorem variableCoeffSolve_equation
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (f : L2) (v : H¹₀(Ω)) :
    (∑ i : Fin n, ∑ j : Fin n,
      ⟪A i j
          (derivCoordCLM (n := n) (Ω := Ω) j
            (variableCoeffSolve (n := n) (Ω := Ω)
              hn hΩbounded A hA f)),
        derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  have hweak := variableCoeffSolve_isWeakSolution
    (n := n) (Ω := Ω) hn hΩbounded A hA f
  change
    variableCoeffForm (n := n) (Ω := Ω) A
        (variableCoeffSolve (n := n) (Ω := Ω)
          hn hΩbounded A hA f) v =
      loadFunctional (n := n) (Ω := Ω) f v
  exact hweak v

/-- The weak equation against a compactly supported smooth test function. -/
theorem variableCoeffSolve_equation_testFunction
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (f : L2) (phi : TestFunctionOn n Ω) :
    (∑ i : Fin n, ∑ j : Fin n,
      ⟪A i j
          (derivCoordCLM (n := n) (Ω := Ω) j
            (variableCoeffSolve (n := n) (Ω := Ω)
              hn hΩbounded A hA f)),
        derivCoordCLM (n := n) (Ω := Ω) i
          (testFunctionToH10 (n := n) (Ω := Ω) phi)⟫_ℝ) =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω)
        (testFunctionToH10 (n := n) (Ω := Ω) phi)⟫_ℝ :=
  variableCoeffSolve_equation
    (n := n) (Ω := Ω) hn hΩbounded A hA f
      (testFunctionToH10 (n := n) (Ω := Ω) phi)

/-- Continuous dependence of the weak solution on the `L²` forcing datum. -/
theorem variableCoeffSolve_norm_le
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2,
      ‖variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hA f‖ ≤ C * ‖f‖ := by
  let S : L2 →L[ℝ] H¹₀(Ω) :=
    variableCoeffSolveCLM (n := n) (Ω := Ω)
      hn hΩbounded A hA
  let C := ‖S‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_nonneg_of_pos (norm_nonneg S) zero_lt_one
  have hSC : ‖S‖ ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right zero_le_one
  refine ⟨C, hC, ?_⟩
  intro f
  change ‖S f‖ ≤ C * ‖f‖
  exact (@ContinuousLinearMap.le_opNorm
      ℝ ℝ L2 H¹₀(Ω)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (RingHom.id ℝ) inferInstance
      S f).trans
    (mul_le_mul_of_nonneg_right hSC (norm_nonneg f))

/--
Continuous dependence of the uniformly elliptic variable-coefficient weak solution on
the `L²` forcing datum, with the coefficient operator held fixed.

This is the Evans/Lax–Milgram stability estimate for divergence-form equations:
changing the forcing from `f` to `g` changes the weak solution by at most a constant
times `‖f - g‖`.
-/
theorem variableCoeffSolve_sub_variableCoeffSolve_norm_le
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : L2,
      ‖variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hA f -
          variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hA g‖ ≤
        C * ‖f - g‖ := by
  let S : L2 →L[ℝ] H¹₀(Ω) :=
    variableCoeffSolveCLM (n := n) (Ω := Ω)
      hn hΩbounded A hA
  let C := ‖S‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_nonneg_of_pos (norm_nonneg S) zero_lt_one
  have hSC : ‖S‖ ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right zero_le_one
  refine ⟨C, hC, ?_⟩
  intro f g
  change ‖S f - S g‖ ≤ C * ‖f - g‖
  calc
    ‖S f - S g‖ = ‖S (f - g)‖ := by rw [map_sub]
    _ ≤ ‖S‖ * ‖f - g‖ := @ContinuousLinearMap.le_opNorm
      ℝ ℝ L2 H¹₀(Ω)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (RingHom.id ℝ) inferInstance
      S (f - g)
    _ ≤ C * ‖f - g‖ :=
      mul_le_mul_of_nonneg_right hSC (norm_nonneg (f - g))

/--
Continuous dependence for Evans' measurable divergence-form weak solution under the
almost-everywhere ellipticity hypothesis.
-/
theorem weakDivergenceSolve_sub_weakDivergenceSolve_norm_le
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : L2,
      ‖weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a ha f -
          weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a ha g‖ ≤
        C * ‖f - g‖ := by
  simpa [weakDivergenceSolve] using
    variableCoeffSolve_sub_variableCoeffSolve_norm_le
      (n := n) (Ω := Ω) hn hΩbounded
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae
        (n := n) (Ω := Ω) a ha)

/-- The quadratic energy associated with a symmetric variable-coefficient divergence-form
operator, `J_A(v) = 1/2 B_A(v,v) - ⟪f,v⟫`. -/
noncomputable def variableCoeffEnergy
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (f : L2) (v : H¹₀(Ω)) : ℝ :=
  @energy H¹₀(Ω) inferInstance
    inferInstance
    (variableCoeffForm (n := n) (Ω := Ω) A)
    (loadFunctional (n := n) (Ω := Ω) f)
    v

/-- Evans' Dirichlet principle for symmetric uniformly elliptic variable-coefficient
problems: every weak solution minimizes the associated quadratic energy on `H¹₀(Ω)`. -/
theorem variableCoeffEnergy_minimal_of_weakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hEll : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hSymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (f : L2) {u : H¹₀(Ω)}
    (hu :
      IsWeakSolution
        (variableCoeffForm (n := n) (Ω := Ω) A)
        (loadFunctional (n := n) (Ω := Ω) f)
        u)
    (v : H¹₀(Ω)) :
    variableCoeffEnergy (n := n) (Ω := Ω) A f u ≤
      variableCoeffEnergy (n := n) (Ω := Ω) A f v := by
  exact @IsWeakSolution.energy_le
    H¹₀(Ω)
    inferInstance
    inferInstance
    (variableCoeffForm (n := n) (Ω := Ω) A)
    (loadFunctional (n := n) (Ω := Ω) f)
    u
    (fun a b ↦ variableCoeffForm_symm (n := n) (Ω := Ω) hSymm a b)
    (fun w ↦
      @IsCoercive.self_nonneg
        H¹₀(Ω)
        inferInstance
        inferInstance
        (variableCoeffForm (n := n) (Ω := Ω) A)
        (variableCoeffForm_isCoercive
          (n := n) (Ω := Ω) hn hΩbounded A hEll)
        w)
    hu v

/-- The named Lax–Milgram solution of a symmetric uniformly elliptic variable-coefficient
problem minimizes the associated energy. -/
theorem variableCoeffSolve_minimizesEnergy
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hEll : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hSymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (f : L2) (v : H¹₀(Ω)) :
    variableCoeffEnergy (n := n) (Ω := Ω) A f
        (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f) ≤
      variableCoeffEnergy (n := n) (Ω := Ω) A f v :=
  variableCoeffEnergy_minimal_of_weakSolution
    (n := n) (Ω := Ω) hn hΩbounded A hEll hSymm f
    (variableCoeffSolve_isWeakSolution
      (n := n) (Ω := Ω) hn hΩbounded A hEll f)
    v

/-- Evans' Dirichlet principle for measurable symmetric uniformly elliptic
divergence-form equations: every weak divergence-form solution minimizes the
associated quadratic energy on `H¹₀(Ω)`. -/
theorem weakDivergenceEnergy_minimal_of_weakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hEll : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hSymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (f : L2) {u : H¹₀(Ω)}
    (hu : IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u)
    (v : H¹₀(Ω)) :
    variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f u ≤
      variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f v := by
  exact variableCoeffEnergy_minimal_of_weakSolution
    (n := n) (Ω := Ω) hn hΩbounded
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a hEll)
    (symmetricCoefficientOperator_multiplication_of_ae
      (n := n) (Ω := Ω) a hSymm)
    f
    ((isWeakSolution_iff_isWeakDivergenceSolution
      (n := n) (Ω := Ω) hu.isOpen a f u).2 hu)
    v

/-- Evans' Dirichlet principle for measurable symmetric uniformly elliptic
divergence-form equations.  The hypotheses are the usual almost-everywhere
coefficient assumptions; the conclusion is the energy-minimizing property of
the named weak solution. -/
theorem weakDivergenceSolve_minimizesEnergy
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hEll : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hSymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (f : L2) (v : H¹₀(Ω)) :
    variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f
        (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f) ≤
      variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f v := by
  simpa [weakDivergenceSolve] using
    variableCoeffSolve_minimizesEnergy
      (n := n) (Ω := Ω) hn hΩbounded
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae
        (n := n) (Ω := Ω) a hEll)
      (symmetricCoefficientOperator_multiplication_of_ae
        (n := n) (Ω := Ω) a hSymm)
      f v

/-- Equality in the symmetric variable-coefficient energy principle occurs exactly at the
Lax–Milgram weak solution. -/
theorem variableCoeffEnergy_eq_min_iff
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hEll : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hSymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (f : L2) {v : H¹₀(Ω)} :
    variableCoeffEnergy (n := n) (Ω := Ω) A f v =
        variableCoeffEnergy (n := n) (Ω := Ω) A f
          (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f) ↔
      v = variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f := by
  exact @IsWeakSolution.energy_eq_iff
    H¹₀(Ω)
    inferInstance
    inferInstance
    (variableCoeffForm (n := n) (Ω := Ω) A)
    (variableCoeffForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded A hEll)
    (loadFunctional (n := n) (Ω := Ω) f)
    (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f)
    v
    (fun a b ↦ variableCoeffForm_symm (n := n) (Ω := Ω) hSymm a b)
    (variableCoeffSolve_isWeakSolution
      (n := n) (Ω := Ω) hn hΩbounded A hEll f)

/-- Equality in the measurable-coefficient Dirichlet principle occurs exactly
at Evans' named weak solution. -/
theorem weakDivergenceEnergy_eq_min_iff
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hEll : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hSymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (f : L2) {v : H¹₀(Ω)} :
    variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f v =
        variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f
          (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f) ↔
      v = weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f := by
  simpa [weakDivergenceSolve] using
    variableCoeffEnergy_eq_min_iff
      (n := n) (Ω := Ω) hn hΩbounded
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae
        (n := n) (Ω := Ω) a hEll)
      (symmetricCoefficientOperator_multiplication_of_ae
        (n := n) (Ω := Ω) a hSymm)
      f

/-- Strict Evans Dirichlet principle for symmetric uniformly elliptic variable-coefficient
forms: every other `H¹₀` field has strictly larger energy. -/
theorem variableCoeffSolve_energy_lt_of_ne
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hEll : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hSymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (f : L2) {v : H¹₀(Ω)}
    (hv : v ≠ variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f) :
    variableCoeffEnergy (n := n) (Ω := Ω) A f
        (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f) <
      variableCoeffEnergy (n := n) (Ω := Ω) A f v := by
  exact @IsWeakSolution.energy_lt_of_ne
    H¹₀(Ω)
    inferInstance
    inferInstance
    (variableCoeffForm (n := n) (Ω := Ω) A)
    (variableCoeffForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded A hEll)
    (loadFunctional (n := n) (Ω := Ω) f)
    (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f)
    v
    (fun a b ↦ variableCoeffForm_symm (n := n) (Ω := Ω) hSymm a b)
    (variableCoeffSolve_isWeakSolution
      (n := n) (Ω := Ω) hn hΩbounded A hEll f)
    hv

/-- Strict measurable-coefficient Dirichlet principle: every field other than
Evans' named weak solution has strictly larger energy. -/
theorem weakDivergenceSolve_energy_lt_of_ne
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hEll : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hSymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (f : L2) {v : H¹₀(Ω)}
    (hv : v ≠ weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f) :
    variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f
        (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f) <
      variableCoeffEnergy (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f v := by
  simpa [weakDivergenceSolve] using
    variableCoeffSolve_energy_lt_of_ne
      (n := n) (Ω := Ω) hn hΩbounded
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae
        (n := n) (Ω := Ω) a hEll)
      (symmetricCoefficientOperator_multiplication_of_ae
        (n := n) (Ω := Ω) a hSymm)
      f hv

/-- Evans' Euler–Lagrange characterization for symmetric uniformly elliptic
variable-coefficient forms: global minimizers of the quadratic energy are exactly weak
solutions. -/
theorem variableCoeffEnergy_minimizer_iff_weakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hEll : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hSymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (f : L2) {u : H¹₀(Ω)} :
    (∀ v : H¹₀(Ω),
      variableCoeffEnergy (n := n) (Ω := Ω) A f u ≤
        variableCoeffEnergy (n := n) (Ω := Ω) A f v) ↔
      IsWeakSolution
        (variableCoeffForm (n := n) (Ω := Ω) A)
        (loadFunctional (n := n) (Ω := Ω) f)
        u := by
  exact @IsWeakSolution.energy_minimizer_iff
    H¹₀(Ω)
    inferInstance
    inferInstance
    inferInstance
    (variableCoeffForm (n := n) (Ω := Ω) A)
    (variableCoeffForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded A hEll)
    (loadFunctional (n := n) (Ω := Ω) f)
    u
    (fun a b ↦ variableCoeffForm_symm (n := n) (Ω := Ω) hSymm a b)

/-- Evans' Euler–Lagrange characterization for measurable symmetric
uniformly elliptic divergence-form equations: global minimizers of the
quadratic energy are exactly weak divergence-form solutions. -/
theorem IsWeakDivergenceSolution.energy_minimizer_iff
    (hΩopen : IsOpen Ω) (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hEll : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hSymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (f : L2) {u : H¹₀(Ω)} :
    (∀ v : H¹₀(Ω),
      variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f u ≤
        variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f v) ↔
      IsWeakDivergenceSolution (n := n) (Ω := Ω) a f u := by
  rw [← isWeakSolution_iff_isWeakDivergenceSolution
    (n := n) (Ω := Ω) hΩopen a f u]
  exact variableCoeffEnergy_minimizer_iff_weakSolution
    (n := n) (Ω := Ω) hn hΩbounded
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Ω) a hEll)
    (symmetricCoefficientOperator_multiplication_of_ae
      (n := n) (Ω := Ω) a hSymm)
    f

/-- The symmetric variable-coefficient Lax–Milgram solution is the unique
global minimizer of its quadratic energy. -/
theorem variableCoeffSolve_unique_energyMinimizer
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) {alpha : ℝ}
    (hEll : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hSymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A)
    (f : L2) {u : H¹₀(Ω)}
    (hu : ∀ v : H¹₀(Ω),
      variableCoeffEnergy (n := n) (Ω := Ω) A f u ≤
        variableCoeffEnergy (n := n) (Ω := Ω) A f v) :
    u = variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f := by
  have hEq :
      variableCoeffEnergy (n := n) (Ω := Ω) A f u =
        variableCoeffEnergy (n := n) (Ω := Ω) A f
          (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f) :=
    le_antisymm
      (hu (variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded A hEll f))
      (variableCoeffSolve_minimizesEnergy
        (n := n) (Ω := Ω) hn hΩbounded A hEll hSymm f u)
  exact (variableCoeffEnergy_eq_min_iff
    (n := n) (Ω := Ω) hn hΩbounded A hEll hSymm f).mp hEq

/-- The measurable symmetric divergence-form weak solution is the unique
global minimizer of the associated Evans energy. -/
theorem weakDivergenceSolve_unique_energyMinimizer
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (hEll : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hSymm : AESymmetricCoefficient (n := n) (Ω := Ω) a)
    (f : L2) {u : H¹₀(Ω)}
    (hu : ∀ v : H¹₀(Ω),
      variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f u ≤
        variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f v) :
    u = weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f := by
  have hEq :
      variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f u =
        variableCoeffEnergy (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) f
          (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f) :=
    le_antisymm
      (hu (weakDivergenceSolve (n := n) (Ω := Ω) hn hΩbounded a hEll f))
      (weakDivergenceSolve_minimizesEnergy
        (n := n) (Ω := Ω) hn hΩbounded a hEll hSymm f u)
  exact (weakDivergenceEnergy_eq_min_iff
    (n := n) (Ω := Ω) hn hΩbounded a hEll hSymm f).mp hEq

end LaxMilgram

end GraphSpace

end SobolevSpace
