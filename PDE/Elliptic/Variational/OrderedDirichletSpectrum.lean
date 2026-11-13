/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.OrderedSpectrum
public import PDE.Elliptic.Variational.DirichletSpectrum
import PDE.Analysis.MeasureTheory.Lp.L2Infinite
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# Ordered Dirichlet eigenvalues and minmax

On a nonempty bounded open subset of a positive-dimensional Euclidean space,
a symmetric uniformly elliptic form admits a complete sequence of weak Dirichlet
eigenfunctions. Their positive eigenvalues are nondecreasing, count multiplicities,
and tend to infinity. The eigenvalue at index `k` is the least uniform Rayleigh
bound on a subspace of `H¹₀` of dimension `k + 1`.

The complete sequence of eigenfunctions and the ordered eigenvalues tending to infinity are Evans's
§6.5.1, Theorem 1(ii)-(iii). Evans assumes `aⁱʲ ∈ C^∞(Ū)` in (2), the symmetry (3), and a
connected domain; we assume bounded measurable symmetric coefficients. The minmax characterization
is not part of Evans's Theorem 1; §6.6, Problem 13 (Courant minimax principle) states the dual
max-min form.

Infinite dimension of `L²` follows from the nonzero locally finite restricted volume
measure and its null singletons. Poincaré coercivity, Rellich compactness, and density
then discharge the hypotheses of the abstract ordered variational spectrum.
The coefficient version gives distributional eigenfunctions for measurable symmetric
uniformly elliptic `L∞` coefficients. No boundary smoothness or connectedness is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.1, (2)-(3), p. 354, and Theorem 1 (Eigenvalues of
  symmetric elliptic operators) and its proof, pp. 355-356; §6.6, Problem 13 (Courant minimax
  principle), p. 368.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- On a nonempty bounded open subset of a positive-dimensional Euclidean space,
symmetric uniformly elliptic operator coefficients have a complete ordered Dirichlet
eigenfamily. Eigenvalues are positive, counted with multiplicity, and tend to infinity.
The eigenvalue at index `k` is the least uniform Rayleigh bound on a
`(k + 1)`-dimensional subspace of `H¹₀`. No boundary regularity is required. -/
theorem exists_ordered_hilbertBasis_variableCoeff_eigenfunctions
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hΩne : Ω.Nonempty)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hsymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A) :
    ∃ (b : HilbertBasis ℕ ℝ L2) (lambda : ℕ → ℝ) (u : ℕ → H¹₀(Ω)),
      Monotone lambda ∧ Tendsto lambda atTop atTop ∧
      (∀ i, 0 < lambda i ∧ baseCoordCLM (n := n) (Ω := Ω) (u i) = b i ∧
        Weak.IsWeakEigenfunction (variableCoeffForm (n := n) (Ω := Ω) A)
          (massFormCLM (n := n) (Ω := Ω)) (lambda i) (u i)) ∧
      ∀ k, IsLeast {r : ℝ | ∃ W : Submodule ℝ H¹₀(Ω),
        Module.finrank ℝ W = k + 1 ∧ ∀ v ∈ W,
          variableCoeffForm (n := n) (Ω := Ω) A v v ≤
            r * ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2} (lambda k) := by
  have : Nontrivial (ℝ^n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  have hμ : domainMeasure n Ω ≠ 0 := by
    intro hzero
    have hvol : (volume : Measure (ℝ^n)) Ω = 0 := by
      simpa [domainMeasure] using congrArg (fun μ : Measure (ℝ^n) ↦ μ Set.univ) hzero
    exact hΩopen.measure_ne_zero volume hΩne hvol
  have hL2 : ¬FiniteDimensional ℝ L2 :=
    Lp.not_finiteDimensional_of_nullSingleton (𝕜 := ℝ) (domainMeasure n Ω) hμ
  have hcoercive : IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) :=
    variableCoeffForm_isCoercive hn hΩbounded A hA
  obtain ⟨b, lambda, u, hmono, htendsto, h, hmin⟩ :=
    @PDE.Analysis.Variational.exists_ordered_hilbertBasis_weakEigenfunctions
      H¹₀(Ω) L2 inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (variableCoeffForm (n := n) (Ω := Ω) A) hcoercive (variableCoeffForm_symm hsymm)
      (baseCoordCLM (n := n) (Ω := Ω))
      (baseCoordCLM.isCompactOperator_of_bounded hΩopen.measurableSet hΩbounded)
      (baseCoordCLM_denseRange hΩopen) hL2
  have hbase (i : ℕ) : baseCoordCLM (n := n) (Ω := Ω) (u i) = b i := (h i).2.1
  refine ⟨b, lambda, u, hmono, htendsto, ?_, hmin⟩
  intro i
  refine ⟨(h i).1, hbase i, ?_, ?_⟩
  · intro hzero
    apply b.orthonormal.ne_zero i
    calc
      b i = baseCoordCLM (n := n) (Ω := Ω) (u i) := (hbase i).symm
      _ = baseCoordCLM (n := n) (Ω := Ω) 0 :=
        congrArg (baseCoordCLM (n := n) (Ω := Ω)) hzero
      _ = 0 := (baseCoordCLM (n := n) (Ω := Ω)).map_zero
  · intro v
    have hmass : massFormCLM (n := n) (Ω := Ω) (u i) v =
        ⟪b i, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
      rw [massFormCLM_apply, hbase i]
    exact ((h i).2.2 v).trans (congrArg (lambda i * ·) hmass.symm)

/-- Measurable symmetric uniformly elliptic `L∞` coefficients on a nonempty bounded
open domain admit an `L²` Hilbert basis of weak Dirichlet eigenfunctions. Their
eigenvalues, counted with multiplicity, increase to infinity and obey the minmax
principle on `H¹₀`. Neither classical eigenfunction regularity nor boundary
smoothness is assumed. -/
theorem exists_ordered_hilbertBasis_weakDivergence_eigenfunctions
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hΩne : Ω.Nonempty)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ (b : HilbertBasis ℕ ℝ L2) (lambda : ℕ → ℝ) (u : ℕ → H¹₀(Ω)),
      Monotone lambda ∧ Tendsto lambda atTop atTop ∧
      (∀ i, 0 < lambda i ∧ baseCoordCLM (n := n) (Ω := Ω) (u i) = b i ∧
        u i ≠ 0 ∧ IsWeakDivergenceSolution (n := n) (Ω := Ω) a (lambda i • b i) (u i)) ∧
      ∀ k, IsLeast {r : ℝ | ∃ W : Submodule ℝ H¹₀(Ω),
        Module.finrank ℝ W = k + 1 ∧ ∀ v ∈ W,
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) v v ≤
              r * ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2} (lambda k) := by
  obtain ⟨b, lambda, u, hmono, htendsto, h, hmin⟩ :=
    exists_ordered_hilbertBasis_variableCoeff_eigenfunctions hn hΩopen hΩbounded hΩne
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae a ha)
      (symmetricCoefficientOperator_multiplication_of_ae a hsymm)
  refine ⟨b, lambda, u, hmono, htendsto, ?_, hmin⟩
  intro i
  refine ⟨(h i).1, (h i).2.1, (h i).2.2.1, ?_⟩
  apply (isWeakSolution_iff_isWeakDivergenceSolution hΩopen a (lambda i • b i) (u i)).mp
  intro v
  have hbase : baseCoordCLM (n := n) (Ω := Ω) (u i) = b i := (h i).2.1
  have hload : loadFunctional (n := n) (Ω := Ω) (lambda i • b i) v =
      lambda i * massFormCLM (n := n) (Ω := Ω) (u i) v := by
    rw [loadFunctional_apply, real_inner_smul_left, massFormCLM_apply, hbase]
  exact ((h i).2.2.2 v).trans hload.symm

end SobolevSpace.GraphSpace
