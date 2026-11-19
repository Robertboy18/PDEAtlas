/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.Rayleigh
public import PDE.Elliptic.Variational.WeakSpectrum
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# A complete family of weak Dirichlet eigenfunctions

On a bounded open subset of `ℝⁿ`, with `n > 0`, a symmetric uniformly elliptic divergence
form has a complete orthonormal family of eigenfunctions in `L²(Ω)`. Each basis vector is
the base coordinate of an `H¹₀(Ω)` element, and its eigenvalue is positive.

The proof discharges the abstract variational spectral hypotheses using Poincaré coercivity,
Rellich compactness of `H¹₀(Ω) → L²(Ω)`, and density of the test functions in `L²(Ω)`.
Neither connectedness nor boundary regularity is required. For measurable `L∞` coefficients,
almost-everywhere symmetry and ellipticity give the distributional eigenvalue equation.

Completeness is bundled as a Mathlib `HilbertBasis`; the ordered enumeration by natural
numbers is `OrderedDirichletSpectrum`. On a nonempty domain, the first eigenvalue
is also characterized as the attained minimum of the Rayleigh quotient over nonzero
`H¹₀` functions.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- Symmetric uniformly elliptic operator coefficients on a bounded open domain give an
`L²` Hilbert basis whose `H¹₀` lifts solve the weak eigenvalue equation, with positive
eigenvalues. Compactness, density, and coercivity are derived from the domain and
coefficient hypotheses. -/
theorem exists_hilbertBasis_variableCoeff_eigenfunctions
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hsymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ L2) (lambda : ι → ℝ) (u : ι → H¹₀(Ω)),
      ∀ i, 0 < lambda i ∧ baseCoordCLM (n := n) (Ω := Ω) (u i) = b i ∧
        Weak.IsWeakEigenfunction (variableCoeffForm (n := n) (Ω := Ω) A)
          (massFormCLM (n := n) (Ω := Ω)) (lambda i) (u i) := by
  have hcoercive : IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) :=
    variableCoeffForm_isCoercive hn hΩbounded A hA
  obtain ⟨ι, b, lambda, u, h⟩ :=
    @PDE.Analysis.Variational.exists_hilbertBasis_weakEigenfunctions
      H¹₀(Ω) inferInstance inferInstance inferInstance
      L2 inferInstance inferInstance inferInstance
      (variableCoeffForm (n := n) (Ω := Ω) A) hcoercive (variableCoeffForm_symm hsymm)
      (baseCoordCLM (n := n) (Ω := Ω))
      (baseCoordCLM.isCompactOperator_of_bounded hΩopen.measurableSet hΩbounded)
      (baseCoordCLM_denseRange hΩopen)
  have hbase (i : ι) : baseCoordCLM (n := n) (Ω := Ω) (u i) = b i := (h i).2.1
  refine ⟨ι, b, lambda, u, fun i ↦ ⟨(h i).1, hbase i, ?_, ?_⟩⟩
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

/-- Measurable essentially bounded coefficients that are symmetric and uniformly elliptic
almost everywhere admit a complete `L²` family satisfying
`-div(a ∇uᵢ) = lambdaᵢ uᵢ` in the distributional sense, with zero Dirichlet boundary condition
encoded by membership in `H¹₀(Ω)`. No classical differentiability of the coefficients or
eigenfunctions is assumed. -/
theorem exists_hilbertBasis_weakDivergence_eigenfunctions
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ L2) (lambda : ι → ℝ) (u : ι → H¹₀(Ω)),
      ∀ i, 0 < lambda i ∧ baseCoordCLM (n := n) (Ω := Ω) (u i) = b i ∧ u i ≠ 0 ∧
        IsWeakDivergenceSolution (n := n) (Ω := Ω) a (lambda i • b i) (u i) := by
  obtain ⟨ι, b, lambda, u, h⟩ := exists_hilbertBasis_variableCoeff_eigenfunctions
    hn hΩopen hΩbounded (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    (integratedElliptic_multiplication_of_ae a ha)
    (symmetricCoefficientOperator_multiplication_of_ae a hsymm)
  refine ⟨ι, b, lambda, u, fun i ↦ ⟨(h i).1, (h i).2.1, (h i).2.2.1, ?_⟩⟩
  apply (isWeakSolution_iff_isWeakDivergenceSolution hΩopen a (lambda i • b i) (u i)).1
  intro v
  have hbase : baseCoordCLM (n := n) (Ω := Ω) (u i) = b i := (h i).2.1
  have hload : loadFunctional (n := n) (Ω := Ω) (lambda i • b i) v =
      lambda i * massFormCLM (n := n) (Ω := Ω) (u i) v := by
    rw [loadFunctional_apply, real_inner_smul_left, massFormCLM_apply, hbase]
  exact ((h i).2.2.2 v).trans hload.symm

/-- On a nonempty bounded open domain, the first Dirichlet eigenvalue is the attained
minimum of the energy divided by the squared `L²` norm over all nonzero `H¹₀` functions.
The minimizing eigenfunction has unit `L²` norm. Neither connectedness nor boundary
regularity is required. -/
theorem exists_first_variableCoeff_eigenfunction
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hΩne : Ω.Nonempty)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) {alpha : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hsymm : SymmetricCoefficientOperator (n := n) (Ω := Ω) A) :
    ∃ (lambda : ℝ) (u : H¹₀(Ω)), 0 < lambda ∧
      ‖baseCoordCLM (n := n) (Ω := Ω) u‖ = 1 ∧
      Weak.IsWeakEigenfunction (variableCoeffForm (n := n) (Ω := Ω) A)
        (massFormCLM (n := n) (Ω := Ω)) lambda u ∧
      IsLeast ((fun v : H¹₀(Ω) ↦ variableCoeffForm (n := n) (Ω := Ω) A v v /
        ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) '' {v | v ≠ 0}) lambda := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    ⟨by simpa [domainMeasure] using hΩbounded.measure_lt_top (μ := volume)⟩
  have : NeZero (domainMeasure n Ω) := by
    constructor
    intro hzero
    have hvol : (volume : Measure (ℝ^n)) Ω = 0 := by
      simpa [domainMeasure] using congrArg (fun μ : Measure (ℝ^n) ↦ μ Set.univ) hzero
    exact hΩopen.measure_ne_zero volume hΩne hvol
  have : Nontrivial L2 := by
    let hconst : MemLp (fun _ : ℝ^n ↦ (1 : ℝ)) 2 (domainMeasure n Ω) := memLp_const 1
    apply nontrivial_of_ne (hconst.toLp _) 0
    intro hzero
    have hae : (fun _ : ℝ^n ↦ (1 : ℝ)) =ᵐ[domainMeasure n Ω] 0 :=
      hconst.coeFn_toLp.symm.trans ((Lp.ext_iff.mp hzero).trans (Lp.coeFn_zero ℝ 2 _))
    obtain ⟨_, hx⟩ := hae.exists
    exact one_ne_zero hx
  have hcoercive : IsCoercive
      (variableCoeffForm (n := n) (Ω := Ω) A) :=
    variableCoeffForm_isCoercive hn hΩbounded A hA
  obtain ⟨lambda, u, hpos, _, hnorm, hweak, hleast⟩ :=
    @PDE.Analysis.Variational.exists_first_weakEigenfunction
      H¹₀(Ω) L2 inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (variableCoeffForm (n := n) (Ω := Ω) A) hcoercive (variableCoeffForm_symm hsymm)
      (baseCoordCLM (n := n) (Ω := Ω))
      (baseCoordCLM.isCompactOperator_of_bounded hΩopen.measurableSet hΩbounded)
      (baseCoordCLM_denseRange hΩopen)
  have hnonzero (v : H¹₀(Ω)) : baseCoordCLM (n := n) (Ω := Ω) v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro hv hzero
      exact hv (by rw [hzero, map_zero])
    · intro hv hzero
      exact hv ((baseCoordCLM_injective hΩopen)
        (hzero.trans (baseCoordCLM (n := n) (Ω := Ω)).map_zero.symm))
  refine ⟨lambda, u, hpos, hnorm, ⟨?_, ?_⟩, ?_⟩
  · exact (hnonzero u).mp (norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero))
  · intro v
    have hmass : massFormCLM (n := n) (Ω := Ω) u v =
        ⟪baseCoordCLM (n := n) (Ω := Ω) u, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
      rw [massFormCLM_apply]
    exact (hweak v).trans (congrArg (lambda * ·) hmass.symm)
  · constructor
    · obtain ⟨v, hv, hval⟩ := hleast.1
      exact ⟨v, (hnonzero v).mp hv, hval⟩
    · rintro r ⟨v, hv, rfl⟩
      exact hleast.2 ⟨v, (hnonzero v).mpr hv, rfl⟩

/-- For measurable symmetric uniformly elliptic `L∞` coefficients, the minimum
Dirichlet Rayleigh quotient is attained by a normalized distributional eigenfunction.
The statement concerns weak solutions and requires no pointwise regularity of the
coefficients or of the minimizing function. -/
theorem exists_first_weakDivergence_eigenfunction
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hΩne : Ω.Nonempty)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ (lambda : ℝ) (u : H¹₀(Ω)), 0 < lambda ∧
      ‖baseCoordCLM (n := n) (Ω := Ω) u‖ = 1 ∧ u ≠ 0 ∧
      IsWeakDivergenceSolution (n := n) (Ω := Ω) a
        (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u ∧
      IsLeast ((fun v : H¹₀(Ω) ↦
        variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) v v /
        ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) '' {v | v ≠ 0}) lambda := by
  obtain ⟨lambda, u, hpos, hnorm, heigen, hleast⟩ :=
    exists_first_variableCoeff_eigenfunction hn hΩopen hΩbounded hΩne
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae a ha)
      (symmetricCoefficientOperator_multiplication_of_ae a hsymm)
  refine ⟨lambda, u, hpos, hnorm, heigen.1, ?_, hleast⟩
  apply (isWeakSolution_iff_isWeakDivergenceSolution hΩopen a
    (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u).mp
  intro v
  have hload : loadFunctional (n := n) (Ω := Ω)
      (lambda • baseCoordCLM (n := n) (Ω := Ω) u) v =
      lambda * massFormCLM (n := n) (Ω := Ω) u v := by
    rw [loadFunctional_apply, real_inner_smul_left, massFormCLM_apply]
  exact (heigen.2 v).trans hload.symm

end SobolevSpace.GraphSpace
