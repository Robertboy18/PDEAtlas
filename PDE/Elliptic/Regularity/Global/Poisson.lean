/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletDomain
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian
import PDE.Analysis.MeasureTheory.Lp.ConstantMultiplier

/-!
# Global Poisson regularity from boundary geometry

Identity principal coefficients reduce the full divergence operator to the
Dirichlet form and its strong load to minus the weak Laplacian. Their classical
closure data are constructed from constants, including vanishing coefficient derivatives.
The global `H²` theorem then applies on a bounded open domain with a `C²` graph boundary.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev Laplacian

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Classical identity coefficients induce the identity multiplier on every diagonal. -/
theorem multiplicationCoefficientOperator_identity_toLp
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    multiplicationCoefficientOperator
        (fun i j : Fin n ↦
          (ContDiffUpToBoundary.const (k := 1) (scalarIdentityMatrix 1 i j)).toLp
            hopen hbounded ∞) =
      identityCoefficientOperator (n := n) (Ω := Ω) := by
  apply multiplicationCoefficientOperator_eq_identity_of_ae
  intro i j
  simpa only [scalarIdentityMatrix, mul_one] using
    (ContDiffUpToBoundary.const (k := 1) (scalarIdentityMatrix 1 i j)).toLp_coeFn
      hopen hbounded ∞

/-- The constant principal coefficients have zero first weak derivatives. -/
theorem constant_coefficient_deriv_eq_zero
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (c : ℝ) (i : Fin n) :
    ((ContDiffUpToBoundary.const (k := 1) c).toWkpSpaceOn hopen hbounded ∞ :
      WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i) = 0 := by
  apply Lp.ext
  filter_upwards
    [(ContDiffUpToBoundary.const (k := 1) c).toWkpSpaceOn_apply_ae
      hopen hbounded ∞ (singleDerivIndex n i), Lp.coeFn_zero (E := ℝ) (p := ∞)
        (μ := domainMeasure n Ω)] with x hx hz
  simpa only [singleDerivIndex_toList, iteratedPartialDeriv, PDE.partialDeriv_const, hz,
    Pi.zero_apply] using hx

/-- The full strong load of identity principal coefficients and zero lower terms is `-Δ`. -/
theorem fullStrongLoad_identity_eq_neg_laplacian
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (U : W^{2,2}(Ω)) :
    fullStrongLoad
        (fun i j : Fin n ↦
          (ContDiffUpToBoundary.const (k := 1) (scalarIdentityMatrix 1 i j)).toWkpSpaceOn
            hopen hbounded ∞) 0 0 U =
      -(Δ U) := by
  classical
  have hbase (i j : Fin n) (f : DerivLp n 2 Ω) :
      (((ContDiffUpToBoundary.const (k := 1) (scalarIdentityMatrix 1 i j)).toWkpSpaceOn
        hopen hbounded ∞ : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)) • f =
      (scalarIdentityMatrix 1 i j) • f := by
    apply Lp.lpSMul_eq_const_smul
    exact (ContDiffUpToBoundary.const _).toWkpSpaceOn_base_ae hopen hbounded ∞
  simp only [fullStrongLoad, strongLoad, constant_coefficient_deriv_eq_zero hopen hbounded,
    hbase, Pi.zero_apply, Lp.zero_smul, add_zero, Finset.sum_const_zero,
    laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [scalarIdentityMatrix, ite_smul]

/-- Identity principal coefficients and zero lower terms give exactly the Dirichlet form. -/
theorem fullDivergenceForm_identity_eq_dirichletForm
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (u : H¹₀(Ω)) :
    fullDivergenceForm
        (multiplicationCoefficientOperator (fun i j : Fin n ↦
          (ContDiffUpToBoundary.const (k := 1) (scalarIdentityMatrix 1 i j)).toLp
            hopen hbounded ∞))
        (multiplicationFirstOrderOperator 0) (multiplicationZeroOrderOperator 0) u =
      dirichletForm u := by
  classical
  rw [multiplicationCoefficientOperator_identity_toLp]
  ext v
  simp only [fullDivergenceForm, add_apply, variableCoeffForm_identity,
    lowerOrderForm_apply, multiplicationFirstOrderOperator_apply,
    multiplicationZeroOrderOperator_apply, Pi.zero_apply, Lp.zero_smul, inner_zero_left,
    Finset.sum_const_zero, add_zero]

/-- An `L²` Poisson load on a bounded `C²` domain is equivalent to an `H²`
representative of the given zero-boundary field with exactly that weak Laplacian. -/
theorem dirichletForm_eq_load_iff_h2 [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (u : H¹₀(Ω)) (f : DerivLp n 2 Ω) :
    dirichletForm u = loadFunctional f ↔
      ∃ U : W^{2,2}(Ω), wkpBaseCoordinateCLM U = baseCoordCLM u ∧
        -(Δ U) = f := by
  have hell (x : ℝ^n) (_hx : x ∈ Ω) :
      MatrixEllipticLowerBound (scalarIdentityMatrix (n := n) 1) 1 := by
    intro ξ
    rw [principalEnergy_scalarIdentityMatrix]
  have hpivot : (h10L2GelfandTriple hopen).pivotToDual f = loadFunctional f := by
    ext v
    rfl
  simpa only [fullDivergenceForm_identity_eq_dirichletForm,
    fullStrongLoad_identity_eq_neg_laplacian, hpivot] using
    fullDivergenceForm_eq_pivotToDual_iff_h2 hopen hbounded hgraph
      (fun _ ↦ scalarIdentityMatrix 1)
      (fun i j ↦ ContDiffUpToBoundary.const (scalarIdentityMatrix 1 i j))
      0 0 1 zero_lt_one hell u f

end SobolevSpace.GraphSpace.BoundaryRegularity
