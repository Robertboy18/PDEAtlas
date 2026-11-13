/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ShiftedDivergenceHigherEstimate

/-!
# Full-operator solvers at every Sobolev order

At every shift at or above the Gårding threshold `coerciveShift`, the full lower-order operator has
a bounded solution map `H^m → H^{m+2}` (`exists_shiftedFullHigherSolutionOperator`,
`shiftedFullHigherSolutionOperator`). The qualitative induction supplies the regularity input to
`higherSolutionOperator`; that construction proves boundedness by closed graph. Its values have zero
Dirichlet trace and solve the full weak equation, and every weak solution at such a shift is
represented by the solver (`exists_global_higherOrder_norm_le_of_coerciveShift_le`). This is the
estimate without `L²` term in the remark after Evans's §6.3.2, Theorem 5, for the unique weak
solution of §6.2.2, Theorem 3.

The threshold uses only the `L∞` norms of the coefficient base coordinates. Higher coefficient
derivatives enter the regularity hypothesis, not the weak coercivity threshold. No symmetry of the
principal matrix is required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.2, Theorem 3 (First Existence Theorem for weak
  solutions), p. 319; §6.3.2, Theorem 5 (Higher boundary regularity) and the remark after it,
  pp. 340-341.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Omega : Set (ℝ^n)}
  (m : ℕ)
  (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
  (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
    ContDiff ℝ (m + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
  (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
    ContDiff ℝ (m + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
  (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
  (a : ℝ^n → Fin n → Fin n → ℝ)
  (haRep : ∀ i j,
    ⇑(wkpBaseCoordinateCLM (A i j)) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
  (haContDiff : ∀ i j, ContDiff ℝ (m + 1) (fun x ↦ a x i j))
  (B : Fin n → W^{m,∞}(Omega))
  (C : W^{m,∞}(Omega))
  (alpha mu : ℝ) (halpha : 0 < alpha)
  (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
  (hmu : coerciveShift (n := n) alpha
    ‖fun i ↦ wkpBaseCoordinateCLM (B i)‖ ‖wkpBaseCoordinateCLM C‖ ≤ mu)

include hChart hChartSymm haRep haContDiff halpha hElliptic hmu in
/-- Existence of a bounded full-operator solution map whose values have the
correct `H¹₀` trace and satisfy the distributional equation. -/
theorem exists_shiftedFullHigherSolutionOperator :
    ∃ S : W^{m,2}(Omega) →L[ℝ] W^{m + 2,2}(Omega),
      ∀ F : W^{m,2}(Omega), ∃ u : H¹₀(Omega),
        lowerOrderCLM (n := n) (k := 1) (m := m + 2) (p := 2)
            (Ω := Omega) (by omega) (S F) = (u : H¹(Omega)) ∧
        IsWeakShiftedFullDivergenceSolution
          (fun i j ↦ wkpBaseCoordinateCLM (A i j))
          (fun i ↦ wkpBaseCoordinateCLM (B i)) (wkpBaseCoordinateCLM C)
          mu (wkpBaseCoordinateCLM F) 0 u := by
  let coeffA := fun i j ↦ wkpBaseCoordinateCLM (A i j)
  let coeffB := fun i ↦ wkpBaseCoordinateCLM (B i)
  let coeffC := wkpBaseCoordinateCLM C
  let A1 := fun i j ↦ lowerOrderCLM
    (n := n) (k := 1) (m := m + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
  have hA : IntegratedElliptic (multiplicationCoefficientOperator coeffA) alpha :=
    integratedElliptic_multiplication_of_ae coeffA
      (coefficientBase_aeUniformlyElliptic hOmega.toC1ExtensionAtlas.isOpen.measurableSet
        A1 a (fun i j ↦ by simpa [A1] using haRep i j) alpha halpha hElliptic)
  let S := fullDivergenceWeakSolveCLM coeffA coeffB coeffC hA
    (norm_nonneg _) (norm_nonneg _) (fun i ↦ norm_le_pi_norm coeffB i) le_rfl hmu
  have hweak (f : DerivLp n 2 Omega) :
      IsWeakShiftedFullDivergenceSolution coeffA coeffB coeffC mu f 0 (S f) :=
    fullDivergenceWeakSolveCLM_isWeakSolution coeffA coeffB coeffC hA
      (norm_nonneg _) (norm_nonneg _) (fun i ↦ norm_le_pi_norm coeffB i) le_rfl
      hmu hOmega.toC1ExtensionAtlas.isOpen f
  have hreg : HasHigherSolutionLift m S := by
    intro F
    obtain ⟨W, hW⟩ :=
      globalHigherRegularity.exists_of_weak_shifted_full_divergence_solution
        m hOmega hChart hChartSymm A a haRep haContDiff B C mu F
        (S (wkpBaseCoordinateCLM F)) (hweak _) alpha halpha hElliptic
    exact ⟨W, Lp.ext hW⟩
  refine ⟨higherSolutionOperator hOmega.toC1ExtensionAtlas.isOpen S hreg, ?_⟩
  intro F
  refine ⟨S (wkpBaseCoordinateCLM F), ?_, hweak _⟩
  apply wkpBaseCoordinateCLM_injective hOmega.toC1ExtensionAtlas.isOpen
  exact higherSolutionOperator_base hOmega.toC1ExtensionAtlas.isOpen S hreg F

/-- The bounded `H^m → H^{m+2}` solution operator for the full equation at a
coercive shift. Its values are uniquely determined by the weak equation. -/
def shiftedFullHigherSolutionOperator :
    W^{m,2}(Omega) →L[ℝ] W^{m + 2,2}(Omega) :=
  (exists_shiftedFullHigherSolutionOperator m hOmega hChart hChartSymm
    A a haRep haContDiff B C alpha mu halpha hElliptic hmu).choose

/-- The higher-order solver has zero Dirichlet trace and solves the full
shifted equation with the prescribed forcing. -/
theorem shiftedFullHigherSolutionOperator_spec (F : W^{m,2}(Omega)) :
    ∃ u : H¹₀(Omega),
      lowerOrderCLM (n := n) (k := 1) (m := m + 2) (p := 2) (Ω := Omega) (by omega)
          (shiftedFullHigherSolutionOperator m hOmega hChart hChartSymm
            A a haRep haContDiff B C alpha mu halpha hElliptic hmu F) =
        (u : H¹(Omega)) ∧
      IsWeakShiftedFullDivergenceSolution
        (fun i j ↦ wkpBaseCoordinateCLM (A i j))
        (fun i ↦ wkpBaseCoordinateCLM (B i)) (wkpBaseCoordinateCLM C)
        mu (wkpBaseCoordinateCLM F) 0 u :=
  (exists_shiftedFullHigherSolutionOperator m hOmega hChart hChartSymm
    A a haRep haContDiff B C alpha mu halpha hElliptic hmu).choose_spec F

/-- At a coercive shift the solution term disappears from the estimate.
Every weak solution is represented by the bounded higher-order solver. -/
theorem exists_global_higherOrder_norm_le_of_coerciveShift_le
    (F : W^{m,2}(Omega)) (u : H¹₀(Omega))
    (hu : IsWeakShiftedFullDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM (A i j))
      (fun i ↦ wkpBaseCoordinateCLM (B i)) (wkpBaseCoordinateCLM C)
      mu (wkpBaseCoordinateCLM F) 0 u) :
    ∃ W : W^{m + 2,2}(Omega),
      lowerOrderCLM (n := n) (k := 1) (m := m + 2) (p := 2) (Ω := Omega)
          (by omega) W = (u : H¹(Omega)) ∧
      ‖W‖ ≤ ‖shiftedFullHigherSolutionOperator m hOmega hChart hChartSymm
        A a haRep haContDiff B C alpha mu halpha hElliptic hmu‖ * ‖F‖ := by
  let S := shiftedFullHigherSolutionOperator m hOmega hChart hChartSymm
    A a haRep haContDiff B C alpha mu halpha hElliptic hmu
  obtain ⟨v, htrace, hv⟩ := shiftedFullHigherSolutionOperator_spec
    m hOmega hChart hChartSymm A a haRep haContDiff B C alpha mu halpha hElliptic hmu F
  let A1 := fun i j ↦ lowerOrderCLM
    (n := n) (k := 1) (m := m + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
  have ha := coefficientBase_aeUniformlyElliptic
    hOmega.toC1ExtensionAtlas.isOpen.measurableSet A1 a
    (fun i j ↦ by simpa [A1] using haRep i j) alpha halpha hElliptic
  have hunique := existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic_of_coerciveShift_le
    hOmega.toC1ExtensionAtlas.isOpen
    (fun i j ↦ wkpBaseCoordinateCLM (A i j))
    (fun i ↦ wkpBaseCoordinateCLM (B i)) (wkpBaseCoordinateCLM C) ha
    (norm_nonneg _) (norm_nonneg _)
    (fun i ↦ norm_le_pi_norm (fun j ↦ wkpBaseCoordinateCLM (B j)) i) le_rfl
    hmu (wkpBaseCoordinateCLM F) 0
  have hvu : v = u := hunique.unique hv hu
  exact ⟨S F, hvu ▸ htrace, S.le_opNorm F⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
