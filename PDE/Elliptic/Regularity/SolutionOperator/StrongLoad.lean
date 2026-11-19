/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# Boundedness of the strong divergence expression on `H²`

The weak product rule identifies the strong load `strongLoad` with the
divergence operator. Here its finite coordinate formula is written as a
bounded linear map, so the norm of an initial elliptic load is controlled
by the `H²` norm of the datum.

The strong operator depends continuously on its `W¹,∞` coefficients. On
the Dirichlet domain it is inverse to the constructed elliptic solution
operator; these identities also allow the coefficients to vary with time.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The principal divergence expression as a bounded map from `H²` to `L²`. -/
def strongLoadCLM (A : Fin n → Fin n → W^{1,∞}(Ω)) :
    W^{2,2}(Ω) →L[ℝ] DerivLp n 2 Ω :=
  -∑ i, ∑ j, (
    (mulLpLeft ((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))).comp
        (wkpCoordinateCLM (pairDerivIndex n j i)) +
      (mulLpLeft ((A i j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i))).comp
        (wkpCoordinateCLM (firstDerivIndex n 2 (by norm_num) j)))

/-- The bounded operator is exactly the strong load formula. -/
theorem strongLoadCLM_apply (A : Fin n → Fin n → W^{1,∞}(Ω))
    (G : W^{2,2}(Ω)) :
    strongLoadCLM A G = strongLoad A G := by
  simp only [strongLoadCLM, strongLoad, neg_apply, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, wkpCoordinateCLM_apply, mulLpLeft_apply]

/-- The elliptic load of an `H²` initial datum is bounded by a constant
depending only on the principal coefficients. -/
theorem norm_strongLoad_le (A : Fin n → Fin n → W^{1,∞}(Ω))
    (G : W^{2,2}(Ω)) :
    ‖strongLoad A G‖ ≤ ‖strongLoadCLM A‖ * ‖G‖ := by
  rw [← strongLoadCLM_apply]
  exact (strongLoadCLM A).le_opNorm G

/-- The classical divergence load of an `H²` datum is exactly its variational
principal operator in the energy dual. The identity holds against every
`H¹₀` test by density. -/
theorem pivotToDual_strongLoad (hopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (G : W^{2,2}(Ω)) (g : H¹₀(Ω))
    (hG : lowerOrderCLM (k := 1) (m := 2) (by omega) G = (g : H¹(Ω))) :
    (h10L2GelfandTriple hopen).pivotToDual (strongLoad A G) =
      variableCoeffForm (multiplicationCoefficientOperator (coefficientBase A)) g := by
  have hweak := (isWeakSolution_iff_isWeakDivergenceSolution hopen
    (coefficientBase A) (strongLoad A G) g).2
      (strongLoad_isWeakDivergenceSolution hopen A G g hG)
  ext v
  exact (hweak v).symm

private def multiplierCLM :
    DerivLp n ∞ Ω →L[ℝ] (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) :=
  LinearMap.mkContinuous
    { toFun := mulLpLeft
      map_add' := by
        intro a b
        apply ContinuousLinearMap.ext
        intro u
        change (a + b) • u = a • u + b • u
        exact Lp.smul_add a b u
      map_smul' := by
        intro c a
        apply ContinuousLinearMap.ext
        intro u
        change (c • a) • u = c • (a • u)
        exact Lp.smul_assoc c a u }
    1 (fun a ↦ by simpa using norm_mulLpLeft_le (p := 2) a)

/-- The strong divergence operator depends continuously on its spatial `W¹,∞`
coefficient matrix, in the operator norm from `H²` to `L²`. -/
theorem continuous_strongLoadCLM :
    Continuous (strongLoadCLM (n := n) (Ω := Ω)) := by
  unfold strongLoadCLM
  apply Continuous.neg
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  apply Continuous.add
  · exact ((multiplierCLM.continuous.comp
      ((wkpCoordinateCLM (baseIndex n 1)).continuous.comp
        ((continuous_apply j).comp (continuous_apply i)))).clm_comp continuous_const)
  · exact ((multiplierCLM.continuous.comp
      ((wkpCoordinateCLM (singleDerivIndex n i)).continuous.comp
        ((continuous_apply j).comp (continuous_apply i)))).clm_comp continuous_const)

section Inverse

variable [Fact (0 < n)]
variable (hΩ : C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)

/-- Applying the strong divergence operator to the constructed elliptic inverse
recovers its `L²` load. Density of the energy space identifies the load. -/
theorem strongLoadCLM_globalH2SolveCLM (f : DerivLp n 2 Ω) :
    strongLoadCLM A (globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic f) = f := by
  let hopen := hΩ.toC1ExtensionAtlas.isOpen
  apply (h10L2GelfandTriple hopen).pivotToDual_injective
  rw [strongLoadCLM_apply, pivotToDual_strongLoad hopen A _ _
    (globalH2SolveCLM_orderOne hΩ A a haRep haC1 alpha halpha hElliptic f)]
  ext v
  exact (isWeakSolution_iff_isWeakDivergenceSolution hopen (coefficientBase A) f _).2
    (globalH2WeakSolveCLM_isWeakDivergenceSolution hΩ A a haRep alpha halpha hElliptic f) v

/-- The elliptic inverse recovers every `H²` function whose first-order restriction
has zero boundary values. This common domain is what permits time-dependent inversion. -/
theorem globalH2SolveCLM_strongLoadCLM
    (G : W^{2,2}(Ω)) (g : H¹₀(Ω))
    (hG : lowerOrderCLM (k := 1) (m := 2) (by omega) G = h10SubtypeL g) :
    globalH2SolveCLM hΩ A a haRep haC1 alpha halpha hElliptic
      (strongLoadCLM A G) = G := by
  apply lowerOrderCLM_injective (by omega : 1 ≤ 2) hΩ.toC1ExtensionAtlas.isOpen
  rw [globalH2SolveCLM_orderOne, hG]
  congr 1
  apply Eq.symm
  apply eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution
  rw [strongLoadCLM_apply]
  exact strongLoad_isWeakDivergenceSolution hΩ.toC1ExtensionAtlas.isOpen A G g hG

end Inverse

end SobolevSpace.GraphSpace.BoundaryRegularity
