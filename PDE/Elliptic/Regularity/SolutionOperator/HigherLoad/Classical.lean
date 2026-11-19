/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Sobolev
public import PDE.Elliptic.Variational.PivotOperator
public import PDE.FDeriv.Calculus

/-!
# Full spatial operators from smooth classical coefficients

The data are the three coefficient functions and their classical
regularity up to the boundary at every finite order. They construct the full
variational form and the coherent higher Sobolev load maps. Symmetry and
ellipticity are separate hypotheses; no coercivity of the full form is required.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

/-- Smooth coefficients of the full autonomous divergence operator. -/
structure SmoothFullCoefficients (n : ℕ) (Ω : Set (ℝ^n)) where
  /-- The principal matrix, with the divergence index first. -/
  principal : ℝ^n → Fin n → Fin n → ℝ
  /-- The drift coefficients. -/
  drift : Fin n → ℝ^n → ℝ
  /-- The zeroth-order coefficient. -/
  potential : ℝ^n → ℝ
  /-- All principal derivatives extend continuously to the boundary. -/
  principal_smooth : ∀ r i j, ContDiffUpToBoundary r (fun x ↦ principal x i j) Ω
  /-- All drift derivatives extend continuously to the boundary. -/
  drift_smooth : ∀ r i, ContDiffUpToBoundary r (drift i) Ω
  /-- All potential derivatives extend continuously to the boundary. -/
  potential_smooth : ∀ r, ContDiffUpToBoundary r potential Ω

namespace SmoothFullCoefficients

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full variational operator built from the classical coefficient values. -/
def form (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
  fullDivergenceForm
    (multiplicationCoefficientOperator
      (fun i j ↦ (P.principal_smooth 0 i j).toLp hopen hbounded ∞))
    (fun i ↦ mulLpLeft ((P.drift_smooth 0 i).toLp hopen hbounded ∞))
    (mulLpLeft ((P.potential_smooth 0).toLp hopen hbounded ∞))

/-- The full higher spatial operator, constructed at every order from the same
classical coefficients. -/
def load (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (r : ℕ) :
    W^{r + 2,2}(Ω) →L[ℝ] W^{r,2}(Ω) :=
  higherFullLoadCLM r hopen
    (fun i j ↦ (P.principal_smooth (r + 1) i j).toWkpSpaceOn hopen hbounded ∞)
    (fun i ↦ (P.drift_smooth (r + 1) i).toWkpSpaceOn hopen hbounded ∞)
    ((P.potential_smooth (r + 1)).toWkpSpaceOn hopen hbounded ∞)

/-- The full signed classical divergence expression. The first principal index is
the divergence direction, so all coefficient derivatives remain in the expression. -/
def classicalLoad (P : SmoothFullCoefficients n Ω) (z : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  -(∑ i, ∑ j, (∂[i] (fun y ↦ P.principal y i j * (∂[j] z) y)) x) +
    (∑ i, P.drift i x * (∂[i] z) x) + P.potential x * z x

/-- The classical load depends only on the function on the open domain.
No choice of its values outside the domain affects the operator there. -/
theorem classicalLoad_congr (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) {z w : ℝ^n → ℝ} (h : EqOn z w Ω) :
    EqOn (P.classicalLoad z) (P.classicalLoad w) Ω := by
  have hd (j : Fin n) : EqOn (∂[j] z) (∂[j] w) Ω := by
    intro x hx
    exact PDE.partialDeriv_congr_nhds j (h.eventuallyEq_of_mem (hopen.mem_nhds hx))
  intro x hx
  have hflux (i j : Fin n) :
      (∂[i] (fun y ↦ P.principal y i j * (∂[j] z) y)) x =
        (∂[i] (fun y ↦ P.principal y i j * (∂[j] w) y)) x := by
    apply PDE.partialDeriv_congr_nhds
    filter_upwards [(hd j).eventuallyEq_of_mem (hopen.mem_nhds hx)] with y hy
    rw [hy]
  simp only [classicalLoad, hflux, hd _ hx, h hx]

/-- Applying the full classical operator loses two spatial derivatives.
No boundary condition, ellipticity, or sign restriction is needed. -/
theorem classicalLoad_regular (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {r : ℕ} {z : ℝ^n → ℝ} (hz : ContDiffUpToBoundary (r + 2) z Ω) :
    ContDiffUpToBoundary r (P.classicalLoad z) Ω := by
  have hflux (i j : Fin n) :
      ContDiffUpToBoundary r
        (∂[i] (fun y ↦ P.principal y i j * (∂[j] z) y)) Ω :=
    ((P.principal_smooth (r + 1) i j).mul
      (hz.partialDeriv_of_succ hopen j) hopen hbounded).partialDeriv_of_succ hopen i
  have hprincipal := ContDiffUpToBoundary.sum Finset.univ
    (fun i _ ↦ ContDiffUpToBoundary.sum Finset.univ (fun j _ ↦ hflux i j)
      hopen) hopen
  have hdrift := ContDiffUpToBoundary.sum Finset.univ
    (fun i _ ↦ (P.drift_smooth r i).mul
      ((hz.partialDeriv_of_succ hopen i).of_le (Nat.le_succ r)) hopen hbounded)
    hopen
  exact ((hprincipal.neg hopen).add hdrift hopen).add
    ((P.potential_smooth r).mul (hz.of_le (by omega)) hopen hbounded) hopen

/-- The coherent Sobolev operator is the full classical load on classical
input. The identity is in `H^r`, so every derivative coordinate agrees as well. -/
theorem load_toWkpSpaceOn (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {r : ℕ} {z : ℝ^n → ℝ} (hz : ContDiffUpToBoundary (r + 2) z Ω) :
    P.load hopen hbounded r (hz.toWkpSpaceOn hopen hbounded 2) =
      (P.classicalLoad_regular hopen hbounded hz).toWkpSpaceOn hopen hbounded 2 := by
  simp only [load, higherFullLoadCLM, neg_apply, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum,
    ContDiffUpToBoundary.derivativeWord_toWkpSpaceOn,
    ContDiffUpToBoundary.wkTopMultiplier_toWkpSpaceOn,
    ContDiffUpToBoundary.lowerOrder_toWkpSpaceOn]
  simp only [← ContDiffUpToBoundary.toWkpSpaceOn_sum,
    ← ContDiffUpToBoundary.toWkpSpaceOn_neg, ← ContDiffUpToBoundary.toWkpSpaceOn_add]
  congr 1
  funext x
  exact (add_assoc _ _ _).symm

private theorem classical_base_eq {k l : ℕ} {f : ℝ^n → ℝ}
    (hf : ContDiffUpToBoundary k f Ω) (hg : ContDiffUpToBoundary l f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    wkpBaseCoordinateCLM (hf.toWkpSpaceOn hopen hbounded ∞) =
      hg.toLp hopen hbounded ∞ :=
  Lp.ext ((hf.toWkpSpaceOn_base_ae hopen hbounded ∞).trans
    (hg.toLp_coeFn hopen hbounded ∞).symm)

/-- Restriction preserves the spatial operator built from coefficients. -/
theorem lowerOrder_load (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {r s : ℕ} (hsr : s ≤ r) (U : W^{r + 2,2}(Ω)) :
    lowerOrderCLM hsr (P.load hopen hbounded r U) =
      P.load hopen hbounded s (lowerOrderCLM (Nat.add_le_add_right hsr 2) U) := by
  unfold load
  rw [lowerOrderCLM_higherFullLoadCLM]
  congr 1

/-- Every higher load represents the same full weak form. The only boundary
condition is the zero trace of the input represented by `u`. -/
theorem form_eq_load (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (r : ℕ)
    (U : W^{r + 2,2}(Ω)) (u v : H¹₀(Ω))
    (hbase : wkpBaseCoordinateCLM U = baseCoordCLM u) :
    P.form hopen hbounded u v =
      ⟪wkpBaseCoordinateCLM (P.load hopen hbounded r U), baseCoordCLM v⟫_ℝ := by
  have h := fullDivergenceForm_eq_higherFullLoad r hopen
    (fun i j ↦ (P.principal_smooth (r + 1) i j).toWkpSpaceOn hopen hbounded ∞)
    (fun i ↦ (P.drift_smooth (r + 1) i).toWkpSpaceOn hopen hbounded ∞)
    ((P.potential_smooth (r + 1)).toWkpSpaceOn hopen hbounded ∞) U u hbase v
  have hA : (fun i j ↦ wkpBaseCoordinateCLM
      ((P.principal_smooth (r + 1) i j).toWkpSpaceOn hopen hbounded ∞)) =
        fun i j ↦ (P.principal_smooth 0 i j).toLp hopen hbounded ∞ := by
    funext i j
    exact classical_base_eq _ _ hopen hbounded
  have hb : (fun i ↦ wkpBaseCoordinateCLM
      ((P.drift_smooth (r + 1) i).toWkpSpaceOn hopen hbounded ∞)) =
        fun i ↦ (P.drift_smooth 0 i).toLp hopen hbounded ∞ := by
    funext i
    exact classical_base_eq _ _ hopen hbounded
  rw [hA, hb, classical_base_eq _ (P.potential_smooth 0) hopen hbounded] at h
  exact h

/-- Uniform ellipticity gives a coercive principal part and a bounded
pivot-valued perturbation. The drift and potential have arbitrary signs. -/
theorem exists_coercive_decomposition [Fact (0 < n)] (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) :
    ∃ (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
      (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω) (C : ℝ), 0 < C ∧
      P.form hopen hbounded = A + (h10L2GelfandTriple hopen).pivotToDual.comp R ∧
      ∀ u, C * ‖u‖ ^ 2 ≤ A u u := by
  let coeff := fun i j ↦ (P.principal_smooth 0 i j).toLp hopen hbounded ∞
  let principalSobolev := fun i j ↦
    (P.principal_smooth 1 i j).toWkpSpaceOn hopen hbounded ∞
  have hcoeff : coefficientBase principalSobolev = coeff := by
    funext i j
    exact classical_base_eq (P.principal_smooth 1 i j)
      (P.principal_smooth 0 i j) hopen hbounded
  have hellAE := coefficientBase_aeUniformlyElliptic hopen.measurableSet
    principalSobolev P.principal
    (fun i j ↦ (P.principal_smooth 1 i j).toWkpSpaceOn_base_ae hopen hbounded ∞)
    alpha halpha hell
  rw [hcoeff] at hellAE
  obtain ⟨C, hC, hcoercive⟩ := variableCoeffForm_isCoercive
    (Fact.out : 0 < n) hbounded (multiplicationCoefficientOperator coeff)
    (integratedElliptic_multiplication_of_ae coeff hellAE)
  refine ⟨variableCoeffForm (multiplicationCoefficientOperator coeff),
    lowerOrderOperator (fun i ↦ mulLpLeft ((P.drift_smooth 0 i).toLp hopen hbounded ∞))
      (mulLpLeft ((P.potential_smooth 0).toLp hopen hbounded ∞)), C, hC, ?_, ?_⟩
  · exact fullDivergenceForm_eq_principal_add_pivot_comp hopen _ _ _
  · intro u
    simpa only [pow_two, mul_assoc] using hcoercive u

end SmoothFullCoefficients

end SobolevSpace.GraphSpace.BoundaryRegularity
