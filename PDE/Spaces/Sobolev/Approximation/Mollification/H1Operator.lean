/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.L2Regularity
public import PDE.Spaces.Sobolev.Calculus.Product.Operator
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceL2

/-!
# Mollification as a bounded map into H¹

The L² mollifier and its derivative kernels specify an element of the H¹
graph space. The weak derivative identities from `L2Regularity` show that these rows
belong to the graph, giving the bounded map `mollifierH1CLM`.

On H¹ input, derivative kernels commute with the weak derivative rows. Combining
this identity with the W¹,∞ weak product rule gives the differentiated coefficient term.
No second derivative of the input is assumed. The L²-to-H¹ bound may depend on the
positive scale; the row L² map is contractive, and the standard row mollifier is
self-adjoint.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace PDE.Analysis

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- The L2 mollifier in the whole-space Sobolev coordinate model. -/
def mollifierRowCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) : L2 →L[ℝ] L2 :=
  (wholeSpaceL2Equiv (n := n)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((mollifierL2CLM μ hε).comp
      (wholeSpaceL2Equiv (n := n)).toLinearIsometry.toContinuousLinearMap)

/-- The derivative-kernel operator in the whole-space Sobolev coordinate model. -/
def mollifierDerivativeRowCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (j : Fin n) : L2 →L[ℝ] L2 :=
  (wholeSpaceL2Equiv (n := n)).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((mollifierDerivativeL2CLM μ hε j).comp
      (wholeSpaceL2Equiv (n := n)).toLinearIsometry.toContinuousLinearMap)

/-- Identity pullback intertwines the two realizations of mollification. -/
@[simp]
theorem wholeSpaceL2Equiv_mollifierRowCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : L2) :
    wholeSpaceL2Equiv (mollifierRowCLM μ hε u) =
      mollifierL2CLM μ hε (wholeSpaceL2Equiv u) := by
  change wholeSpaceL2Equiv (wholeSpaceL2Equiv.symm _) = _
  exact wholeSpaceL2Equiv.apply_symm_apply _

/-- Identity pullback also intertwines the derivative-kernel operators. -/
@[simp]
theorem wholeSpaceL2Equiv_mollifierDerivativeRowCLM
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (j : Fin n) (u : L2) :
    wholeSpaceL2Equiv (mollifierDerivativeRowCLM μ hε j u) =
      mollifierDerivativeL2CLM μ hε j (wholeSpaceL2Equiv u) := by
  change wholeSpaceL2Equiv (wholeSpaceL2Equiv.symm _) = _
  exact wholeSpaceL2Equiv.apply_symm_apply _

/-- The base and first derivative kernels define a bounded map into the ambient H1 rows. -/
def mollifierH1AmbientCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    L2 →L[ℝ] WkpAmbientOn n 1 2 univ :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : DerivIndex n 1 ↦ L2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (firstOrderRows (mollifierRowCLM μ hε) (mollifierDerivativeRowCLM μ hε)))

/-- The prescribed mollifier rows satisfy the weak derivative relations. -/
theorem mollifierH1AmbientCLM_mem (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : L2) :
    mollifierH1AmbientCLM μ hε u ∈ wkpSubmoduleOn n 1 2 univ := by
  obtain ⟨U, hbase, hderiv⟩ := exists_H1_mollifierL2CLM μ hε (wholeSpaceL2Equiv u)
  have hrows : mollifierH1AmbientCLM μ hε u = (U : WkpAmbientOn n 1 2 univ) := by
    apply PiLp.ext
    intro a
    apply wholeSpaceL2Equiv.injective
    change wholeSpaceL2Equiv
      ((firstOrderRows (mollifierRowCLM μ hε) (mollifierDerivativeRowCLM μ hε) a) u) =
        wholeSpaceL2Equiv ((U : WkpAmbientOn n 1 2 univ) a)
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨j, ha⟩
    · subst a
      rw [firstOrderRows_baseIndex, wholeSpaceL2Equiv_mollifierRowCLM]
      apply Lp.ext
      exact hbase.symm.trans (wholeSpaceL2Equiv_ae _).symm
    · subst a
      rw [firstOrderRows_singleDerivIndex, wholeSpaceL2Equiv_mollifierDerivativeRowCLM]
      apply Lp.ext
      exact (hderiv j).symm.trans (wholeSpaceL2Equiv_ae _).symm
  rw [hrows]
  exact U.property

/-- Mollification as a bounded map from L2 into the H1 graph space.
Its bound may depend on epsilon; every derivative row is constructed from the kernel. -/
def mollifierH1CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) : L2 →L[ℝ] H¹(ℝ^n) :=
  (mollifierH1AmbientCLM μ hε).codRestrict
    (wkpSubmoduleOn n 1 2 univ) (mollifierH1AmbientCLM_mem μ hε)

/-- The base of the lifted mollifier is the original mollified L2 class. -/
theorem mollifierH1CLM_base (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (u : L2) :
    wkpCoordinateCLM (baseIndex n 1) (mollifierH1CLM μ hε u) =
      mollifierRowCLM μ hε u := by
  change (firstOrderRows (mollifierRowCLM μ hε)
    (mollifierDerivativeRowCLM μ hε) (baseIndex n 1)) u = _
  rw [firstOrderRows_baseIndex]

/-- The weak derivative of the lifted mollifier is the derivative-kernel operator. -/
theorem mollifierH1CLM_derivative (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : L2) (j : Fin n) :
    wkpCoordinateCLM (singleDerivIndex n j) (mollifierH1CLM μ hε u) =
      mollifierDerivativeRowCLM μ hε j u := by
  change (firstOrderRows (mollifierRowCLM μ hε)
    (mollifierDerivativeRowCLM μ hε) (singleDerivIndex n j)) u = _
  rw [firstOrderRows_singleDerivIndex]

/-- On H1 data the derivative kernel equals mollification of the weak derivative. -/
theorem mollifierDerivativeRowCLM_base (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (j : Fin n) (U : H¹(ℝ^n)) :
    mollifierDerivativeRowCLM μ hε j (wkpCoordinateCLM (baseIndex n 1) U) =
      mollifierRowCLM μ hε (wkpCoordinateCLM (singleDerivIndex n j) U) := by
  apply wholeSpaceL2Equiv.injective
  simp only [wholeSpaceL2Equiv_mollifierDerivativeRowCLM,
    wholeSpaceL2Equiv_mollifierRowCLM]
  exact mollifierDerivativeL2CLM_eq_of_H1 μ hε j U _ _
    (wholeSpaceL2Equiv_ae _).symm (wholeSpaceL2Equiv_ae _).symm

/-- The two ways of differentiating a mollified H1 field agree. This follows from
uniqueness of the translation derivative, without assuming second derivatives of the input. -/
theorem mollifierDerivativeRowCLM_derivative_comm
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (l j : Fin n) (U : H¹(ℝ^n)) :
    mollifierDerivativeRowCLM μ hε l (wkpCoordinateCLM (singleDerivIndex n j) U) =
      mollifierDerivativeRowCLM μ hε j (wkpCoordinateCLM (singleDerivIndex n l) U) := by
  let u := wholeSpaceL2Equiv (wkpCoordinateCLM (baseIndex n 1) U)
  let g := fun i ↦ wholeSpaceL2Equiv (wkpCoordinateCLM (singleDerivIndex n i) U)
  have hcomm : mollifierDerivativeL2CLM μ hε j u = mollifierL2CLM μ hε (g j) :=
    mollifierDerivativeL2CLM_eq_of_H1 μ hε j U u (g j)
      (wholeSpaceL2Equiv_ae _).symm (wholeSpaceL2Equiv_ae _).symm
  have hleft := hasDerivAt_translate_mollifierL2CLM μ hε (g j) l
  have hright := hasDerivAt_translate_convolutionL2CLM_of_hasDerivAt
    (fun x ↦ fderiv ℝ (scaled μ ε) x (EuclideanSpace.single j 1))
    (integrable_fderiv_scaled_apply μ hε j)
    (EuclideanSpace.single l 1) u (g l)
    (hasDerivAt_translateL2_of_H1 l U u (g l)
      (wholeSpaceL2Equiv_ae _).symm (wholeSpaceL2Equiv_ae _).symm)
  change HasDerivAt
    (fun t : ℝ ↦ translateL2 ℝ (-(t • EuclideanSpace.single l 1))
      (mollifierDerivativeL2CLM μ hε j u))
    (mollifierDerivativeL2CLM μ hε j (g l)) 0 at hright
  rw [hcomm] at hright
  apply wholeSpaceL2Equiv.injective
  simpa only [wholeSpaceL2Equiv_mollifierDerivativeRowCLM] using hleft.unique hright

/-- Differentiating the smoothed coefficient term gives its principal derivative
and the weak derivative of the coefficient. The input needs only one spatial derivative. -/
theorem derivative_mollifier_coefficient_term
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (A : W^{1,∞}(ℝ^n))
    (l j : Fin n) (U : H¹(ℝ^n)) :
    mollifierDerivativeRowCLM μ hε l
        (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierDerivativeRowCLM μ hε j (wkpCoordinateCLM (baseIndex n 1) U)) =
      mollifierRowCLM μ hε
        (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierDerivativeRowCLM μ hε j
            (wkpCoordinateCLM (singleDerivIndex n l) U)) +
      mollifierRowCLM μ hε
        (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)) •
          mollifierRowCLM μ hε (wkpCoordinateCLM (singleDerivIndex n j) U)) := by
  let V := mollifierH1CLM μ hε (wkpCoordinateCLM (singleDerivIndex n j) U)
  have hbase : wkpCoordinateCLM (baseIndex n 1) V =
      mollifierDerivativeRowCLM μ hε j (wkpCoordinateCLM (baseIndex n 1) U) := by
    rw [mollifierDerivativeRowCLM_base]
    exact mollifierH1CLM_base μ hε _
  have hderiv : wkpCoordinateCLM (singleDerivIndex n l) V =
      mollifierDerivativeRowCLM μ hε j
        (wkpCoordinateCLM (singleDerivIndex n l) U) := by
    rw [mollifierH1CLM_derivative]
    exact mollifierDerivativeRowCLM_derivative_comm μ hε l j U
  have h := mollifierDerivativeRowCLM_base μ hε l
    (w1TopMultiplierCLM isOpen_univ A V)
  simp only [wkpCoordinateCLM_apply, w1TopMultiplierCLM_apply_coe,
    w1TopMultiplierAmbient_base, w1TopMultiplierAmbient_singleDeriv] at h
  change mollifierDerivativeRowCLM μ hε l
      (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
        wkpCoordinateCLM (baseIndex n 1) V) =
    mollifierRowCLM μ hε
      (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
        wkpCoordinateCLM (singleDerivIndex n l) V +
      ((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)) •
        wkpCoordinateCLM (baseIndex n 1) V) at h
  rw [hbase, hderiv, map_add, mollifierDerivativeRowCLM_base μ hε j U] at h
  simpa only [mollifierDerivativeRowCLM_base μ hε j U] using h

end SobolevSpace.Approximation

namespace SobolevSpace.Approximation

open PDE.Analysis GraphSpace

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- The mollifier remains contractive in the Sobolev coordinate model. -/
theorem norm_mollifierRowCLM_apply_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : L2) : ‖mollifierRowCLM μ hε u‖ ≤ ‖u‖ := by
  rw [← wholeSpaceL2Equiv.norm_map (mollifierRowCLM μ hε u),
    wholeSpaceL2Equiv_mollifierRowCLM, ← wholeSpaceL2Equiv.norm_map u]
  let J : Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (ℝ^n)) := mollifierL2CLM μ hε
  calc
    ‖J (wholeSpaceL2Equiv u)‖ ≤ ‖J‖ * ‖wholeSpaceL2Equiv u‖ := J.le_opNorm _
    _ ≤ 1 * ‖wholeSpaceL2Equiv u‖ :=
      mul_le_mul_of_nonneg_right (norm_mollifierL2CLM_le (E := ℝ) μ hε) (norm_nonneg _)
    _ = ‖wholeSpaceL2Equiv u‖ := one_mul _

/-- The standard row mollifier is self-adjoint, by the even-kernel identity. -/
theorem inner_standardMollifierRowCLM_left {ε : ℝ} (hε : 0 < ε) (u v : L2) :
    ⟪mollifierRowCLM (standardMollifier n) hε u, v⟫_ℝ =
      ⟪u, mollifierRowCLM (standardMollifier n) hε v⟫_ℝ := by
  rw [← wholeSpaceL2Equiv.inner_map_map (mollifierRowCLM (standardMollifier n) hε u) v,
    ← wholeSpaceL2Equiv.inner_map_map u (mollifierRowCLM (standardMollifier n) hε v)]
  simp only [wholeSpaceL2Equiv_mollifierRowCLM]
  exact inner_standardMollifierL2CLM_left hε _ _

end SobolevSpace.Approximation
