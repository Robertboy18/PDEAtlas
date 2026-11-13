/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Convolution.HigherOrder
public import PDE.Spaces.Sobolev.Approximation.Mollification.HigherOrderOperator
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Regularity gained by the mollifier

The smooth-kernel convolution map constructs an Hᵏ output from arbitrary L²
input. For input already in Hᵏ it agrees with the graph mollifier.
Thus the regularity gain, contraction on each fixed Sobolev space, and
commutation with weak derivative coordinates belong to one convolution.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory GraphSpace
open scoped ENNReal InnerProductSpace Sobolev

variable {n k r s : ℕ}

/-- Positive-scale mollification, with any prescribed finite Sobolev
output order. Its L²-to-Hᵏ norm may depend on the scale. -/
def mollifierSmoothingCLM (r : ℕ) (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) :
    DerivLp n 2 Set.univ →L[ℝ] W^{r,2}(ℝ^n) :=
  (convolutionHkCLM r (scaled_contDiff μ) (scaled_hasCompactSupport μ hδ)).comp
    wholeSpaceL2Equiv.toLinearIsometry.toContinuousLinearMap

/-- Forgetting the derivatives of the smoothed graph recovers the L² mollifier. -/
theorem mollifierSmoothingCLM_base (r : ℕ) (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (u : DerivLp n 2 Set.univ) :
    wkpBaseCoordinateCLM (mollifierSmoothingCLM r μ hδ u) = mollifierRowCLM μ hδ u := by
  simp only [mollifierSmoothingCLM, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, convolutionHkCLM_base]
  rfl

/-- The regularity-gaining map agrees with the Hᵏ mollifier when the
input has that order of weak derivatives. -/
theorem mollifierSmoothingCLM_baseCoordinate (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (U : W^{r,2}(ℝ^n)) :
    mollifierSmoothingCLM r μ hδ (wkpBaseCoordinateCLM U) = mollifierHkCLM μ hδ U := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [mollifierSmoothingCLM_base]
  rfl

/-- Order restriction preserves the constructed smoothing, including order zero. -/
theorem lowerOrderCLM_mollifierSmoothingCLM (hrs : s ≤ r)
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (u : DerivLp n 2 Set.univ) :
    lowerOrderCLM hrs (mollifierSmoothingCLM r μ hδ u) =
      mollifierSmoothingCLM s μ hδ u := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex] using
    (mollifierSmoothingCLM_base r μ hδ u).trans
      (mollifierSmoothingCLM_base s μ hδ u).symm

/-- Smoothing to a higher order is contractive in every order already
possessed by the input. The higher-order norm itself need not be uniform
in the smoothing scale. -/
theorem norm_lowerOrderCLM_mollifierSmoothingCLM_base_le (hrs : r ≤ s)
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{r,2}(ℝ^n)) :
    ‖lowerOrderCLM hrs (mollifierSmoothingCLM s μ hδ (wkpBaseCoordinateCLM U))‖ ≤
      ‖U‖ := by
  rw [lowerOrderCLM_mollifierSmoothingCLM, mollifierSmoothingCLM_baseCoordinate]
  exact norm_mollifierHkCLM_apply_le μ hδ U

/-- The higher-order smoothing represents the literal scaled-kernel
convolution of the original Sobolev base function. -/
theorem mollifierSmoothingCLM_baseCoordinate_ae
    (s : ℕ) (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{r,2}(ℝ^n)) :
    (wkpBaseCoordinateCLM (mollifierSmoothingCLM s μ hδ (wkpBaseCoordinateCLM U)) :
      ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
        fun x ↦ mollify μ δ (wkpBaseCoordinateCLM U) x := by
  rw [mollifierSmoothingCLM_base]
  simpa only [wkpBaseCoordinateCLM_apply, mollifierHkCLM_coordinate,
    baseRepresentative, domainMeasure, Measure.restrict_univ] using
    mollifierHkCLM_base_ae μ hδ U

/-- At order one this is the L²-to-H¹ mollifier. -/
theorem mollifierSmoothingCLM_one (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (u : DerivLp n 2 Set.univ) :
    mollifierSmoothingCLM 1 μ hδ u = mollifierH1CLM μ hδ u := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  exact (mollifierSmoothingCLM_base 1 μ hδ u).trans
    (mollifierH1CLM_base μ hδ u).symm

/-- Weak derivative extraction commutes with convolution on Sobolev graphs. -/
theorem derivativeWordCLM_mollifierHkCLM
    (α : List (Fin n)) (hα : α.length + r ≤ k)
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{k,2}(ℝ^n)) :
    derivativeWordCLM α hα (mollifierHkCLM μ hδ U) =
      mollifierHkCLM μ hδ (derivativeWordCLM α hα U) := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [derivativeWordCLM_apply, mollifierHkCLM_coordinate]

/-- Smoothing and weak differentiation commute even when the requested
output order exceeds the regularity of the original function. -/
theorem derivativeWordCLM_mollifierSmoothingCLM
    (α : List (Fin n)) (hα : α.length ≤ k) (hαs : α.length + r ≤ s)
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{k,2}(ℝ^n)) :
    derivativeWordCLM α hαs
        (mollifierSmoothingCLM s μ hδ (wkpBaseCoordinateCLM U)) =
      mollifierSmoothingCLM r μ hδ (wkpCoordinateCLM (derivIndexOfList α hα) U) := by
  have hlow :
      lowerOrderCLM (show α.length ≤ s by omega)
        (mollifierSmoothingCLM s μ hδ (wkpBaseCoordinateCLM U)) =
      mollifierHkCLM μ hδ (lowerOrderCLM hα U) := by
    rw [lowerOrderCLM_mollifierSmoothingCLM, ← mollifierSmoothingCLM_baseCoordinate]
    rfl
  have hrow := congrArg
    (fun V : W^{α.length,2}(ℝ^n) ↦
      wkpCoordinateCLM (derivIndexOfList α le_rfl) V) hlow
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [mollifierSmoothingCLM_base]
  simpa only [wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
    derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply,
    lowerOrderCLM_apply, mollifierHkCLM_coordinate, DerivIndex.castOrder,
    derivIndexOfList] using hrow

/-- Even standard mollification is self-adjoint in every Hilbert
Sobolev graph, since the same self-adjoint L² operator acts on every row. -/
theorem inner_standardMollifierHkCLM_left {δ : ℝ} (hδ : 0 < δ)
    (U V : W^{r,2}(ℝ^n)) :
    ⟪mollifierHkCLM (standardMollifier n) hδ U, V⟫_ℝ =
      ⟪U, mollifierHkCLM (standardMollifier n) hδ V⟫_ℝ := by
  change inner ℝ (mollifierHkCLM (standardMollifier n) hδ U).val V.val =
    inner ℝ U.val (mollifierHkCLM (standardMollifier n) hδ V).val
  simp only [PiLp.inner_apply, mollifierHkCLM_coordinate]
  exact Finset.sum_congr rfl fun a _ ↦ inner_standardMollifierRowCLM_left hδ _ _

end SobolevSpace.Approximation
