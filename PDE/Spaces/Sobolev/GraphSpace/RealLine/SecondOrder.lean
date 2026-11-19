/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Pullback
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
import CAS.ExactTactic

/-!
# Real-line multipliers and assembly of a second weak derivative

A bounded C¹ multiplier acts on an H¹ graph with an explicit two-row
estimate. Compatible H¹ graphs for a function and its first derivative
then assemble into an H² graph through the successor-order
constructor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis.Evolution
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- Lowering an H² graph to H¹ preserves its real-line base coordinate. -/
theorem realLineCoordinateCLM_base_lowerOrder (W : W^{2,2}(ℝ^1)) :
    realLineCoordinateCLM (baseIndex 1 1) (lowerOrderCLM (by decide : 1 ≤ 2) W) =
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) := by
  apply congrArg oneDimensionalPushforwardL2
  change ((lowerOrderCLM (by decide : 1 ≤ 2) W : W^{1,2}(ℝ^1)) :
    WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (W : WkpAmbientOn 1 2 2 univ) (baseIndex 1 2)
  simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]

/-- The H² first-derivative base row is the derivative row of its H¹ restriction. -/
theorem realLineCoordinateCLM_partialDeriv_h2_base (W : W^{2,2}(ℝ^1)) :
    realLineCoordinateCLM (baseIndex 1 1) (partialDerivCLM 0 W) =
      realLineCoordinateCLM (singleDerivIndex 1 0)
        (lowerOrderCLM (by decide : 1 ≤ 2) W) := by
  apply congrArg oneDimensionalPushforwardL2
  change ((partialDerivCLM 0 W : W^{1,2}(ℝ^1)) : WkpAmbientOn 1 1 2 univ)
    (baseIndex 1 1) =
      ((lowerOrderCLM (by decide : 1 ≤ 2) W : W^{1,2}(ℝ^1)) :
        WkpAmbientOn 1 1 2 univ) (singleDerivIndex 1 0)
  simp only [partialDerivCLM, derivativeWordCLM_apply,
    derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
    DerivIndex.castOrder_singleDerivIndex]

/-- A bounded C¹ multiplier constructs an H¹ graph with the exact weak
Leibniz row and a quantitative graph bound. -/
theorem exists_h1_mul_of_bounded_c1
    (V : W^{1,2}(ℝ^1)) {m m' : ℝ → ℝ} {M N : ℝ}
    (hm : Continuous m) (hm' : Continuous m')
    (hderiv : ∀ x, HasDerivAt m (m' x) x)
    (hbound : ∀ x, ‖m x‖ ≤ M) (hbound' : ∀ x, ‖m' x‖ ≤ N) :
    ∃ W : W^{1,2}(ℝ^1),
      ‖W‖ ≤ (M + N) * ‖realLineCoordinateCLM (baseIndex 1 1) V‖ +
        M * ‖realLineCoordinateCLM (singleDerivIndex 1 0) V‖ ∧
      realLineRepresentative W = (fun x ↦ realLineRepresentative V x * m x) ∧
      (realLineCoordinateCLM (singleDerivIndex 1 0) W : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ realLineCoordinateCLM (singleDerivIndex 1 0) V x * m x +
          realLineRepresentative V x * m' x) := by
  let v := realLineRepresentative V
  let g := realLineCoordinateCLM (singleDerivIndex 1 0) V
  have hv := memLp_realLineRepresentative V
  have hg := Lp.memLp g
  have hvm := memLp_mul_of_bounded hv hm hbound
  have hgm := memLp_mul_of_bounded hg hm hbound
  have hvm' := memLp_mul_of_bounded hv hm' hbound'
  have hweak := hasWeakTimeDerivativeOn_mul_of_bounded_c1
    (continuous_realLineRepresentative V) hv hg
    (hasWeakTimeDerivativeOn_realLineRepresentative V) hm hm' hderiv hbound hbound'
  let W := mkW12OfWeakDerivative hvm (hgm.add hvm') hweak
  refine ⟨W, ?_,
    realLineRepresentative_mkW12 hvm (hgm.add hvm') hweak
      ((continuous_realLineRepresentative V).mul hm), ?_⟩
  · change ‖realLineH1Jet _ _‖ ≤ _
    apply (norm_realLineH1Jet_le _ _).trans
    rw [MemLp.toLp_add hgm hvm']
    apply (add_le_add (norm_toLp_mul_of_bounded hv hm hbound)
      ((norm_add_le _ _).trans (add_le_add
        (norm_toLp_mul_of_bounded hg hm hbound)
        (norm_toLp_mul_of_bounded hv hm' hbound')))).trans
    simp only [toLp_realLineRepresentative, Lp.toLp_coeFn]
    apply le_of_eq
    cas
  · change (realLineCoordinateCLM (singleDerivIndex 1 0)
      (mkW12OfWeakDerivative hvm (hgm.add hvm') hweak) : ℝ → ℝ) =ᵐ[volume] _
    rw [realLineCoordinateCLM_mkW12_single]
    exact (hgm.add hvm').coeFn_toLp

/-- Compatible H¹ graphs give a pointwise first derivative of the continuous
representative, without assuming any classical second derivative. -/
theorem hasDerivAt_realLineRepresentative_of_h1_derivative
    (U V : W^{1,2}(ℝ^1))
    (hV : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U) (x : ℝ) :
    HasDerivAt (realLineRepresentative U) (realLineRepresentative V x) x := by
  have hweak := (hasWeakTimeDerivativeOn_realLineRepresentative U).congr_ae
    Filter.EventuallyEq.rfl (hV ▸ realLineCoordinate_ae_representative V)
  have heq : realLineRepresentative U =
      fun y ↦ realLineRepresentative U 0 + ∫ s in 0..y, realLineRepresentative V s := by
    funext y
    rw [hweak.intervalIntegral_eq_sub (continuous_realLineRepresentative U) 0 y]
    cas
  rw [heq]
  simpa only [zero_add] using
    ((continuous_realLineRepresentative V).integral_hasStrictDerivAt 0 x).hasDerivAt.const_add
      (realLineRepresentative U 0)

/-- Compatible real-line H¹ graphs assemble an H² graph with the same base
L² class and the successor-order norm estimate. -/
theorem exists_h2_of_realLine_h1_derivative
    (U V : W^{1,2}(ℝ^1))
    (hV : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U) :
    ∃ W : W^{2,2}(ℝ^1),
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) =
        realLineCoordinateCLM (baseIndex 1 1) U ∧
      ‖W‖ ≤ succOrderAssemblyNormBound 1 1 * (‖U‖ + ‖V‖) := by
  have hcompat (i : Fin 1) :
      (V : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
        (U : WkpAmbientOn 1 1 2 univ) (firstDerivIndex 1 1 (by decide) i) := by
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    apply oneDimensionalPushforwardL2.injective
    exact hV
  obtain ⟨W, hbase, hnorm⟩ :=
    exists_succOrder_of_firstDerivatives_with_norm (by decide) U (fun _ ↦ V) hcompat
  refine ⟨W, ?_, ?_⟩
  · exact congrArg oneDimensionalPushforwardL2 (Lp.ext hbase)
  · simpa only [Fin.sum_univ_one] using hnorm

end SobolevSpace.GraphSpace
