/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealL2
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.WeakDerivative
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall
import CAS.ExactTactic

/-!
# The H¹ graph of a Hilbert coefficient's derivative

A weak H² vorticity determines a weak H¹ graph for the derivative of its
continuous Hilbert coefficient. Both graph coordinates are constructed
using the spectral Hilbert transform and weak derivative commutation.
Its L² isometry bounds each coordinate by the original H² budget.

This retains the highest weak derivative needed for the transport
Jacobian; a pointwise C¹ bound alone would not suffice for H² closure.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Apply the real Hilbert transform to both rows of an H¹ graph. -/
def realHilbertH1 (U : W^{1,2}(ℝ^1)) : W^{1,2}(ℝ^1) :=
  mkW12OfWeakDerivative
    (Lp.memLp (realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (Lp.memLp (realHilbertTransformL2 (realLineCoordinateCLM (singleDerivIndex 1 0) U)))
    ((isHilbertPair_realHilbertTransformL2 _).hasWeakTimeDerivativeOn
      (isHilbertPair_realHilbertTransformL2 _)
      (hasWeakTimeDerivativeOn_realLineCoordinates U))

/-- The Hilbert graph has the canonical transformed base row. -/
@[simp] theorem realLineCoordinateCLM_realHilbertH1_base (U : W^{1,2}(ℝ^1)) :
    realLineCoordinateCLM (baseIndex 1 1) (realHilbertH1 U) =
      realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) U) := by
  simp only [realHilbertH1, realLineCoordinateCLM_mkW12_base, Lp.toLp_coeFn]

/-- Its weak derivative is the canonical transform of the derivative row. -/
@[simp] theorem realLineCoordinateCLM_realHilbertH1_single (U : W^{1,2}(ℝ^1)) :
    realLineCoordinateCLM (singleDerivIndex 1 0) (realHilbertH1 U) =
      realHilbertTransformL2 (realLineCoordinateCLM (singleDerivIndex 1 0) U) := by
  simp only [realHilbertH1, realLineCoordinateCLM_mkW12_single, Lp.toLp_coeFn]

/-- Hilbert isometry bounds the transformed H¹ graph. -/
theorem norm_realHilbertH1_le (U : W^{1,2}(ℝ^1)) :
    ‖realHilbertH1 U‖ ≤ 2 * ‖U‖ := by
  change ‖realLineH1Jet _ _‖ ≤ _
  simp only [Lp.toLp_coeFn]
  apply (norm_realLineH1Jet_le _ _).trans
  simp only [norm_realHilbertTransformL2]
  have h₀ := norm_realLineCoordinateCLM_le (baseIndex 1 1) U
  have h₁ := norm_realLineCoordinateCLM_le (singleDerivIndex 1 0) U
  linarith

/-- The transformed graph depends continuously on the original H¹ state. -/
theorem continuous_realHilbertH1 : Continuous realHilbertH1 := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : W^{1,2}(ℝ^1) ↦ realLineH1Jet _ _)
  simp only [Lp.toLp_coeFn]
  exact continuous_realLineH1Jet.comp
    ((realHilbertTransformL2.continuous.comp
      (realLineCoordinateCLM (baseIndex 1 1)).continuous).prodMk
      (realHilbertTransformL2.continuous.comp
        (realLineCoordinateCLM (singleDerivIndex 1 0)).continuous))

/-- The continuous multiplier is the Hilbert transform of the H¹ base. -/
theorem isHilbertPair_realHilbertH1 (U : W^{1,2}(ℝ^1)) :
    IsHilbertPair (realLineCoordinateCLM (baseIndex 1 1) U)
      (realLineRepresentative (realHilbertH1 U)) := by
  apply (isHilbertPair_realHilbertTransformL2 _).congr_right_ae
  simpa only [realLineCoordinateCLM_realHilbertH1_base] using
    realLineCoordinate_ae_representative (realHilbertH1 U)

/-- The canonical H¹ Hilbert graph respects subtraction. -/
theorem realHilbertH1_sub (U V : W^{1,2}(ℝ^1)) :
    realHilbertH1 (U - V) = realHilbertH1 U - realHilbertH1 V := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  apply oneDimensionalPushforwardL2.injective
  change realLineCoordinateCLM (baseIndex 1 1) (realHilbertH1 (U - V)) =
    realLineCoordinateCLM (baseIndex 1 1) (realHilbertH1 U - realHilbertH1 V)
  simp only [map_sub, realLineCoordinateCLM_realHilbertH1_base]

/-- Differentiation of the continuous Hilbert coefficient agrees
pointwise with the Hilbert transform of the first Sobolev derivative. -/
theorem hasDerivAt_hilbert_coefficient_of_h2 (W : W^{2,2}(ℝ^1))
    {c : ℝ → ℝ} (hc : Continuous c)
    (hpair : IsHilbertPair (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W)) c)
    (x : ℝ) :
    HasDerivAt c (realLineRepresentative (realHilbertH1 (∂[0] W)) x) x := by
  let J := lowerOrderCLM (by decide : 1 ≤ 2) W
  let K : W^{1,2}(ℝ^1) := ∂[0] W
  have hb : realLineCoordinateCLM (baseIndex 1 1) J =
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) :=
    realLineCoordinateCLM_base_lowerOrder W
  have he : realLineCoordinateCLM (baseIndex 1 1) K =
      realLineCoordinateCLM (singleDerivIndex 1 0) J :=
    realLineCoordinateCLM_partialDeriv_h2_base W
  have hweak : HasWeakTimeDerivativeOn univ
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W))
      (realLineCoordinateCLM (baseIndex 1 1) K) := by
    simpa only [hb, ← he] using hasWeakTimeDerivativeOn_realLineCoordinates J
  have hcweak := hpair.hasWeakTimeDerivativeOn (isHilbertPair_realHilbertH1 K) hweak
  have heq : c = fun y ↦ c 0 +
      ∫ s in 0..y, realLineRepresentative (realHilbertH1 K) s := by
    funext y
    rw [hcweak.intervalIntegral_eq_sub hc 0 y]
    ring
  rw [heq]
  simpa only [zero_add] using
    ((continuous_realLineRepresentative _).integral_hasStrictDerivAt 0 x).hasDerivAt.const_add
      (c 0)

/-- The spatial derivative of a continuous Hilbert coefficient
of bounded H² input has an H¹ graph. Its two real L² coordinates each
have norm at most the input budget. The derivative equality is pointwise. -/
theorem exists_hilbert_derivative_h1_of_hkBaseBall
    {g : DerivLp 1 2 univ} {B : NNReal} (hg : g ∈ hkBaseBall 1 2 univ B)
    {c : ℝ → ℝ} (hc : Continuous c)
    (hpair : IsHilbertPair (oneDimensionalPushforwardL2 g) c) :
    ∃ V : W^{1,2}(ℝ^1), ‖V‖ ≤ 2 * (B : ℝ) ∧
      ‖realLineCoordinateCLM (baseIndex 1 1) V‖ ≤ B ∧
      ‖realLineCoordinateCLM (singleDerivIndex 1 0) V‖ ≤ B ∧
      ∀ x, HasDerivAt c (realLineRepresentative V x) x := by
  obtain ⟨U, hU, hbase⟩ := hg
  let J : W^{1,2}(ℝ^1) := lowerOrderCLM (by decide : 1 ≤ 2) U
  let K : W^{1,2}(ℝ^1) := derivativeWordCLM [0] (by decide : [0].length + 1 ≤ 2) U
  have hK : ‖K‖ ≤ B := (norm_derivativeWordCLM_apply_le _ _ U).trans hU
  have hb : realLineCoordinateCLM (baseIndex 1 1) J = oneDimensionalPushforwardL2 g := by
    apply congrArg oneDimensionalPushforwardL2
    change (J : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) = g
    simpa only [J, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
      wkpBaseCoordinateCLM_apply] using hbase
  have he : realLineCoordinateCLM (baseIndex 1 1) K =
      realLineCoordinateCLM (singleDerivIndex 1 0) J := by
    apply congrArg oneDimensionalPushforwardL2
    change (K : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (J : WkpAmbientOn 1 1 2 univ) (singleDerivIndex 1 0)
    simp only [K, J, derivativeWordCLM_apply, derivativeWordIndex_singleton_baseIndex,
      lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
  let eta := realLineCoordinateCLM (baseIndex 1 1) K
  let zeta := realLineCoordinateCLM (singleDerivIndex 1 0) K
  have hweak : HasWeakTimeDerivativeOn univ (oneDimensionalPushforwardL2 g) eta := by
    simpa only [hb, ← he] using hasWeakTimeDerivativeOn_realLineCoordinates J
  have heta := isHilbertPair_realHilbertTransformL2 eta
  have hHweak := heta.hasWeakTimeDerivativeOn
    (isHilbertPair_realHilbertTransformL2 zeta)
    (hasWeakTimeDerivativeOn_realLineCoordinates K)
  let V := mkW12OfWeakDerivative (Lp.memLp (realHilbertTransformL2 eta))
    (Lp.memLp (realHilbertTransformL2 zeta)) hHweak
  have hV₀ : realLineCoordinateCLM (baseIndex 1 1) V = realHilbertTransformL2 eta := by
    simp only [V, realLineCoordinateCLM_mkW12_base, Lp.toLp_coeFn]
  have hV₁ : realLineCoordinateCLM (singleDerivIndex 1 0) V =
      realHilbertTransformL2 zeta := by
    simp only [V, realLineCoordinateCLM_mkW12_single, Lp.toLp_coeFn]
  have he₀ : ‖eta‖ ≤ B := (norm_realLineCoordinateCLM_le _ K).trans hK
  have he₁ : ‖zeta‖ ≤ B := (norm_realLineCoordinateCLM_le _ K).trans hK
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · change ‖realLineH1Jet _ _‖ ≤ _
    simp only [Lp.toLp_coeFn]
    exact (norm_realLineH1Jet_le _ _).trans (by
      simp only [norm_realHilbertTransformL2]
      linarith)
  · simpa only [hV₀, norm_realHilbertTransformL2] using he₀
  · simpa only [hV₁, norm_realHilbertTransformL2] using he₁
  · intro x
    have hrep := realLineCoordinate_ae_representative V
    rw [hV₀] at hrep
    have hcweak := (hpair.hasWeakTimeDerivativeOn heta hweak).congr_ae
      EventuallyEq.rfl hrep
    have heq : c = fun y ↦ c 0 + ∫ s in 0..y, realLineRepresentative V s := by
      funext y
      rw [hcweak.intervalIntegral_eq_sub hc 0 y]
      cas
    rw [heq]
    simpa only [zero_add] using
      ((continuous_realLineRepresentative V).integral_hasStrictDerivAt 0 x).hasDerivAt.const_add
        (c 0)

/-- The continuous Hilbert transform of an H² graph has the Hilbert transform of its first
weak derivative as classical derivative. -/
theorem hasDerivAt_realHilbertH1_lowerOrder (Q : W^{2,2}(ℝ^1)) (x : ℝ) :
    HasDerivAt (realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q)))
      (realLineRepresentative (realHilbertH1 (∂[0] Q)) x) x := by
  apply hasDerivAt_hilbert_coefficient_of_h2 Q (continuous_realLineRepresentative _)
  have h := isHilbertPair_realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q)
  rwa [realLineCoordinateCLM_base_lowerOrder] at h

end SobolevSpace.GraphSpace
