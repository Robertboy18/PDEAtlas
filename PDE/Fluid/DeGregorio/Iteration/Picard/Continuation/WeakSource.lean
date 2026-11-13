/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakBochner
public import PDE.Analysis.MeasureTheory.Lp.CubicWork
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.SecondOrder
import PDE.Spaces.Sobolev.GraphSpace.Operators.BochnerIntegral

/-!
# The weak second-derivative source as an L² map

The real Hilbert transform acts continuously on the H¹ graph, by commutation
with its weak derivative. The continuous representative then gives an L∞
multiplier. These maps define the nonconservative source
`−(ρ + Hω)ωₓₓ + ωHωₓₓ + ωₓHωₓ` as a continuous function of the rate and the H² state.

## Main definitions

* `realLineMultiplierCLM`: the continuous H¹ representative as an L∞ multiplier.
* `realHilbertH1` (from `HilbertTransform.RealPair.Sobolev.SecondOrder`): the Hilbert transform
  on H¹ graphs.
* `realSecondDerivativeCLM`: the weak second-derivative row of an H² graph.
* `secondDerivativeSource`: the nonconservative source.

## Main results

* `continuous_secondDerivativeSource`, `norm_secondDerivativeSource_le`: continuity and
  the L² bound of the source.
* `secondDerivativeSource_ae`: its spatial formula.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped ENNReal Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The continuous H¹ representative, viewed as a bounded multiplier. -/
def realLineMultiplierCLM : W^{1,2}(ℝ^1) →L[ℝ] Lp ℝ ∞ (volume : Measure ℝ) :=
  Lp.coefficientCLM
    { toFun := realLineRepresentative
      map_add' := realLineRepresentative_add
      map_smul' := realLineRepresentative_smul }
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun U ↦ (continuous_realLineRepresentative U).aestronglyMeasurable)
    (fun U ↦ Eventually.of_forall (norm_realLineRepresentative_le U))

/-- The multiplier agrees with the continuous representative almost everywhere. -/
theorem realLineMultiplierCLM_ae (U : W^{1,2}(ℝ^1)) :
    (realLineMultiplierCLM U : ℝ → ℝ) =ᵐ[volume] realLineRepresentative U :=
  Lp.coefficientCLM_ae _ _ _ _ U

/-- The one-dimensional Sobolev bound for the multiplier norm. -/
theorem norm_realLineMultiplierCLM_le (U : W^{1,2}(ℝ^1)) :
    ‖realLineMultiplierCLM U‖ ≤ 2 * ‖U‖ :=
  Lp.norm_coefficientCLM_apply_le _ _ _ _ U

/-- Multiplication of an L² state by an L∞ coefficient is jointly continuous. -/
theorem continuous_linf_mul_l2 :
    Continuous (fun z : Lp ℝ ∞ (volume : Measure ℝ) × Lp ℝ 2 (volume : Measure ℝ) ↦
      z.1 • z.2) := by
  let M := (ContinuousLinearMap.mul ℝ ℝ).holderL (volume : Measure ℝ) ∞ 2 2
  have heq (a : Lp ℝ ∞ (volume : Measure ℝ)) (v : Lp ℝ 2 (volume : Measure ℝ)) :
      M a v = a • v := by
    dsimp only [M]
    rw [ContinuousLinearMap.holderL_apply_apply]
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) a v,
      Lp.coeFn_lpSMul (r := 2) a v] with x h hx
    simpa only [ContinuousLinearMap.mul_apply', smul_eq_mul, Pi.mul_apply] using
      h.trans hx.symm
  simpa only [Function.comp_apply, heq] using
    (M.continuous.comp continuous_fst).clm_apply continuous_snd

/-- The weak second-derivative row of an H² graph, in real coordinates. -/
def realSecondDerivativeCLM : W^{2,2}(ℝ^1) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  (realLineCoordinateCLM (singleDerivIndex 1 0)).comp (partialDerivCLM 0)

/-- The source in the nonconservative transport equation for `ωₓₓ`.
All multipliers and higher velocity derivatives are determined by the H² graph. -/
def secondDerivativeSource (ρ : ℝ) (W : W^{2,2}(ℝ^1)) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W
  let Q := partialDerivCLM 0 W
  let r := realSecondDerivativeCLM W
  (-ρ) • r - realLineMultiplierCLM (realHilbertH1 U) • r +
    realLineMultiplierCLM U • realHilbertTransformL2 r +
      realLineMultiplierCLM Q •
        realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q)

/-- The nonlinear source is continuous in rate and H² graph norm. -/
theorem continuous_secondDerivativeSource :
    Continuous (fun z : ℝ × W^{2,2}(ℝ^1) ↦ secondDerivativeSource z.1 z.2) := by
  have hU := (lowerOrderCLM (by decide : 1 ≤ 2)
    (n := 1) (p := 2) (Ω := univ)).continuous.comp
    (continuous_snd : Continuous (Prod.snd : ℝ × W^{2,2}(ℝ^1) → W^{2,2}(ℝ^1)))
  have hQ := (partialDerivCLM (k := 1) (p := 2) (Ω := univ) (0 : Fin 1)).continuous.comp
    (continuous_snd : Continuous (Prod.snd : ℝ × W^{2,2}(ℝ^1) → W^{2,2}(ℝ^1)))
  have hr := realSecondDerivativeCLM.continuous.comp
    (continuous_snd : Continuous (Prod.snd : ℝ × W^{2,2}(ℝ^1) → W^{2,2}(ℝ^1)))
  exact (((continuous_fst.neg.smul hr).sub
    (continuous_linf_mul_l2.comp
      ((realLineMultiplierCLM.continuous.comp (continuous_realHilbertH1.comp hU)).prodMk hr))).add
    (continuous_linf_mul_l2.comp
      ((realLineMultiplierCLM.continuous.comp hU).prodMk
        (realHilbertTransformL2.continuous.comp hr)))).add
    (continuous_linf_mul_l2.comp
      ((realLineMultiplierCLM.continuous.comp hQ).prodMk
        (realHilbertTransformL2.continuous.comp
          ((realLineCoordinateCLM (baseIndex 1 1)).continuous.comp hQ))))

/-- The second derivative is bounded by the H² graph norm. -/
theorem norm_realSecondDerivativeCLM_le (W : W^{2,2}(ℝ^1)) :
    ‖realSecondDerivativeCLM W‖ ≤ ‖W‖ :=
  (norm_realLineCoordinateCLM_le _ _).trans (norm_partialDeriv_le 0 W)

/-- A local H² bound gives a local L² bound for the nonlinear source.
This estimate supplies Bochner integrability; the sharper H¹ production bound
is used separately when closing the energy inequality. -/
theorem norm_secondDerivativeSource_le (ρ : ℝ) (W : W^{2,2}(ℝ^1)) :
    ‖secondDerivativeSource ρ W‖ ≤ |ρ| * ‖W‖ + 8 * ‖W‖ ^ 2 := by
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W
  let Q := partialDerivCLM 0 W
  let r := realSecondDerivativeCLM W
  have hU : ‖U‖ ≤ ‖W‖ := norm_lowerOrderCLM_apply_le _ W
  have hQ : ‖Q‖ ≤ ‖W‖ := norm_partialDeriv_le 0 W
  have hr : ‖r‖ ≤ ‖W‖ := norm_realSecondDerivativeCLM_le W
  have hw : ‖realLineMultiplierCLM U‖ ≤ 2 * ‖W‖ :=
    (norm_realLineMultiplierCLM_le U).trans (mul_le_mul_of_nonneg_left hU (by norm_num))
  have hq : ‖realLineMultiplierCLM Q‖ ≤ 2 * ‖W‖ :=
    (norm_realLineMultiplierCLM_le Q).trans (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hh : ‖realLineMultiplierCLM (realHilbertH1 U)‖ ≤ 4 * ‖W‖ :=
    (norm_realLineMultiplierCLM_le _).trans (by
      have hhU := (norm_realHilbertH1_le U).trans
        (mul_le_mul_of_nonneg_left hU (by norm_num))
      linarith only [hhU])
  have hd : ‖realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q)‖ ≤ ‖W‖ := by
    rw [norm_realHilbertTransformL2]
    exact (norm_realLineCoordinateCLM_le _ Q).trans hQ
  have hs : ‖realHilbertTransformL2 r‖ ≤ ‖W‖ := by
    rwa [norm_realHilbertTransformL2]
  have hmul (c : Lp ℝ ∞ (volume : Measure ℝ)) (v : Lp ℝ 2 (volume : Measure ℝ))
      {C D : ℝ} (hc : ‖c‖ ≤ C) (hv : ‖v‖ ≤ D) (hC : 0 ≤ C) :
      ‖c • v‖ ≤ C * D :=
    (Lp.norm_smul_le c v).trans (mul_le_mul hc hv (norm_nonneg v) hC)
  calc
    ‖secondDerivativeSource ρ W‖ ≤
        ‖(-ρ) • r‖ + ‖realLineMultiplierCLM (realHilbertH1 U) • r‖ +
          ‖realLineMultiplierCLM U • realHilbertTransformL2 r‖ +
            ‖realLineMultiplierCLM Q •
              realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q)‖ := by
      apply (norm_add_le _ _).trans
      apply add_le_add _ le_rfl
      apply (norm_add_le _ _).trans
      exact add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ |ρ| * ‖W‖ + (4 * ‖W‖) * ‖W‖ +
        (2 * ‖W‖) * ‖W‖ + (2 * ‖W‖) * ‖W‖ := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · simpa only [norm_smul, norm_neg, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_left hr (abs_nonneg ρ)
          · exact hmul _ _ hh hr (by positivity)
        · exact hmul _ _ hw hs (by positivity)
      · exact hmul _ _ hq hd (by positivity)
    _ = _ := by ring

/-- The L² source has the stated spatial nonconservative formula. -/
theorem secondDerivativeSource_ae (ρ : ℝ) (W : W^{2,2}(ℝ^1)) :
    let U := lowerOrderCLM (by decide : 1 ≤ 2) W
    let Q := partialDerivCLM 0 W
    let r := realSecondDerivativeCLM W
    (secondDerivativeSource ρ W : ℝ → ℝ) =ᵐ[volume] fun x ↦
      -(ρ + realLineRepresentative (realHilbertH1 U) x) * r x +
        realLineRepresentative U x * realHilbertTransformL2 r x +
          realLineRepresentative Q x *
            realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q) x := by
  intro U Q r
  filter_upwards [Lp.coeFn_add
    ((-ρ) • r - realLineMultiplierCLM (realHilbertH1 U) • r +
      realLineMultiplierCLM U • realHilbertTransformL2 r)
    (realLineMultiplierCLM Q •
      realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q)),
    Lp.coeFn_add ((-ρ) • r - realLineMultiplierCLM (realHilbertH1 U) • r)
      (realLineMultiplierCLM U • realHilbertTransformL2 r),
    Lp.coeFn_sub ((-ρ) • r) (realLineMultiplierCLM (realHilbertH1 U) • r),
    Lp.coeFn_smul (-ρ) r,
    Lp.coeFn_lpSMul (r := 2) (realLineMultiplierCLM (realHilbertH1 U)) r,
    Lp.coeFn_lpSMul (r := 2) (realLineMultiplierCLM U) (realHilbertTransformL2 r),
    Lp.coeFn_lpSMul (r := 2) (realLineMultiplierCLM Q)
      (realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q)),
    realLineMultiplierCLM_ae (realHilbertH1 U), realLineMultiplierCLM_ae U,
    realLineMultiplierCLM_ae Q] with x ha hb hc hd he hf hg hh hi hj
  change ((-ρ) • r - realLineMultiplierCLM (realHilbertH1 U) • r +
    realLineMultiplierCLM U • realHilbertTransformL2 r +
      realLineMultiplierCLM Q •
        realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) Q)) x = _
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    at ha hb hc hd he hf hg
  rw [ha, hb, hc, hd, he, hf, hg, hh, hi, hj]
  ring

/-- A bounded graph curve with measurable L² base constructs a Bochner L²
source. -/
theorem memLp_secondDerivativeSource_of_base
    {ρ : ℝ → ℝ} {W : ℝ → W^{2,2}(ℝ^1)} {a b B D : ℝ}
    (hρ : AEStronglyMeasurable ρ (volume.restrict (Ioc a b)))
    (hbase : AEStronglyMeasurable (fun t ↦ wkpBaseCoordinateCLM (W t))
      (volume.restrict (Ioc a b)))
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖W t‖ ≤ B ∧ |ρ t| ≤ D) :
    MemLp (fun t ↦ secondDerivativeSource (ρ t) (W t)) 2
      (volume.restrict (Ioc a b)) := by
  have hW := aestronglyMeasurable_of_wkpBaseCoordinateCLM _ isOpen_univ W hbase
  apply MemLp.of_bound
    (continuous_secondDerivativeSource.comp_aestronglyMeasurable (hρ.prodMk hW))
    (D * B + 8 * B ^ 2)
  filter_upwards [hbound] with t ht
  apply (norm_secondDerivativeSource_le _ _).trans
  exact add_le_add (mul_le_mul ht.2 ht.1 (norm_nonneg _) hD)
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hB |>.mpr ht.1) (by norm_num))

end DeGregorio.Iteration
