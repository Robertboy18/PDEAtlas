/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Geometry
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator

/-!
# Sobolev and measurable-coefficient rescaling

The bounded chart pullback constructs the rescaled H¹ state and identifies
each weak derivative. Pulling back the coefficient matrix preserves its
essential bounds and ellipticity constant. No regularity of the coefficients
beyond measurability is used.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- The affine pullback of an arbitrary H¹ state, with all first derivatives
identified by the weak chain rule. -/
theorem exists_scaledBallSobolevPullback (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (u : H¹(ball z (a * r))) :
    ∃ v : H¹(ball (0 : ℝ^n) r),
      (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        (fun y ↦ wkpBaseCoordinateCLM u (ballHomeomorph z ha y)) ∧
      ∀ i, (wkpCoordinateCLM (singleDerivIndex n i) v : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (ball 0 r)]
          fun y ↦ a * wkpCoordinateCLM (singleDerivIndex n i) u (ballHomeomorph z ha y) := by
  have hE := contDiff_scaledBallChart z ha r 1
  have hEs := contDiff_scaledBallChart_symm z ha r 1
  let v := WeakChangeOfVariables.boundedW1pPullbackCLM hE hEs isBounded_ball u
  refine ⟨v, WeakChangeOfVariables.boundedW1pPullbackCLM_base_ae
    hE hEs isBounded_ball u, ?_⟩
  intro i
  change (v.val (singleDerivIndex n i) : ℝ^n → ℝ)
    =ᵐ[domainMeasure n (ball (0 : ℝ^n) r)]
      (fun y ↦ a * u.val (singleDerivIndex n i) (ballHomeomorph z ha y))
  have h := WeakChangeOfVariables.boundedW1pPullbackCLM_derivative_ae
    hE hEs isBounded_ball u i
  have hderiv (y : ℝ^n) :
      fderiv ℝ (fun x ↦ scaledBallChart z ha r x) y = a • ContinuousLinearMap.id ℝ (ℝ^n) :=
    (((hasFDerivAt_id y).const_smul a).const_add z).fderiv
  simp only [PDE.partialDeriv, hderiv, smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  filter_upwards [h] with y hy
  exact hy.trans (mul_comm _ _)

/-- Measurable coefficient pullback retains the same matrix bounds and the
same ellipticity constant, independently of the centre and spatial scale. -/
theorem exists_scaledBallCoefficientPullback (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (A : Fin n → Fin n → DerivLp n ∞ (ball z (a * r))) {α Λ : ℝ}
    (hA : AEUniformlyElliptic A α) (hΛ : ∀ i j, ‖A i j‖ ≤ Λ) :
    ∃ B : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) r),
      AEUniformlyElliptic B α ∧ (∀ i j, ‖B i j‖ ≤ Λ) ∧
      ∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        fun y ↦ A i j (ballHomeomorph z ha y) := by
  have hE := contDiff_scaledBallChart z ha r 1
  have hEs := contDiff_scaledBallChart_symm z ha r 1
  let P := WeakChangeOfVariables.boundedPullbackCLM (p := ∞) (F := ℝ)
    hE hEs isBounded_ball
  let B := fun i j ↦ P (A i j)
  have hrep (i j) : (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
      fun y ↦ A i j (ballHomeomorph z ha y) :=
    WeakChangeOfVariables.boundedPullbackLp_apply_ae hE hEs isBounded_ball (A i j)
  refine ⟨B, ⟨hA.1, ?_⟩, ?_, hrep⟩
  · have hq := WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph hE hEs
    filter_upwards [hq.ae hA.2, ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hrep i)]
      with y hy hb
    intro ξ
    apply (hy ξ).trans_eq
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      congrArg (fun t : ℝ ↦ t * ξ j * ξ i) (hb i j).symm
  · intro i j
    calc
      ‖B i j‖ ≤ ‖P‖ * ‖A i j‖ := P.le_opNorm _
      _ ≤ 1 * ‖A i j‖ := mul_le_mul_of_nonneg_right
        (WeakChangeOfVariables.norm_boundedPullbackCLM_top_le hE hEs isBounded_ball)
        (norm_nonneg _)
      _ ≤ Λ := by simpa only [one_mul] using hΛ i j

end SobolevSpace.GraphSpace.MeanScaling
