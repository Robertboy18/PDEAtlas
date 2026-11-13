/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Sobolev
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Testing
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.BoundedOperator

/-!
# The scalar forcing under affine elliptic rescaling

For `v(y) = u(z + a y)`, the divergence equation acquires the load
`a² f(z + a y)`. The derivative factors and the Jacobian are derived in the
smooth test identity, then density recovers the interior weak
predicate. The `L²` pullback also preserves an essential bound, with
the required quadratic spatial factor.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- Affine transport of a scalar divergence equation with its
rescaled load. No coefficient or state continuity is required. -/
theorem isInteriorWeakDivergenceSolution_of_scaledBall_forcing
    (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (A : Fin n → Fin n → DerivLp n ∞ (ball z (a * r)))
    (f : DerivLp n 2 (ball z (a * r))) (u : H¹(ball z (a * r)))
    (hu : IsInteriorWeakDivergenceSolution A f u)
    (B : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) r))
    (g : DerivLp n 2 (ball (0 : ℝ^n) r)) (v : H¹(ball (0 : ℝ^n) r))
    (hB : ∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
      fun y ↦ A i j (ballHomeomorph z ha y))
    (hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
      fun y ↦ a ^ 2 * f (ballHomeomorph z ha y))
    (hv : ∀ i, (wkpCoordinateCLM (singleDerivIndex n i) v : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball 0 r)]
        fun y ↦ a * wkpCoordinateCLM (singleDerivIndex n i) u
          (ballHomeomorph z ha y)) :
    IsInteriorWeakDivergenceSolution B g v := by
  apply (isInteriorWeakDivergenceSolution_iff_testFunctions isOpen_ball B g v).mpr
  intro φ
  let ψ := scaledBallTestFunction z ha r φ
  have horig := (isInteriorWeakDivergenceSolution_iff_testFunctions
    isOpen_ball A f u).mp hu ψ
  have hterm (i j : Fin n) :
      (∫ y, B i j y * wkpCoordinateCLM (singleDerivIndex n j) v y *
        (∂[i] φ.1.toFun) y ∂domainMeasure n (ball 0 r)) =
      (a ^ 2 * (a ^ n)⁻¹) *
        ∫ x, A i j x * wkpCoordinateCLM (singleDerivIndex n j) u x *
          (∂[i] ψ.1.toFun) x ∂domainMeasure n (ball z (a * r)) := by
    calc
      _ = a ^ 2 * ∫ y in ball (0 : ℝ^n) r,
          A i j (ballHomeomorph z ha y) *
            wkpCoordinateCLM (singleDerivIndex n j) u (ballHomeomorph z ha y) *
            (∂[i] ψ.1.toFun) (ballHomeomorph z ha y) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hB i j, hv j] with y hb hd
        rw [hb, hd, partialDeriv_scaledBallTestFunction]
        field_simp [ha.ne']
      _ = _ := by
        rw [integral_comp_ballHomeomorph_mul z ha r (fun x ↦
          A i j x * wkpCoordinateCLM (singleDerivIndex n j) u x *
            (∂[i] ψ.1.toFun) x)]
        exact (mul_assoc _ _ _).symm
  have hload :
      (∫ y, g y * φ.1.toFun y ∂domainMeasure n (ball 0 r)) =
        (a ^ 2 * (a ^ n)⁻¹) *
          ∫ x, f x * ψ.1.toFun x ∂domainMeasure n (ball z (a * r)) := by
    calc
      _ = a ^ 2 * ∫ y in ball (0 : ℝ^n) r,
          f (ballHomeomorph z ha y) * ψ.1.toFun (ballHomeomorph z ha y) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hg] with y hy
        have hψ : ψ.1.toFun (ballHomeomorph z ha y) = φ.1.toFun y :=
          scaledBallTestFunction_apply z ha r φ y
        rw [hy, hψ]
        exact mul_assoc _ _ _
      _ = _ := by
        rw [integral_comp_ballHomeomorph_mul z ha r (fun x ↦ f x * ψ.1.toFun x)]
        exact (mul_assoc _ _ _).symm
  simp only [hterm, ← Finset.mul_sum, horig, hload]

/-- The rescaled scalar load is an `L²` function and its essential
bound carries the quadratic spatial factor. -/
theorem exists_scaledBallLoadPullback (z : ℝ^n) {a : ℝ} (ha : 0 < a) (r : ℝ)
    (f : DerivLp n 2 (ball z (a * r))) {M : ℝ}
    (hf : ∀ᵐ x ∂domainMeasure n (ball z (a * r)), ‖f x‖ ≤ M) :
    ∃ g : DerivLp n 2 (ball (0 : ℝ^n) r),
      (g : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        (fun y ↦ a ^ 2 * f (ballHomeomorph z ha y)) ∧
      ∀ᵐ y ∂domainMeasure n (ball 0 r), ‖g y‖ ≤ a ^ 2 * M := by
  let P : DerivLp n 2 (ball z (a * r)) →L[ℝ] DerivLp n 2 (ball (0 : ℝ^n) r) :=
    WeakChangeOfVariables.boundedPullbackCLM (p := 2) (F := ℝ)
    (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
    isBounded_ball
  have hrep : (a ^ 2 • P f : DerivLp n 2 (ball (0 : ℝ^n) r)) =ᵐ[
      domainMeasure n (ball 0 r)] fun y ↦ a ^ 2 * f (ballHomeomorph z ha y) := by
    filter_upwards [Lp.coeFn_smul (a ^ 2) (P f),
      WeakChangeOfVariables.boundedPullbackLp_apply_ae
        (contDiff_scaledBallChart z ha r 1) (contDiff_scaledBallChart_symm z ha r 1)
        isBounded_ball f] with y hs hp
    exact hs.trans (congrArg (a ^ 2 * ·) hp)
  refine ⟨a ^ 2 • P f, hrep, ?_⟩
  filter_upwards [hrep, (ae_comp_ballHomeomorph_iff z ha r _).mpr hf] with y hy hb
  rw [hy, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg a)

end SobolevSpace.GraphSpace.MeanScaling
