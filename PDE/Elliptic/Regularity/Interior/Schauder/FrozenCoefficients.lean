/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Comparison
public import Mathlib.Topology.MetricSpace.Holder
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.Constant

/-!
# Freezing Hölder coefficients on a ball

Freezing the coefficient matrix at the centre of a ball constructs a constant
coefficient homogeneous comparison in the same Sobolev boundary class. Its
gradient error is bounded by the forcing energy and a coefficient perturbation
of size `R^(2γ)` times the original gradient energy.

The first estimate requires regularity only of the coefficient representatives.
The second also uses Hölder representatives of the forcing and subtracts their
values at the centre. The state is a weak `H¹` solution. This comparison
is the perturbative energy step of the interior divergence-form Schauder argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Sobolev InnerProductSpace ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- Hölder coefficient representatives yield a constant coefficient comparison,
with the coefficient perturbation bounded by the square of the Hölder modulus
at the radius. For positive exponents this tends to zero with the radius.
The ellipticity assumption is only at the freezing point;
the original coefficients need not be symmetric or elliptic for this estimate. -/
theorem exists_frozen_comparison
    (hn : 0 < n) (z : ℝ^n) {R : ℝ} (hR : 0 < R)
    (a : Fin n → Fin n → DerivLp n ∞ (ball z R))
    (A : Fin n → Fin n → ℝ^n → ℝ) {K γ : ℝ≥0}
    (hA : ∀ i j, HolderOnWith K γ (A i j) (ball z R))
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] A i j)
    {α : ℝ} (hα : 0 < α)
    (hell : ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j z * ξ j * ξ i)
    (u : H¹(ball z R)) (F : Fin n → DerivLp n 2 (ball z R))
    (hu : ∀ v : H¹₀(ball z R),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) :
    ∃ b : Fin n → Fin n → DerivLp n ∞ (ball z R), ∃ w : H¹₀(ball z R),
      (∀ i j, (b i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)]
        fun _ ↦ A i j z) ∧
      IsInteriorWeakDivergenceSolution b 0 (u - (w : H¹(ball z R))) ∧
      α ^ 2 * ∑ i, ‖derivCoordCLM i w‖ ^ 2 ≤
        2 * ∑ i, ‖F i‖ ^ 2 + 2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
          ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2 := by
  classical
  let b (i j : Fin n) : DerivLp n ∞ (ball z R) :=
    (memLp_top_const (μ := domainMeasure n (ball z R)) (A i j z)).toLp _
  have hb (i j : Fin n) :
      (b i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] fun _ ↦ A i j z :=
    MemLp.coeFn_toLp _
  have hbEll : AEUniformlyElliptic b α := by
    refine ⟨hα, ?_⟩
    filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hb i)] with x hx
    simpa only [hx] using hell
  have hdiff (i j : Fin n) : ‖b i j - a i j‖ ≤ K * R ^ (γ : ℝ) := by
    apply Lp.norm_top_le_of_ae_bound (by positivity)
    filter_upwards [Lp.coeFn_sub (b i j) (a i j), hb i j, hrep i j,
      ae_restrict_mem isOpen_ball.measurableSet] with x hsub hbx hax hx
    rw [hsub, Pi.sub_apply, hbx, hax, norm_sub_rev]
    simpa only [dist_eq_norm] using
      (hA i j).dist_le_of_le hx (mem_ball_self hR) (mem_ball.mp hx).le
  obtain ⟨w, hhom, henergy⟩ := exists_homogeneous_comparison hn isOpen_ball
    (isBounded_ball (x := z) (r := R)) a b hbEll u F hu
  refine ⟨b, w, hb, hhom, henergy.trans ?_⟩
  exact sum_norm_fluxResidual_sq_le (fun i j ↦ b i j - a i j) F
    (fun j ↦ wkpCoordinateCLM (singleDerivIndex n j) u) hdiff

private theorem norm_sub_frozen_flux_sq_le
    (z : ℝ^n) {R : ℝ} (hR : 0 < R)
    (F C : DerivLp n 2 (ball z R)) (f : ℝ^n → ℝ) {M γ : ℝ≥0}
    (hf : HolderOnWith M γ f (ball z R))
    (hF : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f)
    (hC : (C : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] fun _ ↦ f z) :
    ‖F - C‖ ^ 2 ≤ (volume (ball z R)).toReal * (M * R ^ (γ : ℝ)) ^ 2 := by
  have := isFiniteMeasure_domainMeasure_of_isBounded
    (isBounded_ball (x := z) (r := R))
  rw [Lp.norm_sq_eq_integral_norm_sq]
  calc
    _ ≤ ∫ _x, (M * R ^ (γ : ℝ)) ^ 2 ∂domainMeasure n (ball z R) := by
      apply integral_mono_ae ((Lp.memLp (F - C)).norm.integrable_sq) (integrable_const _)
      filter_upwards [Lp.coeFn_sub F C, hF, hC,
        ae_restrict_mem isOpen_ball.measurableSet] with x hsub hfx hcx hx
      rw [hsub, Pi.sub_apply, hfx, hcx]
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      simpa only [dist_eq_norm] using
        hf.dist_le_of_le hx (mem_ball_self hR) (mem_ball.mp hx).le
    _ = _ := by simp [domainMeasure, measureReal_def, smul_eq_mul]

/-- For Hölder coefficients and Hölder divergence forcing, the comparison error
has order `R^(2γ)` in both terms. Subtracting the constant forcing at the centre
is legitimate because it annihilates all zero-boundary test derivatives.
The comparison function and its equation are conclusions, not hypotheses. -/
theorem exists_frozen_comparison_of_holder_flux
    (hn : 0 < n) (z : ℝ^n) {R : ℝ} (hR : 0 < R)
    (a : Fin n → Fin n → DerivLp n ∞ (ball z R))
    (A : Fin n → Fin n → ℝ^n → ℝ) {K M γ : ℝ≥0}
    (hA : ∀ i j, HolderOnWith K γ (A i j) (ball z R))
    (hrep : ∀ i j, (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] A i j)
    {α : ℝ} (hα : 0 < α)
    (hell : ∀ ξ : Fin n → ℝ,
      α * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A i j z * ξ j * ξ i)
    (u : H¹(ball z R)) (F : Fin n → DerivLp n 2 (ball z R))
    (f : Fin n → ℝ^n → ℝ) (hf : ∀ i, HolderOnWith M γ (f i) (ball z R))
    (hF : ∀ i, (F i : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f i)
    (hu : ∀ v : H¹₀(ball z R),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) :
    ∃ b : Fin n → Fin n → DerivLp n ∞ (ball z R), ∃ w : H¹₀(ball z R),
      (∀ i j, (b i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)]
        fun _ ↦ A i j z) ∧
      IsInteriorWeakDivergenceSolution b 0 (u - (w : H¹(ball z R))) ∧
      α ^ 2 * ∑ i, ‖derivCoordCLM i w‖ ^ 2 ≤
        2 * (n : ℝ) * (volume (ball z R)).toReal * (M * R ^ (γ : ℝ)) ^ 2 +
          2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
            ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2 := by
  have := isFiniteMeasure_domainMeasure_of_isBounded
    (isBounded_ball (x := z) (r := R))
  let C (i : Fin n) : DerivLp n 2 (ball z R) :=
    (memLp_const (μ := domainMeasure n (ball z R)) (f i z)).toLp _
  have hC (i : Fin n) :
      (C i : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] fun _ ↦ f i z :=
    MemLp.coeFn_toLp _
  have hweak (v : H¹₀(ball z R)) :
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i - C i, derivCoordCLM i v⟫_ℝ := by
    rw [hu]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sub_left, inner_constant_derivCoordCLM_eq_zero (f i z) (C i) (hC i)]
    exact (sub_zero _).symm
  obtain ⟨b, w, hb, hhom, henergy⟩ :=
    exists_frozen_comparison hn z hR a A hA hrep hα hell u (fun i ↦ F i - C i) hweak
  refine ⟨b, w, hb, hhom, henergy.trans ?_⟩
  have hsum : (∑ i, ‖F i - C i‖ ^ 2) ≤
      (n : ℝ) * (volume (ball z R)).toReal * (M * R ^ (γ : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, (volume (ball z R)).toReal * (M * R ^ (γ : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦
          norm_sub_frozen_flux_sq_le z hR (F i) (C i) (f i) (hf i) (hF i) (hC i)
      _ = _ := by simp [mul_assoc]
  calc
    _ ≤ 2 * ((n : ℝ) * (volume (ball z R)).toReal * (M * R ^ (γ : ℝ)) ^ 2) +
        2 * (n : ℝ) ^ 2 * (K * R ^ (γ : ℝ)) ^ 2 *
          ∑ j, ‖wkpCoordinateCLM (singleDerivIndex n j) u‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl
    _ = _ := by ring

end SobolevSpace.GraphSpace
