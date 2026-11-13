/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Restricting divergence forcing and gradient averages

The restriction theorem for the coefficient form and the pairing
with zero-extended tests transport a divergence forcing identity to an open
subdomain. Gradient averages use the original representatives throughout;
restriction introduces no new choice of gradient.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped Sobolev ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω V : Set ℝ^n}

/-- The coefficient-form identity with divergence forcing restricts
to every smaller open domain by zero extension of its tests. -/
theorem interiorVariableCoeffForm_eq_divergence_restrict
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hsub : V ⊆ Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) (u : H¹(Ω))
    (F : Fin n → DerivLp n 2 Ω)
    (hu : ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) (v : H¹₀(V)) :
    interiorVariableCoeffForm
        (multiplicationCoefficientOperator (fun i j ↦ restrictDerivLp hsub (a i j)))
        (restrictCLM hV.measurableSet hsub u) v =
      ∑ i, ⟪restrictDerivLp hsub (F i), derivCoordCLM i v⟫_ℝ := by
  rw [interiorVariableCoeffForm_restrict hV hΩ hsub, hu]
  apply Finset.sum_congr rfl
  intro i _
  exact ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
    hV hΩ hsub (F i) v (singleDerivIndex n i)

/-- Averages of any function of a restricted gradient coordinate agree with
the averages of the original coordinate on the smaller measurable set. -/
theorem setAverage_comp_gradient_restrict
    (hV : MeasurableSet V) (hsub : V ⊆ Ω) (u : H¹(Ω))
    (i : Fin n) {s : Set ℝ^n} (hs : s ⊆ V) (g : ℝ → ℝ) :
    (⨍ x in s, g (wkpCoordinateCLM (singleDerivIndex n i)
      (restrictCLM hV hsub u) x)) =
      ⨍ x in s, g (wkpCoordinateCLM (singleDerivIndex n i) u x) := by
  apply average_congr
  filter_upwards [(restrictCLM_apply_ae hV hsub u (singleDerivIndex n i)).filter_mono
    (ae_mono (Measure.restrict_mono hs le_rfl))] with x hx
  exact congrArg g hx

/-- The normalized sum of squared L² gradient norms on a restricted ball is
the sum of mean-square energies of the original gradient coordinates. -/
theorem normalized_gradient_energy_restrict
    (u : H¹(Ω)) {z : ℝ^n} {R : ℝ} (hsub : ball z R ⊆ Ω) :
    (volume.real (ball z R))⁻¹ *
      (∑ i, ‖wkpCoordinateCLM (singleDerivIndex n i)
        (restrictCLM isOpen_ball.measurableSet hsub u)‖ ^ 2) =
      ∑ i, ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) u x‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Lp.norm_sq_eq_integral_norm_sq]
  calc
    _ = ⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i)
        (restrictCLM isOpen_ball.measurableSet hsub u) x‖ ^ 2 := by
      rw [setAverage_eq, smul_eq_mul]
    _ = _ := setAverage_comp_gradient_restrict isOpen_ball.measurableSet hsub u i
      Subset.rfl (fun t ↦ ‖t‖ ^ 2)

end SobolevSpace.GraphSpace
