/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphLinearization
public import PDE.Fluid.NavierStokes.Stationary.Representative

/-!
# The mass and gradient pairings as integrals of representatives

On the whole-space velocity space `H¹(ℝⁿ)ⁿ` the mass pairing is `∫ v·w` of the representatives
and the gradient pairing `gradientForm v w` is `∫ Σᵢⱼ ∂ⱼvᵢ ∂ⱼwᵢ` of the chosen gradient
representatives. When the representatives agree almost everywhere with fields `U`, `V` and the
gradient coordinates with their classical partial derivatives, the pairings are the
corresponding integrals of `U`, `V` and their partial derivatives. These are the energy pairings
of the weak linearization; with a weight `c` they give the energy Gram matrix of finitely many
fields as integrals of classical quantities.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert RealInnerProductSpace

namespace NavierStokes.Selfsimilar

open Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- The mass pairing is the integral of the inner product of the representatives. -/
theorem massPairing_eq_integral_inner (v w : H) :
    massPairing v w = ∫ x, ⟪representative v x, representative w x⟫ := by
  have hint (i : Fin n) : Integrable (fun x ↦ (wkpBaseCoordinateCLM (v i) : ℝ^n → ℝ) x *
      (wkpBaseCoordinateCLM (w i) : ℝ^n → ℝ) x) volume := by
    have h := L2.integrable_inner (𝕜 := ℝ) (wkpBaseCoordinateCLM (v i))
      (wkpBaseCoordinateCLM (w i))
    simp only [domainMeasure, Measure.restrict_univ] at h
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  rw [massPairing_eq_integral, ← integral_finsetSum _ fun i _ ↦ hint i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [PiLp.inner_apply, representative_apply, massCLM_apply, RCLike.inner_apply,
    conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The gradient pairing is the integral of the Frobenius product of the gradient
representatives. -/
theorem gradientForm_eq_integral (v w : H) :
    gradientForm v w = ∫ x, ∑ i, ∑ j, (gradientCLM v i j : ℝ^n → ℝ) x *
      (gradientCLM w i j : ℝ^n → ℝ) x := by
  have hterm (i j : Fin n) :
      inner ℝ (wkpCoordinateCLM (singleDerivIndex n j) (v i))
          (wkpCoordinateCLM (singleDerivIndex n j) (w i)) =
        ∫ x, (gradientCLM v i j : ℝ^n → ℝ) x * (gradientCLM w i j : ℝ^n → ℝ) x := by
    rw [← gradientCLM_apply, ← gradientCLM_apply, L2.inner_def]
    simp only [domainMeasure, Measure.restrict_univ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  have hint (i j : Fin n) : Integrable (fun x ↦ (gradientCLM v i j : ℝ^n → ℝ) x *
      (gradientCLM w i j : ℝ^n → ℝ) x) volume := by
    have h := L2.integrable_inner (𝕜 := ℝ) (gradientCLM v i j) (gradientCLM w i j)
    simp only [domainMeasure, Measure.restrict_univ] at h
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    exact mul_comm _ _
  rw [gradientForm_apply, integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    hint i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint i j]
  exact Finset.sum_congr rfl fun j _ ↦ hterm i j

/-- If the representatives agree almost everywhere with `U` and `V`, the mass pairing is
`∫ U·V`. -/
theorem massPairing_eq_integral_of_ae {v w : H} {U V : ℝ^n → ℝ^n}
    (hv : representative v =ᵐ[volume] U) (hw : representative w =ᵐ[volume] V) :
    massPairing v w = ∫ x, ⟪U x, V x⟫ := by
  rw [massPairing_eq_integral_inner]
  refine integral_congr_ae ?_
  filter_upwards [hv, hw] with x hx hy
  rw [hx, hy]

/-- If the gradient coordinates agree almost everywhere with the classical partial derivatives
of `U` and `V`, the gradient pairing is `∫ Σᵢⱼ ∂ⱼUᵢ ∂ⱼVᵢ`. -/
theorem gradientForm_eq_integral_of_ae {v w : H} {U V : ℝ^n → ℝ^n}
    (hv : ∀ i j, (gradientCLM v i j : ℝ^n → ℝ) =ᵐ[volume] PDE.partialDeriv j (fun x ↦ U x i))
    (hw : ∀ i j, (gradientCLM w i j : ℝ^n → ℝ) =ᵐ[volume] PDE.partialDeriv j (fun x ↦ V x i)) :
    gradientForm v w = ∫ x, ∑ i, ∑ j, PDE.partialDeriv j (fun y ↦ U y i) x *
      PDE.partialDeriv j (fun y ↦ V y i) x := by
  rw [gradientForm_eq_integral]
  refine integral_congr_ae ?_
  have hv' := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hv i)
  have hw' := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hw i)
  filter_upwards [hv', hw'] with x hx hy
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hx i j, hy i j]

end NavierStokes.Selfsimilar
