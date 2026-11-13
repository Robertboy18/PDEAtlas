/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Reconstruction.LocalRepresentative
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Classical

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Reconstructing higher classical regularity from a weak gradient

A continuous Cᵐ representative of a weak gradient gives a Cᵐ⁺¹
representative of its integrable primitive on an interior ball. Compactness
first bounds the gradient locally. The local bounded-gradient theorem then
constructs a continuous representative of the primitive, to which weak
derivative reconstruction applies. Higher integrability of the primitive
is a conclusion of this argument, rather than an additional hypothesis.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Metric
open scoped NNReal InnerProductSpace

namespace SobolevSpace

variable {n : ℕ}

/-- An integrable function whose weak gradient has a continuous Cᵐ
representative has a local Cᵐ⁺¹ representative with that classical derivative.
The base function is not assumed continuous or bounded. -/
theorem exists_contDiffOn_representative_of_weakGradient
    (m : ℕ) {Ω : Set ℝ^n} {f : ℝ^n → ℝ}
    (hf : IntegrableOn f Ω) {G : ℝ^n → ℝ^n} (hG : Continuous G)
    (hGm : ContDiffOn ℝ m G Ω)
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] f (fun x ↦ G x i))
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Ω) :
    ∃ v : ℝ^n → ℝ, Continuous v ∧ ContDiffOn ℝ (m + 1) v (ball z (R / 4)) ∧
      v =ᵐ[volume.restrict (ball z (R / 4))] f ∧
      ∀ x ∈ ball z (R / 4), HasFDerivAt v (innerSL ℝ (G x)) x := by
  obtain ⟨P, hP⟩ := (isCompact_closedBall z (R / 2)).exists_bound_of_continuousOn
    hG.continuousOn
  let C : ℝ≥0 := ⟨max 0 P, le_max_left _ _⟩
  have hsmall : ball z (R / 2) ⊆ Ω :=
    (ball_subset_ball (by linarith : R / 2 ≤ R)).trans hball
  have hC (i : Fin n) : ∀ᵐ x ∂volume.restrict (ball z (R / 2)), ‖G x i‖ ≤ C := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    exact (PiLp.norm_apply_le (G x) i).trans
      ((hP x (ball_subset_closedBall hx)).trans (le_max_right _ _))
  obtain ⟨v, hv, hva⟩ := exists_lipschitz_representative_on_ball_of_weak_derivative_bound
    isOpen_ball (hf.mono_set hsmall) (fun i x ↦ G x i)
    (fun i ↦ (hweak i).mono isOpen_ball.measurableSet hsmall) (fun _ ↦ C) hC
    (by positivity : 0 < R / 2) Subset.rfl
  have hrad : R / 2 / 2 = R / 4 := by ring
  rw [hrad] at hva
  have hinner : ball z (R / 4) ⊆ Ω :=
    (ball_subset_ball (by linarith : R / 4 ≤ R)).trans hball
  have hg (i : Fin n) : Continuous (fun x ↦ G x i) := by fun_prop
  have hweakv (i : Fin n) :
      HasWeakDerivativeOn (ball z (R / 4)) [i] v (fun x ↦ G x i) :=
    ((hweak i).mono isOpen_ball.measurableSet hinner).congr_ae hva.symm
      EventuallyEq.rfl
  have hvm := Approximation.contDiffOn_succ_of_continuous_weakPartialDerivativesOn
    m isOpen_ball hv.continuous hg
    (fun i ↦ (contDiffOn_piLp 2).mp (hGm.mono hinner) i) hweakv
  refine ⟨v, hv.continuous, hvm, hva, ?_⟩
  intro x hx
  have hderiv := Approximation.hasFDerivAt_of_continuous_weakPartialDerivativesOn
    isOpen_ball hv.continuous hg hweakv hx
  have htuple : (WithLp.toLp 2 (fun i ↦ G x i) : ℝ^n) = G x := PiLp.ext fun _ ↦ rfl
  simpa only [htuple] using hderiv

end SobolevSpace
