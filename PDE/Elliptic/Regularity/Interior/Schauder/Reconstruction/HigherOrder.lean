/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
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

`GraphSpace.exists_contDiffOn_representative_of_wkpCoordinate_ae_eq` is the same
statement for an element of `W^{1,p}(Ω)` whose weak derivative coordinates have
continuous representatives on a ball.
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

namespace GraphSpace

open scoped ENNReal Sobolev

/-- A Sobolev function whose first weak derivatives agree almost everywhere on a ball
with the coordinates of a continuous field `G` that is Cᵐ on that ball has a Cᵐ⁺¹
representative on the ball of a quarter of the radius, with classical derivative `G`.
This is `exists_contDiffOn_representative_of_weakGradient` for an element of
`W^{1,p}(Ω)`, for every `1 ≤ p ≤ ∞`. -/
theorem exists_contDiffOn_representative_of_wkpCoordinate_ae_eq
    (m : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n} (u : W^{1,p}(Ω))
    {G : ℝ^n → ℝ^n} (hG : Continuous G) {z : ℝ^n} {R : ℝ} (hR : 0 < R)
    (hball : ball z R ⊆ Ω) (hGm : ContDiffOn ℝ m G (ball z R))
    (hGa : ∀ i, (fun x ↦ G x i) =ᵐ[volume.restrict (ball z R)]
      wkpCoordinateCLM (singleDerivIndex n i) u) :
    ∃ v : ℝ^n → ℝ, Continuous v ∧ ContDiffOn ℝ (m + 1) v (ball z (R / 4)) ∧
      v =ᵐ[volume.restrict (ball z (R / 4))] wkpBaseCoordinateCLM u ∧
      ∀ x ∈ ball z (R / 4), HasFDerivAt v (innerSL ℝ (G x)) x := by
  have : IsFiniteMeasure (volume.restrict (ball z R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hf : IntegrableOn (wkpBaseCoordinateCLM u) (ball z R) :=
    ((Lp.memLp (wkpBaseCoordinateCLM u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable Fact.out
  have hweak (i : Fin n) :
      HasWeakDerivativeOn (ball z R) [i] (wkpBaseCoordinateCLM u) (fun x ↦ G x i) := by
    have hw : HasWeakDerivativeOn Ω [i] (wkpBaseCoordinateCLM u)
        (wkpCoordinateCLM (singleDerivIndex n i) u) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using u.property.hasWeakDerivativeOn_first (by norm_num) i
    exact (hw.mono isOpen_ball.measurableSet hball).congr_ae Filter.EventuallyEq.rfl
      (hGa i).symm
  exact exists_contDiffOn_representative_of_weakGradient m hf hG hGm hweak hR Subset.rfl

end GraphSpace

end SobolevSpace
