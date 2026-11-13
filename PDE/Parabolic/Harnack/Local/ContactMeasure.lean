/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Parabolic.Boundary
public import PDE.Analysis.MeasureTheory.Contact.Image
public import PDE.Parabolic.Harnack.Local.ContactJacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Quantitative measure from parabolic first contacts

Initial and lateral nonnegativity and a negative top value construct a whole
cylinder of vertices. A residual above `κ * (τ + B * (2 * R) + 1)` excludes
contacts outside a prescribed source set; its lower bound controls the contact
Jacobian inside. This gives a quantitative low-sublevel measure bound without assuming
an image bound, a contact set, or a comparison estimate.
-/

open scoped Gradient

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A negative top value forces low-level measure through the parabolic
contact map. Its constant uses coefficient bounds and cylinder geometry only.
The gradient differentiability hypothesis is needed for this Jacobian step;
the `C²,¹` Harnack theorem does not assume it. -/
theorem vertex_measure_le_mul_sublevel_measure
    {R κ α τ B b F : ℝ}
    (hR : 0 < R) (hκ : 0 < κ) (hα : 0 < α) (hb : 0 < b)
    (hshort : b < R ^ 2 / 8) (hscale : κ * R ^ 2 ≤ 1)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
    (hell : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, ∀ z : ℝ^n,
      α * ‖z‖ ^ 2 ≤ ⟪z, (a p.1 p.2).toEuclideanLin z⟫)
    (htrace : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, (a p.1 p.2).trace ≤ τ)
    (hdrift : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, ‖d p.1 p.2‖ ≤ B)
    (w : ℝ^n → ℝ → ℝ)
    (hw : ContinuousOn (Function.uncurry w) (closedBall 0 R ×ˢ Icc 0 b))
    (hgcont : ContinuousOn
      (fun p : ℝ^n × ℝ ↦ ∇ (fun x ↦ w x p.2) p.1)
      (closedBall 0 R ×ˢ Icc 0 b))
    (hwreg : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b,
      DifferentiableAt ℝ (Function.uncurry w) p)
    (hg : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b,
      DifferentiableAt ℝ (fun q : ℝ^n × ℝ ↦ ∇ (fun x ↦ w x q.2) q.1) p)
    (hspace : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b,
      ContDiffAt ℝ 2 (fun x ↦ w x p.2) p.1)
    (hsuper : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b,
      -F ≤ ParabolicMaximum.matrixParabolicOperator a d (fun _ _ ↦ 0) w p.1 p.2)
    (Z : Set (ℝ^n × ℝ))
    (hstrict : ∀ p ∈ ball (0 : ℝ^n) R ×ˢ Ioc 0 b, p ∉ Z →
      κ * (τ + B * (2 * R) + 1) <
        ParabolicMaximum.matrixParabolicOperator a d (fun _ _ ↦ 0) w p.1 p.2)
    (hinitial : ∀ x ∈ closedBall (0 : ℝ^n) R, 0 ≤ w x 0)
    (hlateral : ∀ x ∈ sphere (0 : ℝ^n) R, ∀ t ∈ Icc 0 b, 0 ≤ w x t)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ closedBall (0 : ℝ^n) (R / 2)) (hsmall : w x₀ b ≤ -1) :
    volume (closedBall (0 : ℝ^n) (R / 2) ×ˢ Icc (b / 4) (b / 2)) ≤
      ENNReal.ofReal
        (((τ + B * (2 * R) + κ⁻¹ * F + 1) / α) ^ n *
          (τ + B * (2 * R) + κ⁻¹ * F + 1)) *
        volume (((ball (0 : ℝ^n) R ×ˢ Ioc 0 b) ∩ Z) ∩ {p | w p.1 p.2 ≤ κ * b}) := by
  let : (volume : Measure (ℝ^n × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let K := closedBall (0 : ℝ^n) R ×ˢ Icc 0 b
  let Y := closedBall (0 : ℝ^n) (R / 2) ×ˢ Icc (b / 4) (b / 2)
  let S := parabolicQuadraticContactSet w κ 0 (closedBall 0 R) K Y
  have hcompact : IsCompact S :=
    isCompact_parabolicQuadraticContactSet
      ((isCompact_closedBall (0 : ℝ^n) R).prod isCompact_Icc) Subset.rfl
      (isClosed_closedBall.prod isClosed_Icc) hw hgcont
  have hinside : S ⊆ ball (0 : ℝ^n) R ×ˢ Ioc 0 b :=
    parabolicQuadraticContactSet_subset_interior_of_boundary_nonneg
      hR hκ hb hshort hinitial hlateral
  have hcover : Y ⊆ parabolicQuadraticContactMap w κ '' S :=
    cylinder_subset_image_parabolicQuadraticContactMap_of_boundary_nonneg
      hR hκ hb hshort hscale hw
      (fun p hp ↦ (hspace p hp).differentiableAt (by norm_num))
      hinitial hlateral hx₀ hsmall
  have hdist (p : ℝ^n × ℝ) (hp : p ∈ S) :
      ‖(parabolicQuadraticContactMap w κ p).1 - p.1‖ ≤ 2 * R := by
    have hxnorm : ‖p.1‖ ≤ R := by simpa using hp.1.1
    have hynorm : ‖(parabolicQuadraticContactMap w κ p).1‖ ≤ R / 2 := by
      simpa using hp.2.1.1
    have h := norm_sub_le (parabolicQuadraticContactMap w κ p).1 p.1
    linarith
  have hsource : S ⊆ Z := by
    intro p hp
    by_contra hpZ
    have hi := hinside hp
    have hut : DifferentiableAt ℝ (w p.1) p.2 := by
      have h := ((hwreg p hi).hasFDerivAt.comp p.2
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).differentiableAt
      simpa only [Function.comp_def, Function.uncurry] using h
    have hres := matrixParabolicOperator_le_of_parabolic_support a d (hspace p hi) hut
      hκ hα.le (hell p hi) (htrace p hi) (hdrift p hi) (hdist p hp) hi.2.1
      (closedBall_mem_nhds_of_mem hi.1)
      (parabolicQuadraticTilt_contactMap w hκ.ne' p) hp.2.2
    exact (not_lt_of_ge hres) (hstrict p hi hpZ)
  have hlow : S ⊆ ((ball (0 : ℝ^n) R ×ˢ Ioc 0 b) ∩ Z) ∩ {p | w p.1 p.2 ≤ κ * b} := by
    intro p hp
    refine ⟨⟨hinside hp, hsource hp⟩, ?_⟩
    have hzero := parabolicQuadraticTilt_contactMap w hκ.ne' p
    have hs : 0 ≤ (parabolicQuadraticContactMap w κ p).2 :=
      (show 0 ≤ b / 4 by positivity).trans hp.2.1.2.1
    have htime := mul_le_mul_of_nonneg_left
      (show p.2 - (parabolicQuadraticContactMap w κ p).2 ≤ b by linarith [hp.1.2.2]) hκ.le
    have hnorm := mul_nonneg (show 0 ≤ κ / 2 by positivity)
      (sq_nonneg ‖p.1 - (parabolicQuadraticContactMap w κ p).1‖)
    change w p.1 p.2 ≤ κ * b
    dsimp [parabolicQuadraticTilt, quadraticTilt] at hzero
    linarith
  have hderiv : ∀ p ∈ S, HasFDerivWithinAt (parabolicQuadraticContactMap w κ)
      (fderiv ℝ (parabolicQuadraticContactMap w κ) p) S p := by
    intro p hp
    exact (hasFDerivAt_parabolicQuadraticContactMap
      (hwreg p (hinside hp)) (hg p (hinside hp)) κ).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hdet : ∀ p ∈ S, |(fderiv ℝ (parabolicQuadraticContactMap w κ) p).det| ≤
      ((τ + B * (2 * R) + κ⁻¹ * F + 1) / α) ^ n *
        (τ + B * (2 * R) + κ⁻¹ * F + 1) := by
    intro p hp
    have hi := hinside hp
    exact abs_det_fderiv_parabolicQuadraticContactMap_le a d (hwreg p hi) (hg p hi)
      (hspace p hi) hκ hα (hell p hi) (htrace p hi) (hdrift p hi) (hdist p hp)
      (hsuper p hi) hi.2.1 (closedBall_mem_nhds_of_mem hi.1)
      (parabolicQuadraticTilt_contactMap w hκ.ne' p) hp.2.2
  apply (measure_le_mul_measure_of_subset_differentiable_image volume hcompact.measurableSet
    hderiv hcover hdet).trans
  exact mul_le_mul_right (measure_mono hlow) _

end ParabolicHarnack
