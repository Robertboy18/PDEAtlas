/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.RadialSquareFlux.Sobolev
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator

/-!
# The radial square flux at an arbitrary centre

Pulling back by the translation chart (`boundedW1pPullbackCLM`) moves the centre to
zero. Translation of the
volume and sphere integrals then transports the Hardy-based identity unchanged.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.RadialSquareFlux

open MeasureTheory Metric Set Filter SobolevSpace SobolevSpace.GraphSpace NormedSpace
open SobolevSpace.WeakChangeOfVariables
open scoped Topology RealInnerProductSpace Sobolev

variable {n : ℕ}

/-- The Sobolev chart pullback gives a translated representative on the zero-centred ball. -/
theorem exists_h1_translate {c : ℝ^n} {r : ℝ} (U : H¹(ball c r)) {w : ℝ^n → ℝ}
    (hbase : baseRepresentative U =ᵐ[domainMeasure n (ball c r)] w) :
    ∃ V : H¹(ball (0 : ℝ^n) r),
      baseRepresentative V =ᵐ[domainMeasure n (ball 0 r)] fun x ↦ w (c + x) := by
  have himage : (Homeomorph.addLeft c) '' ball (0 : ℝ^n) r = ball c r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change c + x ∈ ball c r
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx
    · intro hy
      refine ⟨y - c, ?_, by simp⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hy
  let E := (Homeomorph.addLeft c).toOpenPartialHomeomorphOfImageEq
    (ball 0 r) isOpen_ball (ball c r) himage
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := contDiff_const.add contDiff_id
  have hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y) := contDiff_const.neg.add contDiff_id
  have hTarget : Bornology.IsBounded E.target := isBounded_ball
  let V : H¹(ball (0 : ℝ^n) r) := boundedW1pPullbackCLM hE hSymm hTarget U
  refine ⟨V, (boundedW1pPullbackCLM_base_ae hE hSymm hTarget U).trans ?_⟩
  have hpre : (fun x : ℝ^n ↦ c + x) ⁻¹' ball c r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hmeasure : MeasurePreserving (fun x : ℝ^n ↦ c + x)
      (domainMeasure n (ball 0 r)) (domainMeasure n (ball c r)) := by
    have hm := (measurePreserving_add_left (volume : Measure (ℝ^n)) c).restrict_preimage
      (s := ball c r) isOpen_ball.measurableSet
    rw [hpre] at hm
    exact hm
  change (fun x ↦ baseRepresentative U (c + x)) =ᵐ[domainMeasure n (ball 0 r)]
    fun x ↦ w (c + x)
  exact hmeasure.quasiMeasurePreserving.ae_eq_comp hbase

/-- The H¹ radial square-flux identity on an arbitrary ball in dimension at least three.
Only punctured closed-ball C¹ regularity is required; no centre limit is assumed. -/
theorem radial_square_flux_of_h1_at (hn : 3 ≤ n) {c : ℝ^n} {r : ℝ} (hr : 0 < r)
    (U : H¹(ball c r)) {w : ℝ^n → ℝ}
    (hw : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 w x)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n (ball c r)] w) :
    ((n : ℝ) - 1) * (∫ x in ball c r, w x ^ 2 / ‖x - c‖) +
      2 * (∫ x in ball c r, w x * fderiv ℝ w x (normalize (x - c))) =
        sphereIntegral n (fun x ↦ w x ^ 2) c r := by
  obtain ⟨V, hV⟩ := exists_h1_translate U hbase
  let v : ℝ^n → ℝ := fun x ↦ w (c + x)
  have hv : ∀ x ∈ closedBall (0 : ℝ^n) r, x ≠ 0 → ContDiffAt ℝ 1 v x := by
    intro x hx hne
    apply (hw (c + x) (by simpa [mem_closedBall, dist_eq_norm] using hx)
      (by simpa using hne)).comp x (contDiffAt_const.add contDiffAt_id)
  have h := radial_square_flux_of_h1 hn hr V hv hV
  have hd (x : ℝ^n) (hx : x ∈ ball (0 : ℝ^n) r) (hne : x ≠ 0) :
      fderiv ℝ v x = fderiv ℝ w (c + x) := by
    have hw' := (hw (c + x)
      (by simpa [mem_closedBall, dist_eq_norm] using ball_subset_closedBall hx)
      (by simpa using hne)).differentiableAt one_ne_zero
    have hchain := hw'.hasFDerivAt.comp x ((hasFDerivAt_id x).const_add c)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, v] using hchain.fderiv
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa using (show 0 < n by omega))
  have hrad : (∫ x in ball (0 : ℝ^n) r, v x * fderiv ℝ v x (normalize x)) =
      ballIntegral n (fun x ↦ w x * fderiv ℝ w x (normalize (x - c))) c r := by
    rw [← ballIntegral_comp_add_left]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ^n))] with x hx hne
    simp only [v, add_sub_cancel_left, hd x hx hne]
  have hweight : (∫ x in ball (0 : ℝ^n) r, v x ^ 2 / ‖x‖) =
      ballIntegral n (fun x ↦ w x ^ 2 / ‖x - c‖) c r := by
    rw [← ballIntegral_comp_add_left]
    simp only [ballIntegral, v, add_sub_cancel_left]
  have hsphere : sphereIntegral n (fun x ↦ v x ^ 2) 0 r =
      sphereIntegral n (fun x ↦ w x ^ 2) c r :=
    sphereIntegral_comp_add_left (fun x ↦ w x ^ 2) c r
  rw [hrad, hweight, hsphere] at h
  exact h

/-- In dimension three the two cross terms give exactly half the outer square trace. -/
theorem radial_square_flux_three {c : ℝ^3} {r : ℝ} (hr : 0 < r)
    (U : H¹(ball c r)) {w : ℝ^3 → ℝ}
    (hw : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 w x)
    (hbase : baseRepresentative U =ᵐ[domainMeasure 3 (ball c r)] w) :
    (∫ x in ball c r, w x ^ 2 / ‖x - c‖) +
      (∫ x in ball c r, w x * fderiv ℝ w x (normalize (x - c))) =
        (1 / 2 : ℝ) * sphereIntegral 3 (fun x ↦ w x ^ 2) c r := by
  have h := radial_square_flux_of_h1_at (by omega : 3 ≤ 3) hr U hw hbase
  norm_num at h
  linarith

end PDE.Analysis.RadialSquareFlux
