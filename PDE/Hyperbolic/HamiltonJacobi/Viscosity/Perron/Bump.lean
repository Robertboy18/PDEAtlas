/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Perron.Patching
public import PDE.Analysis.Topology.Semicontinuity.Piecewise
public import PDE.Analysis.Topology.Semicontinuity.Regularization
import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The Perron bump argument

The lower regularization of a maximal upper semicontinuous subsolution
below a lower semicontinuous supersolution is a supersolution. A failed
lower test gives a strict classical subsolution after a small quadratic
perturbation. Its maximum with the envelope can be pasted on a ball,
because the quadratic makes it smaller on an annulus. The defining
property of `liminf` selects a nearby value that this bump strictly raises.

The upper barrier excludes a failed test at barrier contact and bounds the
bump elsewhere. Maximality comes from `Maximal`; we prove the local
improvement and the nearby-point selection.

This is the "bump" construction of Lemma 4.4 in Crandall, Ishii and Lions, together with its use
in their proof of Theorem 4.1, specialized to first-order equations and `C¹` tests. Ishii
introduced Perron's method for viscosity solutions of Hamilton–Jacobi equations.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992), 1-67, §4, Theorem 4.1 and
  its proof, Lemma 4.4.
  <https://doi.org/10.1090/S0273-0979-1992-00266-5>
* H. Ishii, *Perron's method for Hamilton-Jacobi equations*, Duke Math. J. 55 (1987), 369-384.
  <https://doi.org/10.1215/S0012-7094-87-05521-9>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Perron

open Set Metric Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The lower regularization of a maximal subsolution below a supersolution
is a supersolution. Local lower bounds ensure a real-valued regularization.
Maximality is only required against upper semicontinuous subsolutions
obtained by raising the original function below the barrier. -/
theorem isSpatialViscositySupersolution_liminf_of_maximal {H : E → E → ℝ} {U : Set (E × ℝ)}
    {u b : E × ℝ → ℝ} (hH : Continuous (fun q : E × E ↦ H q.1 q.2)) (hu : UpperSemicontinuousOn u U)
    (husub : IsSpatialViscositySubsolution H U u)
    (hbound : ∀ x ∈ U, IsBoundedUnder (· ≥ ·) (𝓝[U] x) u) (hb : LowerSemicontinuousOn b U)
    (hbsuper : IsSpatialViscositySupersolution H U b) (hub : ∀ x ∈ U, u x ≤ b x)
    (hmaximal : ∀ w : E × ℝ → ℝ, UpperSemicontinuousOn w U → IsSpatialViscositySubsolution H U w →
      (∀ x ∈ U, u x ≤ w x ∧ w x ≤ b x) → ∀ x ∈ U, w x ≤ u x) :
    IsSpatialViscositySupersolution H U (fun x ↦ liminf u (𝓝[U] x)) := by
  classical
  let a : E × ℝ → ℝ := fun x ↦ liminf u (𝓝[U] x)
  have hau : ∀ y ∈ U, a y ≤ u y := fun y hy ↦ PDE.liminf_nhdsWithin_le hy (hbound y hy)
  have hab : ∀ y ∈ U, a y ≤ b y := fun y hy ↦ (hau y hy).trans (hub y hy)
  refine ⟨husub.1, fun x hx φ hφ hmin ↦ ?_⟩
  by_contra hnot
  have hneg : spatialJetOperator H (x, fderiv ℝ φ x) < 0 := by
    rw [spatialJetOperator_fderiv hφ.differentiableAt_one]
    exact lt_of_not_ge hnot
  have hgap : a x < b x := (hab x hx).lt_of_ne fun heq ↦ hnot (hbsuper.2 x hx φ hφ
    (Filter.EventuallyLE.isLocalMinOn (eventually_nhdsWithin_of_forall fun y hy ↦
      sub_le_sub_right (hab y hy) (φ y)) (by change a x - φ x = b x - φ x; rw [heq]) hmin))
  let Q : E × ℝ → ℝ := quadraticSize
  have hQ : ContDiff ℝ 1 Q := contDiff_quadraticSize
  have hQzero : Q 0 = 0 := by simp [Q, quadraticSize]
  have hQderiv : fderiv ℝ Q 0 = 0 := IsLocalMin.fderiv_eq_zero
    (Eventually.of_forall fun y ↦ hQzero ▸ quadraticSize_nonneg y)
  let ψ : E × ℝ → ℝ := fun y ↦ φ y + (a x - φ x) - Q (y - x)
  have hψx : ψ x = a x := by simp [ψ, hQzero]
  have hψ : ContDiffAt ℝ 1 ψ x := (hφ.add contDiffAt_const).sub
      (hQ.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const))
  have hquad : HasFDerivAt (fun y : E × ℝ ↦ Q (y - x))
      (0 : (E × ℝ) →L[ℝ] ℝ) x := by
    have h := hQ.contDiffAt.differentiableAt_one.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    simpa only [Function.comp_def, id_eq, sub_self, hQderiv, ContinuousLinearMap.zero_comp] using h
  have hψderiv : fderiv ℝ ψ x = fderiv ℝ φ x := by
    simpa only [ψ, sub_zero] using
      ((hφ.differentiableAt_one.hasFDerivAt.add_const (a x - φ x)).fun_sub hquad).fderiv
  have hres : ContinuousAt (fun y ↦ spatialJetOperator H (y, fderiv ℝ ψ y)) x :=
    (continuous_spatialJetOperator hH).continuousAt.comp
      (continuousAt_id.prodMk (hψ.continuousAt_fderiv (by simp)))
  let c : ℝ := (b x - a x) / 4
  have hc : 0 < c := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hψsmall : ∀ᶠ y in 𝓝 x, ψ y < a x + c :=
    hψ.continuousAt.eventually (eventually_lt_nhds (by rw [hψx]; linarith))
  have hbnear : ∀ᶠ y in 𝓝 x, a x + 2 * c < b y := by
    have h := hb x hx (a x + 2 * c) (by dsimp [c]; linarith)
    rwa [nhdsWithin_eq_nhds.mpr (husub.1.mem_nhds hx)] at h
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ a x - φ x ≤ a y - φ y ∧ ContDiffAt ℝ 1 ψ y ∧
        spatialJetOperator H (y, fderiv ℝ ψ y) < 0 ∧ ψ y + c < b y := by
    have hnegative := hres.eventually (eventually_lt_nhds
      (show spatialJetOperator H (x, fderiv ℝ ψ x) < 0 by rw [hψderiv]; exact hneg))
    filter_upwards [husub.1.mem_nhds hx, hmin.isLocalMin (husub.1.mem_nhds hx),
      hψ.eventually (by simp), hnegative, hψsmall, hbnear] with y hy hcontact hd hn hs hb'
    exact ⟨hy, hcontact, hd, hn, by linarith⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let δ : ℝ := min (r ^ 2 / 8) c
  have hδ : 0 < δ := lt_min (by positivity) hc
  have hδr : δ ≤ r ^ 2 / 8 := min_le_left _ _
  have hδc : δ ≤ c := min_le_right _ _
  let χ : E × ℝ → ℝ := fun y ↦ ψ y + δ
  have hglue : ∀ z ∈ U, z ∉ ball x r →
      ∀ᶠ y in 𝓝[U] z, y ∈ ball x r → χ y ≤ u y := by
    intro z _ hz
    have hfar : ∀ᶠ y in 𝓝 z, r / 2 < dist y x :=
      (continuous_id.dist continuous_const).continuousAt.eventually
        (eventually_gt_nhds ((half_lt_self hr).trans_le (le_of_not_gt hz)))
    filter_upwards [mem_nhdsWithin_of_mem_nhds hfar] with y hy hyball
    have hyclosed := ball_subset_closedBall hyball
    have hcontact := (hball hyclosed).2.1
    have hyu := hau y (hball hyclosed).1
    have hquadlower := norm_sq_le_quadraticSize (y - x)
    rw [dist_eq_norm] at hy
    change φ y + (a x - φ x) - quadraticSize (y - x) + δ ≤ u y
    nlinarith [norm_nonneg (y - x)]
  have hχdiff : ∀ y ∈ U ∩ ball x r, ContDiffAt ℝ 1 χ y :=
    fun y hy ↦ ((hball (ball_subset_closedBall hy.2)).2.2.1).add contDiffAt_const
  have hχsub : IsSpatialViscositySubsolution H (U ∩ ball x r) χ :=
    isSpatialViscositySubsolution_of_differentiableOn (husub.1.inter isOpen_ball)
      (fun y hy ↦ (hχdiff y hy).differentiableAt_one.differentiableWithinAt) fun y hy ↦ by
        change spatialJetOperator H (y, fderiv ℝ (fun z ↦ ψ z + δ) y) ≤ 0
        rw [fderiv_add_const]
        exact (hball (ball_subset_closedBall hy.2)).2.2.2.1.le
  let w : E × ℝ → ℝ := (ball x r).piecewise (fun y ↦ max (u y) (χ y)) u
  have hwusc : UpperSemicontinuousOn w U := PDE.upperSemicontinuousOn_piecewise_max hu isOpen_ball
      (fun y hy ↦ ContinuousWithinAt.upperSemicontinuousWithinAt
        (hχdiff y hy).continuousAt.continuousWithinAt) hglue
  have hwsub : IsSpatialViscositySubsolution H U w :=
    isSpatialViscositySubsolution_piecewise_max husub isOpen_ball hχsub hglue
  have hwb : ∀ y ∈ U, u y ≤ w y ∧ w y ≤ b y := by
    intro y hy
    by_cases hyball : y ∈ ball x r
    · rw [show w y = max (u y) (χ y) from piecewise_eq_of_mem _ _ _ hyball]
      exact ⟨le_max_left _ _, max_le (hub y hy) (show ψ y + δ ≤ b y by
        linarith [(hball (ball_subset_closedBall hyball)).2.2.2.2])⟩
    · rw [show w y = u y from piecewise_eq_of_notMem _ _ _ hyball]
      exact ⟨le_rfl, hub y hy⟩
  have hfreq : ∃ᶠ y in 𝓝[U] x, u y < a x + δ / 2 :=
    frequently_lt_of_liminf_lt (PDE.isCoboundedUnder_nhdsWithin (R := ℝᵒᵈ) hx)
      (by change a x < a x + δ / 2; linarith)
  have hψnear : ∀ᶠ y in 𝓝[U] x, a x - δ / 2 < ψ y :=
    mem_nhdsWithin_of_mem_nhds (hψ.continuousAt.eventually
      (eventually_gt_nhds (by rw [hψx]; linarith)))
  have hballnear : ∀ᶠ y in 𝓝[U] x, y ∈ ball x r := mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr)
  obtain ⟨z, hzvalue, hzψ, hzball, hzU⟩ := (hfreq.and_eventually
    (hψnear.and (hballnear.and self_mem_nhdsWithin))).exists
  have hzle := hmaximal w hwusc hwsub hwb z hzU
  rw [show w z = max (u z) (χ z) from piecewise_eq_of_mem _ _ _ hzball] at hzle
  exact (show u z < ψ z + δ by linarith).not_ge ((le_max_right _ _).trans hzle)

end HamiltonJacobi.Perron
