/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Topology.Semicontinuity.Regularization
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.JetOperator
import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Subsolution stability of the Perron envelope

The upper regularization of a locally bounded supremum of upper
semicontinuous subsolutions is a subsolution. A quadratic perturbation makes
each contact strict. A family value near the regularized supremum then
forces an attained maximum into the interior of a small compact ball.
Continuity of the first-order operator transfers the inequality.

We prove the selection of the family member and its contact point.
Finite dimensionality is used only to supply compact balls.

This is Lemma 4.2 of Crandall, Ishii and Lions, the first step of Perron's method, for
first-order equations and `C¹` tests. The selection is their Proposition 4.3, whose proof
maximizes over a compact ball after the same kind of quadratic perturbation. The supersolution
property is proved in `Bump`.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992), 1-67, §4, Lemma 4.2 and
  Proposition 4.3.
  <https://doi.org/10.1090/S0273-0979-1992-00266-5>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set Metric Filter
open scoped Topology

namespace Perron

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  [Nonempty ι]

/-- Upper-contact inequalities pass to the upper regularization of a
locally bounded supremum. The operator only needs continuity at the
limiting contact jet. Compact maximization derives a contact with
one member of the family. -/
theorem le_zero_of_limsup_ciSup_upper_contacts {Q : X → ℝ} (hQ : ContDiff ℝ 1 Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y) {U : Set X} (hU : IsOpen U) {v : ι → X → ℝ} {φ : X → ℝ}
    (hv : ∀ i, UpperSemicontinuousOn (v i) U)
    (hbound : ∀ x ∈ U, ∃ b, ∀ᶠ y in 𝓝[U] x, ∀ i, v i y ≤ b) {x : X} (hx : x ∈ U)
    (hφ : ContDiffAt ℝ 1 φ x)
    (hcontact : IsLocalMaxOn (fun y ↦ limsup (fun z ↦ ⨆ i, v i z) (𝓝[U] y) - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ} (hF : ContinuousAt F (x, fderiv ℝ φ x))
    (htest : ∀ i y, y ∈ U → ∀ ψ : X → ℝ, ContDiffAt ℝ 1 ψ y →
      IsLocalMaxOn (fun z ↦ v i z - ψ z) U y → F (y, fderiv ℝ ψ y) ≤ 0) :
    F (x, fderiv ℝ φ x) ≤ 0 := by
  by_contra hnot
  have hpos : 0 < F (x, fderiv ℝ φ x) := lt_of_not_ge hnot
  let u : X → ℝ := fun y ↦ limsup (fun z ↦ ⨆ i, v i z) (𝓝[U] y)
  have hle : ∀ y ∈ U, ∀ i, v i y ≤ u y :=
    fun y hy i ↦ PDE.le_limsup_ciSup_nhdsWithin hy (hbound y hy) i
  have hQmin : IsLocalMin Q 0 := by
    filter_upwards [] with y
    rw [hQzero]
    exact (sq_nonneg ‖y‖).trans (hQlower y)
  have hQderiv : fderiv ℝ Q 0 = 0 := hQmin.fderiv_eq_zero
  let ψ : X → ℝ := fun y ↦ φ y + Q (y - x)
  have hψ : ContDiffAt ℝ 1 ψ x := hφ.add (hQ.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const))
  have hψx : ψ x = φ x := by simp only [ψ, sub_self, hQzero, add_zero]
  have hquad : HasFDerivAt (fun y : X ↦ Q (y - x)) (0 : X →L[ℝ] ℝ) x := by
    have h := (hQ.contDiffAt.differentiableAt_one.hasFDerivAt).comp x
      ((hasFDerivAt_id x).sub_const x)
    simpa only [Function.comp_def, id_eq, sub_self, hQderiv, ContinuousLinearMap.zero_comp] using h
  have hψderiv : fderiv ℝ ψ x = fderiv ℝ φ x := by
    simpa only [add_zero] using (hφ.differentiableAt_one.hasFDerivAt.fun_add hquad).fderiv
  have hjet : ContinuousAt (fun y ↦ (y, fderiv ℝ ψ y)) x :=
    continuousAt_id.prodMk (hψ.continuousAt_fderiv (by simp))
  have hres : ContinuousAt (fun y ↦ F (y, fderiv ℝ ψ y)) x :=
    hF.comp_of_eq hjet (by rw [hψderiv])
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ u y - φ y ≤ u x - φ x ∧ ContDiffAt ℝ 1 ψ y ∧
        0 < F (y, fderiv ℝ ψ y) := by
    have hpositive := hres.eventually (eventually_gt_nhds
      (show 0 < F (x, fderiv ℝ ψ x) by rw [hψderiv]; exact hpos))
    filter_upwards [hU.mem_nhds hx, hcontact.isLocalMax (hU.mem_nhds hx),
      hψ.eventually (by simp), hpositive] with y hy hmax hdiff hgreater
    exact ⟨hy, hmax, hdiff, hgreater⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hballU : closedBall x r ⊆ U := fun y hy ↦ (hball hy).1
  have hsmall : {y | ψ y < ψ x + r ^ 2 / 4} ∈ 𝓝[U] x :=
    mem_nhdsWithin_of_mem_nhds (hψ.continuousAt.eventually
      (eventually_lt_nhds (by linarith [sq_pos_of_pos hr])))
  obtain ⟨z, ⟨⟨hzball, hzψ⟩, _⟩, i, hi⟩ := PDE.exists_lt_of_lt_limsup_ciSup hx
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr)) hsmall)
      (show u x - r ^ 2 / 4 < u x by linarith [sq_pos_of_pos hr])
  have hzvalue : u x - φ x - r ^ 2 / 2 < v i z - ψ z := by
    change ψ z < ψ x + r ^ 2 / 4 at hzψ
    rw [hψx] at hzψ
    linarith
  have hψcont : ContinuousOn ψ (closedBall x r) :=
    fun y hy ↦ (hball hy).2.2.1.continuousAt.continuousWithinAt
  have hupper : UpperSemicontinuousOn (fun y ↦ v i y - ψ y) (closedBall x r) := by
    simpa only [sub_eq_add_neg] using! ((hv i).mono hballU).add hψcont.neg.upperSemicontinuousOn
  obtain ⟨y, hy, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    ⟨x, mem_closedBall_self hr.le⟩ (isCompact_closedBall x r) hupper
  have hybound : ‖y - x‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm] using hy
  have hyinner : ‖y - x‖ < r := by
    by_contra h
    have hysphere : ‖y - x‖ = r := le_antisymm hybound (le_of_not_gt h)
    have hcompare := hmax (ball_subset_closedBall hzball)
    have hquadlower := hQlower (y - x)
    rw [hysphere] at hquadlower
    have hlimit := (hball hy).2.1
    have hfamily := hle y (hball hy).1 i
    change v i z - ψ z ≤ v i y - (φ y + Q (y - x)) at hcompare
    linarith [sq_pos_of_pos hr]
  have hlocal : IsLocalMaxOn (fun z ↦ v i z - ψ z) U y :=
    (hmax.isLocalMax (closedBall_mem_nhds_of_mem
      (by simpa only [mem_ball, dist_eq_norm] using hyinner))).isLocalMaxOn U
  exact (not_lt_of_ge (htest i y (hball hy).1 ψ (hball hy).2.2.1 hlocal)) (hball hy).2.2.2

end Perron

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nonempty ι]

/-- The upper semicontinuous regularization of a nonempty, locally
uniformly bounded-above family of upper semicontinuous subsolutions is a
subsolution. The Hamiltonian may depend continuously on position and momentum. -/
theorem isSpatialViscositySubsolution_limsup_ciSup {H : E → E → ℝ} {U : Set (E × ℝ)}
    {v : ι → E × ℝ → ℝ} (hH : Continuous (fun q : E × E ↦ H q.1 q.2))
    (hv : ∀ i, UpperSemicontinuousOn (v i) U) (hsub : ∀ i, IsSpatialViscositySubsolution H U (v i))
    (hbound : ∀ x ∈ U, ∃ b, ∀ᶠ y in 𝓝[U] x, ∀ i, v i y ≤ b) :
    IsSpatialViscositySubsolution H U (fun x ↦ limsup (fun y ↦ ⨆ i, v i y) (𝓝[U] x)) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨(hsub i).1, fun z hz φ hφ hcontact ↦ ?_⟩
  have h := Perron.le_zero_of_limsup_ciSup_upper_contacts
    (Q := quadraticSize (E := E)) contDiff_quadraticSize
    (by simp [quadraticSize]) norm_sq_le_quadraticSize (hsub i).1 hv hbound hz hφ hcontact
    (continuous_spatialJetOperator hH).continuousAt
    (fun j y hy ψ hψ hmax ↦ by
      rw [spatialJetOperator_fderiv hψ.differentiableAt_one]
      exact (hsub j).2 y hy ψ hψ hmax)
  simpa only [spatialJetOperator_fderiv hφ.differentiableAt_one] using h

end HamiltonJacobi
