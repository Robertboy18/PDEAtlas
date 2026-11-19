/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import PDE.Analysis.Calculus.ContactStability.Quadratic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First-order inequalities under locally uniform limits

A local upper contact with the limit need not remain a contact with any
approximating function. Adding a quadratic penalty makes the contact strict.
On a small closed ball, uniform convergence then keeps a maximum of the
approximating difference away from the boundary. This gives an actual nearby
contact where its first-order inequality applies.

The upper result requires upper semicontinuity of the approximants; the
lower result requires lower semicontinuity. No semicontinuity assumption on
the limit is needed for these individual contact inequalities. The errors
in the approximating inequalities may tend to zero through either sign.

The domain is any open subset of a proper real normed space admitting a
`C¹` quadratic lower bound. Supplying that quadratic explicitly also covers
products equipped with the maximum norm, whose squared norm is not smooth.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology ContDiff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- First-order upper-contact inequalities with errors tending to zero pass
to a locally uniform limit. The operator need only be continuous at the
particular limiting point and derivative being tested. -/
theorem le_zero_of_tendstoLocallyUniformlyOn_upper_contacts
    {Q : X → ℝ} (hQ : ContDiff ℝ 1 Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {U : Set X} (hU : IsOpen U) {v : ℕ → X → ℝ} {u φ : X → ℝ}
    (hv : ∀ n, UpperSemicontinuousOn (v n) U)
    (hvu : TendstoLocallyUniformlyOn v u atTop U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {x : X} (hx : x ∈ U) (hφ : ContDiffAt ℝ 1 φ x)
    (hcontact : IsLocalMaxOn (fun y ↦ u y - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ}
    (hF : ContinuousAt F (x, fderiv ℝ φ x))
    (htest : ∀ n y, y ∈ U → ∀ ψ : X → ℝ, ContDiffAt ℝ 1 ψ y →
      IsLocalMaxOn (fun z ↦ v n z - ψ z) U y →
        F (y, fderiv ℝ ψ y) ≤ ε n) :
    F (x, fderiv ℝ φ x) ≤ 0 := by
  by_contra hnot
  have hpos : 0 < F (x, fderiv ℝ φ x) := lt_of_not_ge hnot
  let c := F (x, fderiv ℝ φ x) / 2
  have hc : 0 < c := half_pos hpos
  have hcF : c < F (x, fderiv ℝ φ x) := half_lt_self hpos
  have hQmin : IsLocalMin Q 0 := by
    filter_upwards [] with y
    rw [hQzero]
    exact (sq_nonneg ‖y‖).trans (hQlower y)
  have hQderiv : fderiv ℝ Q 0 = 0 := hQmin.fderiv_eq_zero
  let ψ : X → ℝ := fun y ↦ φ y + Q (y - x)
  have hψ : ContDiffAt ℝ 1 ψ x :=
    hφ.add (hQ.contDiffAt.comp x (contDiffAt_id.sub contDiffAt_const))
  have hquad : HasFDerivAt (fun y : X ↦ Q (y - x)) (0 : X →L[ℝ] ℝ) x := by
    have h := (hQ.contDiffAt.differentiableAt_one.hasFDerivAt).comp x
      ((hasFDerivAt_id x).sub_const x)
    simpa only [Function.comp_def, id_eq, sub_self, hQderiv,
      ContinuousLinearMap.zero_comp]
      using h
  have hψderiv : fderiv ℝ ψ x = fderiv ℝ φ x := by
    simpa only [add_zero] using (hφ.differentiableAt_one.hasFDerivAt.fun_add hquad).fderiv
  have hjet : ContinuousAt (fun y ↦ (y, fderiv ℝ ψ y)) x :=
    continuousAt_id.prodMk (hψ.continuousAt_fderiv (by simp))
  have hres : ContinuousAt (fun y ↦ F (y, fderiv ℝ ψ y)) x := by
    exact hF.comp_of_eq hjet (by rw [hψderiv])
  have hnear : ∀ᶠ y in 𝓝 x,
      y ∈ U ∧ u y - φ y ≤ u x - φ x ∧ ContDiffAt ℝ 1 ψ y ∧
        c < F (y, fderiv ℝ ψ y) := by
    have hpositive := hres.eventually (eventually_gt_nhds
      (show c < F (x, fderiv ℝ ψ x) by rw [hψderiv]; exact hcF))
    filter_upwards [hU.mem_nhds hx, hcontact.isLocalMax (hU.mem_nhds hx),
      hψ.eventually (by simp), hpositive] with y hy hmax hdiff hgreater
    exact ⟨hy, hmax, hdiff, hgreater⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hballU : closedBall x r ⊆ U := fun y hy ↦ (hball hy).1
  have hψcont : ContinuousOn ψ (closedBall x r) :=
    fun y hy ↦ (hball hy).2.2.1.continuousAt.continuousWithinAt
  have hcontacts := eventually_exists_upper_contact_of_quadratic_penalty
    hQzero hQlower hr hballU hv hvu hψcont (fun y hy ↦ (hball hy).2.1)
  obtain ⟨n, ⟨y, hyball, hlocal⟩, hεn⟩ :=
    (hcontacts.and (hε.eventually (eventually_lt_nhds hc))).exists
  have hy := ball_subset_closedBall hyball
  have hle := htest n y (hball hy).1 ψ (hball hy).2.2.1 hlocal
  exact (not_lt_of_ge hle) (hεn.trans (hball hy).2.2.2)

/-- Lower-contact inequalities are stable under locally uniform convergence
of lower semicontinuous functions, with errors tending to zero. Negating
both the functions and the first-order operator reduces this to upper contacts. -/
theorem zero_le_of_tendstoLocallyUniformlyOn_lower_contacts
    {Q : X → ℝ} (hQ : ContDiff ℝ 1 Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {U : Set X} (hU : IsOpen U) {v : ℕ → X → ℝ} {u φ : X → ℝ}
    (hv : ∀ n, LowerSemicontinuousOn (v n) U)
    (hvu : TendstoLocallyUniformlyOn v u atTop U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {x : X} (hx : x ∈ U) (hφ : ContDiffAt ℝ 1 φ x)
    (hcontact : IsLocalMinOn (fun y ↦ u y - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ}
    (hF : ContinuousAt F (x, fderiv ℝ φ x))
    (htest : ∀ n y, y ∈ U → ∀ ψ : X → ℝ, ContDiffAt ℝ 1 ψ y →
      IsLocalMinOn (fun z ↦ v n z - ψ z) U y →
        -ε n ≤ F (y, fderiv ℝ ψ y)) :
    0 ≤ F (x, fderiv ℝ φ x) := by
  have hvneg : ∀ n, UpperSemicontinuousOn (fun y ↦ -v n y) U := fun n ↦
    (continuous_neg : Continuous (fun t : ℝ ↦ -t)).comp_lowerSemicontinuousOn_antitone
      (hv n) (fun _ _ hab ↦ neg_le_neg hab)
  have hconvneg : TendstoLocallyUniformlyOn (fun n y ↦ -v n y)
      (fun y ↦ -u y) atTop U := hvu.neg
  have hmax : IsLocalMaxOn (fun y ↦ -u y - -φ y) U x := by
    filter_upwards [hcontact] with y hy
    linarith
  have hφneg : fderiv ℝ (fun y ↦ -φ y) x = -fderiv ℝ φ x :=
    hφ.differentiableAt_one.hasFDerivAt.neg.fderiv
  have hFneg : ContinuousAt (fun q : X × (X →L[ℝ] ℝ) ↦ -F (q.1, -q.2))
      (x, fderiv ℝ (fun y ↦ -φ y) x) := by
    rw [hφneg]
    have hmap : ContinuousAt (fun q : X × (X →L[ℝ] ℝ) ↦ (q.1, -q.2))
        (x, -fderiv ℝ φ x) := continuousAt_fst.prodMk continuousAt_snd.neg
    simpa only [Function.comp_def, Pi.neg_def] using!
      (hF.comp_of_eq hmap (by simp only [neg_neg])).neg
  have htestneg : ∀ n y, y ∈ U → ∀ ψ : X → ℝ, ContDiffAt ℝ 1 ψ y →
      IsLocalMaxOn (fun z ↦ -v n z - ψ z) U y →
        -F (y, -fderiv ℝ ψ y) ≤ ε n := by
    intro n y hy ψ hψ hupper
    have hlower : IsLocalMinOn (fun z ↦ v n z - -ψ z) U y := by
      filter_upwards [hupper] with z hz
      linarith
    have h := htest n y hy (fun z ↦ -ψ z) hψ.neg hlower
    change -ε n ≤ F (y, fderiv ℝ (-ψ) y) at h
    rw [hψ.differentiableAt_one.hasFDerivAt.neg.fderiv] at h
    linarith
  have h := le_zero_of_tendstoLocallyUniformlyOn_upper_contacts hQ hQzero hQlower
    hU hvneg hconvneg hε hx hφ.neg hmax hFneg htestneg
  simpa only [hφneg, neg_neg, neg_nonpos] using h

end PDE.Analysis

end
