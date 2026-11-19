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
# Vanishing perturbations at smooth contacts

Suppose the inequality for an approximating function has an error
`εₙ G(ψ)(y)` at a smooth test `ψ`. If `εₙ → 0` and `G(ψ)` is continuous
for each fixed test, this perturbation disappears in a locally uniform limit.
In particular, `G` may differentiate the test more than once: no bound on
derivatives of the approximating functions is needed.

A fixed quadratic penalty supplies nearby contacts. Its perturbation is
bounded near the limiting contact, which is enough to pass the inequality.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology ContDiff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- An upper-contact inequality survives a perturbation tending to zero on
every fixed smooth test. The operator is continuous only at the limiting jet. -/
theorem le_zero_of_vanishing_perturbation_at_upper_contacts
    {Q : X → ℝ} (hQ : ContDiff ℝ ∞ Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {U : Set X} (hU : IsOpen U) {v : ℕ → X → ℝ} {u φ : X → ℝ}
    (hv : ∀ n, UpperSemicontinuousOn (v n) U)
    (hvu : TendstoLocallyUniformlyOn v u atTop U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {x : X} (hx : x ∈ U) (hφ : ContDiff ℝ ∞ φ)
    (hcontact : IsLocalMaxOn (fun y ↦ u y - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ}
    (hF : ContinuousAt F (x, fderiv ℝ φ x))
    {G : (X → ℝ) → X → ℝ}
    (hG : ∀ ψ, ContDiff ℝ ∞ ψ → Continuous (G ψ))
    (htest : ∀ n y, y ∈ U → ∀ ψ : X → ℝ, ContDiff ℝ ∞ ψ →
      IsLocalMaxOn (fun z ↦ v n z - ψ z) U y →
        F (y, fderiv ℝ ψ y) ≤ ε n * G ψ y) :
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
  have hψ : ContDiff ℝ ∞ ψ := hφ.add (hQ.comp (contDiff_id.sub contDiff_const))
  have hquad : HasFDerivAt (fun y : X ↦ Q (y - x)) (0 : X →L[ℝ] ℝ) x := by
    have hd : HasFDerivAt Q (0 : X →L[ℝ] ℝ) (id x - x) := by
      simpa only [id_eq, sub_self, hQderiv] using
        ((hQ.differentiable (by simp)) 0).hasFDerivAt
    have h := hd.comp x (f := fun y : X ↦ y - x)
      ((hasFDerivAt_id x).sub_const x)
    simpa only [Function.comp_def, id_eq,
      ContinuousLinearMap.zero_comp] using h
  have hψderiv : fderiv ℝ ψ x = fderiv ℝ φ x := by
    simpa only [add_zero] using
      (((hφ.differentiable (by simp)) x).hasFDerivAt.fun_add hquad).fderiv
  have hjet : ContinuousAt (fun y ↦ (y, fderiv ℝ ψ y)) x :=
    continuousAt_id.prodMk (hψ.continuous_fderiv (by simp)).continuousAt
  have hres : ContinuousAt (fun y ↦ F (y, fderiv ℝ ψ y)) x :=
    hF.comp_of_eq hjet (by rw [hψderiv])
  let M := |G ψ x| + 1
  have hnear : ∀ᶠ y in 𝓝 x,
      y ∈ U ∧ u y - φ y ≤ u x - φ x ∧
        c < F (y, fderiv ℝ ψ y) ∧ |G ψ y| < M := by
    have hpositive := hres.eventually (eventually_gt_nhds
      (show c < F (x, fderiv ℝ ψ x) by rw [hψderiv]; exact hcF))
    have hbound := (hG ψ hψ).abs.continuousAt.eventually
      (eventually_lt_nhds (show |G ψ x| < M by dsimp [M]; linarith))
    filter_upwards [hU.mem_nhds hx, hcontact.isLocalMax (hU.mem_nhds hx),
      hpositive, hbound] with y hy hmax hgreater hbounded
    exact ⟨hy, hmax, hgreater, hbounded⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hballU : closedBall x r ⊆ U := fun y hy ↦ (hball hy).1
  have hcontacts := eventually_exists_upper_contact_of_quadratic_penalty
    hQzero hQlower hr hballU hv hvu hψ.continuous.continuousOn
      (fun y hy ↦ (hball hy).2.1)
  have hsmall : Tendsto (fun n ↦ |ε n| * M) atTop (𝓝 0) := by
    simpa only [abs_zero, zero_mul] using hε.abs.mul_const M
  obtain ⟨n, ⟨y, hyball, hlocal⟩, hεn⟩ :=
    (hcontacts.and (hsmall.eventually (eventually_lt_nhds hc))).exists
  have hy := ball_subset_closedBall hyball
  have hle := htest n y (hball hy).1 ψ hψ hlocal
  have herror : ε n * G ψ y ≤ |ε n| * M :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left (hball hy).2.2.2.le (abs_nonneg _)))
  exact (not_lt_of_ge (hle.trans herror)) (hεn.trans (hball hy).2.2.1)

/-- The lower-contact version of vanishing perturbation stability follows
by negating the functions, the operator and the test perturbation. -/
theorem zero_le_of_vanishing_perturbation_at_lower_contacts
    {Q : X → ℝ} (hQ : ContDiff ℝ ∞ Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {U : Set X} (hU : IsOpen U) {v : ℕ → X → ℝ} {u φ : X → ℝ}
    (hv : ∀ n, LowerSemicontinuousOn (v n) U)
    (hvu : TendstoLocallyUniformlyOn v u atTop U)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {x : X} (hx : x ∈ U) (hφ : ContDiff ℝ ∞ φ)
    (hcontact : IsLocalMinOn (fun y ↦ u y - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ}
    (hF : ContinuousAt F (x, fderiv ℝ φ x))
    {G : (X → ℝ) → X → ℝ}
    (hG : ∀ ψ, ContDiff ℝ ∞ ψ → Continuous (G ψ))
    (htest : ∀ n y, y ∈ U → ∀ ψ : X → ℝ, ContDiff ℝ ∞ ψ →
      IsLocalMinOn (fun z ↦ v n z - ψ z) U y →
        ε n * G ψ y ≤ F (y, fderiv ℝ ψ y)) :
    0 ≤ F (x, fderiv ℝ φ x) := by
  have hvneg : ∀ n, UpperSemicontinuousOn (fun y ↦ -v n y) U := fun n ↦
    (continuous_neg : Continuous (fun t : ℝ ↦ -t)).comp_lowerSemicontinuousOn_antitone
      (hv n) (fun _ _ hab ↦ neg_le_neg hab)
  have hmax : IsLocalMaxOn (fun y ↦ -u y - -φ y) U x := by
    filter_upwards [hcontact] with y hy
    linarith
  have hφneg : fderiv ℝ (fun y ↦ -φ y) x = -fderiv ℝ φ x :=
    ((hφ.differentiable (by simp)) x).hasFDerivAt.neg.fderiv
  have hFneg : ContinuousAt (fun q : X × (X →L[ℝ] ℝ) ↦ -F (q.1, -q.2))
      (x, fderiv ℝ (fun y ↦ -φ y) x) := by
    rw [hφneg]
    have hmap : ContinuousAt (fun q : X × (X →L[ℝ] ℝ) ↦ (q.1, -q.2))
        (x, -fderiv ℝ φ x) := continuousAt_fst.prodMk continuousAt_snd.neg
    simpa only [Function.comp_def, Pi.neg_def] using!
      (hF.comp_of_eq hmap (by simp only [neg_neg])).neg
  have htestneg : ∀ n y, y ∈ U → ∀ ψ : X → ℝ, ContDiff ℝ ∞ ψ →
      IsLocalMaxOn (fun z ↦ -v n z - ψ z) U y →
        -F (y, -fderiv ℝ ψ y) ≤ ε n * (-G (-ψ) y) := by
    intro n y hy ψ hψ hupper
    have hlower : IsLocalMinOn (fun z ↦ v n z - -ψ z) U y := by
      filter_upwards [hupper] with z hz
      linarith
    have h := htest n y hy (-ψ) hψ.neg hlower
    rw [((hψ.differentiable (by simp)) y).hasFDerivAt.neg.fderiv] at h
    linarith
  have h := le_zero_of_vanishing_perturbation_at_upper_contacts
    hQ hQzero hQlower hU hvneg hvu.neg hε hx hφ.neg hmax hFneg
      (G := fun ψ y ↦ -G (-ψ) y) (fun ψ hψ ↦ (hG (-ψ) hψ.neg).neg) htestneg
  simpa only [hφneg, neg_neg, neg_nonpos] using h

end PDE.Analysis
