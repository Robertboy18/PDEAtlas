/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Smooth contacts near a differentiable contact

A differentiable upper test need not admit a smooth majorant with the same
jet at the same point. Instead, maximize the function minus its affine
tangent and a small quadratic on a small closed ball. The tangent error
excludes the sphere, and upper semicontinuity gives an interior maximizer.
Both the contact point and the derivative of the new smooth test can be
made arbitrarily close to the original ones.

The quadratic is explicit because a normed product has a maximum norm,
whose square need not be smooth. The assumptions below cover a Hilbert
norm squared and sums of such squares. Compactness of closed balls is the
only finite-dimensional ingredient; it is expressed by `ProperSpace`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology ContDiff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/-- Approximate an upper contact by globally smooth upper tests at nearby
points, with derivatives close in operator norm. The original test only
needs to be differentiable at its contact. The smooth tests touch at the
nearby points, not necessarily at the original contact. -/
theorem exists_contDiff_upper_contact
    {Q : X → ℝ} (hQ : ContDiff ℝ ∞ Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {B : ℝ} (hB : 0 ≤ B) (hQderiv : ∀ y, ‖fderiv ℝ Q y‖ ≤ B * ‖y‖)
    {U : Set X} (hU : IsOpen U) {u φ : X → ℝ}
    (hu : UpperSemicontinuousOn u U) {x : X} (hx : x ∈ U)
    {p : X →L[ℝ] ℝ} (hφ : HasFDerivAt φ p x)
    (hcontact : IsLocalMaxOn (fun y ↦ u y - φ y) U x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ U, ∃ ψ : X → ℝ, ContDiff ℝ ∞ ψ ∧
      IsLocalMaxOn (fun z ↦ u z - ψ z) U y ∧
      ‖y - x‖ < ε ∧ ‖fderiv ℝ ψ y - p‖ < ε := by
  let η := ε / (4 * (B + 1))
  have hη : 0 < η := by positivity
  have hηB : 2 * η * B < ε := by
    have heq : η * (4 * (B + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    linarith [mul_nonneg hη.le hB]
  have hnear : ∀ᶠ z in 𝓝 x,
      z ∈ U ∧ u z - φ z ≤ u x - φ x ∧ ‖φ z - φ x - p (z - x)‖ ≤ η * ‖z - x‖ := by
    filter_upwards [hU.mem_nhds hx, hcontact.isLocalMax (hU.mem_nhds hx),
      hφ.isLittleO.bound hη] with z hz hmax herror using ⟨hz, hmax, herror⟩
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let r := min r₀ (ε / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hε)
  have hball : ∀ z ∈ closedBall x r,
      z ∈ U ∧ u z - φ z ≤ u x - φ x ∧ ‖φ z - φ x - p (z - x)‖ ≤ η * ‖z - x‖ :=
    fun z hz ↦ hball₀ (closedBall_subset_closedBall (min_le_left _ _) hz)
  have hmajor (z : X) (hz : z ∈ closedBall x r) : u z - u x - p (z - x) ≤ η * ‖z - x‖ := by
    linarith [(hball z hz).2.1, (Real.le_norm_self _).trans (hball z hz).2.2]
  let c := 2 * η / r
  have hc : 0 < c := by positivity
  have hcr : c * r = 2 * η := div_mul_cancel₀ _ hr.ne'
  let ψ : X → ℝ := fun z ↦ p (z - x) + c * Q (z - x)
  have hψ : ContDiff ℝ ∞ ψ :=
    (p.contDiff.comp (contDiff_id.sub contDiff_const)).add
      (contDiff_const.mul (hQ.comp (contDiff_id.sub contDiff_const)))
  have hupper : UpperSemicontinuousOn (fun z ↦ u z - ψ z) (closedBall x r) := by
    simpa only [sub_eq_add_neg] using!
      (hu.mono (fun z hz ↦ (hball z hz).1)).add
        hψ.continuous.neg.continuousOn.upperSemicontinuousOn
  obtain ⟨y, hy, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    ⟨x, mem_closedBall_self hr.le⟩ (isCompact_closedBall x r) hupper
  have hybound : ‖y - x‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hyinner : ‖y - x‖ < r := by
    by_contra h
    have hcenter : u x - ψ x ≤ u y - ψ y := (isMaxOn_iff.mp hmax) x (mem_closedBall_self hr.le)
    simp only [ψ, sub_self, map_zero, hQzero, mul_zero, add_zero] at hcenter
    have hquad := mul_le_mul_of_nonneg_left (hQlower (y - x)) hc.le
    have hlin := hmajor y hy
    rw [le_antisymm hybound (not_lt.1 h)] at hquad hlin
    have hcrsq : c * r ^ 2 = 2 * η * r := by rw [sq, ← mul_assoc, hcr]
    linarith [mul_pos hη hr]
  have hψderiv : HasFDerivAt ψ (p + c • fderiv ℝ Q (y - x)) y := by
    have hshift : HasFDerivAt (fun z : X ↦ z - x) (ContinuousLinearMap.id ℝ X) y :=
      (hasFDerivAt_id y).sub_const x
    have hlinear : HasFDerivAt (fun z ↦ p (z - x)) p y := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using!
        p.hasFDerivAt.comp y hshift
    have hquad : HasFDerivAt (fun z ↦ Q (z - x)) (fderiv ℝ Q (y - x)) y := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using!
        ((hQ.differentiable (by simp)) (y - x)).hasFDerivAt.comp y hshift
    exact hlinear.add (hquad.const_mul c)
  refine ⟨y, (hball y hy).1, ψ, hψ, (hmax.isLocalMax (closedBall_mem_nhds_of_mem
    (by simpa only [mem_ball, dist_eq_norm] using hyinner))).isLocalMaxOn U,
    hyinner.trans ((min_le_right _ _).trans_lt (half_lt_self hε)), ?_⟩
  rw [hψderiv.fderiv, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  calc c * ‖fderiv ℝ Q (y - x)‖ ≤ c * (B * r) := by
        gcongr
        exact (hQderiv _).trans (by gcongr)
    _ = 2 * η * B := by rw [← hcr]; ring
    _ < ε := hηB

/-- A continuous first-order inequality verified at every smooth upper
contact also holds at each differentiable upper contact. Continuity is
needed only at the limiting point and derivative. -/
theorem le_zero_of_contDiff_upper_contacts
    {Q : X → ℝ} (hQ : ContDiff ℝ ∞ Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {B : ℝ} (hQderiv : ∀ y, ‖fderiv ℝ Q y‖ ≤ B * ‖y‖)
    {U : Set X} (hU : IsOpen U) {u φ : X → ℝ}
    (hu : UpperSemicontinuousOn u U) {x : X} (hx : x ∈ U)
    {p : X →L[ℝ] ℝ} (hφ : HasFDerivAt φ p x)
    (hcontact : IsLocalMaxOn (fun y ↦ u y - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ} (hF : ContinuousAt F (x, p))
    (htest : ∀ y ∈ U, ∀ ψ : X → ℝ, ContDiff ℝ ∞ ψ →
      IsLocalMaxOn (fun z ↦ u z - ψ z) U y → F (y, fderiv ℝ ψ y) ≤ 0) :
    F (x, p) ≤ 0 := by
  -- On the zero space the constant test touches at `x`; otherwise `hQderiv` gives `0 ≤ B`.
  rcases subsingleton_or_nontrivial X with hX | hX
  · have hp : p = 0 := ContinuousLinearMap.ext fun z ↦ by
      rw [Subsingleton.elim z 0, map_zero, map_zero]
    have h := htest x hx (fun _ ↦ 0) contDiff_const
      (Filter.Eventually.of_forall fun z ↦ by rw [Subsingleton.elim z x])
    simpa [hp] using h
  obtain ⟨y, hy⟩ := exists_ne (0 : X)
  have hB : 0 ≤ B :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hQderiv y)) (norm_pos_iff.mpr hy)
  by_contra h
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_nhds_iff.mp (hF.eventually (eventually_gt_nhds (not_le.1 h)))
  obtain ⟨y, hy, ψ, hψ, hmax, hyclose, hpclose⟩ :=
    exists_contDiff_upper_contact hQ hQzero hQlower hB hQderiv
      hU hu hx hφ hcontact hδ
  have hpair : (y, fderiv ℝ ψ y) ∈ ball (x, p) δ := by
    simpa only [mem_ball, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, max_lt_iff] using! And.intro hyclose hpclose
  exact (not_lt_of_ge (htest y hy ψ hψ hmax)) (hnear hpair)

/-- The lower-contact version follows by negating the function, test, and
inequality. Only lower semicontinuity of the tested function is required. -/
theorem zero_le_of_contDiff_lower_contacts
    {Q : X → ℝ} (hQ : ContDiff ℝ ∞ Q) (hQzero : Q 0 = 0)
    (hQlower : ∀ y, ‖y‖ ^ 2 ≤ Q y)
    {B : ℝ} (hQderiv : ∀ y, ‖fderiv ℝ Q y‖ ≤ B * ‖y‖)
    {U : Set X} (hU : IsOpen U) {u φ : X → ℝ}
    (hu : LowerSemicontinuousOn u U) {x : X} (hx : x ∈ U)
    {p : X →L[ℝ] ℝ} (hφ : HasFDerivAt φ p x)
    (hcontact : IsLocalMinOn (fun y ↦ u y - φ y) U x)
    {F : X × (X →L[ℝ] ℝ) → ℝ} (hF : ContinuousAt F (x, p))
    (htest : ∀ y ∈ U, ∀ ψ : X → ℝ, ContDiff ℝ ∞ ψ →
      IsLocalMinOn (fun z ↦ u z - ψ z) U y → 0 ≤ F (y, fderiv ℝ ψ y)) :
    0 ≤ F (x, p) := by
  have huneg : UpperSemicontinuousOn (fun y ↦ -u y) U :=
    (continuous_neg : Continuous (fun t : ℝ ↦ -t)).comp_lowerSemicontinuousOn_antitone
      hu (fun _ _ hab ↦ neg_le_neg hab)
  have hmax : IsLocalMaxOn (fun y ↦ -u y - -φ y) U x := by
    filter_upwards [hcontact] with y hy
    linarith
  have hFneg : ContinuousAt (fun q : X × (X →L[ℝ] ℝ) ↦ -F (q.1, -q.2)) (x, -p) := by
    have hmap : ContinuousAt (fun q : X × (X →L[ℝ] ℝ) ↦ (q.1, -q.2)) (x, -p) :=
      continuousAt_fst.prodMk continuousAt_snd.neg
    simpa only [Function.comp_def, Pi.neg_def] using!
      (hF.comp_of_eq hmap (by simp only [neg_neg])).neg
  have htestneg : ∀ y ∈ U, ∀ ψ : X → ℝ, ContDiff ℝ ∞ ψ →
      IsLocalMaxOn (fun z ↦ -u z - ψ z) U y → -F (y, -fderiv ℝ ψ y) ≤ 0 := by
    intro y hy ψ hψ hupper
    have hnonneg := htest y hy (fun z ↦ -ψ z) hψ.neg (by
      filter_upwards [hupper] with z hz
      linarith)
    change 0 ≤ F (y, fderiv ℝ (-ψ) y) at hnonneg
    rw [((hψ.differentiable (by simp)) y).hasFDerivAt.neg.fderiv] at hnonneg
    exact neg_nonpos.mpr hnonneg
  simpa only [neg_neg, neg_nonpos] using le_zero_of_contDiff_upper_contacts hQ hQzero hQlower
    hQderiv hU huneg hx hφ.neg hmax hFneg htestneg

end PDE.Analysis

end
