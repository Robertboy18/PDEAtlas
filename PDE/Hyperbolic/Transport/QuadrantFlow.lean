/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import PDE.Analysis.Evolution.ODE.Nonautonomous.Lipschitz

/-!
# Characteristics of fields tangent to the boundary of an orthant

Let `S` be a set of coordinates of `EuclideanSpace ℝ ι`. The closed orthant `closedOrthant S` is
`{x | 0 ≤ x j for j ∈ S}` and the open orthant `openOrthant S` is `{x | 0 < x j for j ∈ S}`; for
`ι = Fin 2` and `S = univ` they are the closed and the open quadrant `ℝ²₊₊`, for `S = {1}` the
closed and the open upper half-plane. A time-dependent velocity `v` that is continuous in time,
Lipschitz on the closed orthant uniformly in time, and tangent to its faces (`v t x j = 0` when
`x j = 0`) has a global flow on any finite time interval, and the flow maps the closed orthant
onto itself and the open orthant onto itself. The velocity is only assumed on the closed orthant
and on the time interval: it is extended by the projection `orthantClamp S` onto the closed
orthant and by clamping the time, and the characteristics of the extension never leave the closed
orthant.

This is the flow used by Chen and Hou, Part I, Lemmas A.1 and A.2, for the transport field
`b = c̄_l x + ū + u(ω)` on the quadrant, and for the two-point field `(b(x), b(z))` on the
product of two quadrants.

## Main results

* `eqOn_zero_of_abs_deriv_le`, `pos_of_abs_deriv_le`, `nonneg_of_abs_deriv_le`: a real function
  with `|y'| ≤ K |y|` that vanishes at one time vanishes everywhere, and otherwise keeps its sign.
* `IsTangentLipschitzField`: the hypotheses on the velocity.
* `IsTangentLipschitzField.exists_characteristic`: the forward characteristic from a point of the
  closed orthant stays in the closed orthant, and in the open orthant if it starts there.
* `IsTangentLipschitzField.exists_backward_characteristic`: every point of the closed (open)
  orthant at every time is the endpoint of a characteristic that stays in the closed (open)
  orthant on the whole earlier interval.
* `IsTangentLipschitzField.eqOn_of_characteristic`, `eqOn_of_characteristic_of_right`:
  uniqueness forward and backward.
* `IsTangentLipschitzField.exists_flow`: the flow map `Φ t`, with `Φ t₀ = id`, is injective on the
  closed orthant and maps the closed orthant onto itself and the open orthant onto itself.
* `IsTangentLipschitzField.exists_backward_pair_characteristic`: the two-point version for the
  field `(v t x, v t z)` on the product of two orthants; distinct endpoints give characteristics
  that never meet.
* `IsTangentLipschitzField.comp_add_const`: the field shifted in time.

## References

* J. Chen and T. Y. Hou, *Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis*, arXiv:2210.07191, Appendix A.
  <https://arxiv.org/abs/2210.07191>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace PDE.Hyperbolic.Transport

/-! ### Sign preservation for `|y'| ≤ K |y|` -/

section Sign

variable {y y' : ℝ → ℝ} {a b K : ℝ}

/-- A real function on `[a, b]` with `|y'| ≤ K |y|` that vanishes at one time vanishes on the
whole interval (Grönwall's inequality forward and backward from that time). -/
theorem eqOn_zero_of_abs_deriv_le (hy : ∀ s ∈ Icc a b, HasDerivAt y (y' s) s)
    (hK : ∀ s ∈ Icc a b, |y' s| ≤ K * |y s|) {r : ℝ} (hr : r ∈ Icc a b) (hzero : y r = 0) :
    EqOn y 0 (Icc a b) := by
  have hforward : ∀ s ∈ Icc r b, y s = 0 := by
    have hsub : Icc r b ⊆ Icc a b := Icc_subset_Icc_left hr.1
    intro s hs
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := y) (f' := y') (δ := 0)
      (K := K) (ε := 0) (a := r) (b := b)
      (fun s hs ↦ (hy s (hsub hs)).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hy s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (by simp [hzero])
      (fun s hs ↦ by
        simpa only [Real.norm_eq_abs, add_zero] using hK s (hsub (Ico_subset_Icc_self hs)))
      s hs
    rw [gronwallBound_ε0_δ0] at h
    exact norm_le_zero_iff.mp h
  have hbackward : ∀ s ∈ Icc a r, y s = 0 := by
    have hsub : ∀ s ∈ Icc (-r) (-a), -s ∈ Icc a b := fun s hs ↦
      ⟨le_neg.mp hs.2, (neg_le.mp hs.1).trans hr.2⟩
    intro s hs
    have hs' : -s ∈ Icc (-r) (-a) := ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s ↦ y (-s))
      (f' := fun s ↦ -y' (-s)) (δ := 0) (K := K) (ε := 0) (a := -r) (b := -a)
      (fun s hs ↦ ((hy (-s) (hsub s hs)).continuousAt.comp
        continuous_neg.continuousAt).continuousWithinAt)
      (fun s hs ↦ by
        have h := (hy (-s) (hsub s (Ico_subset_Icc_self hs))).comp s (hasDerivAt_neg s)
        simpa [Function.comp_def] using h.hasDerivWithinAt)
      (by simp [hzero])
      (fun s hs ↦ by
        simpa only [Real.norm_eq_abs, add_zero, abs_neg] using
          hK (-s) (hsub s (Ico_subset_Icc_self hs)))
      (-s) hs'
    rw [gronwallBound_ε0_δ0, neg_neg] at h
    exact norm_le_zero_iff.mp h
  intro s hs
  rcases le_total s r with hsr | hrs
  · exact hbackward s ⟨hs.1, hsr⟩
  · exact hforward s ⟨hrs, hs.2⟩

/-- A real function on `[a, b]` with `|y'| ≤ K |y|` that is positive at one time is positive on
the whole interval. -/
theorem pos_of_abs_deriv_le (hy : ∀ s ∈ Icc a b, HasDerivAt y (y' s) s)
    (hK : ∀ s ∈ Icc a b, |y' s| ≤ K * |y s|) {r : ℝ} (hr : r ∈ Icc a b) (hpos : 0 < y r) :
    ∀ s ∈ Icc a b, 0 < y s := by
  intro s hs
  by_contra hneg
  have hcont : ContinuousOn y (uIcc s r) := fun u hu ↦
    (hy u (uIcc_subset_Icc hs hr hu)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hyc⟩ := intermediate_value_uIcc hcont
    (show (0 : ℝ) ∈ uIcc (y s) (y r) from mem_uIcc.mpr (Or.inl ⟨le_of_not_gt hneg, hpos.le⟩))
  have hzero := eqOn_zero_of_abs_deriv_le hy hK (uIcc_subset_Icc hs hr hc) hyc hr
  exact hpos.ne' hzero

/-- A real function on `[a, b]` with `|y'| ≤ K |y|` that is nonnegative at one time is
nonnegative on the whole interval. -/
theorem nonneg_of_abs_deriv_le (hy : ∀ s ∈ Icc a b, HasDerivAt y (y' s) s)
    (hK : ∀ s ∈ Icc a b, |y' s| ≤ K * |y s|) {r : ℝ} (hr : r ∈ Icc a b) (hnonneg : 0 ≤ y r) :
    ∀ s ∈ Icc a b, 0 ≤ y s := by
  rcases hnonneg.lt_or_eq with hpos | hzero
  · exact fun s hs ↦ (pos_of_abs_deriv_le hy hK hr hpos s hs).le
  · exact fun s hs ↦ (eqOn_zero_of_abs_deriv_le hy hK hr hzero.symm hs).ge

end Sign

/-! ### Orthants -/

section Orthant

variable {ι : Type*} {S : Set ι}

/-- The closed orthant `{x | 0 ≤ x j for j ∈ S}`. -/
def closedOrthant (S : Set ι) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ j ∈ S, 0 ≤ x j}

/-- The open orthant `{x | 0 < x j for j ∈ S}`. -/
def openOrthant (S : Set ι) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ j ∈ S, 0 < x j}

/-- The open orthant lies in the closed orthant. -/
theorem openOrthant_subset_closedOrthant : openOrthant S ⊆ closedOrthant S :=
  fun _ hx j hj ↦ (hx j hj).le

open Classical in
/-- The nearest point of the closed orthant: the coordinates in `S` are replaced by their
positive parts. -/
def orthantClamp (S : Set ι) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun j ↦ if j ∈ S then max (x j) 0 else x j

/-- A coordinate in `S` of the clamped point is the positive part of that coordinate. -/
theorem orthantClamp_apply_of_mem {j : ι} (hj : j ∈ S) (x : EuclideanSpace ℝ ι) :
    orthantClamp S x j = max (x j) 0 := by
  simp [orthantClamp, hj]

/-- A coordinate outside `S` is not changed by the clamp. -/
theorem orthantClamp_apply_of_notMem {j : ι} (hj : j ∉ S) (x : EuclideanSpace ℝ ι) :
    orthantClamp S x j = x j := by
  simp [orthantClamp, hj]

/-- The clamped point lies in the closed orthant. -/
theorem orthantClamp_mem (x : EuclideanSpace ℝ ι) : orthantClamp S x ∈ closedOrthant S :=
  fun j hj ↦ by rw [orthantClamp_apply_of_mem hj]; exact le_max_right _ _

/-- The clamp fixes every point of the closed orthant. -/
theorem orthantClamp_of_mem {x : EuclideanSpace ℝ ι} (hx : x ∈ closedOrthant S) :
    orthantClamp S x = x := by
  ext j
  by_cases hj : j ∈ S
  · rw [orthantClamp_apply_of_mem hj, max_eq_left (hx j hj)]
  · rw [orthantClamp_apply_of_notMem hj]

variable [Fintype ι]

/-- The projection onto the closed orthant is `1`-Lipschitz. -/
theorem lipschitzWith_orthantClamp (S : Set ι) : LipschitzWith 1 (orthantClamp S) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  gcongr with j
  by_cases hj : j ∈ S
  · simp only [orthantClamp_apply_of_mem hj, Real.dist_eq]
    exact abs_max_sub_max_le_abs _ _ _
  · simp only [orthantClamp_apply_of_notMem hj, le_refl]

/-- A field that is `K`-Lipschitz on the closed orthant and tangent to the face `x j = 0`
satisfies `|w(clamp x) j| ≤ K |x j|` everywhere. -/
theorem abs_apply_orthantClamp_le {w : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {K : ℝ≥0}
    (hw : LipschitzOnWith K w (closedOrthant S))
    (htan : ∀ x ∈ closedOrthant S, ∀ j ∈ S, x j = 0 → w x j = 0) {j : ι} (hj : j ∈ S)
    (x : EuclideanSpace ℝ ι) : |w (orthantClamp S x) j| ≤ K * |x j| := by
  classical
  set y := orthantClamp S x
  set y' := y - EuclideanSpace.single j (y j)
  have hy : y ∈ closedOrthant S := orthantClamp_mem x
  have hy'j : y' j = 0 := by simp [y']
  have hy' : y' ∈ closedOrthant S := by
    intro k hk
    by_cases hkj : k = j
    · subst hkj; rw [hy'j]
    · simpa [y', PiLp.single_apply, hkj] using hy k hk
  have hwy' : w y' j = 0 := htan y' hy' j hj hy'j
  have hdiff : y - y' = EuclideanSpace.single j (y j) := by simp [y']
  calc |w y j| = ‖(w y - w y') j‖ := by simp [hwy']
    _ ≤ ‖w y - w y'‖ := PiLp.norm_apply_le _ j
    _ ≤ K * ‖y - y'‖ := hw.norm_sub_le hy hy'
    _ = K * |max (x j) 0| := by
        rw [hdiff, PiLp.norm_single, Real.norm_eq_abs, orthantClamp_apply_of_mem hj]
    _ ≤ K * |x j| := by
        have h : |max (x j) 0| ≤ |x j| := by
          rw [abs_of_nonneg (le_max_right _ _)]
          exact max_le (le_abs_self _) (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left h K.coe_nonneg

end Orthant

/-! ### Flows of tangent fields -/

section Flow

variable {ι : Type*} [Fintype ι] {S : Set ι}

/-- The hypotheses on a velocity `v t x` on the closed orthant over the times `[t₀, T]`:
continuity in time, a uniform Lipschitz constant `K` in space, and tangency to every face
`x j = 0`, `j ∈ S` (the normal component vanishes there). Linear growth follows from the
Lipschitz bound. Nothing is assumed outside the closed orthant or outside `[t₀, T]`. The
characteristics from the open orthant never reach its boundary, but the hypotheses involve the
values of `v` on the faces: for a velocity given in the open orthant these should be its
continuous extension, which exists by the Lipschitz bound. -/
structure IsTangentLipschitzField (S : Set ι) (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (t₀ T : ℝ) (K : ℝ≥0) : Prop where
  /-- Continuity in time at every point of the closed orthant. -/
  continuousOn : ∀ x ∈ closedOrthant S, ContinuousOn (fun t ↦ v t x) (Icc t₀ T)
  /-- A uniform Lipschitz bound on the closed orthant. -/
  lipschitzOnWith : ∀ t ∈ Icc t₀ T, LipschitzOnWith K (v t) (closedOrthant S)
  /-- Tangency to the faces of the closed orthant. -/
  tangent : ∀ t ∈ Icc t₀ T, ∀ x ∈ closedOrthant S, ∀ j ∈ S, x j = 0 → v t x j = 0

namespace IsTangentLipschitzField

variable {v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {t₀ T : ℝ} {K : ℝ≥0}

/-- The clamped time `max t₀ (min t T)`. -/
private def clampTime (t₀ T t : ℝ) : ℝ :=
  max t₀ (min t T)

/-- For `t₀ ≤ T` the clamped time lies in `[t₀, T]`. -/
private theorem clampTime_mem (hT : t₀ ≤ T) (t : ℝ) : clampTime t₀ T t ∈ Icc t₀ T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-- The clamp fixes every time of `[t₀, T]`. -/
private theorem clampTime_of_mem {t : ℝ} (ht : t ∈ Icc t₀ T) : clampTime t₀ T t = t := by
  rw [clampTime, min_eq_left ht.2, max_eq_right ht.1]

/-- The clamped time depends continuously on the time. -/
private theorem continuous_clampTime : Continuous (clampTime t₀ T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The extension of `v` to all times and all points, by clamping both. -/
private def extend (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (S : Set ι) (t₀ T t : ℝ)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  v (clampTime t₀ T t) (orthantClamp S x)

omit [Fintype ι] in
/-- On `[t₀, T]` times the closed orthant the extended field equals `v`. -/
private theorem extend_of_mem {t : ℝ} (ht : t ∈ Icc t₀ T) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ closedOrthant S) : extend v S t₀ T t x = v t x := by
  rw [extend, clampTime_of_mem ht, orthantClamp_of_mem hx]

/-- The extended field is continuous in time at every point. -/
private theorem continuous_extend (hv : IsTangentLipschitzField S v t₀ T K) (hT : t₀ ≤ T)
    (x : EuclideanSpace ℝ ι) : Continuous fun t ↦ extend v S t₀ T t x :=
  (hv.continuousOn _ (orthantClamp_mem x)).comp_continuous continuous_clampTime
    (clampTime_mem hT)

/-- At every time the extended field is `K`-Lipschitz on the whole space. -/
private theorem lipschitzWith_extend (hv : IsTangentLipschitzField S v t₀ T K) (hT : t₀ ≤ T)
    (t : ℝ) : LipschitzWith K (extend v S t₀ T t) := by
  have h := (hv.lipschitzOnWith _ (clampTime_mem hT t)).comp
    ((lipschitzWith_orthantClamp S).lipschitzOnWith (s := univ))
    (fun x _ ↦ orthantClamp_mem (S := S) x)
  rw [mul_one] at h
  exact lipschitzOnWith_univ.mp h

/-- The extended field is jointly continuous in `(t, x)`. -/
private theorem continuous_uncurry_extend (hv : IsTangentLipschitzField S v t₀ T K)
    (hT : t₀ ≤ T) : Continuous (Function.uncurry (extend v S t₀ T)) :=
  continuous_prod_of_continuous_lipschitzWith' _ K (lipschitzWith_extend hv hT)
    (continuous_extend hv hT)

/-- Along an integral curve of the extended field every coordinate in `S` satisfies
`|y'| ≤ K |y|`. -/
private theorem abs_deriv_coord_le (hv : IsTangentLipschitzField S v t₀ T K) (hT : t₀ ≤ T)
    {γ : ℝ → EuclideanSpace ℝ ι} {a b : ℝ}
    (hγ : ∀ s ∈ Icc a b, HasDerivAt γ (extend v S t₀ T s (γ s)) s) {j : ι} (hj : j ∈ S) :
    (∀ s ∈ Icc a b, HasDerivAt (fun s ↦ γ s j) (extend v S t₀ T s (γ s) j) s) ∧
      ∀ s ∈ Icc a b, |extend v S t₀ T s (γ s) j| ≤ K * |γ s j| := by
  refine ⟨fun s hs ↦ ?_, fun s _ ↦ ?_⟩
  · exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt s (hγ s hs)
  · exact abs_apply_orthantClamp_le (hv.lipschitzOnWith _ (clampTime_mem hT s))
      (hv.tangent _ (clampTime_mem hT s)) hj (γ s)

/-- An integral curve of the extended field that lies in the closed (open) orthant at one time
lies in it at every time of the interval. -/
private theorem mem_of_extend (hv : IsTangentLipschitzField S v t₀ T K) (hT : t₀ ≤ T)
    {γ : ℝ → EuclideanSpace ℝ ι} {a b : ℝ}
    (hγ : ∀ s ∈ Icc a b, HasDerivAt γ (extend v S t₀ T s (γ s)) s) {r : ℝ} (hr : r ∈ Icc a b) :
    (γ r ∈ closedOrthant S → ∀ s ∈ Icc a b, γ s ∈ closedOrthant S) ∧
      (γ r ∈ openOrthant S → ∀ s ∈ Icc a b, γ s ∈ openOrthant S) := by
  constructor
  · intro hmem s hs j hj
    obtain ⟨hd, hK⟩ := abs_deriv_coord_le hv hT hγ hj
    exact nonneg_of_abs_deriv_le hd hK hr (hmem j hj) s hs
  · intro hmem s hs j hj
    obtain ⟨hd, hK⟩ := abs_deriv_coord_le hv hT hγ hj
    exact pos_of_abs_deriv_le hd hK hr (hmem j hj) s hs

/-- **Forward characteristics.** From every point `x₀` of the closed orthant at time `t₀` there
is a characteristic `γ' = v(γ)` on `[t₀, T]` that stays in the closed orthant, and in the open
orthant if `x₀` lies in it. -/
theorem exists_characteristic (hv : IsTangentLipschitzField S v t₀ T K) (hT : t₀ ≤ T)
    {x₀ : EuclideanSpace ℝ ι} (hx₀ : x₀ ∈ closedOrthant S) :
    ∃ γ : ℝ → EuclideanSpace ℝ ι, γ t₀ = x₀ ∧
      (∀ t ∈ Icc t₀ T, γ t ∈ closedOrthant S ∧ HasDerivAt γ (v t (γ t)) t) ∧
      (x₀ ∈ openOrthant S → ∀ t ∈ Icc t₀ T, γ t ∈ openOrthant S) := by
  obtain ⟨γ, -, hγ₀, hγ⟩ := PDE.Analysis.Evolution.exists_eq_hasDerivAt_on_Icc_of_lipschitz
    (F := extend v S t₀ T) (continuous_uncurry_extend hv hT)
    (fun t _ ↦ lipschitzWith_extend hv hT t) ⟨t₀, left_mem_Icc.mpr hT⟩ x₀
  have hmem := mem_of_extend hv hT hγ (left_mem_Icc.mpr hT)
  rw [hγ₀] at hmem
  refine ⟨γ, hγ₀, fun t ht ↦ ⟨hmem.1 hx₀ t ht, ?_⟩, hmem.2⟩
  simpa only [extend_of_mem ht (hmem.1 hx₀ t ht)] using hγ t ht

/-- **Backward characteristics.** Every point `p` of the closed orthant at a time `t ∈ [t₀, T]`
is the endpoint of a characteristic on `[t₀, t]` that stays in the closed orthant, and in the
open orthant if `p` lies in it. -/
theorem exists_backward_characteristic (hv : IsTangentLipschitzField S v t₀ T K)
    {t : ℝ} (ht : t ∈ Icc t₀ T) {p : EuclideanSpace ℝ ι} (hp : p ∈ closedOrthant S) :
    ∃ γ : ℝ → EuclideanSpace ℝ ι, γ t = p ∧
      (∀ s ∈ Icc t₀ t, γ s ∈ closedOrthant S ∧ HasDerivAt γ (v s (γ s)) s) ∧
      (p ∈ openOrthant S → ∀ s ∈ Icc t₀ t, γ s ∈ openOrthant S) := by
  have hT : t₀ ≤ T := ht.1.trans ht.2
  obtain ⟨γ, -, hγt, hγ⟩ := PDE.Analysis.Evolution.exists_eq_hasDerivAt_on_Icc_of_lipschitz
    (F := extend v S t₀ T) (continuous_uncurry_extend hv hT)
    (fun s _ ↦ lipschitzWith_extend hv hT s) ⟨t, right_mem_Icc.mpr ht.1⟩ p
  have hmem := mem_of_extend hv hT hγ (right_mem_Icc.mpr ht.1)
  rw [hγt] at hmem
  have hsub : Icc t₀ t ⊆ Icc t₀ T := Icc_subset_Icc_right ht.2
  refine ⟨γ, hγt, fun s hs ↦ ⟨hmem.1 hp s hs, ?_⟩, hmem.2⟩
  simpa only [extend_of_mem (hsub hs) (hmem.1 hp s hs)] using hγ s hs

/-- **Uniqueness.** Two characteristics in the closed orthant that agree at time `a` agree on
`[a, b] ⊆ [t₀, T]`. -/
theorem eqOn_of_characteristic (hv : IsTangentLipschitzField S v t₀ T K) {a b : ℝ}
    (hab : Icc a b ⊆ Icc t₀ T) {γ γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ s ∈ Icc a b, γ s ∈ closedOrthant S ∧ HasDerivAt γ (v s (γ s)) s)
    (hγ' : ∀ s ∈ Icc a b, γ' s ∈ closedOrthant S ∧ HasDerivAt γ' (v s (γ' s)) s)
    (ha : γ a = γ' a) : EqOn γ γ' (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ closedOrthant S)
    (fun s hs ↦ hv.lipschitzOnWith s (hab (Ico_subset_Icc_self hs)))
    (fun s hs ↦ (hγ s hs).2.continuousAt.continuousWithinAt)
    (fun s hs ↦ (hγ s (Ico_subset_Icc_self hs)).2.hasDerivWithinAt)
    (fun s hs ↦ (hγ s (Ico_subset_Icc_self hs)).1)
    (fun s hs ↦ (hγ' s hs).2.continuousAt.continuousWithinAt)
    (fun s hs ↦ (hγ' s (Ico_subset_Icc_self hs)).2.hasDerivWithinAt)
    (fun s hs ↦ (hγ' s (Ico_subset_Icc_self hs)).1) ha

/-- **Backward uniqueness.** Two characteristics in the closed orthant that agree at time `b`
agree on `[a, b] ⊆ [t₀, T]`. -/
theorem eqOn_of_characteristic_of_right (hv : IsTangentLipschitzField S v t₀ T K) {a b : ℝ}
    (hab : Icc a b ⊆ Icc t₀ T) {γ γ' : ℝ → EuclideanSpace ℝ ι}
    (hγ : ∀ s ∈ Icc a b, γ s ∈ closedOrthant S ∧ HasDerivAt γ (v s (γ s)) s)
    (hγ' : ∀ s ∈ Icc a b, γ' s ∈ closedOrthant S ∧ HasDerivAt γ' (v s (γ' s)) s)
    (hb : γ b = γ' b) : EqOn γ γ' (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_left (s := fun _ ↦ closedOrthant S)
    (fun s hs ↦ hv.lipschitzOnWith s (hab (Ioc_subset_Icc_self hs)))
    (fun s hs ↦ (hγ s hs).2.continuousAt.continuousWithinAt)
    (fun s hs ↦ (hγ s (Ioc_subset_Icc_self hs)).2.hasDerivWithinAt)
    (fun s hs ↦ (hγ s (Ioc_subset_Icc_self hs)).1)
    (fun s hs ↦ (hγ' s hs).2.continuousAt.continuousWithinAt)
    (fun s hs ↦ (hγ' s (Ioc_subset_Icc_self hs)).2.hasDerivWithinAt)
    (fun s hs ↦ (hγ' s (Ioc_subset_Icc_self hs)).1) hb

/-- **The flow.** There is a map `Φ t` with `Φ t₀ = id` such that `t ↦ Φ t x` is the
characteristic from `x` for every `x` in the closed orthant, and for every `t ∈ [t₀, T]` the map
`Φ t` is injective on the closed orthant and sends the closed orthant onto itself and the open
orthant onto itself. -/
theorem exists_flow (hv : IsTangentLipschitzField S v t₀ T K) (hT : t₀ ≤ T) :
    ∃ Φ : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι, (∀ x, Φ t₀ x = x) ∧
      (∀ x ∈ closedOrthant S, ∀ t ∈ Icc t₀ T, HasDerivAt (fun s ↦ Φ s x) (v t (Φ t x)) t) ∧
      ∀ t ∈ Icc t₀ T,
        MapsTo (Φ t) (closedOrthant S) (closedOrthant S) ∧
        SurjOn (Φ t) (closedOrthant S) (closedOrthant S) ∧
        InjOn (Φ t) (closedOrthant S) ∧
        MapsTo (Φ t) (openOrthant S) (openOrthant S) ∧
        SurjOn (Φ t) (openOrthant S) (openOrthant S) := by
  classical
  have hchar (x : EuclideanSpace ℝ ι) (hx : x ∈ closedOrthant S) :=
    exists_characteristic hv hT hx
  let γ (x : EuclideanSpace ℝ ι) : ℝ → EuclideanSpace ℝ ι :=
    if hx : x ∈ closedOrthant S then (hchar x hx).choose else fun _ ↦ x
  have hγ (x : EuclideanSpace ℝ ι) (hx : x ∈ closedOrthant S) :
      γ x t₀ = x ∧
        (∀ t ∈ Icc t₀ T, γ x t ∈ closedOrthant S ∧ HasDerivAt (γ x) (v t (γ x t)) t) ∧
        (x ∈ openOrthant S → ∀ t ∈ Icc t₀ T, γ x t ∈ openOrthant S) := by
    simp only [γ, hx, dite_true]
    exact (hchar x hx).choose_spec
  refine ⟨fun t x ↦ γ x t, fun x ↦ ?_, fun x hx t ht ↦ (hγ x hx).2.1 t ht |>.2, ?_⟩
  · by_cases hx : x ∈ closedOrthant S
    · exact (hγ x hx).1
    · simp [γ, hx]
  intro t ht
  have hsurj (p : EuclideanSpace ℝ ι) (hp : p ∈ closedOrthant S) :
      ∃ x ∈ closedOrthant S, (p ∈ openOrthant S → x ∈ openOrthant S) ∧ γ x t = p := by
    obtain ⟨β, hβt, hβ, hβopen⟩ := exists_backward_characteristic hv ht hp
    have hx : β t₀ ∈ closedOrthant S := (hβ t₀ (left_mem_Icc.mpr ht.1)).1
    refine ⟨β t₀, hx, fun hpo ↦ hβopen hpo t₀ (left_mem_Icc.mpr ht.1), ?_⟩
    have hsub : Icc t₀ t ⊆ Icc t₀ T := Icc_subset_Icc_right ht.2
    have heq := eqOn_of_characteristic hv hsub
      (fun s hs ↦ (hγ (β t₀) hx).2.1 s (hsub hs)) hβ (hγ (β t₀) hx).1
      (right_mem_Icc.mpr ht.1)
    rw [heq, hβt]
  have hsub : Icc t₀ t ⊆ Icc t₀ T := Icc_subset_Icc_right ht.2
  refine ⟨fun x hx ↦ ((hγ x hx).2.1 t ht).1, fun p hp ↦ ?_, fun x hx y hy hxy ↦ ?_,
    fun x hx ↦ ?_, fun p hp ↦ ?_⟩
  · obtain ⟨x, hx, -, hxp⟩ := hsurj p hp
    exact ⟨x, hx, hxp⟩
  · have heq := eqOn_of_characteristic_of_right hv hsub
      (fun s hs ↦ (hγ x hx).2.1 s (hsub hs)) (fun s hs ↦ (hγ y hy).2.1 s (hsub hs)) hxy
      (left_mem_Icc.mpr ht.1)
    rwa [(hγ x hx).1, (hγ y hy).1] at heq
  · exact (hγ x (openOrthant_subset_closedOrthant hx)).2.2 hx t ht
  · obtain ⟨x, -, hxo, hxp⟩ := hsurj p (openOrthant_subset_closedOrthant hp)
    exact ⟨x, hxo hp, hxp⟩

/-- **Two-point characteristics.** For the field `(v t x, v t z)` on the product of two
orthants, every pair `(x, z)` of points of the closed orthant at a time `t ∈ [t₀, T]` is the
endpoint of a pair of characteristics on `[t₀, t]` in the closed orthant, in the open orthant
for each point that lies in it. -/
theorem exists_backward_pair_characteristic (hv : IsTangentLipschitzField S v t₀ T K)
    {t : ℝ} (ht : t ∈ Icc t₀ T) {x z : EuclideanSpace ℝ ι} (hx : x ∈ closedOrthant S)
    (hz : z ∈ closedOrthant S) :
    ∃ γ : ℝ → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, γ t = (x, z) ∧
      (∀ s ∈ Icc t₀ t, (γ s).1 ∈ closedOrthant S ∧ (γ s).2 ∈ closedOrthant S ∧
        HasDerivAt γ (v s (γ s).1, v s (γ s).2) s) ∧
      (x ∈ openOrthant S → ∀ s ∈ Icc t₀ t, (γ s).1 ∈ openOrthant S) ∧
      (z ∈ openOrthant S → ∀ s ∈ Icc t₀ t, (γ s).2 ∈ openOrthant S) ∧
      (x ≠ z → ∀ s ∈ Icc t₀ t, (γ s).1 ≠ (γ s).2) := by
  obtain ⟨X, hXt, hX, hXo⟩ := exists_backward_characteristic hv ht hx
  obtain ⟨Z, hZt, hZ, hZo⟩ := exists_backward_characteristic hv ht hz
  refine ⟨fun s ↦ (X s, Z s), by simp [hXt, hZt], fun s hs ↦
    ⟨(hX s hs).1, (hZ s hs).1, (hX s hs).2.prodMk (hZ s hs).2⟩, hXo, hZo, ?_⟩
  intro hxz s hs hXZ
  have hsub : Icc s t ⊆ Icc t₀ T := Icc_subset_Icc hs.1 ht.2
  have hsub' : Icc s t ⊆ Icc t₀ t := Icc_subset_Icc_left hs.1
  have heq := eqOn_of_characteristic hv hsub (fun u hu ↦ hX u (hsub' hu))
    (fun u hu ↦ hZ u (hsub' hu)) hXZ (right_mem_Icc.mpr hs.2)
  exact hxz (hXt ▸ hZt ▸ heq)

/-- **Shifting time**: a tangent Lipschitz field on `[t₀, T]`, shifted in time by `c`, is a tangent
Lipschitz field on `[t₀ - c, T - c]`. -/
theorem comp_add_const (hv : IsTangentLipschitzField S v t₀ T K) (c : ℝ) :
    IsTangentLipschitzField S (fun t ↦ v (t + c)) (t₀ - c) (T - c) K where
  continuousOn x hx := (hv.continuousOn x hx).comp (continuous_id.add continuous_const).continuousOn
    fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  lipschitzOnWith t ht := hv.lipschitzOnWith (t + c) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  tangent t ht := hv.tangent (t + c) ⟨by linarith [ht.1], by linarith [ht.2]⟩

end IsTangentLipschitzField

end Flow

end PDE.Hyperbolic.Transport
