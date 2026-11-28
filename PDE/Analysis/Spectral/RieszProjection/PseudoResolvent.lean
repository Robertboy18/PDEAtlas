/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Spectral.PseudoResolvent
public import PDE.Analysis.Spectral.RieszProjection.Contour

/-!
# The Riesz projection of a pseudo-resolvent

The Riesz projection `P = (2πi)⁻¹ ∮_{|z - c| = r} R z dz` is usually built from the resolvent of
one operator, on a circle around the origin. Only the first resolvent identity is used, so we
state everything for a pseudo-resolvent `R : ℂ → 𝔸` on an open set `U` that contains the circle
`C(c, r)`, with any centre `c`. This covers the resolvent of an element of a Banach algebra and
the resolvent of an unbounded operator (`LinearPMap.isIdempotentElem_rieszProjection_resolvent`).
The Dunford integral with a scalar weight `g` is `Φ(g) = (2πi)⁻¹ ∮_{C(c, r)} g z R z dz`, and the
Riesz projection is `Φ(1)`. Only circles are treated. For a pseudo-resolvent that is holomorphic
on an open set the integral depends only on the homology class of the contour, but circles are
all the applications need so far.

## Main results

* `dunfordIntegral`, `rieszProjection`: the two integrals, for every family `R : ℂ → 𝔸`, centre
  and radius.
* `rieszProjection_mul_dunfordIntegral`: the product rule `P₁ Φ₂(g) = Φ₁(ĝ)` for two circles in
  `U` such that the closed disc of the first does not meet the second circle.
* `isIdempotentElem_rieszProjection`: for `r > 0` and a pseudo-resolvent on an open set that
  contains the circle, the Riesz projection is idempotent.
* `rieszProjection_mul_rieszProjection_of_disjoint`: the projections for disjoint closed discs
  annihilate each other.
* `dunfordIntegral_eq_smul_add_mul`: the domain rule, which gives `A Φ(g) = Φ(z g) - (2πi)⁻¹ ∮ g`
  for the resolvent of an operator `A`.
* `dunfordIntegral_eq_of_annulus`, `dunfordIntegral_eq_zero`: Cauchy's theorem on an annulus and
  on a disc.
* `rieszIntegral_eq_dunfordIntegral`, `rieszInner_eq_rieszProjection`: the Riesz integral and the
  Riesz projection of an element `a` of a Banach algebra are the case `R = resolvent a`, `c = 0`.

## How it works

For a second circle `C(c₂, r₂)` in `U` that does not meet the closed disc of the first, the
resolvent identity writes `R z R w` on the product of the two circles as `(R z - R w) / (w - z)`.
The part with `R w` is the circle integral, over the first circle, of a function that is
holomorphic on the closed first disc, so it vanishes. What is left is `P₁ Φ₂(g) = Φ₁(ĝ)` with the
Cauchy transform `ĝ z = (2πi)⁻¹ ∮_{C(c₂, r₂)} (w - z)⁻¹ g w dw`. If the first disc lies inside
the second, `ĝ = 1` for `g = 1`, and moving the first circle outward across an annulus in `U`
does not change `P₁`, so `P₁² = P₁`. If the two closed discs are disjoint, `ĝ = 0` for `g = 1`, so
`P₁ P₂ = 0`. For a point `z₀` of `U`, the identity `R z = R z₀ + (z₀ - z) R z₀ R z` gives the
domain rule `Φ(g) = ((2πi)⁻¹ ∮ g) R z₀ + R z₀ Φ((z₀ - z) g)`.
-/

@[expose] public noncomputable section

open Complex Metric Set
open scoped Real

namespace PDE.Analysis.Spectral

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]

/-- The Dunford integral `(2πi)⁻¹ ∮_{|z - c| = r} g z • R z dz` of a family `R` with the scalar
weight `g`. For a pseudo-resolvent `R` this is the contour integral that defines the
holomorphic functional calculus; that it is multiplicative in `g` is not proved here. -/
def dunfordIntegral (R : ℂ → 𝔸) (c : ℂ) (r : ℝ) (g : ℂ → ℂ) : 𝔸 :=
  ((2 * π * I)⁻¹ : ℂ) • ∮ z in C(c, r), g z • R z

/-- The Riesz projection `(2πi)⁻¹ ∮_{|z - c| = r} R z dz` of a family `R` for the circle
`C(c, r)`. For a pseudo-resolvent on an open set that contains the circle, it is idempotent. -/
def rieszProjection (R : ℂ → 𝔸) (c : ℂ) (r : ℝ) : 𝔸 :=
  dunfordIntegral R c r 1

variable {R : ℂ → 𝔸} {U : Set ℂ} {c c₁ c₂ : ℂ} {r r₁ r₂ : ℝ} {g g₁ g₂ : ℂ → ℂ}

omit [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] in
/-- A circle of positive radius lies in every set that contains the closed disc without its
centre. This is how an isolated point of a spectrum gives a circle in the resolvent set. -/
theorem sphere_subset_of_closedBall_sdiff_subset (hr : 0 < r)
    (h : closedBall c r \ {c} ⊆ U) : sphere c r ⊆ U := fun _ hz ↦
  h ⟨sphere_subset_closedBall hz, ne_of_mem_sphere hz hr.ne'⟩

/-- The Riesz projection is `(2πi)⁻¹ ∮_{|z - c| = r} R z dz`. -/
theorem rieszProjection_eq (R : ℂ → 𝔸) (c : ℂ) (r : ℝ) :
    rieszProjection R c r = ((2 * π * I)⁻¹ : ℂ) • ∮ z in C(c, r), R z := by
  simp [rieszProjection, dunfordIntegral]

/-- The Riesz integral of an element of a Banach algebra is the Dunford integral of its
resolvent on a circle centred at `0`. -/
theorem rieszIntegral_eq_dunfordIntegral (a : 𝔸) (r : ℝ) (g : ℂ → ℂ) :
    rieszIntegral a r g = dunfordIntegral (resolvent a) 0 r g :=
  rfl

/-- The Riesz projection of an element of a Banach algebra is the Riesz projection of its
resolvent on a circle centred at `0`. -/
theorem rieszInner_eq_rieszProjection (a : 𝔸) (r : ℝ) :
    rieszInner a r = rieszProjection (resolvent a) 0 r :=
  rieszInner_eq_rieszIntegral a r

/-- The Dunford integral depends only on the weight on the circle. -/
theorem dunfordIntegral_congr (hr : 0 ≤ r) (h : EqOn g₁ g₂ (sphere c r)) :
    dunfordIntegral R c r g₁ = dunfordIntegral R c r g₂ := by
  unfold dunfordIntegral
  congr 1
  exact circleIntegral.integral_congr hr fun z hz ↦ by simp only [h hz]

/-- The Dunford integral with weight `0` vanishes. -/
@[simp]
theorem dunfordIntegral_zero (R : ℂ → 𝔸) (c : ℂ) (r : ℝ) : dunfordIntegral R c r 0 = 0 := by
  simp [dunfordIntegral, circleIntegral]

/-- The Dunford integral is homogeneous in the weight. -/
theorem dunfordIntegral_const_mul (a : ℂ) :
    dunfordIntegral R c r (fun z ↦ a * g z) = a • dunfordIntegral R c r g := by
  unfold dunfordIntegral
  simp only [mul_smul]
  rw [circleIntegral.integral_smul, smul_comm]

/-- The norm bound `‖Φ(g)‖ ≤ r C` when `‖g z • R z‖ ≤ C` on the circle. -/
theorem norm_dunfordIntegral_le (hr : 0 ≤ r) {C : ℝ}
    (h : ∀ z ∈ sphere c r, ‖g z • R z‖ ≤ C) : ‖dunfordIntegral R c r g‖ ≤ r * C :=
  circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr h

/-- For continuous `g` and `R` on the circle, `g z • R z` is circle integrable. -/
theorem circleIntegrable_smul (hr : 0 ≤ r) (hg : ContinuousOn g (sphere c r))
    (hR : ContinuousOn R (sphere c r)) : CircleIntegrable (fun z ↦ g z • R z) c r :=
  (hg.smul hR).circleIntegrable hr

/-- The Dunford integral is additive in continuous weights. -/
theorem dunfordIntegral_add (hr : 0 ≤ r) (hR : ContinuousOn R (sphere c r))
    (hg₁ : ContinuousOn g₁ (sphere c r)) (hg₂ : ContinuousOn g₂ (sphere c r)) :
    dunfordIntegral R c r (fun z ↦ g₁ z + g₂ z) =
      dunfordIntegral R c r g₁ + dunfordIntegral R c r g₂ := by
  unfold dunfordIntegral
  rw [← smul_add, ← circleIntegral.integral_add (circleIntegrable_smul hr hg₁ hR)
    (circleIntegrable_smul hr hg₂ hR)]
  simp only [add_smul]

/-- The Dunford integral is subtractive in continuous weights. -/
theorem dunfordIntegral_sub (hr : 0 ≤ r) (hR : ContinuousOn R (sphere c r))
    (hg₁ : ContinuousOn g₁ (sphere c r)) (hg₂ : ContinuousOn g₂ (sphere c r)) :
    dunfordIntegral R c r (fun z ↦ g₁ z - g₂ z) =
      dunfordIntegral R c r g₁ - dunfordIntegral R c r g₂ := by
  unfold dunfordIntegral
  rw [← smul_sub, ← circleIntegral.integral_sub (circleIntegrable_smul hr hg₁ hR)
    (circleIntegrable_smul hr hg₂ hR)]
  simp only [sub_smul]

/-- `∮_{|z - c| = r} (z - w)⁻¹ dz = 0` for `w` outside the closed disc. -/
theorem circleIntegral_sub_inv_of_notMem_closedBall {w : ℂ} (hr : 0 ≤ r)
    (hw : w ∉ closedBall c r) : (∮ z in C(c, r), (z - w)⁻¹) = 0 := by
  have hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (fun z : ℂ ↦ (z - w)⁻¹) z := fun z hz ↦ by
    have hne : z - w ≠ 0 := sub_ne_zero.mpr fun h ↦ hw (h ▸ hz)
    fun_prop (disch := exact hne)
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    (fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt)
    fun z hz ↦ hd z (ball_subset_closedBall hz.1)

/-- **Cauchy's theorem on an annulus.** For a pseudo-resolvent on an open set that contains the
closed annulus `r₁ ≤ |z - c| ≤ r₂`, and a weight that is holomorphic on the annulus, the Dunford
integrals on the two circles agree. -/
theorem dunfordIntegral_eq_of_annulus (h : IsPseudoResolventOn R U) (hU : IsOpen U)
    (h₀ : 0 < r₁) (hle : r₁ ≤ r₂) (hann : closedBall c r₂ \ ball c r₁ ⊆ U)
    (hg : ∀ z ∈ closedBall c r₂ \ ball c r₁, DifferentiableAt ℂ g z) :
    dunfordIntegral R c r₂ g = dunfordIntegral R c r₁ g := by
  have hd : ∀ z ∈ closedBall c r₂ \ ball c r₁, DifferentiableAt ℂ (fun z ↦ g z • R z) z :=
    fun z hz ↦ (hg z hz).smul (h.differentiableAt (hU.mem_nhds (hann hz)))
  unfold dunfordIntegral
  congr 1
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable h₀ hle countable_empty
    (fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt) fun z hz ↦ hd z ?_
  exact ⟨ball_subset_closedBall hz.1.1, fun hz' ↦ hz.1.2 (ball_subset_closedBall hz')⟩

/-- The Riesz projection does not change across an annulus in `U`. -/
theorem rieszProjection_eq_of_annulus (h : IsPseudoResolventOn R U) (hU : IsOpen U)
    (h₀ : 0 < r₁) (hle : r₁ ≤ r₂) (hann : closedBall c r₂ \ ball c r₁ ⊆ U) :
    rieszProjection R c r₂ = rieszProjection R c r₁ :=
  dunfordIntegral_eq_of_annulus h hU h₀ hle hann fun _ _ ↦ differentiableAt_const _

/-- **Cauchy's theorem on a disc.** For a pseudo-resolvent on an open set that contains the
closed disc, and a weight that is holomorphic on the disc, the Dunford integral vanishes. -/
theorem dunfordIntegral_eq_zero (h : IsPseudoResolventOn R U) (hU : IsOpen U) (hr : 0 ≤ r)
    (hb : closedBall c r ⊆ U) (hg : ∀ z ∈ closedBall c r, DifferentiableAt ℂ g z) :
    dunfordIntegral R c r g = 0 := by
  have hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (fun z ↦ g z • R z) z :=
    fun z hz ↦ (hg z hz).smul (h.differentiableAt (hU.mem_nhds (hb hz)))
  unfold dunfordIntegral
  rw [circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    (fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt)
    fun z hz ↦ hd z (ball_subset_closedBall hz.1), smul_zero]

/-- The Riesz projection of a pseudo-resolvent on a closed disc vanishes. -/
theorem rieszProjection_eq_zero (h : IsPseudoResolventOn R U) (hU : IsOpen U) (hr : 0 ≤ r)
    (hb : closedBall c r ⊆ U) : rieszProjection R c r = 0 :=
  dunfordIntegral_eq_zero h hU hr hb fun _ _ ↦ differentiableAt_const _

/-- A circle in an open set lies in an open annulus in that set. -/
theorem exists_annulus_subset_of_sphere_subset (hU : IsOpen U) (hr : 0 < r)
    (hs : sphere c r ⊆ U) :
    ∃ δ, 0 < δ ∧ δ < r ∧ ∀ z : ℂ, r - δ < dist z c → dist z c < r + δ → z ∈ U := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := (isCompact_sphere c r).exists_thickening_subset_open hU hs
  refine ⟨min δ₀ (r / 2), lt_min hδ₀ (half_pos hr), (min_le_right _ _).trans_lt (half_lt_self hr),
    fun z h₁ h₂ ↦ hsub ?_⟩
  have hm₁ := min_le_left δ₀ (r / 2)
  have hm₂ := min_le_right δ₀ (r / 2)
  have hd : 0 < dist z c := by linarith
  have hzc : ‖z - c‖ = dist z c := (dist_eq_norm z c).symm
  refine mem_thickening_iff.mpr ⟨c + ((r / dist z c : ℝ) : ℂ) * (z - c), ?_, ?_⟩
  · rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hd), hzc, div_mul_cancel₀ r hd.ne']
  · have e : z - (c + ((r / dist z c : ℝ) : ℂ) * (z - c)) =
        ((1 - r / dist z c : ℝ) : ℂ) * (z - c) := by
      push_cast
      ring
    rw [dist_eq_norm, e, norm_mul, norm_real, Real.norm_eq_abs, hzc, ← abs_of_pos hd,
      ← abs_mul, abs_of_pos hd, sub_mul, one_mul, div_mul_cancel₀ r hd.ne']
    exact (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩).trans_le hm₁

variable [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- The Dunford integral depends only on the family on the circle. -/
theorem dunfordIntegral_congr_left {R₁ R₂ : ℂ → 𝔸} (hr : 0 ≤ r) (h : EqOn R₁ R₂ (sphere c r))
    (g : ℂ → ℂ) : dunfordIntegral R₁ c r g = dunfordIntegral R₂ c r g := by
  unfold dunfordIntegral
  congr 1
  exact circleIntegral.integral_congr hr fun z hz ↦ by simp only [h hz]

/-- Multiplication on the right goes inside the Dunford integral of a continuous family. -/
theorem dunfordIntegral_mul_right (hr : 0 ≤ r) (hg : ContinuousOn g (sphere c r))
    (hR : ContinuousOn R (sphere c r)) (b : 𝔸) :
    dunfordIntegral R c r g * b = dunfordIntegral (fun z ↦ R z * b) c r g := by
  have h := ((ContinuousLinearMap.mul ℂ 𝔸).flip b).map_circleIntegral
    (circleIntegrable_smul hr hg hR)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h
  unfold dunfordIntegral
  rw [smul_mul_assoc, h]
  simp only [smul_mul_assoc]

/-- An element that commutes with `R z` on the circle commutes with every Dunford integral. -/
theorem commute_dunfordIntegral (hr : 0 ≤ r) {b : 𝔸} (hb : ∀ z ∈ sphere c r, Commute b (R z))
    (g : ℂ → ℂ) : Commute b (dunfordIntegral R c r g) := by
  unfold dunfordIntegral
  refine Commute.smul_right ?_ _
  by_cases hint : CircleIntegrable (fun z ↦ g z • R z) c r
  · have hl := (ContinuousLinearMap.mul ℂ 𝔸 b).map_circleIntegral hint
    have hr' := ((ContinuousLinearMap.mul ℂ 𝔸).flip b).map_circleIntegral hint
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hl hr'
    change b * _ = _ * b
    rw [hl, hr']
    refine circleIntegral.integral_congr hr fun z hz ↦ ?_
    simp only [mul_smul_comm, smul_mul_assoc, (hb z hz).eq]
  · rw [circleIntegral.integral_undef hint]
    exact Commute.zero_right b

/-- An element that commutes with `R z` on the circle commutes with the Riesz projection. -/
theorem commute_rieszProjection (hr : 0 ≤ r) {b : 𝔸} (hb : ∀ z ∈ sphere c r, Commute b (R z)) :
    Commute b (rieszProjection R c r) :=
  commute_dunfordIntegral hr hb 1

omit [CompleteSpace 𝔸] in
/-- For `z` off the circle, `Φ(w (z - w)⁻¹) = z Φ((z - w)⁻¹) - P`: the weights satisfy
`z (z - w)⁻¹ - w (z - w)⁻¹ = 1`. -/
theorem dunfordIntegral_id_mul_sub_inv (hr : 0 ≤ r) (hR : ContinuousOn R (sphere c r)) {z : ℂ}
    (hz : z ∉ sphere c r) :
    dunfordIntegral R c r (fun w ↦ w * (z - w)⁻¹) =
      z • dunfordIntegral R c r (fun w ↦ (z - w)⁻¹) - rieszProjection R c r := by
  have hne : ∀ w ∈ sphere c r, z - w ≠ 0 := fun w hw h ↦ hz (sub_eq_zero.mp h ▸ hw)
  have hg : ContinuousOn (fun w : ℂ ↦ (z - w)⁻¹) (sphere c r) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hne
  have hg₁ : ContinuousOn (fun w : ℂ ↦ z * (z - w)⁻¹) (sphere c r) := continuousOn_const.mul hg
  have hg₂ : ContinuousOn (fun w : ℂ ↦ w * (z - w)⁻¹) (sphere c r) := continuousOn_id.mul hg
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', ← dunfordIntegral_const_mul,
    ← dunfordIntegral_sub hr hR hg₁ hg₂]
  exact dunfordIntegral_congr hr fun w hw ↦ by
    rw [Pi.one_apply, ← sub_mul, mul_inv_cancel₀ (hne w hw)]

/-- **The domain rule.** For a pseudo-resolvent on `U ⊇ C(c, r)` and a point `z₀` of `U`,
`Φ(g) = ((2πi)⁻¹ ∮ g) R z₀ + R z₀ Φ((z₀ - z) g)`. For the resolvent of an operator `A` this
is `A Φ(g) = Φ(z g) - (2πi)⁻¹ ∮ g`, with `Φ(g)` mapping into the domain of `A`. -/
theorem dunfordIntegral_eq_smul_add_mul (h : IsPseudoResolventOn R U) (hr : 0 ≤ r)
    (hs : sphere c r ⊆ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hg : ContinuousOn g (sphere c r)) :
    dunfordIntegral R c r g = ((2 * π * I)⁻¹ * ∮ z in C(c, r), g z) • R z₀ +
      R z₀ * dunfordIntegral R c r (fun z ↦ (z₀ - z) * g z) := by
  have hR : ContinuousOn R (sphere c r) := h.continuousOn.mono hs
  have hg' : ContinuousOn (fun z ↦ (z₀ - z) * g z) (sphere c r) :=
    (continuousOn_const.sub continuousOn_id).mul hg
  have hi₁ : CircleIntegrable (fun z ↦ g z • R z₀) c r :=
    (hg.smul continuousOn_const).circleIntegrable hr
  have hi₂ := circleIntegrable_smul hr hg' hR
  have hi₃ : CircleIntegrable (fun z ↦ R z₀ * (((z₀ - z) * g z) • R z)) c r :=
    (continuousOn_const.mul (hg'.smul hR)).circleIntegrable hr
  have hl := (ContinuousLinearMap.mul ℂ 𝔸 (R z₀)).map_circleIntegral hi₂
  simp only [ContinuousLinearMap.mul_apply'] at hl
  have hcongr : (∮ z in C(c, r), g z • R z) =
      ∮ z in C(c, r), (g z • R z₀ + R z₀ * (((z₀ - z) * g z) • R z)) := by
    refine circleIntegral.integral_congr hr fun z hz ↦ ?_
    have e : R z = R z₀ + (z₀ - z) • (R z₀ * R z) := by
      rw [← neg_sub z z₀, neg_smul, ← h hz₀ (hs hz)]
      abel
    calc g z • R z = g z • (R z₀ + (z₀ - z) • (R z₀ * R z)) := by rw [← e]
      _ = g z • R z₀ + R z₀ * (((z₀ - z) * g z) • R z) := by
          rw [smul_add, smul_smul, mul_smul_comm, mul_comm (g z)]
  unfold dunfordIntegral
  rw [hcongr, circleIntegral.integral_add hi₁ hi₃,
    circleIntegral.integral_smul_const, ← hl, smul_add, smul_smul, mul_smul_comm]

/-- **The product rule.** For a pseudo-resolvent on `U`, two circles in `U`, and the closed
disc of the first circle disjoint from the second circle,
`P₁ Φ₂(g) = Φ₁(ĝ)` with `ĝ z = (2πi)⁻¹ ∮_{C(c₂, r₂)} (w - z)⁻¹ g w dw`. Idempotence of a Riesz
projection and the vanishing of products for disjoint discs are the cases `g = 1` with the
first disc inside or outside the second circle. The proof writes `R z R w` on the product of
the two circles with the resolvent identity as `(R z - R w) / (w - z)`; the part with `R w`
integrates to zero over the first circle, because `(w - z)⁻¹` is holomorphic in `z` on its
closed disc. -/
theorem rieszProjection_mul_dunfordIntegral (h : IsPseudoResolventOn R U) (h₁ : 0 ≤ r₁)
    (h₂ : 0 ≤ r₂) (hs₁ : sphere c₁ r₁ ⊆ U) (hs₂ : sphere c₂ r₂ ⊆ U)
    (hd : Disjoint (closedBall c₁ r₁) (sphere c₂ r₂)) (hg : ContinuousOn g (sphere c₂ r₂)) :
    rieszProjection R c₁ r₁ * dunfordIntegral R c₂ r₂ g =
      dunfordIntegral R c₁ r₁ fun z ↦ (2 * π * I)⁻¹ * ∮ w in C(c₂, r₂), (w - z)⁻¹ * g w := by
  set k : ℂ := (2 * π * I)⁻¹ with hk
  have hR₁ : ContinuousOn R (sphere c₁ r₁) := h.continuousOn.mono hs₁
  have hR₂ : ContinuousOn R (sphere c₂ r₂) := h.continuousOn.mono hs₂
  set G : ℂ → 𝔸 := fun z ↦ ∮ w in C(c₂, r₂), (w - z)⁻¹ • (g w • R w) with hGdef
  set f : ℂ → ℂ := fun z ↦ ∮ w in C(c₂, r₂), (w - z)⁻¹ • g w with hfdef
  have hgR := circleIntegrable_smul h₂ hg hR₂
  have hnot : ∀ z ∈ closedBall c₁ r₁, z ∉ sphere c₂ |r₂| := fun z hz hzs ↦ by
    rw [abs_of_nonneg h₂] at hzs
    exact Set.disjoint_left.mp hd hz hzs
  have hGd : ∀ z ∈ closedBall c₁ r₁, DifferentiableAt ℂ G z := fun z hz ↦
    (hasDerivAt_circleIntegral_sub_inv_smul hgR (hnot z hz)).differentiableAt
  have hfd : ∀ z ∈ closedBall c₁ r₁, DifferentiableAt ℂ f z := fun z hz ↦
    (hasDerivAt_circleIntegral_sub_inv_smul (hg.circleIntegrable h₂) (hnot z hz)).differentiableAt
  have hG0 : (∮ z in C(c₁, r₁), G z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable h₁ countable_empty
      (fun z hz ↦ (hGd z hz).continuousAt.continuousWithinAt)
      fun z hz ↦ hGd z (ball_subset_closedBall hz.1)
  -- the identity at a point of the first circle
  have hpt : ∀ z ∈ sphere c₁ r₁,
      R z * dunfordIntegral R c₂ r₂ g = (k * f z) • R z - k • G z := by
    intro z hz
    have hne : ∀ w ∈ sphere c₂ r₂, w ≠ z := fun w hw hwz ↦
      Set.disjoint_left.mp hd (sphere_subset_closedBall hz) (hwz ▸ hw)
    have hinv : ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere c₂ r₂) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.mpr (hne w hw)
    have hi₁ : CircleIntegrable (fun w ↦ ((w - z)⁻¹ * g w) • R z) c₂ r₂ :=
      ((hinv.mul hg).smul continuousOn_const).circleIntegrable h₂
    have hi₂ : CircleIntegrable (fun w ↦ (w - z)⁻¹ • (g w • R w)) c₂ r₂ :=
      (hinv.smul (hg.smul hR₂)).circleIntegrable h₂
    have hl := (ContinuousLinearMap.mul ℂ 𝔸 (R z)).map_circleIntegral hgR
    simp only [ContinuousLinearMap.mul_apply'] at hl
    unfold dunfordIntegral
    rw [mul_smul_comm, hl, circleIntegral.integral_congr h₂ fun w hw ↦ show
        R z * (g w • R w) = ((w - z)⁻¹ * g w) • R z - (w - z)⁻¹ • (g w • R w) by
        rw [mul_smul_comm, h.mul_eq (hs₁ hz) (hs₂ hw) (hne w hw).symm]
        simp only [smul_sub, smul_smul]
        rw [mul_comm (g w)],
      circleIntegral.integral_sub hi₁ hi₂, circleIntegral.integral_smul_const, smul_sub,
      smul_smul]
    rfl
  have hRi : CircleIntegrable R c₁ r₁ := hR₁.circleIntegrable h₁
  have hr := ((ContinuousLinearMap.mul ℂ 𝔸).flip
    (dunfordIntegral R c₂ r₂ g)).map_circleIntegral hRi
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at hr
  have hsph : sphere c₁ r₁ ⊆ closedBall c₁ r₁ := sphere_subset_closedBall
  have hfc : ContinuousOn (fun z ↦ (k * f z) • R z) (sphere c₁ r₁) :=
    (continuousOn_const.mul fun z hz ↦
      (hfd z (hsph hz)).continuousAt.continuousWithinAt).smul hR₁
  have hGc : ContinuousOn (fun z ↦ k • G z) (sphere c₁ r₁) :=
    continuousOn_const.smul fun z hz ↦ (hGd z (hsph hz)).continuousAt.continuousWithinAt
  rw [rieszProjection_eq, smul_mul_assoc, hr, circleIntegral.integral_congr h₁ hpt,
    circleIntegral.integral_sub (hfc.circleIntegrable h₁) (hGc.circleIntegrable h₁),
    circleIntegral.integral_smul, hG0, smul_zero, sub_zero]
  rfl

/-- For a disc inside a second disc, `P₁ P₂ = P₁`. -/
theorem rieszProjection_mul_rieszProjection_of_subset (h : IsPseudoResolventOn R U)
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (hs₁ : sphere c₁ r₁ ⊆ U) (hs₂ : sphere c₂ r₂ ⊆ U)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) :
    rieszProjection R c₁ r₁ * rieszProjection R c₂ r₂ = rieszProjection R c₁ r₁ := by
  have hd : Disjoint (closedBall c₁ r₁) (sphere c₂ r₂) :=
    Set.disjoint_left.mpr fun z hz hzs ↦ (mem_ball.mp (hsub hz)).ne (mem_sphere.mp hzs)
  rw [show rieszProjection R c₂ r₂ = dunfordIntegral R c₂ r₂ 1 from rfl,
    rieszProjection_mul_dunfordIntegral (g := 1) h h₁ h₂ hs₁ hs₂ hd continuousOn_const]
  refine dunfordIntegral_congr h₁ fun z hz ↦ ?_
  simp only [Pi.one_apply, mul_one,
    circleIntegral.integral_sub_inv_of_mem_ball (hsub (sphere_subset_closedBall hz))]
  exact inv_mul_cancel₀ two_pi_I_ne_zero

/-- **Projections for disjoint discs annihilate each other**: `P₁ P₂ = 0`. -/
theorem rieszProjection_mul_rieszProjection_of_disjoint (h : IsPseudoResolventOn R U)
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (hs₁ : sphere c₁ r₁ ⊆ U) (hs₂ : sphere c₂ r₂ ⊆ U)
    (hdisj : Disjoint (closedBall c₁ r₁) (closedBall c₂ r₂)) :
    rieszProjection R c₁ r₁ * rieszProjection R c₂ r₂ = 0 := by
  have hd : Disjoint (closedBall c₁ r₁) (sphere c₂ r₂) :=
    hdisj.mono_right sphere_subset_closedBall
  rw [show rieszProjection R c₂ r₂ = dunfordIntegral R c₂ r₂ 1 from rfl,
    rieszProjection_mul_dunfordIntegral (g := 1) h h₁ h₂ hs₁ hs₂ hd continuousOn_const,
    ← dunfordIntegral_zero R c₁ r₁]
  refine dunfordIntegral_congr h₁ fun z hz ↦ ?_
  simp only [Pi.one_apply, mul_one, Pi.zero_apply,
    circleIntegral_sub_inv_of_notMem_closedBall h₂
      (Set.disjoint_left.mp hdisj (sphere_subset_closedBall hz)), mul_zero]

/-- **Idempotence of the Riesz projection.** For a pseudo-resolvent on an open set that
contains the circle `C(c, r)`, `r > 0`, the Riesz projection is idempotent. The projection on a
slightly larger circle is the same, and the product rule applies to the two circles. -/
theorem isIdempotentElem_rieszProjection (h : IsPseudoResolventOn R U) (hU : IsOpen U)
    (hr : 0 < r) (hs : sphere c r ⊆ U) : IsIdempotentElem (rieszProjection R c r) := by
  obtain ⟨δ, hδ, -, hann⟩ := exists_annulus_subset_of_sphere_subset hU hr hs
  have hs₂ : sphere c (r + δ / 2) ⊆ U := fun z hz ↦
    hann z (by rw [mem_sphere.mp hz]; linarith) (by rw [mem_sphere.mp hz]; linarith)
  have heq : rieszProjection R c (r + δ / 2) = rieszProjection R c r :=
    rieszProjection_eq_of_annulus h hU hr (by linarith) fun z hz ↦
      hann z (by linarith [not_lt.mp (fun h' ↦ hz.2 (mem_ball.mpr h'))])
        (by linarith [mem_closedBall.mp hz.1])
  unfold IsIdempotentElem
  calc rieszProjection R c r * rieszProjection R c r
      = rieszProjection R c r * rieszProjection R c (r + δ / 2) := by rw [heq]
    _ = rieszProjection R c r :=
        rieszProjection_mul_rieszProjection_of_subset h hr.le (by linarith) hs hs₂
          (closedBall_subset_ball (by linarith))

end PDE.Analysis.Spectral
