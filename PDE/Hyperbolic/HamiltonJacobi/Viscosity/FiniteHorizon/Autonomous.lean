/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.FiniteHorizon.Basic
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.LocalizedMaximum

/-!
# Finite-horizon comparison for a continuous autonomous Hamiltonian

Two viscosity solutions of `u_t + H(Dₓu) = 0` with the same initial values
agree on a prescribed closed slab if both are bounded and uniformly continuous
on that slab and solve the equation only in its interior. Ordered initial values give
an ordering between a subsolution and a supersolution in this class.
The Hamiltonian is continuous; convexity is not required.

The proof doubles both space and time. A quadratic penalty brings the two
contact points together, so uniform continuity rules out initial-time
contact. Reciprocal time barriers exclude a later terminal face. A small
quadratic localization gives an attained maximum on a bounded set.

Localization changes the two spatial test derivatives slightly. We first
fix the doubling scale, which bounds their common momentum, and then choose
the localization scale using uniform continuity of `H` on a compact momentum
ball.

For each target time, choose a later barrier horizon strictly below the supplied
horizon. The compact set ends earlier still, before either reciprocal barrier has
a zero denominator. At `S` the barrier exceeds the bounded difference `u - v`,
so the maximizing pair has both times strictly below `S`.

These results concern a finite-dimensional real inner product space and an
autonomous Hamiltonian. Finite dimensionality supplies compact balls in the
spatial and momentum spaces; the preceding contact estimates do not use it.
The viscosity inequalities are tested using locally `C¹` functions. The
quadratic and reciprocal penalties have this regularity at every interior
contact used in the proof.

This is Theorem 1 of Evans, §10.2, in comparison form, for an autonomous Hamiltonian that need
not satisfy the Lipschitz condition (3). Evans uses one parameter `ε` for the doubling and the
localization in (5) and bounds the Hamiltonian difference by (3) in (15); with two scales,
continuity of `H` suffices. The reciprocal barriers, as in the proof of his Lemma (Extrema at a
terminal time), take the place of the time penalty `λ(t+s)`: they supply the positive time term
and keep the maximum away from the terminal face. The position-dependent theorem is in
`FiniteHorizon.Spatial`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, Lemma (Extrema at a terminal time), condition (3),
  Theorem 1 and its proof, equations (4)-(15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open Set
open scoped Topology

-- The reciprocal barrier ends strictly inside the supplied horizon.
private theorem le_of_initial_le_of_lt_horizon {H : E → ℝ} {u v : (E × ℝ) → ℝ} {U V : Set (E × ℝ)}
    {T₀ : ℝ} (hu : IsSpatialViscositySubsolution (fun p _ ↦ H p) U u)
    (hv : IsSpatialViscositySupersolution (fun p _ ↦ H p) V v) (hU : openTimeSlab T₀ ⊆ U)
    (hV : openTimeSlab T₀ ⊆ V) (hH : Continuous H)
    (hub : Bornology.IsBounded (u '' closedTimeSlab T₀) ∧ UniformContinuousOn u (closedTimeSlab T₀))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T₀) ∧ UniformContinuousOn v (closedTimeSlab T₀))
    (hinit : ∀ x : E, u (x, 0) ≤ v (x, 0)) {z₀ : (E × ℝ)} (hz₀ : 0 ≤ z₀.2) (hz₀T₀ : z₀.2 < T₀) :
    u z₀ ≤ v z₀ := by
  by_contra hnot
  have hgap : 0 < u z₀ - v z₀ := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨T, hz₀ltT, hTT₀⟩ := exists_between hz₀T₀
  have hT : 0 < T := lt_of_le_of_lt hz₀ hz₀ltT
  have hslab : closedTimeSlab (E := E) T ⊆ closedTimeSlab T₀ :=
    fun _ hz ↦ ⟨hz.1, hz.2.trans hTT₀.le⟩
  have hubT : Bornology.IsBounded (u '' closedTimeSlab T) ∧
      UniformContinuousOn u (closedTimeSlab T) :=
    ⟨hub.1.subset (image_mono hslab), hub.2.mono hslab⟩
  have hvbT : Bornology.IsBounded (v '' closedTimeSlab T) ∧
      UniformContinuousOn v (closedTimeSlab T) :=
    ⟨hvb.1.subset (image_mono hslab), hvb.2.mono hslab⟩
  obtain ⟨M, hM, a, ha, S, hST, ε₀, hε₀, hlocalize⟩ :=
    exists_localized_maximum_of_initial_le hubT.1 hvbT.1 hubT.2 hvbT.2 hinit hz₀ hz₀ltT hgap
  let ε := ε₀ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < ε₀ := by dsimp [ε]; linarith only [hε₀]
  let B := (2 * ε * M + 1) / ε + 1
  let c := a / T ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hHuc : UniformContinuousOn H (Metric.closedBall 0 B) :=
    (isCompact_closedBall (0 : E) B).uniformContinuousOn_of_continuous hH.continuousOn
  obtain ⟨δ, hδ, hHclose⟩ := Metric.uniformContinuousOn_iff.mp hHuc c hc
  let r := min δ 1
  have hr : 0 < r := lt_min hδ zero_lt_one
  obtain ⟨α, hα, hαH, R, hmaximum⟩ := hlocalize r hr
  let K : Set (E × ℝ) := closedTimeSlab S ∩ Metric.closedBall 0 R
  have hden {z : (E × ℝ)} (hz : z ∈ K) : 0 < T - z.2 := sub_pos.mpr (hz.1.2.trans_lt hST)
  obtain ⟨z, hzK, w, hwK, ⟨hzpos, hwpos⟩, hbds, _, hlocal, htime_lower⟩ := hmaximum ε ⟨hε, hεlt⟩
  have hcontact := hu.doubling_barrier_inequality hv (hU ⟨hzpos, (hzK.1.2.trans_lt hST).trans hTT₀⟩)
    (hV ⟨hwpos, (hwK.1.2.trans_lt hST).trans hTT₀⟩) hε.ne'
    (hden hzK).ne' (hden hwK).ne' (hlocal.isLocalMaxOn _)
  have htime_nonneg : 0 ≤ 2 * α * (z.2 + w.2) := by positivity
  have htime_other : 0 ≤ a / (T - w.2) ^ 2 := by positivity
  let p : E := ε⁻¹ • (z.1 - w.1)
  have hp : ‖p‖ < B - 1 := by
    have hd2 := (div_lt_iff₀ (show 0 < 2 * ε by positivity)).mp hbds.1
    have hsep : ‖z.1 - w.1‖ ^ 2 ≤ quadraticSize (z - w) := norm_fst_sq_le_quadraticSize (z - w)
    have hnorm : ‖z.1 - w.1‖ < 2 * ε * M + 1 := by
      nlinarith only [hd2, hsep, sq_nonneg (‖z.1 - w.1‖ - 1), norm_nonneg (z.1 - w.1)]
    have hquot := div_lt_div_of_pos_right hnorm hε
    dsimp only [p, B]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
    simpa only [inv_mul_eq_div, add_sub_cancel_right] using hquot
  have hgz := norm_localization_gradient_lt hα hM hr hαH hbds.2.1
  have hgw := norm_localization_gradient_lt hα hM hr hαH hbds.2.2
  have hrδ : r ≤ δ := min_le_left _ _
  have hr_one : r ≤ 1 := min_le_right _ _
  have hp₁ : p - (2 * α) • w.1 ∈ Metric.closedBall 0 B := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := norm_sub_le p ((2 * α) • w.1)
    linarith only [h, hp, hgw, hr_one]
  have hp₂ : p + (2 * α) • z.1 ∈ Metric.closedBall 0 B := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := norm_add_le p ((2 * α) • z.1)
    linarith only [h, hp, hgz, hr_one]
  have hpd : dist (p - (2 * α) • w.1) (p + (2 * α) • z.1) < δ := by
    have heq : (p - (2 * α) • w.1) - (p + (2 * α) • z.1) =
        -((2 * α) • w.1 + (2 * α) • z.1) := by abel
    rw [dist_eq_norm, heq, norm_neg]
    have h := norm_add_le ((2 * α) • w.1) ((2 * α) • z.1)
    linarith only [h, hgw, hgz, hrδ]
  have hHamiltonian := hHclose _ hp₁ _ hp₂ hpd
  rw [Real.dist_eq] at hHamiltonian
  have hdiff := (abs_lt.mp hHamiltonian).2
  dsimp only [p] at hdiff
  linarith only [hcontact, htime_lower, htime_nonneg, htime_other, hdiff]

/-- Comparison on a prescribed closed slab for a continuous autonomous Hamiltonian.
The candidates need only solve the equation on the open slab. Their ambient values
outside the closed slab impose no condition, and terminal comparison follows by continuity. -/
theorem IsSpatialViscositySubsolution.le_of_initial_le_on_slab {H : E → ℝ} {u v : E × ℝ → ℝ}
    {U V : Set (E × ℝ)} {T : ℝ} (hu : IsSpatialViscositySubsolution (fun p _ ↦ H p) U u)
    (hv : IsSpatialViscositySupersolution (fun p _ ↦ H p) V v) (hU : openTimeSlab T ⊆ U)
    (hV : openTimeSlab T ⊆ V) (hH : Continuous H)
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (hinit : ∀ x, u (x, 0) ≤ v (x, 0)) (hT : 0 < T) {z : E × ℝ} (hz : z ∈ closedTimeSlab T) :
    u z ≤ v z := by
  apply le_on_closedTimeSlab hT hub.2.continuousOn hvb.2.continuousOn ?_ z hz
  exact fun _ hw ↦ le_of_initial_le_of_lt_horizon hu hv hU hV hH hub hvb hinit hw.1.le hw.2

/-- Uniqueness on the closed finite slab with no equation assumed beyond its horizon. -/
theorem IsSpatialViscositySolution.eqOn_closedTimeSlab {H : E → ℝ} {u v : E × ℝ → ℝ} {T : ℝ}
    (hu : IsSpatialViscositySolution (fun p _ ↦ H p) (openTimeSlab T) u)
    (hv : IsSpatialViscositySolution (fun p _ ↦ H p) (openTimeSlab T) v) (hH : Continuous H)
    (hub : Bornology.IsBounded (u '' closedTimeSlab T) ∧ UniformContinuousOn u (closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T) ∧ UniformContinuousOn v (closedTimeSlab T))
    (hinit : ∀ x, u (x, 0) = v (x, 0)) (hT : 0 < T) :
    EqOn u v (closedTimeSlab T) := by
  intro z hz
  exact le_antisymm (hu.1.le_of_initial_le_on_slab hv.2 Subset.rfl Subset.rfl hH hub hvb
      (fun x ↦ (hinit x).le) hT hz)
    (hv.1.le_of_initial_le_on_slab hu.2 Subset.rfl Subset.rfl hH hvb hub
      (fun x ↦ (hinit x).ge) hT hz)

end

end HamiltonJacobi
