/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# A chain rule for derivatives in a weaker norm

Let `J : V →L[ℝ] H`. Suppose the differential of a potential on `V` factors
through `J`, with a continuous `H`-dual gradient. A curve continuous in `V`
then obeys the chain rule whenever its image in `H` is differentiable. The
curve need not be differentiable in `V`.

The proof integrates the differential along a segment. Continuity of the
gradient makes the remainder small relative to the `H` increment, rather
than merely relative to the stronger `V` increment.
-/

@[expose] public section

noncomputable section

open Filter Set Asymptotics
open scoped Topology

namespace PDE.Analysis.Calculus

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A bound on the variation of the pivot gradient along a segment controls
the first-order remainder by the pivot norm of the increment. -/
theorem norm_pivot_remainder_le (J : V →L[ℝ] H)
    (Φ : V → ℝ) (G : V → H →L[ℝ] ℝ)
    (hΦ : ∀ v, HasFDerivAt Φ ((G v).comp J) v)
    (x y : V) (ε : ℝ)
    (hG : ∀ a ∈ Icc (0 : ℝ) 1, ‖G (x + a • (y - x)) - G x‖ ≤ ε) :
    ‖Φ y - Φ x - G x (J (y - x))‖ ≤ ε * ‖J (y - x)‖ := by
  let c := fun a : ℝ ↦ x + a • (y - x)
  let R := fun a : ℝ ↦ Φ (c a) - G x (J (c a))
  have hc (a : ℝ) : HasDerivAt c (y - x) a := by
    simpa only [c, id_eq, one_smul] using
      ((hasDerivAt_id a).smul_const (y - x)).const_add x
  have hR (a : ℝ) : HasDerivAt R ((G (c a) - G x) (J (y - x))) a := by
    have hleft : HasDerivAt (fun b ↦ Φ (c b)) (G (c a) (J (y - x))) a :=
      (hΦ (c a)).comp_hasDerivAt a (hc a)
    have hright : HasDerivAt (fun b ↦ G x (J (c b))) (G x (J (y - x))) a :=
      ((G x).comp J).hasFDerivAt.comp_hasDerivAt a (hc a)
    change HasDerivAt (fun b ↦ Φ (c b) - G x (J (c b)))
      (G (c a) (J (y - x)) - G x (J (y - x))) a
    exact hleft.sub hright
  have hbound : ‖R 1 - R 0‖ ≤ ε * ‖J (y - x)‖ := by
    apply norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun a _ ↦ (hR a).hasDerivWithinAt)
    intro a ha
    exact ((G (c a) - G x).le_opNorm (J (y - x))).trans
      (mul_le_mul_of_nonneg_right (hG a ⟨ha.1, ha.2.le⟩) (norm_nonneg _))
  have hc1 : c 1 = y := by
    dsimp [c]
    rw [one_smul]
    abel
  have hc0 : c 0 = x := by simp only [c, zero_smul, add_zero]
  have hRdiff : R 1 - R 0 = Φ y - Φ x - G x (J (y - x)) := by
    simp only [R, hc1, hc0, map_sub]
    ring
  rwa [hRdiff] at hbound

/-- A potential whose differential has a continuous pivot gradient satisfies
the chain rule along curves differentiable only after applying `J`. Neither
injectivity of `J` nor completeness of the spaces is needed. -/
theorem hasDerivAt_of_pivot_gradient (J : V →L[ℝ] H)
    (Φ : V → ℝ) (G : V → H →L[ℝ] ℝ)
    (hΦ : ∀ v, HasFDerivAt Φ ((G v).comp J) v)
    {q : ℝ → V} {p : H} {t : ℝ}
    (hG : ContinuousAt G (q t)) (hq : ContinuousAt q t)
    (hp : HasDerivAt (fun s ↦ J (q s)) p t) :
    HasDerivAt (fun s ↦ Φ (q s)) (G (q t) p) t := by
  have hrem :
      (fun y ↦ Φ y - Φ (q t) - G (q t) (J (y - q t))) =o[𝓝 (q t)]
        (fun y ↦ J (y - q t)) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.mp hG ε hε
    filter_upwards [Metric.ball_mem_nhds (q t) hδ] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    apply norm_pivot_remainder_le J Φ G hΦ (q t) y ε
    intro a ha
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hδG
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ha.1]
    exact (mul_le_of_le_one_left (norm_nonneg (y - q t)) ha.2).trans_lt hy
  have hpbig : (fun s ↦ J (q s - q t)) =O[𝓝 t] (fun s ↦ s - t) := by
    simpa only [map_sub] using hp.isBigO_sub
  have hremtime := (hrem.comp_tendsto hq).trans_isBigO hpbig
  have hlinear :
      HasDerivAt (fun s ↦ G (q t) (J (q s))) (G (q t) p) t :=
    (G (q t)).hasFDerivAt.comp_hasDerivAt t hp
  apply HasDerivAt.of_isLittleO
  exact (hremtime.add hlinear.isLittleO).congr_left fun s ↦ by
    simp only [Function.comp_apply, map_sub, smul_eq_mul]
    ring

end PDE.Analysis.Calculus
