/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.Contour

/-!
# Pseudo-resolvents

A family `R : 𝕜 → 𝔸` with values in a normed algebra is a pseudo-resolvent on a set `U` when it
satisfies the first resolvent identity `R z - R w = (w - z) R z R w` for all `z, w ∈ U`. No
operator appears, so what follows from the identity alone holds at once for the resolvent of an
element of a normed algebra (`isPseudoResolventOn_resolvent`) and for the resolvent of a closed
unbounded operator (`LinearPMap.isPseudoResolventOn_resolvent`). On an open set a
pseudo-resolvent is holomorphic, with no completeness and no Neumann series. The Riesz
projection of a pseudo-resolvent on a circle (`rieszProjection`) is built on that. That a
pseudo-resolvent on a connected open set extends to a maximal one, and that one whose values
are injective with dense range is the resolvent of a closed operator, are not proved here.

## Main results

* `IsPseudoResolventOn R U`: the first resolvent identity on `U`.
* `IsPseudoResolventOn.commute`: the values of a pseudo-resolvent commute.
* `IsPseudoResolventOn.mul_eq`: `R z R w = (w - z)⁻¹ (R z - R w)` for `z ≠ w`.
* `IsPseudoResolventOn.norm_le_two_mul`: the local bound `‖R w‖ ≤ 2 ‖R z‖` once
  `|w - z| ‖R z‖ ≤ 1/2`.
* `IsPseudoResolventOn.hasDerivWithinAt`, `hasDerivAt`, `differentiableOn`, `continuousOn`: the
  derivative of `R` at `z` is `-R z²`.
* `isPseudoResolventOn_resolvent`: the resolvent of an element `a` of a complex normed algebra
  is a pseudo-resolvent on the resolvent set of `a`.

## How it works

Exchanging `z` and `w` in the identity shows that the values commute. Solving it for `R w` gives
`‖R w‖ ≤ 2 ‖R z‖` once `|w - z| ‖R z‖ ≤ 1/2`, so `R` is locally bounded. Inserting the identity
into itself gives `R w - R z + (w - z) R z² = (w - z)² R z² R w`, which says that `R` has the
derivative `-R z²` at `z`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace PDE.Analysis.Spectral

variable {𝕜 𝔸 : Type*} [NontriviallyNormedField 𝕜] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]

/-- The family `R` is a pseudo-resolvent on `U`: it satisfies the first resolvent identity
`R z - R w = (w - z) R z R w` for all `z` and `w` in `U`. The resolvent of an element of a normed
algebra and the resolvent of a closed operator are the two instances. -/
def IsPseudoResolventOn (R : 𝕜 → 𝔸) (U : Set 𝕜) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃w⦄, w ∈ U → R z - R w = (w - z) • (R z * R w)

namespace IsPseudoResolventOn

variable {R : 𝕜 → 𝔸} {U V : Set 𝕜} {z w : 𝕜}

/-- A pseudo-resolvent on `U` is one on every subset of `U`. -/
theorem mono (h : IsPseudoResolventOn R U) (hVU : V ⊆ U) : IsPseudoResolventOn R V :=
  fun _ hz _ hw ↦ h (hVU hz) (hVU hw)

/-- The values of a pseudo-resolvent commute: exchange `z` and `w` in the resolvent identity. -/
theorem commute (h : IsPseudoResolventOn R U) (hz : z ∈ U) (hw : w ∈ U) :
    Commute (R z) (R w) := by
  rcases eq_or_ne z w with rfl | hne
  · exact Commute.refl _
  refine smul_right_injective 𝔸 (sub_ne_zero.mpr hne.symm) ?_
  change (w - z) • (R z * R w) = (w - z) • (R w * R z)
  rw [← h hz hw, ← neg_sub (R w) (R z), h hw hz, ← neg_smul, neg_sub]

/-- For distinct points, `R z R w = (w - z)⁻¹ (R z - R w)`. -/
theorem mul_eq (h : IsPseudoResolventOn R U) (hz : z ∈ U) (hw : w ∈ U) (hzw : z ≠ w) :
    R z * R w = (w - z)⁻¹ • (R z - R w) := by
  rw [h hz hw, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hzw.symm), one_smul]

/-- A pseudo-resolvent is locally bounded: `‖R w‖ ≤ 2 ‖R z‖` when `|w - z| ‖R z‖ ≤ 1/2`. -/
theorem norm_le_two_mul (h : IsPseudoResolventOn R U) (hz : z ∈ U) (hw : w ∈ U)
    (hzw : ‖w - z‖ * ‖R z‖ ≤ 1 / 2) : ‖R w‖ ≤ 2 * ‖R z‖ := by
  have h1 : R w = R z - (w - z) • (R z * R w) := by rw [← h hz hw, sub_sub_cancel]
  have h2 : ‖R w‖ ≤ ‖R z‖ + ‖w - z‖ * ‖R z‖ * ‖R w‖ :=
    calc ‖R w‖ = ‖R z - (w - z) • (R z * R w)‖ := congrArg norm h1
      _ ≤ ‖R z‖ + ‖(w - z) • (R z * R w)‖ := norm_sub_le _ _
      _ ≤ ‖R z‖ + ‖w - z‖ * ‖R z‖ * ‖R w‖ := by
          rw [norm_smul, mul_assoc]
          gcongr
          exact norm_mul_le _ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hzw) (norm_nonneg (R w))]

/-- The second-order form of the resolvent identity:
`R w - R z + (w - z) R z² = (w - z)² R z² R w`. -/
theorem sub_sub_smul_eq (h : IsPseudoResolventOn R U) (hz : z ∈ U) (hw : w ∈ U) :
    R w - R z - (w - z) • (-(R z * R z)) = (w - z) • ((w - z) • (R z * R z * R w)) := by
  have e := h hz hw
  calc R w - R z - (w - z) • (-(R z * R z)) = (w - z) • (R z * (R z - R w)) := by
        rw [mul_sub, smul_sub, ← e, smul_neg]
        abel
    _ = (w - z) • ((w - z) • (R z * R z * R w)) := by rw [e, mul_smul_comm, mul_assoc]

/-- **A pseudo-resolvent is differentiable**, with derivative `-R z²` at `z`, within the set
where the resolvent identity holds. -/
theorem hasDerivWithinAt (h : IsPseudoResolventOn R U) (hz : z ∈ U) :
    HasDerivWithinAt R (-(R z * R z)) U z := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set C := ‖R z‖
  have hC : 0 ≤ C := norm_nonneg _
  set K := 2 * C ^ 3 + C + 1
  have hK : 0 < K := by positivity
  have hδ : 0 < min (1 / 2) ε / K := div_pos (lt_min one_half_pos hε) hK
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds z hδ)]
    with w hwU hw
  rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ hK] at hw
  have hd : 0 ≤ ‖w - z‖ := norm_nonneg _
  have h1 : ‖w - z‖ * C ≤ 1 / 2 := by nlinarith [min_le_left (1 / 2) ε, pow_nonneg hC 3]
  have h2 : ‖w - z‖ * (2 * C ^ 3) ≤ ε := by nlinarith [min_le_right (1 / 2) ε]
  have hRw : ‖R w‖ ≤ 2 * C := h.norm_le_two_mul hz hwU h1
  rw [h.sub_sub_smul_eq hz hwU, norm_smul, norm_smul, mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ hd
  calc ‖w - z‖ * ‖R z * R z * R w‖ ≤ ‖w - z‖ * (C * C * (2 * C)) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) hRw (norm_nonneg _)
          (mul_nonneg hC hC))
    _ = ‖w - z‖ * (2 * C ^ 3) := by ring
    _ ≤ ε := h2

/-- A pseudo-resolvent is continuous on the set where the resolvent identity holds. -/
theorem continuousOn (h : IsPseudoResolventOn R U) : ContinuousOn R U :=
  fun _ hz ↦ (h.hasDerivWithinAt hz).continuousWithinAt

/-- At an interior point of `U`, a pseudo-resolvent has the derivative `-R z²`. -/
theorem hasDerivAt (h : IsPseudoResolventOn R U) (hU : U ∈ 𝓝 z) :
    HasDerivAt R (-(R z * R z)) z :=
  (h.hasDerivWithinAt (mem_of_mem_nhds hU)).hasDerivAt hU

/-- At an interior point of `U`, a pseudo-resolvent is differentiable. -/
theorem differentiableAt (h : IsPseudoResolventOn R U) (hU : U ∈ 𝓝 z) :
    DifferentiableAt 𝕜 R z :=
  (h.hasDerivAt hU).differentiableAt

/-- A pseudo-resolvent is differentiable on the set where the resolvent identity holds. -/
theorem differentiableOn (h : IsPseudoResolventOn R U) : DifferentiableOn 𝕜 R U :=
  fun _ hz ↦ (h.hasDerivWithinAt hz).differentiableWithinAt

end IsPseudoResolventOn

/-- The resolvent of an element of a complex normed algebra is a pseudo-resolvent on its
resolvent set: this is the first resolvent identity `resolvent_sub_resolvent_eq_smul_mul`. -/
theorem isPseudoResolventOn_resolvent {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] (a : 𝔸) :
    IsPseudoResolventOn (resolvent a) (resolventSet ℂ a) :=
  fun _ hz _ hw ↦ resolvent_sub_resolvent_eq_smul_mul hz hw

end PDE.Analysis.Spectral
