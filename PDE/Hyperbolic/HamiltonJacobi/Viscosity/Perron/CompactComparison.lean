/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.DoublingMaximum
import PDE.Analysis.Metric.QuadraticPenalty
import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier
import CAS.ExactTactic

/-!
# Compact comparison under continuous boundary barriers

An upper semicontinuous subsolution and a lower semicontinuous supersolution
of the same autonomous equation can be compared on a compact spacetime set
when continuous barriers control their boundary values. The barriers give
the small quadratic-penalty estimate at boundary pairs. Compact maximum
attainment and the doubled contact inequality then rule out a positive gap.

The boundary is the full spacetime frontier, including any terminal-time
face. This theorem is therefore a compact Dirichlet comparison result.
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Perron

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Continuous boundary barriers suffice for comparison of semicontinuous
viscosity subsolutions and supersolutions on a compact set. The autonomous
Hamiltonian cancels at doubled contacts and needs no regularity here. -/
theorem le_on_compact_of_boundary_barriers {H : E → ℝ} {K : Set (E × ℝ)} {u v l b : E × ℝ → ℝ}
    (hK : IsCompact K) (hu : UpperSemicontinuousOn u K) (hv : LowerSemicontinuousOn v K)
    (husub : IsSpatialViscositySubsolution (fun p _ ↦ H p) (interior K) u)
    (hvsuper : IsSpatialViscositySupersolution (fun p _ ↦ H p) (interior K) v)
    (hl : ContinuousOn l K) (hb : ContinuousOn b K) (hub : ∀ x ∈ K, u x ≤ b x)
    (hlv : ∀ x ∈ K, l x ≤ v x) (hboundary : ∀ x ∈ frontier K, b x ≤ l x) :
    ∀ x ∈ K, u x ≤ v x := by
  intro x hx
  by_contra hnot
  let d := u x - v x
  have hd : 0 < d := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨R, hR, htime⟩ := Bornology.IsBounded.exists_pos_norm_le
    (hK.image continuous_snd).isBounded
  have ht : ∀ z ∈ K, |z.2| ≤ R := by
    intro z hz
    simpa only [Real.norm_eq_abs] using htime z.2 (mem_image_of_mem Prod.snd hz)
  let c := d / (8 * R)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcR : c * R = d / 8 := by
    dsimp [c]
    cas using hR.ne'
  obtain ⟨ε₀, hε₀, hsmall⟩ := Metric.exists_sq_dist_penalty_le_of_mem
    (hK.uniformContinuousOn_of_continuous hb) (hK.uniformContinuousOn_of_continuous hl)
    (hK.image_of_continuousOn hb).isBounded (hK.image_of_continuousOn hl).isBounded
    (fun z _ hz ↦ hboundary z hz) (show 0 < d / 4 by positivity)
  let ε := ε₀ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < ε₀ := half_lt_self hε₀
  let P : E × ℝ → ℝ := fun y ↦ quadraticSize y / (2 * ε)
  have hP : ContDiff ℝ 1 P := contDiff_quadraticSize.div_const _
  obtain ⟨z, hz, w, hw, hfront, hmax⟩ :=
    husub.exists_isMaxOn_doubling_frontier hvsuper hK hK ⟨x, hx⟩ ⟨x, hx⟩ hu hv hP hc
  have hbound := hsmall ε ⟨hε, hεlt⟩ z hz w hw hfront
  have hquad : dist z w ^ 2 / (2 * ε) ≤ P (z - w) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [dist_eq_norm]
    exact norm_sq_le_quadraticSize (z - w)
  have hmax' := hmax (show (x, x) ∈ K ×ˢ K from ⟨hx, hx⟩)
  change u x - v x - (P (x - x) + c * x.2) ≤ u z - v w - (P (z - w) + c * z.2) at hmax'
  have hPzero : P (x - x) = 0 := by simp [P, quadraticSize]
  rw [hPzero, zero_add] at hmax'
  have hxt := mul_le_mul_of_nonneg_left (abs_le.mp (ht x hx)).2 hc.le
  have hzt := mul_le_mul_of_nonneg_left (abs_le.mp (ht z hz)).1 hc.le
  have huz := hub z hz
  have hvw := hlv w hw
  change d - c * x.2 ≤ _ at hmax'
  nlinarith

end HamiltonJacobi.Perron
