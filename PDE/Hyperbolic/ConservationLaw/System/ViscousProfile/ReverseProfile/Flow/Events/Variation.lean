/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.LevelDerivative
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle

/-!
# Variations of supplied level-event maps

The shared level-event derivative rule differentiates the two supplied event
identities while keeping their solution family fixed.

The prescribed-clock application differentiates the supplied late zero and upward
205 event for the same family `F`. At the reference parameter `(μ,a) = (0,0)`,
the time derivatives are `-8` and `g 205 + 1`. The initial-state identity gives
parameter variation `(ξ.2,0)` at time zero.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The initialization `F(0,(μ,a)) = (a,1)` gives zero initial speed
variation and unit initial middle-displacement variation. -/
theorem fderiv_prescribed_initial_state {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)} (hN : IsOpen N)
    (hbase : (0, 0) ∈ N) (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun p ↦ F (0, p)) (0, 0) ξ = (ξ.2, 0) := by
  have heq : (fun p ↦ F (0, p)) =ᶠ[𝓝 ((0, 0) : ℝ × ℝ)] (fun p : ℝ × ℝ ↦ (p.2, (1 : ℝ))) :=
    Filter.Eventually.mono (hN.mem_nhds hbase) fun p hp ↦ hinitial p hp
  have haffine : HasFDerivAt (fun p : ℝ × ℝ ↦ (p.2, (1 : ℝ)))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)) (0, 0) :=
    hasFDerivAt_snd.prodMk (hasFDerivAt_const (1 : ℝ) ((0, 0) : ℝ × ℝ))
  exact congrArg (fun D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) ↦ D ξ) (haffine.congr_of_eventuallyEq heq).fderiv

/-- The two event derivatives of the same supplied prescribed-clock family.
Joint `C¹` regularity is needed only at the two reference events. The event maps
are `C¹` on the supplied open neighborhood and satisfy their level
identities there. The time-derivative hypotheses are the reference velocities derived from the
fixed-clock equations and switching margins. -/
theorem fderiv_prescribed_speed_events {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {N : Set (ℝ × ℝ)}
    {L Bhit : ℝ × ℝ → ℝ} {τ0 b₀ : ℝ} (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hFL : ContDiffAt ℝ 1 F (τ0, (0, 0))) (hFB : ContDiffAt ℝ 1 F (b₀, (0, 0)))
    (hL : ContDiffOn ℝ 1 L N) (hBhit : ContDiffOn ℝ 1 Bhit N) (hLbase : L (0, 0) = τ0)
    (hBbase : Bhit (0, 0) = b₀) (hLlevel : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hBlevel : ∀ p ∈ N, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) τ0)
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (MiddleClock.g 205 + 1) b₀) (ξ : ℝ × ℝ) :
    fderiv ℝ L (0, 0) ξ = (fderiv ℝ (fun p ↦ F (τ0, p)) (0, 0) ξ).1 / 8 ∧
      fderiv ℝ Bhit (0, 0) ξ = -(fderiv ℝ (fun p ↦ F (b₀, p)) (0, 0) ξ).1 / (MiddleClock.g 205 +
        1) := by
  have hnhds : N ∈ 𝓝 ((0, 0) : ℝ × ℝ) := hN.mem_nhds hbase
  have hLd : DifferentiableAt ℝ L (0, 0) := (hL.contDiffAt hnhds).differentiableAt_one
  have hBd : DifferentiableAt ℝ Bhit (0, 0) := (hBhit.contDiffAt hnhds).differentiableAt_one
  let R : (ℝ × ℝ) × ℝ → ℝ := fun p ↦ (F (p.2, p.1)).1
  have hRL : DifferentiableAt ℝ R ((0, 0), τ0) :=
    (hFL.comp ((0, 0), τ0) (contDiffAt_snd.prodMk contDiffAt_fst)).fst.differentiableAt_one
  have hRB : DifferentiableAt ℝ R ((0, 0), b₀) :=
    (hFB.comp ((0, 0), b₀) (contDiffAt_snd.prodMk contDiffAt_fst)).fst.differentiableAt_one
  have hprojection (t : ℝ) (ht : ContDiffAt ℝ 1 F (t, (0, 0))) :
      fderiv ℝ (fun p ↦ (F (t, p)).1) (0, 0) ξ =
        (fderiv ℝ (fun p ↦ F (t, p)) (0, 0) ξ).1 := by
    have hs : DifferentiableAt ℝ (fun p ↦ F (t, p)) (0, 0) := ht.differentiableAt_one.comp (0, 0)
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t ((0, 0) : ℝ × ℝ)).differentiableAt
    exact congrArg (fun D : (ℝ × ℝ) →L[ℝ] ℝ ↦ D ξ) hs.hasFDerivAt.fst.fderiv
  constructor
  · have hlate := PDE.Analysis.fderiv_level_event_apply
      (f := R) (τ := L) (p₀ := ((0, 0) : ℝ × ℝ)) (c := 0) (v := -8)
      (by simpa only [hLbase] using hRL) hLd (Filter.Eventually.mono hnhds fun p hp ↦ hLlevel p hp)
      (by simpa only [R, hLbase] using hLtime) (by norm_num) ξ
    simpa only [R, hLbase, hprojection τ0 hFL, neg_div_neg_eq] using hlate
  · have hspeed : MiddleClock.g 205 + 1 ≠ 0 := by
      linarith only [MiddleClock.g_nonneg (205 : ℝ)]
    have hup := PDE.Analysis.fderiv_level_event_apply
      (f := R) (τ := Bhit) (p₀ := ((0, 0) : ℝ × ℝ)) (c := 205) (v := MiddleClock.g 205 + 1)
      (by simpa only [hBbase] using hRB) hBd (Filter.Eventually.mono hnhds fun p hp ↦ hBlevel p hp)
      (by simpa only [R, hBbase] using hBtime) hspeed ξ
    simpa only [R, hBbase, hprojection b₀ hFB] using hup

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
