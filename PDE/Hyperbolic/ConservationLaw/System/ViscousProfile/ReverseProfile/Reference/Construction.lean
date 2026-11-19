/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.ReturnIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Branches.UniformPassages
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Localization
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.Selection.Transversality
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Reference.Brackets
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Reference.ItineraryNeighborhood
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.Branches

import CAS.ExactTactic

/-!
# Constructing the reference and selecting one flux

Start with the common clock at fast parameter zero. Keep that clock `Y` when
constructing its prescribed extension `X`: their agreement ends at the downward
205 crossing, while `X` supplies the subsequent lower return. Its return time is
the inverse-integral anchor.

One speed/displacement family supplies both event maps. We restrict its parameter
neighborhood successively for the itinerary, both complete gate passages, and the
forcing integral. The last neighborhood works for every continuous supported
forcing before any bump is selected. The transverse selector then constructs a
positive parameter and one full flow with the required matching equations.

The final proposition collects the hypotheses of the retained second-jet
cancellation theorem, together with the stronger inner support and the negative
terminal velocity.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open ClockSwitch MiddleClock Gate.Weights

/-- A common clock, its prescribed extension, and one uniform flow
neighborhood. The integral identity is uniform in the forcing, not a condition imposed on a bump
chosen later. `exists_unconditional_prescribed_clock_reference` constructs this proposition without
reference trajectories or event maps as inputs. -/
structure SelectedReferenceData
    (Y Z X : ℝ → ℝ) (Tclock τ205 τ0 upBaseTime A B Hmax : ℝ)
    (F : ℝ × (ℝ × ℝ) → ℝ × ℝ) (L Bhit : ℝ × ℝ → ℝ)
    (N : Set (ℝ × ℝ)) : Prop where
  common_initial : Y 0 = 0
  fast_initial : Z 0 = 1
  prescribed_initial : X 0 = 0
  fast_ode : ∀ t, HasDerivAt Z (fastLogCosh 0 (Z t)) t
  fast_lower : ∀ t, 0 ≤ t → 1 + t ≤ Z t
  switch_time : Tclock ∈ Ioc 1 (417 / 2)
  common_ode : ∀ t, HasDerivAt Y
    (g (Y t) + clockFeedback (Z Tclock) (Z (Tclock + 1 / 2)) (Z t)) t
  switch_hit : Y Tclock = 415 / 2
  descending_time : Tclock + 1 / 2 < τ205
  descending_hit : Y τ205 = 205
  before_descending_hit : ∀ t ∈ Ico Tclock τ205, 205 < Y t
  prescribed_ode : ∀ t, HasDerivAt X (prescribedClockField A B (Z t) (X t)) t
  common_agreement : EqOn X Y (Icc 0 τ205)
  lower_ode : ∀ t ≥ Tclock + 1 / 2, HasDerivAt X (lowerClockField (X t)) t
  return_time : τ0 ∈ Ioc τ205 (τ205 + 205 / 2)
  return_hit : X τ0 = 0
  lower_strictAnti : StrictAntiOn X (Icc τ205 τ0)
  first_threshold : A = Z Tclock
  second_threshold : B = Z (Tclock + 1 / 2)
  threshold_order : A ^ 2 < B ^ 2
  integral_terminal : (clockGatePassageData upBaseTime τ205 0).terminalTime = τ0
  lower_inverse : ∀ y ∈ Icc (0 : ℝ) 205,
    (clockGatePassageData upBaseTime τ205 0).tMinus y ∈ Icc τ205 τ0 ∧
    X ((clockGatePassageData upBaseTime τ205 0).tMinus y) = y ∧
    ∀ t ∈ Icc τ205 τ0, X t = y ↔
      t = (clockGatePassageData upBaseTime τ205 0).tMinus y
  flow_smooth : ContDiff ℝ ∞ F
  parameter_open : IsOpen N
  parameter_base : (0, 0) ∈ N
  parameter_speed : ∀ p ∈ N, |p.1| < 1 / 410
  flow_initial : ∀ p, F (0, p) = (p.2, 1)
  flow_reference : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t))
    (Icc (-1 : ℝ) (τ0 + 1))
  flow_ode : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
    HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t
  return_smooth : ContDiffOn ℝ ∞ L N
  upward_smooth : ContDiffOn ℝ ∞ Bhit N
  return_base : L (0, 0) = τ0
  upward_base : Bhit (0, 0) = upBaseTime
  return_level : ∀ p ∈ N, (F (L p, p)).1 = 0
  upward_level : ∀ p ∈ N, (F (Bhit p, p)).1 = 205
  return_velocity : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) (L (0, 0))
  upward_velocity : HasDerivAt (fun t ↦ (F (t, (0, 0))).1)
    (g 205 + 1) (Bhit (0, 0))
  cap : Hmax ∈ Ioo τ0 (τ0 + 1 / 2)
  gate_passages : ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
    let D := clockGatePassageData upBaseTime τ205 0
    D.tPlus y ∈ Ioo 1 Tclock ∧ D.tMinus y ∈ Ioc (Tclock + 1 / 2) τ205 ∧
    Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y ∧ 8 / 5 ≤ D.tMinus y - D.tPlus y
  early_geometry : ∀ p ∈ N,
    ∀ t ∈ Icc (0 : ℝ) ((clockGatePassageData upBaseTime τ205 0).tPlus (41001 / 200)),
    (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ (F (t, p)).2 ^ 2 < A ^ 2
  middle_geometry : ∀ p ∈ N,
    ∀ t ∈ Icc ((clockGatePassageData upBaseTime τ205 0).tPlus (41001 / 200))
      ((clockGatePassageData upBaseTime τ205 0).tMinus (41001 / 200)),
    205 < (F (t, p)).1
  late_geometry : ∀ p ∈ N,
    ∀ t ∈ Icc ((clockGatePassageData upBaseTime τ205 0).tMinus (41001 / 200)) Hmax,
    (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 < (F (t, p)).2 ^ 2
  flow_passages : ∀ p ∈ N, ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
    let D := clockGatePassageData upBaseTime τ205 0
    let Dp := parameterizedClockPassageData L Bhit p
    let sUp := (1 + upBaseTime) / 2
    let eUp := (D.tPlus (2051 / 10) + Tclock) / 2
    let sDown := (Tclock + 1 / 2 + D.tMinus (2051 / 10)) / 2
    (Dp.tPlus y ∈ Icc sUp eUp ∧ (F (Dp.tPlus y, p)).1 = y ∧
      ∀ t ∈ Icc sUp eUp, (F (t, p)).1 = y ↔ t = Dp.tPlus y) ∧
    (Dp.tMinus y ∈ Icc sDown (L p) ∧ (F (Dp.tMinus y, p)).1 = y ∧
      ∀ t ∈ Icc sDown (L p), (F (t, p)).1 = y ↔ t = Dp.tMinus y)
  forcing_integral : ∀ b : ℝ → ℝ,
    Continuous b → tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10) → ∀ p ∈ N,
    (∫ t in (0 : ℝ)..L p, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) =
      prescribedClockWeightMoment b L Bhit p

/-- Construct the common and prescribed clocks, both events, and the single
uniform neighborhood needed by the selector. -/
theorem exists_unconditional_prescribed_clock_reference :
    ∃ (Y Z X : ℝ → ℝ) (Tclock τ205 τ0 upBaseTime A B Hmax : ℝ)
      (F : ℝ × (ℝ × ℝ) → ℝ × ℝ) (L Bhit : ℝ × ℝ → ℝ) (N : Set (ℝ × ℝ)),
      SelectedReferenceData Y Z X Tclock τ205 τ0 upBaseTime A B Hmax F L Bhit N := by
  have hδ : |(0 : ℝ)| < 1 / 4 := by cas
  obtain ⟨Y, Z, Tclock, τ205, _τOld, hYzero, hZzero, hZ, hY, hZlower,
    hTclock, hYT, _hbeforeT, _hdT, _hvT, hsq, _hoff, _hswitch,
    hτ205, _hOldOrder, hhit205, _hOldZero, hbefore205, _hOldPositive,
    _hd205, _hv205, _hdOld⟩ := exists_clock_upward_and_return hδ
  -- Keep this same `Y` when choosing its upward integral anchor and lower extension.
  obtain ⟨upBaseTime, hgate⟩ := exists_clock_gate_integral_identification_of_clock
    hδ hZ hZlower hTclock.1.le hY hYzero hYT hτ205 hhit205 hbefore205 0
  obtain ⟨X, τ0, hXzero, hX, heqXY, hpost, hτ0, _hX205, hzero,
    _hpositive, hantiX, _hd0, hterminal, _htimeIntegral, _himage, _halong, hinverse⟩ :=
    exists_prescribed_clock_lower_return_integral hδ hZ hZlower hTclock.1.le
      hYzero hY hτ205 hhit205 hbefore205 upBaseTime 0
  let A := Z Tclock
  let B := Z (Tclock + 1 / 2)
  let D := clockGatePassageData upBaseTime τ205 0
  let sUp := (1 + upBaseTime) / 2
  let eUp := (D.tPlus (2051 / 10) + Tclock) / 2
  let sDown := (Tclock + 1 / 2 + D.tMinus (2051 / 10)) / 2
  have hgateSimple : ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
      D.tPlus y ∈ Ioo 1 Tclock ∧ D.tMinus y ∈ Ioc (Tclock + 1 / 2) τ205 ∧
        Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y := fun y hy ↦
    ⟨(hgate y hy).1, (hgate y hy).2.1, (hgate y hy).2.2.1, (hgate y hy).2.2.2.1⟩
  have hupBase : D.tPlus 205 = upBaseTime := clockGatePassageData_tPlus_base upBaseTime τ205 0
  have hbTime : upBaseTime ∈ Ioo (1 : ℝ) Tclock := by
    simpa only [hupBase] using (hgateSimple 205 ⟨le_rfl, by cas⟩).1
  have hbY : Y upBaseTime = 205 := by
    simpa only [hupBase] using (hgateSimple 205 ⟨le_rfl, by cas⟩).2.2.1
  have hbX : X upBaseTime = 205 :=
    (heqXY ⟨by linarith only [hbTime.1],
      by linarith only [hbTime.2, hτ205]⟩).trans hbY
  have hZlinear (t : ℝ) : HasDerivAt Z (2 * Z t) t := by
    simpa only [fastLogCosh, zero_mul, add_zero] using hZ t
  have hAB : A ^ 2 < B ^ 2 := hsq
  obtain ⟨F, N0, L, Bhit, hN0, h0N0, hμ, hF, hinitial, href, hode,
    hL, hBhit, hLbase, hBbase, hLhit, hBhitLevel, _hLunique, _hBunique⟩ :=
    exists_prescribed_speed_family_events A B (T := Tclock) (d := τ205)
      (τ0 := τ0) (b₀ := upBaseTime) rfl rfl hXzero hZzero hZlinear hZlower
      hτ205 hτ0.1 hbTime hX hbX hzero
  have hLtime := (hLhit (0, 0) h0N0).2.2.2
  have hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1)
      (g 205 + 1) (Bhit (0, 0)) := by
    simpa only [mul_zero, sub_zero] using (hBhitLevel (0, 0) h0N0).2.2.2.2.1
  have hItinerary := prescribed_clock_reference_itinerary (D := D) (A := A) (B := B)
    hZlinear hZlower hTclock.1.le hY hYzero hYT hτ205 hhit205 hbefore205
    heqXY hτ0.1.le hzero hantiX hupBase hgateSimple rfl rfl
  -- The outer cap lies strictly inside the ODE slab; its endpoint is not
  -- an arbitrary local chart time and no later support choice determines it.
  have hrefClosed : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc 0 τ0) :=
    fun t ht ↦ href ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  obtain ⟨Hmax, Ngeo, hcap, hNgeo, h0Ngeo, hgeoSub, hgeometry⟩ :=
    exists_prescribed_clock_itinerary_neighborhood (D := D) (T := Tclock) (upBaseTime := upBaseTime)
      (A := A) (B := B) (Hmax := τ0 + 1 / 2)
      hF.continuous hN0 h0N0 hrefClosed (by linarith) hItinerary
  -- The reference-bracket theorem already derives all the wider branch bands.
  obtain ⟨_hAB, hBbracket, hdownTime, hrefUp, hrefDown, hstartUp, hendUp,
    hstartDown, hupSlab⟩ := prescribed_clock_reference_brackets (D := D)
      (A := A) (B := B) hZlinear hZlower hTclock.1.le hY hYzero hYT
      hτ205 hhit205 hbefore205 heqXY hτ0.1.le hzero hantiX hupBase hgateSimple
      rfl rfl href (hBhitLevel (0, 0) h0N0).1 (hBhitLevel (0, 0) h0N0).2.1
  have hse : sUp ≤ eUp := (hBbracket.1.trans hBbracket.2).le
  have hupTime : -1 ≤ sUp ∧ eUp ≤ τ0 + 1 := ⟨(hupSlab ⟨le_rfl, hse⟩).1, (hupSlab ⟨hse, le_rfl⟩).2⟩
  obtain ⟨Npass, hNpass, h0Npass, hpassSub, hpassages⟩ :=
    exists_prescribed_speed_uniform_passages (sUp := sUp) (eUp := eUp) (sDown := sDown)
      hAB hF.continuous hNgeo h0Ngeo (fun p hp ↦ hμ p (hgeoSub hp)) (fun p hp ↦ hode p (hgeoSub hp))
      (hL.mono hgeoSub).continuousOn (hBhit.mono hgeoSub).continuousOn hLbase hBbracket
      (fun p hp ↦ (hLhit p (hgeoSub hp)).2.1) (fun p hp ↦ (hBhitLevel p (hgeoSub hp)).2.1)
      hupTime hdownTime hrefUp hrefDown hstartUp hendUp hstartDown
  have hpassSub0 : Npass ⊆ N0 := fun _ hp ↦ hgeoSub (hpassSub hp)
  -- This final restriction precedes `∀ b`: the selector may choose its entire
  -- smooth coefficient family afterwards without changing the neighborhood.
  obtain ⟨N, hN, h0N, hNsub, hMoment⟩ := exists_prescribed_speed_integral_eq_weight_moment
      (sUp := sUp) (eUp := eUp) (sDown := sDown)
      hF.continuous hNpass h0Npass (hL.mono hpassSub0) (hBhit.mono hpassSub0)
      hItinerary.1.1.le hItinerary.1.2.2.2.1.le (fun p hp ↦ (hgeometry p (hpassSub hp)).2.2.2.2.1)
      (fun p hp ↦ (hgeometry p (hpassSub hp)).2.2.2.2.2) hpassages
  have hNgeoSub : N ⊆ Ngeo := fun _ hp ↦ hpassSub (hNsub hp)
  have hN0Sub : N ⊆ N0 := fun _ hp ↦ hgeoSub (hNgeoSub hp)
  exact ⟨Y, Z, X, Tclock, τ205, τ0, upBaseTime, A, B, Hmax, F, L, Bhit, N, {
    common_initial := hYzero
    fast_initial := hZzero
    prescribed_initial := hXzero
    fast_ode := hZ
    fast_lower := hZlower
    switch_time := hTclock
    common_ode := hY
    switch_hit := hYT
    descending_time := hτ205
    descending_hit := hhit205
    before_descending_hit := hbefore205
    prescribed_ode := hX
    common_agreement := heqXY
    lower_ode := hpost
    return_time := hτ0
    return_hit := hzero
    lower_strictAnti := hantiX
    first_threshold := rfl
    second_threshold := rfl
    threshold_order := hAB
    integral_terminal := hterminal
    lower_inverse := hinverse
    flow_smooth := hF
    parameter_open := hN
    parameter_base := h0N
    parameter_speed := fun p hp ↦ hμ p (hN0Sub hp)
    flow_initial := hinitial
    flow_reference := href
    flow_ode := fun p hp ↦ hode p (hN0Sub hp)
    return_smooth := hL.mono hN0Sub
    upward_smooth := hBhit.mono hN0Sub
    return_base := hLbase
    upward_base := hBbase
    return_level := fun p hp ↦ (hLhit p (hN0Sub hp)).2.1
    upward_level := fun p hp ↦ (hBhitLevel p (hN0Sub hp)).2.1
    return_velocity := hLtime
    upward_velocity := hBtime
    cap := hcap
    gate_passages := hgate
    early_geometry := fun p hp ↦ (hgeometry p (hNgeoSub hp)).1
    middle_geometry := fun p hp ↦ (hgeometry p (hNgeoSub hp)).2.1
    late_geometry := fun p hp ↦ (hgeometry p (hNgeoSub hp)).2.2.2.1
    flow_passages := fun p hp ↦ hpassages p (hNsub hp)
    forcing_integral := hMoment }⟩

/-- The selected data used by the retained second-jet cancellation
theorem. The three scalar matching equations, gate determinants, canonical tangent
expansion and negative terminal velocity belong to this same `Ψ`, `T`, and flux.
The whole initial section is retained for every parameter, while the ODE is
asserted only on its compact time slab and open parameter domain. -/
structure SelectedRankInputs
    (δ A B H tStar : ℝ) (c : Fin 3 → ℝ) (b : (Fin 3 → ℝ) × ℝ → ℝ)
    (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
    (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
    (N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))) (i j : Fin 3) : Prop where
  positive : 0 < δ
  small : δ < 1 / 4
  threshold_order : A ^ 2 < B ^ 2
  forcing_smooth : ContDiff ℝ ∞ b
  forcing_support : ∀ c', HasCompactSupport (fun y ↦ b (c', y)) ∧
    tsupport (fun y ↦ b (c', y)) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100)
  gate_support : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)
  flow_smooth : ContDiff ℝ ∞ Ψ
  parameter_open : IsOpen N
  selected_mem : ((δ, c), (0, 0)) ∈ N
  event_smooth : ContDiffOn ℝ ∞ T N
  initial : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3)
  ode : ∀ θ ∈ N, ∀ s ∈ Icc (0 : ℝ) H,
    HasDerivAt (fun u ↦ Ψ (u, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B)
        (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 • Ψ (s, θ)) s
  event : ∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0
  distinct : i ≠ j
  gate_time : tStar ∈ Ioo (0 : ℝ) (T ((δ, c), (0, 0)))
  gate_state : Ψ (tStar, ((δ, c), (0, 0))) 1 ∈ Ioo (205 : ℝ) (2051 / 10) ∧
    2 < Ψ (tStar, ((δ, c), (0, 0))) 2 ∧
    (Ψ (tStar, ((δ, c), (0, 0))) 2) ^ 2 < A ^ 2
  terminal_positive : 0 < retainedTerminalState Ψ T (δ, c) (0, 0) 2
  terminal_ratio : retainedTerminalState Ψ T (δ, c) (0, 0) 0 /
    retainedTerminalState Ψ T (δ, c) (0, 0) 2 = 1
  displacement_match : deriv (fun a ↦ retainedTerminalState Ψ T (δ, c) (0, a) 0 /
    retainedTerminalState Ψ T (δ, c) (0, a) 2) 0 = 0
  weighted_match :
    let Q := retainedTerminalState Ψ T (δ, c)
    Q (0, 0) 2 * deriv (fun μ ↦ Q (μ, 0) 0 / Q (μ, 0) 2) 0 +
      2 * deriv (fun μ ↦ Q (μ, 0) 2) 0 +
      2000000 * deriv (fun a ↦ Q (0, a) 2) 0 = 0
  gate_rank :
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, ((δ, c), (0, 0)))
    let W := prescribedClockFullVariation Ψ (δ, c) (1, 0)
    let r := GatedFlux.rightEigenvector (fastLogCosh δ) g cutoff
      (clockFeedback A B) (fun y ↦ b (c, y)) (γ tStar)
    Matrix.det ![⇑(deriv γ tStar), ⇑(r i), ⇑(W tStar)] ≠ 0 ∧
    Matrix.det ![⇑(deriv γ tStar), ⇑(r j), ⇑(W tStar)] ≠ 0 ∧
    ∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ deriv γ tStar = ∑ k, a k • r k
  terminal_velocity :
    (concreteGatedFlux δ (clockFeedback A B) (fun y ↦ b (c, y))
      (retainedTerminalState Ψ T (δ, c) (0, 0))) 1 < -4
  event_velocity : ∀ θ ∈ N, eventMiddleVelocity Ψ T θ < -4
  global_flux :
    let f := concreteGatedFlux δ (clockFeedback A B) (fun y ↦ b (c, y))
    ContDiff ℝ ∞ f ∧ IsStrictlyHyperbolicOn f univ ∧
      ∀ k : Fin 3, IsGenuinelyNonlinearFamily f k

/-- There is a selected positive-parameter flux and full family on its original time domain
with all the inputs needed for retained second-jet cancellation. The proof first constructs the
reference and then applies the transverse selector. -/
theorem exists_unconditional_selected_rank_inputs :
    ∃ (δ A B H tStar : ℝ) (c : Fin 3 → ℝ) (b : (Fin 3 → ℝ) × ℝ → ℝ)
      (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
      (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
      (N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))) (i j : Fin 3),
      SelectedRankInputs δ A B H tStar c b Ψ T N i j := by
  obtain ⟨Y, Z, X, Tclock, τ205, τ0, upBaseTime, A, B, Hmax, F, L, Bhit, N, hR⟩ :=
    exists_unconditional_prescribed_clock_reference
  have hHslab : Hmax < τ0 + 1 := by linarith only [hR.cap.2]
  obtain ⟨β, hselected⟩ := exists_prescribed_clock_selected_positive_rank_transverse
    (κ := 0) (ε := 1) hR.fast_ode hR.fast_lower hR.switch_time.1.le
    hR.common_ode hR.common_initial hR.switch_hit hR.descending_time
    hR.descending_hit hR.before_descending_hit hR.common_agreement hR.return_time.1.le
    hR.lower_ode hR.return_hit hR.lower_strictAnti hR.first_threshold hR.second_threshold
    hR.flow_smooth hR.parameter_open hR.parameter_base hR.return_smooth hR.upward_smooth
    hR.return_base hR.upward_base hR.flow_reference hR.cap.1 hHslab hR.flow_ode
    (fun p _ ↦ hR.flow_initial p) hR.return_level hR.upward_level
    hR.return_velocity hR.upward_velocity one_pos
    hR.gate_passages hR.early_geometry hR.middle_geometry hR.late_geometry hR.forcing_integral
  let D0 := parameterizedClockPassageData L Bhit (0, 0)
  let b : (Fin 3 → ℝ) × ℝ → ℝ := fun w ↦ (Ioo (205 : ℝ) (2051 / 10)).indicator
      (fun y ↦ (∑ j, w.1 j * β j y) / D0.wMinus y) w.2
  obtain ⟨_cStar, H, Ψ, T, Nout, _Uout, _Vout, _S, δ, c, tStar, i, j, _Ω,
    _hβ, _hdisjoint, hb, hsupport, _hH, hΨ, hinitial, hNout, _hbaseOut,
    _hS, _hbaseS, _hselectedS, _hNoutS, hode, hT, _hTbase, hevent,
    _hUout, _h0Uout, _hUoutN, _hVout, _hcStar, _hc, _hcommon,
    hδpos, hδsmall, hselectedMem, _htBranch, htStar, hgate, hzgate, hAgate,
    hij, hi, hj, hexpansion, hz, hratio, hdisplacement, hweighted,
    hflux, hhyper, hGN, _hΩ, _h0Ω, _hpaths, hvelocity, hterminalVelocity⟩ := hselected
  have hsmall : δ < 1 / 4 := hδsmall.trans_le (min_le_right _ _)
  exact ⟨δ, A, B, H, tStar, c, b, Ψ, T, Nout, i, j, {
    positive := hδpos
    small := hsmall
    threshold_order := hR.threshold_order
    forcing_smooth := hb
    forcing_support := fun c' ↦ ⟨(hsupport c').1, (hsupport c').2.2⟩
    gate_support := (hsupport c).2.2.trans (Ioo_subset_Ioo (by norm_num) (by norm_num))
    flow_smooth := hΨ
    parameter_open := hNout
    selected_mem := hselectedMem
    event_smooth := hT
    initial := hinitial
    ode := hode
    event := hevent
    distinct := hij
    gate_time := htStar
    gate_state := ⟨hgate, hzgate, hAgate⟩
    terminal_positive := hz
    terminal_ratio := hratio
    displacement_match := hdisplacement
    weighted_match := hweighted
    gate_rank := ⟨hi, hj, hexpansion⟩
    terminal_velocity := hterminalVelocity
    event_velocity := hvelocity
    global_flux := ⟨hflux, hhyper, hGN⟩ }⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
