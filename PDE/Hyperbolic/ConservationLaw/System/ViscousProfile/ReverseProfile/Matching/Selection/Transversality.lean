/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Rank.Full
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.Selection.FullTerminal
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Reference.Itinerary

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.ReturnIntegral
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Rank.Persistence
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.Selection.PositiveParameter
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# A transverse terminal section retained before positive-parameter selection

The reference middle velocity is `-8`. Smooth dependence of the full flow and
its event time gives an open parameter neighborhood where this velocity
stays below `-4`. The matching selector runs inside that neighborhood, together
with the gate-rank restrictions. Both physical speed paths remain in it.

The strengthened selection theorem keeps the same full flow, terminal map,
coefficient family and physical variation through this restriction. The negative
velocity is an output of the selection, ready for the middle-coordinate section
used by the integrated correction.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open ClockSwitch Gate.Weights MiddleClock

/-- The middle time derivative of a full flow at its retained event time.
The time derivative is taken with the parameter fixed. -/
def eventMiddleVelocity {E : Type*} (Ψ : ℝ × E → ℝ^3) (T : E → ℝ) (θ : E) : ℝ :=
  deriv (fun s ↦ Ψ (s, θ) 1) (T θ)

/-- A smoothly moving event preserves continuity of the flow's middle velocity.
Differentiation is in time before evaluation at the moving event. -/
theorem continuousOn_eventMiddleVelocity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ × E → ℝ^3} {T : E → ℝ} {N : Set E} (hΨ : ContDiff ℝ ∞ Ψ) (hT : ContDiffOn ℝ ∞ T N) :
    ContinuousOn (eventMiddleVelocity Ψ T) N := by
  have hmiddle : ContDiff ℝ ∞ (fun p : E × ℝ ↦ Ψ (p.2, p.1) 1) :=
    (show ContDiff ℝ ∞ (fun u : ℝ^3 ↦ u 1) from contDiff_piLp_apply (2 : ENNReal)).comp
        (hΨ.comp (contDiff_snd.prodMk contDiff_fst))
  have hderiv : ContDiff ℝ (0 : ℕ) (fun p : E × ℝ ↦ deriv (fun s ↦ Ψ (s, p.1) 1) p.2) :=
    contDiff_deriv_prod_snd (m := 0) (hmiddle.of_le (by simp))
  exact hderiv.continuous.comp_continuousOn (continuousOn_id.prodMk hT.continuousOn)

/-- For a zero-speed trajectory, the event velocity is the middle
component of the vector field at the terminal state. -/
theorem eventMiddleVelocity_eq_field_middle {E : Type*} {Ψ : ℝ × E → ℝ^3} {T : E → ℝ} {θ : E}
    {f : (ℝ^3) → ℝ^3} (hode : HasDerivAt (fun s ↦ Ψ (s, θ)) (f (Ψ (T θ, θ))) (T θ)) :
    eventMiddleVelocity Ψ T θ = f (Ψ (T θ, θ)) 1 := by
  have hmiddle : HasDerivAt (fun s ↦ Ψ (s, θ) 1)
      (f (Ψ (T θ, θ)) 1) (T θ) := by
    simpa only [Function.comp_def] using!
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) (Ψ (T θ, θ)) (1 : Fin 3)).comp_hasDerivAt
        (T θ) hode
  exact hmiddle.deriv

/-- If the middle coordinate of the flow at `θ` agrees on `Icc a b` with a curve `φ`
and `HasDerivAt φ v (T θ)` at an event time `T θ ∈ Ioo a b`, then
`eventMiddleVelocity Ψ T θ = v`. -/
theorem eventMiddleVelocity_eq_of_eqOn {E : Type*} {Ψ : ℝ × E → ℝ^3} {T : E → ℝ} {θ : E} {φ : ℝ → ℝ}
    {a b v : ℝ} (heq : EqOn (fun s ↦ Ψ (s, θ) 1) φ (Icc a b)) (hT : T θ ∈ Ioo a b)
    (hφ : HasDerivAt φ v (T θ)) :
    eventMiddleVelocity Ψ T θ = v := by
  have hnear : (fun s ↦ Ψ (s, θ) 1) =ᶠ[𝓝 (T θ)] φ := by
    filter_upwards [Icc_mem_nhds hT.1 hT.2] with s hs
    exact heq hs
  exact (hφ.congr_of_eventuallyEq hnear).deriv

/-- At the base parameter the upward passage times of the event-defined data are those of
the clock gate data with the same upward anchor `Bhit (0, 0) = upBaseTime`. -/
theorem parameterizedClockPassageData_zero_tPlus {L Bhit : ℝ × ℝ → ℝ}
    {upBaseTime downBaseTime κ : ℝ} (hBhit : Bhit (0, 0) = upBaseTime) :
    (parameterizedClockPassageData L Bhit (0, 0)).tPlus =
      (clockGatePassageData upBaseTime downBaseTime κ).tPlus := by
  funext y
  simp only [parameterizedClockPassageData_zero, clockGatePassageData, PassageData.tPlus,
    clockPassageData, hBhit]

/-- At the base parameter the downward passage times of the event-defined data are those of
the clock gate data whose terminal time is the base event time `L (0, 0)`. -/
theorem parameterizedClockPassageData_zero_tMinus {L Bhit : ℝ × ℝ → ℝ}
    {upBaseTime downBaseTime κ : ℝ}
    (hterminal : (clockGatePassageData upBaseTime downBaseTime κ).terminalTime = L (0, 0)) :
    (parameterizedClockPassageData L Bhit (0, 0)).tMinus =
      (clockGatePassageData upBaseTime downBaseTime κ).tMinus := by
  funext y
  rw [PassageData.tMinus, PassageData.tMinus, hterminal]
  simp only [parameterizedClockPassageData_zero, clockGatePassageData, PassageData.downTime,
    PassageData.downSpeed, clockPassageData]

/-- A trajectory `X` that agrees with `Y` on `Icc 0 τ205` satisfies the upward equation
`X' = g X + 1` wherever `Y` does on `Icc 1 Tclock`, provided `Tclock < τ205`. -/
private theorem hasDerivAt_g_add_one_of_eqOn {X Y : ℝ → ℝ} {Tclock τ205 : ℝ}
    (heqXY : EqOn X Y (Icc 0 τ205)) (hT205 : Tclock < τ205)
    (hupY : ∀ t ∈ Icc 1 Tclock, HasDerivAt Y (g (Y t) + 1) t) :
    ∀ t ∈ Icc 1 Tclock, HasDerivAt X (g (X t) + 1) t := by
  intro t ht
  have hnear : X =ᶠ[𝓝 t] Y := by
    filter_upwards [Ioo_mem_nhds (zero_lt_one.trans_le ht.1) (ht.2.trans_lt hT205)] with s hs
    exact heqXY ⟨hs.1.le, hs.2.le⟩
  simpa only [hnear.eq_of_nhds] using (hupY t ht).congr_of_eventuallyEq hnear

/-- The switch value `B = Z (Tclock + 1 / 2)` of the fast clock lies below its value
`(F (τ0, (0, 0))).2 = Z τ0` at the terminal time `τ0` of the reference flow. -/
private theorem switch_lt_terminal_snd {X Z : ℝ → ℝ} {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {Tclock τ0 B : ℝ}
    (hZfast : ∀ t, HasDerivAt Z (fastLogCosh 0 (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hS0 : 0 ≤ Tclock + 1 / 2) (hSτ : Tclock + 1 / 2 < τ0) (hB : B = Z (Tclock + 1 / 2))
    (hBnonneg : 0 ≤ B)
    (href : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc (-1 : ℝ) (τ0 + 1))) :
    B < (F (τ0, (0, 0))).2 := by
  have hτ0pos : 0 < τ0 := hS0.trans_lt hSτ
  rw [congrArg Prod.snd (href (show τ0 ∈ Icc (-1 : ℝ) (τ0 + 1) from ⟨by linarith, by linarith⟩))]
  refine (sq_lt_sq₀ hBnonneg (by linarith [hZlower τ0 hτ0pos.le])).mp ?_
  rw [hB]
  exact strictMonoOn_fast_clock_sq (by cas) hZfast hZlower hS0 hτ0pos.le hSτ

/-- If `N` is open and contains `((e, c₀), p₀)`, then open neighborhoods `V` of `c₀` and
`U` of `p₀` contain open neighborhoods `V'` and `U'` with `((e, c), p) ∈ N` for all
`c ∈ V'` and `p ∈ U'`. -/
private theorem exists_isOpen_prod_subset_slice {E C P : Type*} [TopologicalSpace E]
    [TopologicalSpace C] [TopologicalSpace P] {N : Set ((E × C) × P)} {V : Set C} {U : Set P}
    {e : E} {c₀ : C} {p₀ : P} (hN : IsOpen N) (hV : IsOpen V) (hU : IsOpen U) (hc₀ : c₀ ∈ V)
    (hp₀ : p₀ ∈ U) (hbase : ((e, c₀), p₀) ∈ N) :
    ∃ V' U', IsOpen V' ∧ c₀ ∈ V' ∧ IsOpen U' ∧ p₀ ∈ U' ∧ V' ⊆ V ∧ U' ⊆ U ∧
      ∀ p ∈ U', ∀ c ∈ V', ((e, c), p) ∈ N := by
  let ι : C × P → (E × C) × P := fun u ↦ ((e, u.1), u.2)
  have hι : Continuous ι := (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  have hdomain : IsOpen ((V ×ˢ U) ∩ ι ⁻¹' N) := (hV.prod hU).inter (hN.preimage hι)
  obtain ⟨V', U', hV', hc', hU', hp', hsub⟩ :=
    mem_nhds_prod_iff'.mp (hdomain.mem_nhds ⟨⟨hc₀, hp₀⟩, hbase⟩)
  exact ⟨V', U', hV', hc', hU', hp', fun c hc ↦ (hsub (mk_mem_prod hc hp')).1.1,
    fun p hp ↦ (hsub (mk_mem_prod hc' hp)).1.2, fun p hp c hc ↦ (hsub (mk_mem_prod hc hp)).2⟩

/-- Select moments and a positive matching parameter once, retaining the full
flow, terminal event, two nonzero gate determinants, and the all-nonzero tangent
expansion in the same normalized eigenvectors for that same flux. The middle
velocity at every retained terminal event is below `-4`. This neighborhood is
chosen using the reference velocity `-8`, before the positive parameter is chosen.

The hypotheses under `D` are the retained given-clock passage conclusion and the
uniform itinerary/localization conclusions for `F`. The lower equation
retains its full cutoff. The event-level and time-derivative hypotheses are outputs
of the original speed-event construction, not derivatives of a matching residual. -/
theorem exists_prescribed_clock_selected_positive_rank_transverse {Y Z X : ℝ → ℝ}
    {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ} {N : Set (ℝ × ℝ)}
    {Tclock τ205 τ0 upBaseTime κ A B Hmax ε : ℝ}
    (hZfast : ∀ t, HasDerivAt Z (fastLogCosh 0 (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t)
    (hTclock : 1 ≤ Tclock)
    (hY : ∀ t, HasDerivAt Y (g (Y t) + clockFeedback (Z Tclock) (Z (Tclock + 1 / 2)) (Z t)) t)
    (hYzero : Y 0 = 0) (hYT : Y Tclock = 415 / 2) (hτ205 : Tclock + 1 / 2 < τ205)
    (hhit205 : Y τ205 = 205) (hbefore205 : ∀ t ∈ Ico Tclock τ205, 205 < Y t)
    (heqXY : EqOn X Y (Icc 0 τ205)) (hτ0 : τ205 ≤ τ0)
    (hpost : ∀ t ≥ Tclock + 1 / 2, HasDerivAt X (lowerClockField (X t)) t) (hzero : X τ0 = 0)
    (hantiX : StrictAntiOn X (Icc τ205 τ0)) (hA : A = Z Tclock) (hB : B = Z (Tclock + 1 / 2))
    (hF : ContDiff ℝ ∞ F) (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N)
    (hBhit : ContDiffOn ℝ ∞ Bhit N) (hLbase : L (0, 0) = τ0) (hBhitbase : Bhit (0, 0) = upBaseTime)
    (href : EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t)) (Icc (-1 : ℝ) (τ0 + 1)))
    (hHmax : τ0 < Hmax) (hHslab : Hmax < τ0 + 1)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1)) (hLlevel : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hBlevel : ∀ p ∈ N, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) (L (0, 0)))
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (g 205 + 1) (Bhit (0, 0))) (hε : 0 < ε) :
    let D := clockGatePassageData upBaseTime τ205 κ
    let rUp := D.tPlus (41001 / 200)
    let rDown := D.tMinus (41001 / 200)
    (∀ y ∈ Icc (205 : ℝ) (2051 / 10),
      D.tPlus y ∈ Ioo 1 Tclock ∧ D.tMinus y ∈ Ioc (Tclock + 1 / 2) τ205 ∧
      Y (D.tPlus y) = y ∧ Y (D.tMinus y) = y ∧
      8 / 5 ≤ D.tMinus y - D.tPlus y) →
    (∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) rUp,
      (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ (F (t, p)).2 ^ 2 < A ^ 2) →
    (∀ p ∈ N, ∀ t ∈ Icc rUp rDown, (205 : ℝ) < (F (t, p)).1) →
    (∀ p ∈ N, ∀ t ∈ Icc rDown Hmax,
      (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 < (F (t, p)).2 ^ 2) →
    (∀ b : ℝ → ℝ,
      Continuous b → tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10) → ∀ p ∈ N,
        (∫ t in (0 : ℝ)..L p, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) =
          prescribedClockWeightMoment b L Bhit p) →
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    ∃ β : Fin 3 → ℝ → ℝ,
      let b : (Fin 3 → ℝ) × ℝ → ℝ := fun w ↦
        (Ioo (205 : ℝ) (2051 / 10)).indicator
          (fun y ↦ (∑ j, w.1 j * β j y) / D0.wMinus y) w.2
      let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
        !₂[(F (t, p)).2 * scalarLinearSolution (fun _ : ℝ ↦ 4)
            (fun s ↦ b (c, (F (s, p)).1)) 0 0 t,
          (F (t, p)).1, (F (t, p)).2]
      ∃ (cStar : Fin 3 → ℝ) (H : ℝ)
        (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
        (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
        (Nout : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)))
        (Uout : Set (ℝ × ℝ)) (Vout : Set (Fin 3 → ℝ))
        (S : Set (ℝ × (Fin 3 → ℝ)))
        (δPos : ℝ) (cPos : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) (Ω : Set ℝ),
        let x : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ := fun θ ↦ Ψ (T θ, θ) 0
        let z : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ := fun θ ↦ Ψ (T θ, θ) 2
        let ρ : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ := fun θ ↦ x θ / z θ
        let f := concreteGatedFlux δPos (clockFeedback A B) (fun y ↦ b (cPos, y))
        let γ : ℝ → ℝ^3 := fun s ↦ Ψ (s, ((δPos, cPos), (0, 0)))
        let v : ℝ → ℝ^3 := deriv γ
        let W : ℝ → ℝ^3 := prescribedClockFullVariation Ψ (δPos, cPos) (1, 0)
        let r : Fin 3 → ℝ^3 := GatedFlux.rightEigenvector (fastLogCosh δPos)
          g cutoff (clockFeedback A B) (fun y ↦ b (cPos, y)) (γ t)
        (∀ k, ContDiff ℝ ∞ (β k) ∧ HasCompactSupport (β k) ∧
          tsupport (β k) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) ∧
          (∀ y, 0 ≤ β k y) ∧ (∫ y, β k y) = 1) ∧
        Pairwise (fun k l ↦ Disjoint (tsupport (β k)) (tsupport (β l))) ∧
        ContDiff ℝ ∞ b ∧
        (∀ c, HasCompactSupport (fun y ↦ b (c, y)) ∧
          tsupport (fun y ↦ b (c, y)) ⊆ ⋃ k, tsupport (β k) ∧
          tsupport (fun y ↦ b (c, y)) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100)) ∧
        H ∈ Ioo τ0 Hmax ∧ ContDiff ℝ ∞ Ψ ∧
        (∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3)) ∧
        IsOpen Nout ∧ ((0, cStar), (0, 0)) ∈ Nout ∧
        IsOpen S ∧ (0, cStar) ∈ S ∧ (δPos, cPos) ∈ S ∧ Nout ⊆ Prod.fst ⁻¹' S ∧
        (∀ θ ∈ Nout, ∀ s ∈ Icc (0 : ℝ) H,
          HasDerivAt (fun u ↦ Ψ (u, θ))
            (concreteGatedFlux θ.1.1 (clockFeedback A B)
              (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 • Ψ (s, θ)) s) ∧
        ContDiffOn ℝ ∞ T Nout ∧ T ((0, cStar), (0, 0)) = τ0 ∧
        (∀ θ ∈ Nout, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) ∧
        IsOpen Uout ∧ (0, 0) ∈ Uout ∧ Uout ⊆ N ∧
        IsOpen Vout ∧ cStar ∈ Vout ∧ cPos ∈ Vout ∧
        (∀ p ∈ Uout, ∀ c ∈ Vout,
          ((0, c), p) ∈ Nout ∧ T ((0, c), p) = L p ∧
          EqOn (fun s ↦ Ψ (s, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
          Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p)) ∧
        0 < δPos ∧ δPos < min ε (1 / 4) ∧ ((δPos, cPos), (0, 0)) ∈ Nout ∧
        t ∈ Ioo (D0.tPlus (41001 / 200)) (D0.tPlus (2051 / 10)) ∧
        t ∈ Ioo (0 : ℝ) (T ((δPos, cPos), (0, 0))) ∧
        γ t 1 ∈ Ioo (205 : ℝ) (2051 / 10) ∧ 2 < γ t 2 ∧ (γ t 2) ^ 2 < A ^ 2 ∧
        i ≠ j ∧ Matrix.det ![⇑(v t), ⇑(r i), ⇑(W t)] ≠ 0 ∧
        Matrix.det ![⇑(v t), ⇑(r j), ⇑(W t)] ≠ 0 ∧
        (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ v t = ∑ k, a k • r k) ∧
        0 < z ((δPos, cPos), (0, 0)) ∧ ρ ((δPos, cPos), (0, 0)) = 1 ∧
        deriv (fun a : ℝ ↦ ρ ((δPos, cPos), (0, a))) 0 = 0 ∧
        z ((δPos, cPos), (0, 0)) *
            deriv (fun μ : ℝ ↦ ρ ((δPos, cPos), (μ, 0))) 0 +
          2 * deriv (fun μ : ℝ ↦ z ((δPos, cPos), (μ, 0))) 0 +
          2000000 * deriv (fun a : ℝ ↦ z ((δPos, cPos), (0, a))) 0 = 0 ∧
        ContDiff ℝ ∞ f ∧ IsStrictlyHyperbolicOn f univ ∧
        (∀ k : Fin 3, IsGenuinelyNonlinearFamily f k) ∧
        IsOpen Ω ∧ (0 : ℝ) ∈ Ω ∧
        (∀ μ ∈ Ω,
          ((δPos, cPos), (μ, 0)) ∈ Nout ∧
          ((δPos, cPos), (-μ, -2000000 * μ)) ∈ Nout ∧
          0 < z ((δPos, cPos), (μ, 0)) ∧
          0 < z ((δPos, cPos), (-μ, -2000000 * μ))) ∧
        (∀ θ ∈ Nout, eventMiddleVelocity Ψ T θ < -4) ∧
        (f (γ (T ((δPos, cPos), (0, 0))))) 1 < -4 := by
  classical
  intro D rUp rDown hgate hearly hmiddle hlate hlocalize D0
  have hδ : |(0 : ℝ)| < 1 / 4 := by cas
  have hZlinear (t : ℝ) : HasDerivAt Z (2 * Z t) t := by
    simpa only [fastLogCosh, zero_mul, add_zero] using hZfast t
  have hT0 : 0 ≤ Tclock := zero_le_one.trans hTclock
  have hS0 : 0 ≤ Tclock + 1 / 2 := by cas using [hT0]
  have hT205 : Tclock < τ205 := by cas using [hτ205]
  have hTτ : Tclock < τ0 := hT205.trans_le hτ0
  -- Only passage functions are identified; the event-defined normalizer stays fixed.
  have hPlus : D0.tPlus = D.tPlus := parameterizedClockPassageData_zero_tPlus hBhitbase
  have hMinus : D0.tMinus = D.tMinus := parameterizedClockPassageData_zero_tMinus
    ((prescribed_lower_return_integral_identification hτ0 (fun t ht ↦ hpost t (hτ205.le.trans ht.1))
      ((heqXY ⟨hS0.trans hτ205.le, le_rfl⟩).trans hhit205) hzero hantiX upBaseTime κ).1.trans
      hLbase.symm)
  have hupBase : D.tPlus 205 = upBaseTime := clockGatePassageData_tPlus_base upBaseTime τ205 κ
  have hgateX : ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
      D0.tPlus y ∈ Ioo 1 Tclock ∧ X (D0.tPlus y) = y := by
    intro y hy
    obtain ⟨hp, _, hyp, _, _⟩ := hgate y hy
    rw [hPlus]
    exact ⟨hp, (heqXY ⟨zero_le_one.trans hp.1.le, (hp.2.trans hT205).le⟩).trans hyp⟩
  have hItinerary := prescribed_clock_reference_itinerary
    (D := D) (upBaseTime := upBaseTime) hZlinear hZlower hTclock hY hYzero hYT
    hτ205 hhit205 hbefore205 heqXY hτ0 hzero hantiX hupBase
    (fun y hy ↦ by obtain ⟨hp, hm, hyp, hym, _⟩ := hgate y hy; exact ⟨hp, hm, hyp, hym⟩) hA hB
  have hZmono := strictMonoOn_fast_clock_sq hδ hZfast hZlower
  have hAB : A ^ 2 < B ^ 2 := by rw [hA, hB]; exact hZmono hT0 hS0 (by cas)
  have hBnonneg : 0 ≤ B := by linarith [hZlower _ hS0]
  have hBmem : Bhit (0, 0) ∈ Icc (0 : ℝ) (τ0 + 1) := by
    obtain ⟨h1, h2⟩ := hupBase ▸ (hgate 205 ⟨le_rfl, by cas⟩).1
    rw [hBhitbase]
    constructor <;> linarith
  -- This is the only moment selection and the only full-flow/event construction.
  obtain ⟨β, cStar, H, U, V, hβ, hdisjoint, _, _, hb, hbsupport,
    hH, hU, h0U, hUN, hV, hcV, hzpos, _, hGold, hJUnit, hGoldzero,
    Ψ, T, Nfull, U0, V0, hNfull, hbaseFull, hΨ, hΨzero, hodeFull,
    hT, hTbase, hThit, _, hU0, h0U0, hU0U, hV0, hcV0, hV0V, hcommon⟩ :=
    exists_prescribed_clock_selected_full_terminal
      hF hN hbase hL hBhit hLbase (hS0.trans (hgate (41001 / 200) ⟨by cas, by cas⟩).2.1.1.le)
      hItinerary.1.2.2.2.2.2 hHmax hHslab hAB hBnonneg
      (switch_lt_terminal_snd hZfast hZlower hS0 (hτ205.trans_le hτ0) hB hBnonneg href)
      hode hinitial hearly hmiddle hlate hlocalize
      (fun y hy ↦ by rw [hMinus, hPlus]; exact (hgate y ⟨hy.1.le, hy.2.le⟩).2.2.2.2)
      hBmem hLlevel hBlevel hLtime hBtime
  refine ⟨β, ?_⟩
  intro b q
  have hbsupp (c : Fin 3 → ℝ) : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10) :=
    (hbsupport c).2.2.trans (Ioo_subset_Ioo (by cas) (by cas))
  obtain ⟨t, htH, htBranch, hy, hz, hzA, i, j, hij, hi, hj, a0, ha0, hdecomp0⟩ :=
    exists_prescribed_clock_full_gate_det_ne_zero
      (F := F) (L := L) (b := b) (cStar := cStar) (Ψ := Ψ)
      (N := Nfull) (U0 := U0) (V0 := V0) (X := X) (Z := Z) (tPlus := D0.tPlus)
      (A := A) (B := B) (T := Tclock) (τ0 := τ0) (H := H)
      hF.continuous hb hΨ hNfull hbaseFull hodeFull (hbsupport cStar).2.2
      h0U0 hcV0 hLbase (hzpos (0, 0) h0U) href hTτ hH.1
      (hasDerivAt_g_add_one_of_eqOn heqXY hT205 (clock_gate_branch_properties hδ hZfast
        hZlower hTclock hY hYzero hYT hhit205 hbefore205).1)
      hgateX (by rw [hPlus]; exact fun t ht ↦ (hItinerary.2.1 t ht).1.2) (fun t _ ↦ hZlinear t)
      (fun t ht ↦ hZlower t (zero_le_one.trans ht.1))
      (fun t ht ↦ hA ▸ hZmono (zero_le_one.trans ht.1.le) hT0 ht.2) hAB hGoldzero
      (fun p hp c hc ↦ (hcommon p hp c hc).2.2.1)
  have hvBase : deriv (fun s ↦ Ψ (s, ((0, cStar), (0, 0)))) t =
      concreteGatedFlux 0 (clockFeedback A B) (fun y ↦ b (cStar, y))
        (Ψ (t, ((0, cStar), (0, 0)))) := by
    simpa only [zero_smul, sub_zero] using
      (hodeFull ((0, cStar), (0, 0)) hbaseFull t ⟨htH.1.le, htH.2.le⟩).deriv
  obtain ⟨S, hS, hbaseS, _, _, hpersist⟩ :=
    exists_prescribed_clock_gate_determinants_ne_zero_nhds hΨ hb hbsupp cStar
      hAB hy hz hzA i j hij (by simpa only [hvBase] using hi) (by simpa only [hvBase] using hj)
      ⟨a0, ha0, hvBase.symm.trans hdecomp0⟩
  -- Restrict the same event domain and coefficient neighborhood, including t < T.
  let NRank := (Nfull ∩ Prod.fst ⁻¹' S) ∩ T ⁻¹' Ioi t
  let VRank := V0 ∩ (fun c : Fin 3 → ℝ ↦ ((0 : ℝ), c)) ⁻¹' S
  have hNRank : IsOpen NRank := (hT.mono inter_subset_left).continuousOn.isOpen_inter_preimage
    (hNfull.inter (hS.preimage continuous_fst)) isOpen_Ioi
  have hNRankSub : NRank ⊆ Nfull := fun _ hθ ↦ hθ.1.1
  have hbaseRank : ((0, cStar), (0, 0)) ∈ NRank := ⟨⟨hbaseFull, hbaseS⟩, show t < T _ by
    rw [hTbase]; linarith [htBranch.2, (hgateX (2051 / 10) ⟨by cas, le_rfl⟩).1.2]⟩
  -- At the reference event the full flow has middle velocity -8.
  -- Agreement on a time neighborhood transfers the derivative, not just its value.
  have hmiddleBase : eventMiddleVelocity Ψ T ((0, cStar), (0, 0)) = -8 :=
    eventMiddleVelocity_eq_of_eqOn (φ := fun s ↦ (F (s, (0, 0))).1)
      (fun _ hs ↦ congrArg (fun u : ℝ^3 ↦ u 1) ((hcommon (0, 0) h0U0 cStar hcV0).2.2.1 hs))
      (by rw [hTbase]; exact ⟨hS0.trans_lt (hτ205.trans_le hτ0), hH.1⟩)
      (by rw [hTbase, ← hLbase]; exact hLtime)
  -- Keep a strict margin inside the rank neighborhood before selecting delta.
  let NGood := NRank ∩ eventMiddleVelocity Ψ T ⁻¹' Iio (-4 : ℝ)
  have hNGood : IsOpen NGood :=
    (continuousOn_eventMiddleVelocity hΨ (hT.mono hNRankSub)).isOpen_inter_preimage
      hNRank isOpen_Iio
  have hNGoodSub : NGood ⊆ Nfull := fun _ hθ ↦ hNRankSub hθ.1
  have hbaseGood : ((0, cStar), (0, 0)) ∈ NGood :=
    ⟨hbaseRank, hmiddleBase.trans_lt (by norm_num : (-8 : ℝ) < -4)⟩
  -- Both physical parameters and coefficients must shrink together. The full
  -- zero-delta candidate agreement then remains available to the matching selector.
  obtain ⟨VGood, UGood, hVGood, hcGood, hUGood, h0UGood, hVGoodSub, hUGoodSub, hGoodMem⟩ :=
    exists_isOpen_prod_subset_slice hNGood
      (hV0.inter (hS.preimage (continuous_const.prodMk continuous_id))) hU0 ⟨hcV0, hbaseS⟩ h0U0
      hbaseGood
  have hcommonGood : ∀ p ∈ UGood, ∀ c ∈ VGood, ((0, c), p) ∈ NGood ∧ T ((0, c), p) = L p ∧
      EqOn (fun s ↦ Ψ (s, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
      Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p) := fun p hp c hc ↦
    ⟨hGoodMem p hp c hc, (hcommon p (hUGoodSub hp) c (hVGoodSub hc).1).2⟩
  -- The selector performs the only positive-delta implicit-function step.
  obtain ⟨N1, U1, V1, _, _, hN1sub, _, _, hzN1, _, _, _, _, _, hV1sub, _, δPos, cPos, Ω,
    hδpos, hδsmall, hcPos, hθPos, hρ, hρa, hjet, hΩ, h0Ω, hpaths⟩ :=
    exists_prescribed_clock_positive_delta_terminal (F := F) (b := b) (L := L) (Ψ := Ψ) (T := T)
      (N := NGood) (U := UGood) (V := VGood) (cStar := cStar) (H := H)
      hNGood hbaseGood hΨ (hT.mono hNGoodSub) hUGood h0UGood hVGood hcGood
      (hzpos (0, 0) h0U) hε hcommonGood hGold hJUnit hGoldzero
  have hθGood : ((δPos, cPos), (0, 0)) ∈ NGood := hN1sub hθPos
  obtain ⟨hyPos, hzPos, hzAPos, _, _, _, hiPos, hjPos, aPos, haPos, hdecompPos⟩ :=
    hpersist (δPos, cPos) hθGood.1.1.2
  have hglobal := concreteGatedFlux_smooth_strictlyHyperbolic_genuinelyNonlinear
    hδpos (hδsmall.trans_le (min_le_right _ _)) (contDiff_clockFeedback A B)
    (fun s ↦ clockFeedback_mem_Icc A B s)
    (hb.comp (contDiff_const.prodMk contDiff_id)) (hbsupp cPos)
  refine ⟨cStar, H, Ψ, T, NGood, UGood, VGood, S, δPos, cPos, t, i, j, Ω, ?_⟩
  intro x z ρ f γ v W r
  have hvPos : v t = f (γ t) := by
    simpa only [zero_smul, sub_zero] using
      (hodeFull _ (hNGoodSub hθGood) t ⟨htH.1.le, htH.2.le⟩).deriv
  have hterminalODE : HasDerivAt γ
      (f (γ (T ((δPos, cPos), (0, 0))))) (T ((δPos, cPos), (0, 0))) := by
    simpa only [zero_smul, sub_zero] using hodeFull _ (hNGoodSub hθGood) _
      ⟨(hThit _ (hNGoodSub hθGood)).1.1.le, (hThit _ (hNGoodSub hθGood)).1.2.le⟩
  refine ⟨fun k ↦ ⟨(hβ k).1, (hβ k).2.1, (hβ k).2.2.1, (hβ k).2.2.2.1, (hβ k).2.2.2.2.1⟩,
    hdisjoint, hb, hbsupport, hH, hΨ, hΨzero, hNGood, hbaseGood,
    hS, hbaseS, hθGood.1.1.2, (fun _ hθ ↦ hθ.1.1.2),
    (fun θ hθ s hs ↦ hodeFull θ (hNGoodSub hθ) s hs), hT.mono hNGoodSub,
    hTbase, (fun θ hθ ↦ hThit θ (hNGoodSub hθ)), hUGood, h0UGood,
    (fun _ hp ↦ hUN (hU0U (hUGoodSub hp))), hVGood, hcGood, hV1sub hcPos, hcommonGood,
    hδpos, hδsmall, hθGood, htBranch, ⟨htH.1, hθGood.1.2⟩,
    hyPos, hzPos, hzAPos, hij, hvPos ▸ hiPos, hvPos ▸ hjPos, ⟨aPos, haPos, hvPos.trans hdecompPos⟩,
    hzN1 _ hθPos, hρ, hρa, hjet,
    hglobal.1, hglobal.2.1, hglobal.2.2, hΩ, h0Ω, hpaths, fun _ hθ ↦ hθ.2, ?_⟩
  rw [← eventMiddleVelocity_eq_field_middle (Ψ := Ψ) (T := T)
    (θ := ((δPos, cPos), (0, 0))) (f := f) hterminalODE]
  exact hθGood.2

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
