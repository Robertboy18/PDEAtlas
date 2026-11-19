/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.FiniteContinuation

import CAS.ExactTactic

/-!
# Joining an interpolated strip to its physical branches

Phase alignment moves the two anchor times. The outgoing anchor becomes
`-α`, and the incoming anchor becomes `2e - β`, where `α` and `β` are the
event shifts. The original flows still supply the equations: their translated
time intervals must lie in the domains on which those equations were proved.

If a correction vanishes along these outer segments and realizes the middle
interpolation, the three pieces solve one fixed corrected field. Two applications
of the existing closed-interval gluing theorem preserve the pieces and their
anchor values. Only values need to match at the joins, since both one-sided
derivatives then equal the same field value.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis.ODE

/-- One speed interval controls both moving anchors and the shifted join times.
The envelope width is fixed first, so outer-branch avoidance can be proved on
the fixed compact envelopes `[-d,a]` and `[b,2e+d]`. -/
theorem exists_pos_phase_anchor_radius
    {τout τin : ℝ → ℝ} {J : Set ℝ} {a b e lo hi d : ℝ}
    (hτout : ContinuousAt τout 0) (hτin : ContinuousAt τin 0)
    (hτoutZero : τout 0 = e) (hτinZero : τin 0 = e)
    (hJ : J ∈ 𝓝 (0 : ℝ)) (ha : a ∈ Ioo (0 : ℝ) hi)
    (hb : b ∈ Ioo lo (e + e)) (hd : 0 < d) :
    ∃ r : ℝ, 0 < r ∧ ∀ μ : ℝ, |μ| ≤ r →
      μ ∈ J ∧ a + (τout μ - e) ∈ Ioo (0 : ℝ) hi ∧
      b + (τin μ - e) ∈ Ioo lo (e + e) ∧
      |τout μ - e| < d ∧ |τin μ - e| < d := by
  have hcout : ContinuousAt (fun μ ↦ a + (τout μ - e)) 0 :=
    continuousAt_const.add (hτout.sub continuousAt_const)
  have hcin : ContinuousAt (fun μ ↦ b + (τin μ - e)) 0 :=
    continuousAt_const.add (hτin.sub continuousAt_const)
  have hout : ∀ᶠ μ in 𝓝 (0 : ℝ), a + (τout μ - e) ∈ Ioo (0 : ℝ) hi :=
    hcout.eventually (isOpen_Ioo.mem_nhds (by simpa only [hτoutZero, sub_self,
      add_zero] using ha))
  have hin : ∀ᶠ μ in 𝓝 (0 : ℝ), b + (τin μ - e) ∈ Ioo lo (e + e) :=
    hcin.eventually (isOpen_Ioo.mem_nhds (by simpa only [hτinZero, sub_self,
      add_zero] using hb))
  have houtSmall : ∀ᶠ μ in 𝓝 (0 : ℝ), |τout μ - e| < d :=
    ((hτout.sub continuousAt_const).abs).eventually
      (isOpen_Iio.mem_nhds (by
        change |τout 0 - e| < d
        simpa only [hτoutZero, sub_self, abs_zero] using hd))
  have hinSmall : ∀ᶠ μ in 𝓝 (0 : ℝ), |τin μ - e| < d :=
    ((hτin.sub continuousAt_const).abs).eventually
      (isOpen_Iio.mem_nhds (by
        change |τin 0 - e| < d
        simpa only [hτinZero, sub_self, abs_zero] using hd))
  have hall : {μ : ℝ | μ ∈ J ∧ a + (τout μ - e) ∈ Ioo (0 : ℝ) hi ∧
      b + (τin μ - e) ∈ Ioo lo (e + e) ∧
      |τout μ - e| < d ∧ |τin μ - e| < d} ∈ 𝓝 (0 : ℝ) := by
    filter_upwards [hJ, hout, hin, houtSmall, hinSmall] with μ hμ h₁ h₂ h₃ h₄
    exact ⟨hμ, h₁, h₂, h₃, h₄⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hall
  refine ⟨r, hr, ?_⟩
  intro μ hμ
  apply hball
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hμ

/-- Join the two actual phase-shifted branches through the corrected
interpolation. The conclusion retains the original outgoing and incoming
anchor states exactly. No smoothness of the flux or sign of the speed is needed
for this finite-interval step.

The two translated join times control the whole translated outer intervals.
Vanishing of the correction is supplied on those actual outer segments, while
the middle segment carries its independently proved corrected equation. -/
theorem exists_core_of_phase_interpolation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f P : E → E} {F G U V w : ℝ → E} {θ : ℝ → ℝ}
    {μ e α β a b lo hi : ℝ}
    (hab : a < b) (hlo : lo ≤ 0) (hhi : e + e ≤ hi)
    (ha : a + α ∈ Ioo (0 : ℝ) hi)
    (hb : b + β ∈ Ioo lo (e + e))
    (hF : ∀ t ∈ Icc lo hi, HasDerivAt F (f (F t) - μ • F t) t)
    (hG : ∀ t ∈ Icc lo hi, HasDerivAt G (f (G t) - μ • G t) t)
    (hU : ∀ t, U t = F (t + α)) (hV : ∀ t, V t = G (t + β))
    (hw : ∀ t, w t = U t + θ t • (V t - U t))
    (hθa : θ a = 0) (hθb : θ b = 1)
    (hPleft : ∀ t ∈ Icc (-α) a, P (U t) = 0)
    (hPright : ∀ t ∈ Icc b (e + e - β), P (V t) = 0)
    (hwODE : ∀ t ∈ Icc a b,
      HasDerivWithinAt w ((f + P) (w t) - μ • w t) (Icc a b) t) :
    -α < a ∧ b < e + e - β ∧
      ∃ u : ℝ → E,
        EqOn u U (Icc (-α) a) ∧ EqOn u w (Icc a b) ∧
        EqOn u V (Icc b (e + e - β)) ∧
        u (-α) = F 0 ∧ u (e + e - β) = G (e + e) ∧
        ∀ t ∈ Icc (-α) (e + e - β),
          HasDerivWithinAt u ((f + P) (u t) - μ • u t)
            (Icc (-α) (e + e - β)) t := by
  have hleft : -α < a := by cas using [ha.1]
  have hright : b < e + e - β := by cas using [hb.2]
  have hUfun : U = fun t ↦ F (t + α) := funext hU
  have hVfun : V = fun t ↦ G (t + β) := funext hV
  have hUODE (t : ℝ) (ht : t ∈ Icc (-α) a) :
      HasDerivWithinAt U ((f + P) (U t) - μ • U t) (Icc (-α) a) t := by
    have htime : t + α ∈ Icc lo hi := by
      constructor
      · cas using [ht.1, hlo]
      · cas using [ht.2, ha.2]
    have hD : HasDerivAt U (f (U t) - μ • U t) t := by
      simpa only [hUfun] using HasDerivAt.comp_add_const t α (hF (t + α) htime)
    simpa only [Pi.add_apply, hPleft t ht, add_zero] using hD.hasDerivWithinAt
  have hVODE (t : ℝ) (ht : t ∈ Icc b (e + e - β)) :
      HasDerivWithinAt V ((f + P) (V t) - μ • V t) (Icc b (e + e - β)) t := by
    have htime : t + β ∈ Icc lo hi := by
      constructor
      · cas using [ht.1, hb.1]
      · cas using [ht.2, hhi]
    have hD : HasDerivAt V (f (V t) - μ • V t) t := by
      simpa only [hVfun] using HasDerivAt.comp_add_const t β (hG (t + β) htime)
    simpa only [Pi.add_apply, hPright t ht, add_zero] using hD.hasDerivWithinAt
  have hmatchLeft : U a = w a := by
    rw [hw a, hθa, zero_smul, add_zero]
  have hmatchRight : w b = V b := by
    rw [hw b, hθb, one_smul, add_sub_cancel]
  obtain ⟨u₁, h₁left, h₁middle, h₁ODE⟩ :=
    PDE.Analysis.Evolution.glue_ode_solution_Icc
      (fun _ x ↦ (f + P) x - μ • x) hleft.le hab.le U w
      hmatchLeft hUODE hwODE
  obtain ⟨u, h₂left, h₂right, h₂ODE⟩ :=
    PDE.Analysis.Evolution.glue_ode_solution_Icc
      (fun _ x ↦ (f + P) x - μ • x) (hleft.trans hab).le hright.le u₁ V
      ((h₁middle b ⟨hab.le, le_rfl⟩).trans hmatchRight) h₁ODE hVODE
  have huleft : EqOn u U (Icc (-α) a) := by
    intro t ht
    exact (h₂left t ⟨ht.1, ht.2.trans hab.le⟩).trans (h₁left t ht)
  have humiddle : EqOn u w (Icc a b) := by
    intro t ht
    exact (h₂left t ⟨hleft.le.trans ht.1, ht.2⟩).trans (h₁middle t ht)
  refine ⟨hleft, hright, u, huleft, humiddle, h₂right, ?_, ?_, h₂ODE⟩
  · rw [huleft ⟨le_rfl, hleft.le⟩, hU, neg_add_cancel]
  · rw [h₂right _ ⟨hright.le, le_rfl⟩, hV, sub_add_cancel]

end PDE.Analysis.ODE
