/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.HigherOrder
import PDE.Analysis.Evolution.ODE.Autonomous.Uniqueness

/-!
# Regularity on an existing solution cylinder

A solution family inherits the regularity of its autonomous vector field on its
original open cylinder. We only assume the initial values and the differential
equation; continuity in the initial state is a conclusion.

For each finite derivative order, uniqueness transfers regularity from a local
flow chart. Along a fixed trajectory, the times where this works form an open
set containing zero. A chart at any limit time extends the argument there, so
connectedness gives the entire time interval. Applying this to every finite
order proves smoothness of the same family on the same cylinder.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Filter Metric Set
open scoped ContDiff NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local flow chart transfers the regularity of one time slice to another
state-time point on the same solution family. -/
private theorem contDiffAt_of_solution_chart
    {n : ℕ} {v : E → E} {F : E × ℝ → E} {U : Set E} {a b : ℝ}
    (hLip : ∀ R : ℝ, 0 < R → ∃ K : ℝ≥0, LipschitzOnWith K v (closedBall 0 R))
    (hU : IsOpen U)
    (hode : ∀ q ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun u ↦ F (q, u)) (v (F (q, t))) t)
    {q₀ : E} (hq₀ : q₀ ∈ U) {s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hstate : ContDiffAt ℝ n (fun q ↦ F (q, s)) q₀)
    {ψ : E × ℝ → E} {c : E} {r τ : ℝ} (hτ : 0 < τ)
    (hψ : ContDiffOn ℝ n ψ (ball c r ×ˢ Ioo (-τ) τ))
    (hψ₀ : ∀ q ∈ ball c r, ψ (q, 0) = q)
    (hψode : ∀ q ∈ ball c r, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun u ↦ ψ (q, u)) (v (ψ (q, t))) t)
    (hvalue : F (q₀, s) ∈ ball c r) (htime : t - s ∈ Ioo (-τ) τ) :
    ContDiffAt ℝ n F (q₀, t) := by
  have hlift : ContDiffAt ℝ n
      (fun p : E × ℝ ↦ (F (p.1, s), p.2 - s)) (q₀, t) :=
    (hstate.comp (q₀, t) contDiffAt_fst).prodMk
      (contDiffAt_snd.sub contDiffAt_const)
  have hG : ContDiffAt ℝ n
      (fun p : E × ℝ ↦ ψ (F (p.1, s), p.2 - s)) (q₀, t) :=
    (hψ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨hvalue, htime⟩)).comp (q₀, t) hlift
  apply hG.congr_of_eventuallyEq
  have hq : ∀ᶠ p : E × ℝ in 𝓝 (q₀, t), p.1 ∈ U :=
    continuousAt_fst.eventually (hU.mem_nhds hq₀)
  have hval : ∀ᶠ p : E × ℝ in 𝓝 (q₀, t), F (p.1, s) ∈ ball c r := by
    have hc : ContinuousAt (fun p : E × ℝ ↦ F (p.1, s)) (q₀, t) :=
      hlift.continuousAt.fst
    exact hc.eventually (isOpen_ball.mem_nhds hvalue)
  have hdom : ∀ᶠ p : E × ℝ in 𝓝 (q₀, t), p.2 ∈ Ioo a b :=
    continuousAt_snd.eventually (isOpen_Ioo.mem_nhds ht)
  have hshift : ∀ᶠ p : E × ℝ in 𝓝 (q₀, t), p.2 - s ∈ Ioo (-τ) τ :=
    (continuousAt_snd.sub continuousAt_const).eventually (isOpen_Ioo.mem_nhds htime)
  filter_upwards [hq, hval, hdom, hshift] with p hp hpc hpt hpt'
  have hinit : s ∈ Ioo (max a (s - τ)) (min b (s + τ)) := by
    constructor
    · exact max_lt hs.1 (by linarith)
    · exact lt_min hs.2 (by linarith)
  have hsub {u : ℝ} (hu : u ∈ Ioo (max a (s - τ)) (min b (s + τ))) :
      u ∈ Ioo a b ∧ u - s ∈ Ioo (-τ) τ := by
    rcases max_lt_iff.mp hu.1 with ⟨ha, hτa⟩
    rcases lt_min_iff.mp hu.2 with ⟨hb, hτb⟩
    exact ⟨⟨ha, hb⟩, ⟨by linarith, by linarith⟩⟩
  apply PDE.Analysis.Evolution.eqOn_Ioo_of_hasDerivAt_of_lipschitzOn_balls hLip hinit
    (fun u hu ↦ hode p.1 hp u (hsub hu).1)
    (g := fun u ↦ ψ (F (p.1, s), u - s)) ?_ ?_ ?_
  · intro u hu
    simpa [Function.comp_def] using (hψode _ hpc (u - s) (hsub hu).2).scomp u
      ((hasDerivAt_id u).sub_const s)
  · simpa using (hψ₀ _ hpc).symm
  · constructor
    · exact max_lt hpt.1 (by linarith [hpt'.1])
    · exact lt_min hpt.2 (by linarith [hpt'.2])

variable [FiniteDimensional ℝ E]

/-- Every solution family of a `Cⁿ⁺¹` field is jointly `Cⁿ⁺¹` on its original
open cylinder. Only the initial values and the time-derivative equation are assumed. -/
theorem contDiffOn_succ_of_solution_family (n : ℕ)
    (v : E → E) (hv : ContDiff ℝ (n + 1) v)
    (F : E × ℝ → E) (U : Set E) (hU : IsOpen U) {T : ℝ} (hT : 0 < T)
    (hinitial : ∀ q ∈ U, F (q, 0) = q)
    (hode : ∀ q ∈ U, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u ↦ F (q, u)) (v (F (q, t))) t) :
    ContDiffOn ℝ (n + 1) F (U ×ˢ Ioo (-T) T) := by
  have hv₁ : ContDiff ℝ 1 v := hv.of_le (by simp)
  have hLip (R : ℝ) (_hR : 0 < R) :
      ∃ K : ℝ≥0, LipschitzOnWith K v (closedBall 0 R) :=
    hv₁.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall 0 R) (isCompact_closedBall 0 R)
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  apply (hU.prod isOpen_Ioo).contDiffOn_iff.mpr
  rintro ⟨q₀, t₀⟩ ⟨hq₀, ht₀⟩
  let G : Set ℝ := {t | ContDiffAt ℝ (n + 1) F (q₀, t)}
  have hGopen : IsOpen G := by
    apply isOpen_iff_eventually.mpr
    intro t ht
    have hgood : ContDiffAt ℝ (n + 1) F (q₀, t) := ht
    exact (continuous_const.prodMk continuous_id).continuousAt.eventually
      (hgood.eventually (by simp))
  have hGzero : (0 : ℝ) ∈ G := by
    obtain ⟨r, hr, τ, hτ, ψ, _J, hψ, _hJ, _hLip, hsolve⟩ :=
      exists_local_contDiff_succ_family n v hv q₀
    have hstate : ContDiffAt ℝ (n + 1) (fun q ↦ F (q, 0)) q₀ := by
      apply contDiffAt_id.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hq₀] with q hq
      exact hinitial q hq
    apply contDiffAt_of_solution_chart hLip hU hode hq₀ hzero hzero hstate hτ
      hψ (fun q hq ↦ (hsolve q hq).1)
      (fun q hq t ht ↦ ((hsolve q hq).2.2 t ht).1)
    · simpa only [hinitial q₀ hq₀] using mem_ball_self hr
    · simpa using (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨neg_lt_zero.mpr hτ, hτ⟩)
  have hclosed : closure G ∩ Ioo (-T) T ⊆ G := by
    rintro t ⟨htG, ht⟩
    obtain ⟨r, hr, τ, hτ, ψ, _J, hψ, _hJ, _hLip, hsolve⟩ :=
      exists_local_contDiff_succ_family n v hv (F (q₀, t))
    have hvalues : ∀ᶠ s in 𝓝 t, F (q₀, s) ∈ ball (F (q₀, t)) r :=
      (hode q₀ hq₀ t ht).continuousAt.eventually
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    have htimes : ∀ᶠ s in 𝓝 t, t - s ∈ Ioo (-τ) τ := by
      have hc : ContinuousAt (fun s : ℝ ↦ t - s) t :=
        continuousAt_const.sub continuousAt_id
      apply hc.eventually
      apply isOpen_Ioo.mem_nhds
      simpa using (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨neg_lt_zero.mpr hτ, hτ⟩)
    have hw : {s | s ∈ Ioo (-T) T ∧ F (q₀, s) ∈ ball (F (q₀, t)) r ∧
        t - s ∈ Ioo (-τ) τ} ∈ 𝓝 t := by
      filter_upwards [isOpen_Ioo.mem_nhds ht, hvalues, htimes] with s hs hv hs'
      exact ⟨hs, hv, hs'⟩
    obtain ⟨W, hWsub, hWopen, htW⟩ := _root_.mem_nhds_iff.mp hw
    obtain ⟨s, hsW, hsG⟩ := mem_closure_iff.mp htG W hWopen htW
    obtain ⟨hs, hvalue, htime⟩ := hWsub hsW
    have hgood : ContDiffAt ℝ (n + 1) F (q₀, s) := hsG
    have hstate : ContDiffAt ℝ (n + 1) (fun q ↦ F (q, s)) q₀ :=
      hgood.comp q₀ (contDiffAt_id.prodMk contDiffAt_const)
    exact contDiffAt_of_solution_chart hLip hU hode hq₀ hs ht hstate hτ hψ
      (fun q hq ↦ (hsolve q hq).1)
      (fun q hq t ht ↦ ((hsolve q hq).2.2 t ht).1) hvalue htime
  exact isPreconnected_Ioo.subset_of_closure_inter_subset hGopen
    ⟨0, hzero, hGzero⟩ hclosed ht₀

/-- A solution family of a smooth field is smooth on its existing open cylinder.
The family and its domain are fixed before considering the derivative order. -/
theorem contDiffOn_infty_of_solution_family
    (v : E → E) (hv : ContDiff ℝ ∞ v)
    (F : E × ℝ → E) (U : Set E) (hU : IsOpen U) {T : ℝ} (hT : 0 < T)
    (hinitial : ∀ q ∈ U, F (q, 0) = q)
    (hode : ∀ q ∈ U, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u ↦ F (q, u)) (v (F (q, t))) t) :
    ContDiffOn ℝ ∞ F (U ×ˢ Ioo (-T) T) := by
  apply contDiffOn_infty.mpr
  intro n
  exact (contDiffOn_succ_of_solution_family n v (hv.of_le (by simp))
    F U hU hT hinitial hode).of_le (by simp)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Smooth field parameters and initial states give joint smoothness of an
existing solution family on its original open cylinder. The parameters are
constant along each trajectory. -/
theorem contDiffOn_infty_of_parameterized_solution_family
    (v : P × E → E) (hv : ContDiff ℝ ∞ v)
    (F : (P × E) × ℝ → E) (U : Set (P × E)) (hU : IsOpen U)
    {T : ℝ} (hT : 0 < T)
    (hinitial : ∀ q ∈ U, F (q, 0) = q.2)
    (hode : ∀ q ∈ U, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u ↦ F (q, u)) (v (q.1, F (q, t))) t) :
    ContDiffOn ℝ ∞ F (U ×ˢ Ioo (-T) T) := by
  let w : P × E → P × E := fun q ↦ (0, v q)
  let Γ : (P × E) × ℝ → P × E := fun p ↦ (p.1.1, F p)
  have hΓ : ContDiffOn ℝ ∞ Γ (U ×ˢ Ioo (-T) T) := by
    apply contDiffOn_infty_of_solution_family w (contDiff_const.prodMk hv)
      Γ U hU hT
    · intro q hq
      simp only [Γ, hinitial q hq, Prod.eta]
    · intro q hq t ht
      exact (hasDerivAt_const t q.1).prodMk (hode q hq t ht)
  exact hΓ.snd


end

end PDE.Analysis.ODE
