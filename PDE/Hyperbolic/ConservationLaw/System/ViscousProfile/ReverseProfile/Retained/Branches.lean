/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Reflection

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Analysis.Evolution.ODE.Autonomous.Uniqueness
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.ReflectedJet
import CAS.ExactTactic

/-!
# The physical branches of the uncorrected flow

We keep the supplied full flow `Ψ` and its event map `T`; declarations named `retained...`
are built from this flow and event map, before any flux correction is chosen, and `selected`
refers to the zero and coefficients chosen by the matching selection theorem. The outgoing branch is
its `(μ, 0)` slice. The incoming branch reverses time and state on the very same
flow at `(-μ, -2000000 * μ)`. Reversing the speed as well is essential: both
branches then solve `f - μ • id`, and the incoming anchor is `(1, 2000000 * μ, 0)`.

The selected quotient residual gives the first moving mismatch, including the
middle coordinate through the section equations. The speed derivative of the outgoing branch is
exactly the full variation already used by the selected neutral correction.

The supplied ODE has a finite time domain. We retain its domains:
`[0, H]` outgoing and `[2e - H, 2e]` incoming. Autonomous uniqueness identifies
the incoming base orbit throughout its interval of definition.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The outgoing physical branch is the retained flow with zero initial displacement. -/
def retainedOutgoingBranch
    (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
    (σ : ℝ × (Fin 3 → ℝ)) (t μ : ℝ) : ℝ^3 :=
  Ψ (t, (σ, (μ, 0)))

/-- Reverse the same retained flow at negative speed and negative displacement.
The time `e + e` is fixed before any correction or speed is chosen. -/
def retainedIncomingBranch
    (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
    (σ : ℝ × (Fin 3 → ℝ)) (e t μ : ℝ) : ℝ^3 :=
  GatedFlux.reversal (Ψ (e + e - t, (σ, (-μ, -2000000 * μ))))

/-- The outgoing event of the uncorrected flow comes from the retained event map. -/
def retainedOutgoingEvent
    (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
    (σ : ℝ × (Fin 3 → ℝ)) (μ : ℝ) : ℝ :=
  T (σ, (μ, 0))

/-- The incoming event uses the same event map, with reflected time. -/
def retainedIncomingEvent
    (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
    (σ : ℝ × (Fin 3 → ℝ)) (e μ : ℝ) : ℝ :=
  e + e - T (σ, (-μ, -2000000 * μ))

/-- The retained terminal state with the fixed-flux parameters held constant. -/
def retainedTerminalState
    (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
    (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
    (σ : ℝ × (Fin 3 → ℝ)) (p : ℝ × ℝ) : ℝ^3 :=
  Ψ (T (σ, p), (σ, p))

/-- Taking the outgoing slice preserves the supplied joint smoothness. -/
theorem contDiff_retainedOutgoingBranch
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (σ : ℝ × (Fin 3 → ℝ)) :
    ContDiff ℝ ∞ (retainedOutgoingBranch Ψ σ).uncurry :=
  hΨ.comp (contDiff_fst.prodMk
    (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_const)))

/-- Reversal and the affine physical-parameter line preserve joint smoothness. -/
theorem contDiff_retainedIncomingBranch
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (σ : ℝ × (Fin 3 → ℝ)) (e : ℝ) :
    ContDiff ℝ ∞ (retainedIncomingBranch Ψ σ e).uncurry :=
  GatedFlux.reversal.contDiff.comp (hΨ.comp ((contDiff_const.sub contDiff_fst).prodMk
    (contDiff_const.prodMk (contDiff_snd.neg.prodMk (contDiff_const.mul contDiff_snd)))))

/-- The outgoing speed derivative is the selected full variation `W`, with no new
variational solution or flow chosen. -/
theorem hasDerivAt_retainedOutgoingBranch_speed
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (σ : ℝ × (Fin 3 → ℝ)) (t : ℝ) :
    HasDerivAt (retainedOutgoingBranch Ψ σ t)
      (prescribedClockFullVariation Ψ σ (1, 0) t) 0 := by
  have hsmooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ Ψ (t, (σ, p))) :=
    hΨ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hline : HasDerivAt (fun μ : ℝ ↦ (μ, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  simpa only [retainedOutgoingBranch, prescribedClockFullVariation, Function.comp_def] using!
    (hsmooth.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hline rfl

/-- The incoming speed derivative follows the physical direction `(-1, -2000000)`
before applying state reversal. Its direction is not the outgoing direction. -/
theorem hasDerivAt_retainedIncomingBranch_speed
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (σ : ℝ × (Fin 3 → ℝ)) (e t : ℝ) :
    HasDerivAt (retainedIncomingBranch Ψ σ e t)
      (GatedFlux.reversal
        (prescribedClockFullVariation Ψ σ (-1, -2000000) (e + e - t))) 0 := by
  have hsmooth : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦ Ψ (e + e - t, (σ, p))) :=
    hΨ.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hneg : HasDerivAt (fun μ : ℝ ↦ -μ) (-1) 0 := by cas
  have hmul : HasDerivAt (fun μ : ℝ ↦ -2000000 * μ) (-2000000) 0 := by cas
  exact GatedFlux.reversal.hasFDerivAt.comp_hasDerivAt 0 (by
    simpa only [prescribedClockFullVariation, Function.comp_def] using
      (hsmooth.differentiable (by simp) (0, 0)).hasFDerivAt.comp_hasDerivAt_of_eq 0
        (hneg.prodMk hmul) (by simp))

/-- The two entire physical initial sections are retained, for every speed. -/
theorem retained_branches_initial
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hinit : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (σ : ℝ × (Fin 3 → ℝ)) (e μ : ℝ) :
    retainedOutgoingBranch Ψ σ 0 μ = (!₂[0, 0, 1] : ℝ^3) ∧
      retainedIncomingBranch Ψ σ e (e + e) μ = (!₂[1, 2000000 * μ, 0] : ℝ^3) := by
  simp [retainedOutgoingBranch, retainedIncomingBranch, hinit, GatedFlux.reversal_apply]

/-- Reuse the common orbit returned by the selected zero-speed attachment. The
outgoing and incoming agreements are exactly the agreements supplied by that theorem. -/
theorem retained_branches_base_eq
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {σ : ℝ × (Fin 3 → ℝ)} {e H : ℝ} {q : ℝ → ℝ^3}
    (hout : EqOn q (fun t ↦ Ψ (t, (σ, (0, 0)))) (Icc 0 H))
    (hin : EqOn q
      (fun t ↦ GatedFlux.reversal (Ψ (e + e - t, (σ, (0, 0)))))
      (Icc e (e + e))) :
    EqOn (fun t ↦ retainedOutgoingBranch Ψ σ t 0) q (Icc 0 H) ∧
      EqOn (fun t ↦ retainedIncomingBranch Ψ σ e t 0) q (Icc e (e + e)) := by
  exact ⟨fun t ht ↦ (hout ht).symm,
    fun t ht ↦ by simpa [retainedIncomingBranch] using (hin ht).symm⟩

/-- Both retained branches meet the same supplied orbit at the same base time.
Their common affine section is the middle-coordinate section through `q e`. -/
theorem retained_branches_common_base
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {σ : ℝ × (Fin 3 → ℝ)} {e H : ℝ} {q : ℝ → ℝ^3}
    (he : e ∈ Ioo 0 H) (hsection : Ψ (e, (σ, (0, 0))) 1 = 0)
    (hout : EqOn q (fun t ↦ Ψ (t, (σ, (0, 0)))) (Icc 0 H))
    (hin : EqOn q
      (fun t ↦ GatedFlux.reversal (Ψ (e + e - t, (σ, (0, 0)))))
      (Icc e (e + e))) :
    retainedOutgoingBranch Ψ σ e 0 = q e ∧
      retainedIncomingBranch Ψ σ e e 0 = q e ∧ q e 1 = 0 := by
  have hb := retained_branches_base_eq hout hin
  refine ⟨hb.1 (Ioo_subset_Icc_self he), hb.2 ⟨le_rfl, by linarith [he.1]⟩, ?_⟩
  rw [hout (Ioo_subset_Icc_self he)]
  exact hsection

/-- Autonomous uniqueness identifies the incoming zero-speed branch with the same
complete orbit on its whole interval of definition, including the part before the event.
Only the already established base value is used, not a first-derivative match. -/
theorem retainedIncomingBranch_base_eq_on_native_interval
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {σ : ℝ × (Fin 3 → ℝ)} {e H : ℝ} {q : ℝ → ℝ^3} {f : ℝ^3 → ℝ^3}
    (hf : ContDiff ℝ ∞ f) (he : e ∈ Ioo 0 H)
    (hq : ∀ t, HasDerivAt q (f (q t)) t)
    (hin : ∀ t ∈ Icc (e + e - H) (e + e),
      HasDerivAt (fun s ↦ retainedIncomingBranch Ψ σ e s 0)
        (f (retainedIncomingBranch Ψ σ e t 0)) t)
    (hbase : retainedIncomingBranch Ψ σ e e 0 = q e) :
    EqOn (fun t ↦ retainedIncomingBranch Ψ σ e t 0) q
      (Icc (e + e - H) (e + e)) := by
  apply PDE.Analysis.Evolution.eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls
    (fun R _ ↦ hf.contDiffOn.exists_lipschitzOnWith (by simp)
      (convex_closedBall (0 : ℝ^3) R) (isCompact_closedBall _ _))
    (t₀ := e) ⟨by linarith [he.2], by linarith [he.1]⟩
    (fun t ht ↦ (hin t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hin t (Ioo_subset_Icc_self ht))
    (fun t _ ↦ (hq t).continuousAt.continuousWithinAt) (fun t _ ↦ hq t) hbase

/-- Keep both uncorrected physical branches and their events on one open speed set.
The time domains are the domains inherited from `Ψ`. In particular, no
common time slab or transverse-section hypothesis is silently added here. -/
theorem exists_retained_physical_branch_events
    {A B H : ℝ} {b : (Fin 3 → ℝ) × ℝ → ℝ}
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ}
    {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))}
    {σ : ℝ × (Fin 3 → ℝ)}
    (hN : IsOpen N) (hselected : (σ, (0, 0)) ∈ N)
    (hT : ContDiffOn ℝ ∞ T N)
    (hode : ∀ θ ∈ N, ∀ t ∈ Icc 0 H,
      HasDerivAt (fun s ↦ Ψ (s, θ))
        (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y))
          (Ψ (t, θ)) - θ.2.1 • Ψ (t, θ)) t)
    (hevent : ∀ θ ∈ N, T θ ∈ Ioo 0 H ∧ Ψ (T θ, θ) 1 = 0) :
    let e := T (σ, (0, 0))
    let f := concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))
    let Fout := retainedOutgoingBranch Ψ σ
    let Fincoming := retainedIncomingBranch Ψ σ e
    let τout := retainedOutgoingEvent T σ
    let τin := retainedIncomingEvent T σ e
    ∃ I : Set ℝ, IsOpen I ∧ (0 : ℝ) ∈ I ∧
      (∀ μ ∈ I, (σ, (μ, 0)) ∈ N ∧ (σ, (-μ, -2000000 * μ)) ∈ N) ∧
      ContDiffOn ℝ ∞ τout I ∧ ContDiffOn ℝ ∞ τin I ∧
      τout 0 = e ∧ τin 0 = e ∧ e ∈ Ioo 0 H ∧
      (∀ μ ∈ I, ∀ t ∈ Icc 0 H,
        HasDerivAt (fun s ↦ Fout s μ) (f (Fout t μ) - μ • Fout t μ) t) ∧
      (∀ μ ∈ I, ∀ t ∈ Icc (e + e - H) (e + e),
        HasDerivAt (fun s ↦ Fincoming s μ) (f (Fincoming t μ) - μ • Fincoming t μ) t) ∧
      (∀ μ ∈ I,
        (τout μ ∈ Ioo 0 H ∧ Fout (τout μ) μ 1 = 0) ∧
        (τin μ ∈ Ioo (e + e - H) (e + e) ∧ Fincoming (τin μ) μ 1 = 0)) := by
  intro e f Fout Fincoming τout τin
  let θout : ℝ → ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) := fun μ ↦ (σ, (μ, 0))
  let θin : ℝ → ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) :=
    fun μ ↦ (σ, (-μ, -2000000 * μ))
  have hθout : ContDiff ℝ ∞ θout :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hθin : ContDiff ℝ ∞ θin :=
    contDiff_const.prodMk (contDiff_id.neg.prodMk (contDiff_const.mul contDiff_id))
  let I := θout ⁻¹' N ∩ θin ⁻¹' N
  have hI : IsOpen I :=
    (hN.preimage hθout.continuous).inter (hN.preimage hθin.continuous)
  refine ⟨I, hI, ⟨hselected, by simpa [θin] using hselected⟩, fun μ hμ ↦ hμ,
    hT.comp hθout.contDiffOn fun _ hμ ↦ hμ.1,
    contDiffOn_const.sub (hT.comp hθin.contDiffOn fun _ hμ ↦ hμ.2), rfl,
    by simp [τin, retainedIncomingEvent, e], (hevent _ hselected).1,
    fun μ hμ ↦ hode (θout μ) hμ.1, fun μ hμ t ht ↦ ?_, fun μ hμ ↦ ?_⟩
  · have hR : HasDerivAt (fun s ↦ Fincoming s μ)
        (GatedFlux.reversal
          (-(f (Ψ (e + e - t, θin μ)) - (-μ) • Ψ (e + e - t, θin μ)))) t :=
      GatedFlux.reversal.hasFDerivAt.comp_hasDerivAt t (HasDerivAt.comp_const_sub (e + e) t
        (hode (θin μ) hμ.2 (e + e - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩))
    rw [map_neg] at hR
    exact hR.congr_deriv (GatedFlux.flux_sub_smul_reversal
      (PDE.Analysis.fastLogCosh σ.1) MiddleClock.g cutoff (clockFeedback A B)
      (fun y ↦ b (σ.2, y)) MiddleClock.g_neg μ (Ψ (e + e - t, θin μ))).symm
  · have hin := hevent (θin μ) hμ.2
    have htime : e + e - τin μ = T (θin μ) := sub_sub_cancel _ _
    refine ⟨hevent (θout μ) hμ.1, ⟨by linarith [hin.1.2], by linarith [hin.1.1]⟩, ?_⟩
    change (GatedFlux.reversal (Ψ (e + e - τin μ, θin μ))) 1 = 0
    rw [htime]
    simp [GatedFlux.reversal_apply, hin.2]

/-- Lift the two scalar raw-matching identities to a vector derivative. The middle
coordinate comes from the section germ; the fast coordinates come from the selected
quotient residual. -/
private theorem reflected_terminal_first_match
    {Q : ℝ × ℝ → ℝ^3} (hQ : DifferentiableAt ℝ Q (0, 0)) (h : ℝ)
    (hz : 0 < Q (0, 0) 2) (hρ : Q (0, 0) 0 / Q (0, 0) 2 = 1)
    (hρa : deriv (fun a ↦ Q (0, a) 0 / Q (0, a) 2) 0 = 0)
    (hres : Q (0, 0) 2 * deriv (fun μ ↦ Q (μ, 0) 0 / Q (μ, 0) 2) 0 +
      2 * deriv (fun μ ↦ Q (μ, 0) 2) 0 + h * deriv (fun a ↦ Q (0, a) 2) 0 = 0)
    (hsection : (fun μ : ℝ ↦ Q (μ, 0) 1 + Q (-μ, -h * μ) 1) =ᶠ[𝓝 0]
      fun _ ↦ (0 : ℝ)) :
    let M : ℝ → ℝ^3 := fun μ ↦ Q (μ, 0) - GatedFlux.reversal (Q (-μ, -h * μ))
    M 0 = 0 ∧ HasDerivAt M 0 0 := by
  intro M
  have hcoord (i : Fin 3) : DifferentiableAt ℝ (fun p ↦ Q p i) (0, 0) :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) (Q (0, 0)) i).differentiableAt.comp
      (0, 0) hQ
  have hraw := PDE.Analysis.raw_matching_jet_eq (hcoord 0) (hcoord 2) (ne_of_gt hz) h
  dsimp only at hraw
  have hvalue : Q (0, 0) 0 - Q (0, 0) 2 = 0 := by
    simpa [hρ, hρa, hres] using congrFun hraw (0 : Fin 3)
  have hfirst : deriv (fun μ ↦ Q (μ, 0) 0 - Q (-μ, -h * μ) 2) 0 = 0 := by
    simpa [hρ, hρa, hres] using congrFun hraw (1 : Fin 3)
  have hthird : deriv (fun μ ↦ Q (μ, 0) 2 - Q (-μ, -h * μ) 0) 0 = 0 := by
    simpa [hρ, hρa, hres] using congrFun hraw (2 : Fin 3)
  have hmiddle : HasDerivAt (fun μ : ℝ ↦ Q (μ, 0) 1 + Q (-μ, -h * μ) 1) 0 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).congr_of_eventuallyEq hsection
  have hneg : HasDerivAt (fun μ : ℝ ↦ -μ) (-1) 0 := by cas
  have hmul : HasDerivAt (fun μ : ℝ ↦ -h * μ) (-h) 0 := by cas
  have houtLine : HasDerivAt (fun μ : ℝ ↦ (μ, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  have hout : DifferentiableAt ℝ (fun μ : ℝ ↦ Q (μ, 0)) 0 :=
    (hQ.hasFDerivAt.comp_hasDerivAt_of_eq 0 houtLine rfl).differentiableAt
  have hin : HasDerivAt (fun μ : ℝ ↦ Q (-μ, -h * μ))
      (fderiv ℝ Q (0, 0) (-1, -h)) 0 := by
    simpa only [Function.comp_def] using
      hQ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hneg.prodMk hmul) (by simp)
  have hM : DifferentiableAt ℝ M 0 :=
    hout.sub (GatedFlux.reversal.hasFDerivAt.comp_hasDerivAt 0 hin).differentiableAt
  have hMcoord (i : Fin 3) : HasDerivAt (fun μ ↦ M μ i) ((deriv M 0) i) 0 := by
    simpa only [Function.comp_def] using!
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) (M 0) i).comp_hasDerivAt
        0 hM.hasDerivAt
  constructor
  · ext i
    fin_cases i
    · simpa [M, GatedFlux.reversal_apply] using hvalue
    · simpa [M, GatedFlux.reversal_apply, sub_neg_eq_add] using hsection.eq_of_nhds
    · simpa [M, GatedFlux.reversal_apply] using sub_eq_zero.mpr (sub_eq_zero.mp hvalue).symm
  · refine hM.hasDerivAt.congr_deriv ?_
    ext i
    rw [← (hMcoord i).deriv]
    fin_cases i
    · simpa [M, GatedFlux.reversal_apply] using hfirst
    · simpa [M, GatedFlux.reversal_apply, sub_neg_eq_add] using hmiddle.deriv
    · simpa [M, GatedFlux.reversal_apply] using hthird

/-- The selected residual proves zero value and first derivative of the moving mismatch of
the uncorrected branches. The only scalar equations assumed are the three selected residual
equations; the middle derivative is proved from the section identities of the uncorrected
flow. -/
theorem selected_retained_moving_mismatch_first
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ}
    {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))}
    {σ : ℝ × (Fin 3 → ℝ)} (e : ℝ)
    (hΨ : ContDiff ℝ ∞ Ψ) (hN : IsOpen N) (hselected : (σ, (0, 0)) ∈ N)
    (hT : ContDiffOn ℝ ∞ T N)
    (hsection : ∀ θ ∈ N, Ψ (T θ, θ) 1 = 0)
    (hz : 0 < retainedTerminalState Ψ T σ (0, 0) 2)
    (hρ : retainedTerminalState Ψ T σ (0, 0) 0 /
      retainedTerminalState Ψ T σ (0, 0) 2 = 1)
    (hρa : deriv (fun a ↦ retainedTerminalState Ψ T σ (0, a) 0 /
      retainedTerminalState Ψ T σ (0, a) 2) 0 = 0)
    (hres : retainedTerminalState Ψ T σ (0, 0) 2 *
      deriv (fun μ ↦ retainedTerminalState Ψ T σ (μ, 0) 0 /
        retainedTerminalState Ψ T σ (μ, 0) 2) 0 +
      2 * deriv (fun μ ↦ retainedTerminalState Ψ T σ (μ, 0) 2) 0 +
      2000000 * deriv (fun a ↦ retainedTerminalState Ψ T σ (0, a) 2) 0 = 0) :
    let M : ℝ → ℝ^3 := fun μ ↦
      retainedOutgoingBranch Ψ σ (retainedOutgoingEvent T σ μ) μ -
        retainedIncomingBranch Ψ σ e (retainedIncomingEvent T σ e μ) μ
    M 0 = 0 ∧ HasDerivAt M 0 0 := by
  intro M
  let Q := retainedTerminalState Ψ T σ
  have hparameter : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ ↦ (σ, p)) (0, 0) := contDiffAt_const.prodMk contDiffAt_id
  have hterminalTime : ContDiffAt ℝ ∞
      (fun p : ℝ × ℝ ↦ T (σ, p)) (0, 0) :=
    (hT.contDiffAt (hN.mem_nhds hselected)).comp (0, 0) hparameter
  have hQ : ContDiffAt ℝ ∞ Q (0, 0) :=
    hΨ.contDiffAt.comp (0, 0) (hterminalTime.prodMk hparameter)
  have houtMem : ∀ᶠ μ : ℝ in 𝓝 0, (σ, (μ, 0)) ∈ N :=
    (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt.eventually
      (hN.mem_nhds hselected)
  have hinMem : ∀ᶠ μ : ℝ in 𝓝 0, (σ, (-μ, -2000000 * μ)) ∈ N :=
    (continuous_const.prodMk (continuous_id.neg.prodMk (continuous_const.mul continuous_id))
      ).continuousAt.eventually (hN.mem_nhds (by simpa using hselected))
  have hmiddle : (fun μ : ℝ ↦ Q (μ, 0) 1 + Q (-μ, -2000000 * μ) 1) =ᶠ[𝓝 0]
      fun _ ↦ (0 : ℝ) := by
    filter_upwards [houtMem, hinMem] with μ hout hin
    simp only [Q, retainedTerminalState, hsection _ hout, hsection _ hin, zero_add]
  simp only [M, retainedOutgoingBranch, retainedIncomingBranch, retainedOutgoingEvent,
    retainedIncomingEvent, sub_sub_cancel]
  exact reflected_terminal_first_match (hQ.differentiableAt (by simp)) 2000000 hz hρ hρa hres
    hmiddle

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
