/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Candidate.Agreement
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Full.Events
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Full.Existence

/-!
# A full terminal germ retaining the prescribed clock family

The supplied zero-delta candidates determine a reference on the fixed
closed time slab. The full-flow and event theorems extend this reference to one
smooth parameter family and an interior terminal event. On a common open
coefficient and physical-parameter product, closed-slab uniqueness retains every
supplied candidate, and event uniqueness identifies its original terminal time.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The prescribed candidates give a full flow and smooth terminal event
on the same time slab. On the zero-delta slice, one open product retains their
entire trajectories, original terminal times, and terminal vectors. The initial
section holds for all full parameters; event uniqueness is local at the base. -/
theorem exists_prescribed_clock_full_terminal_germ (A B : ℝ) {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {L : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {V : Set (Fin 3 → ℝ)} {H τ0 v : ℝ}
    (cStar : Fin 3 → ℝ) (hFzero : ∀ p ∈ U, F (0, p) = (p.2, 1)) (hb : ContDiff ℝ ∞ b)
    (hU : IsOpen U) (hbaseU : (0, 0) ∈ U) (hV : IsOpen V) (hbaseV : cStar ∈ V)
    (hL : ContinuousOn L U) (hLbase : L (0, 0) = τ0) (hτ : τ0 ∈ Ioo (0 : ℝ) H)
    (hLtime : ∀ p ∈ U, L p ∈ Icc (0 : ℝ) H) (hLzero : ∀ p ∈ U, (F (L p, p)).1 = 0)
    (htransverse : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) v τ0) (hv : v ≠ 0) :
    let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
      !₂[(F (t, p)).2 * scalarLinearSolution (fun _ : ℝ ↦ 4)
          (fun s ↦ b (c, (F (s, p)).1)) 0 0 t, (F (t, p)).1, (F (t, p)).2]
    (∀ p ∈ U, ∀ c ∈ V, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (q p c)
        (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B)
          (fun y ↦ b (c, y)) (q p c t) - p.1 • q p c t) t) →
    ∃ (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
      (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
      (N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)))
      (U0 : Set (ℝ × ℝ)) (V0 : Set (Fin 3 → ℝ)),
      IsOpen N ∧ ((0, cStar), (0, 0)) ∈ N ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3)) ∧
      (∀ θ ∈ N, ∀ t ∈ Icc (0 : ℝ) H,
        HasDerivAt (fun s ↦ Ψ (s, θ))
          (concreteGatedFlux θ.1.1 (clockFeedback A B)
            (fun y ↦ b (θ.1.2, y)) (Ψ (t, θ)) - θ.2.1 • Ψ (t, θ)) t) ∧
      ContDiffOn ℝ ∞ T N ∧ T ((0, cStar), (0, 0)) = τ0 ∧
      (∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) ∧
      (∀ᶠ z in 𝓝 (((0, cStar), (0, 0)), τ0),
        Ψ (z.2, z.1) 1 = 0 ↔ T z.1 = z.2) ∧
      IsOpen U0 ∧ (0, 0) ∈ U0 ∧ U0 ⊆ U ∧
      IsOpen V0 ∧ cStar ∈ V0 ∧ V0 ⊆ V ∧
      ∀ p ∈ U0, ∀ c ∈ V0,
        ((0, c), p) ∈ N ∧ T ((0, c), p) = L p ∧
        EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
        Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p) := by
  intro q hcandidate
  let γ : ℝ → ℝ^3 := q (0, 0) cStar
  have hfast : fastLogCosh 0 = fun s ↦ 2 * s :=
    funext fun s ↦ by simp only [fastLogCosh, zero_mul, add_zero]
  have hγode (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : HasDerivAt γ
        (concreteGatedFlux 0 (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t)) t := by
    simpa only [γ, q, concreteGatedFlux, hfast, zero_smul, sub_zero] using
      hcandidate (0, 0) hbaseU cStar hbaseV t ht
  have hγzero : γ 0 = (!₂[0, 0, 1] : ℝ^3) := by
    simp only [γ, q, scalarLinearSolution_initial, mul_zero, hFzero (0, 0) hbaseU]
  have hγsection : γ τ0 1 = 0 :=
    show (F (τ0, (0, 0))).1 = 0 by simpa only [hLbase] using hLzero (0, 0) hbaseU
  obtain ⟨Ψ, Nflow, hNflow, hbaseFlow, hΨ, hΨzero, hΨref, hΨode⟩ :=
    exists_prescribed_clock_full_flow A B hb cStar (hτ.1.trans hτ.2) γ hγode hγzero
  obtain ⟨T, N, hN, hbaseN, hNsub, hT, hTbase, hTzero, hunique⟩ :=
    exists_prescribed_clock_full_event hΨ hNflow hbaseFlow hτ hΨref hγsection
      (htransverse : HasDerivAt (fun t ↦ γ t 1) v τ0) hv
  -- The event domain retains the full field equation on the original time slab.
  let ι : (Fin 3 → ℝ) × (ℝ × ℝ) → (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) := fun z ↦ ((0, z.1), z.2)
  have hι : Continuous ι := (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  obtain ⟨Vc, Uc, hVc, hUc, hbaseVc, hbaseUc, hprod⟩ :=
    isOpen_prod_iff.mp (hN.preimage hι) cStar (0, 0) hbaseN
  let U1 : Set (ℝ × ℝ) := U ∩ Uc
  let V1 : Set (Fin 3 → ℝ) := V ∩ Vc
  have hagree (p : ℝ × ℝ) (hp : p ∈ U1) (c : Fin 3 → ℝ) (hc : c ∈ V1) :
      EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) := by
    have hθ : ((0, c), p) ∈ N := hprod (show (c, p) ∈ Vc ×ˢ Uc from ⟨hc.2, hp.2⟩)
    exact eqOn_prescribed_coupled_candidate (X := fun t ↦ (F (t, p)).1) (Z := fun t ↦ (F (t, p)).2)
      (b := fun y ↦ b (c, y)) (A := A) (B := B) (μ := p.1) (H := H)
      (q := fun t ↦ Ψ (t, ((0, c), p)))
      ((hb.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp))
      (fun t ht ↦ by
        simpa only [concreteGatedFlux, hfast] using hΨode ((0, c), p) (hNsub hθ) t ht)
      (hcandidate p hp.1 c hc.1) (by simpa only [hFzero p hp.1] using hΨzero ((0, c), p))
  -- Pull event uniqueness back along the supplied terminal graph before shrinking.
  have hLs : ContinuousAt (fun z : (Fin 3 → ℝ) × (ℝ × ℝ) ↦ L z.2) (cStar, (0, 0)) :=
    (hL.continuousAt (hU.mem_nhds hbaseU)).comp (f := fun z : (Fin 3 → ℝ) × (ℝ × ℝ) ↦ z.2)
      continuous_snd.continuousAt
  have hgraph : Tendsto (fun z ↦ (ι z, L z.2)) (𝓝 (cStar, (0, 0)))
      (𝓝 (((0, cStar), (0, 0)), τ0)) := by
    simpa only [ContinuousAt, ι, hLbase] using hι.continuousAt.prodMk hLs
  have hgood : ∀ᶠ z in 𝓝 (cStar, (0, 0)),
      z.1 ∈ V1 ∧ z.2 ∈ U1 ∧ ι z ∈ N ∧ T (ι z) = L z.2 := by
    filter_upwards [((hV.inter hVc).prod (hU.inter hUc)).mem_nhds
        ⟨⟨hbaseV, hbaseVc⟩, ⟨hbaseU, hbaseUc⟩⟩,
      (hι.tendsto (cStar, (0, 0))) (hN.mem_nhds hbaseN), hgraph hunique] with z hz hNz huniq
    have hclosed := hagree z.2 hz.2 z.1 hz.1 (hLtime z.2 hz.2.1)
    have hmiddle := congrArg (fun u : ℝ^3 ↦ u 1) hclosed
    change Ψ (L z.2, ι z) 1 = (F (L z.2, z.2)).1 at hmiddle
    exact ⟨hz.1, hz.2, hNz, huniq.mp (hmiddle.trans (hLzero z.2 hz.2.1))⟩
  obtain ⟨V0, U0, hV0, hbaseV0, hU0, hbaseU0, hprod0⟩ := mem_nhds_prod_iff'.mp hgood
  have hU0U1 : U0 ⊆ U1 := fun p hp ↦ (hprod0 (show (cStar, p) ∈ V0 ×ˢ U0 from ⟨hbaseV0, hp⟩)).2.1
  have hV0V1 : V0 ⊆ V1 := fun c hc ↦ (hprod0 (show (c, (0, 0)) ∈ V0 ×ˢ U0 from ⟨hc, hbaseU0⟩)).1
  have hU0U : U0 ⊆ U := fun p hp ↦ (hU0U1 hp).1
  refine ⟨Ψ, T, N, U0, V0, hN, hbaseN, hΨ, hΨzero, fun θ hθ t ht ↦ hΨode θ (hNsub hθ) t ht, hT,
    hTbase, hTzero, hunique, hU0, hbaseU0, hU0U, hV0, hbaseV0, fun c hc ↦ (hV0V1 hc).1,
    fun p hp c hc ↦ ?_⟩
  have hpc := hprod0 (show (c, p) ∈ V0 ×ˢ U0 from ⟨hc, hp⟩)
  have hclosed := hagree p (hU0U1 hp) c (hV0V1 hc)
  refine ⟨hpc.2.2.1, hpc.2.2.2, hclosed, ?_⟩
  rw [hpc.2.2.2]
  exact hclosed (hLtime p (hU0U hp))

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
