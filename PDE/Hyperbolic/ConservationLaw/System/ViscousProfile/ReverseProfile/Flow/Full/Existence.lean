/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.Parameter
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import PDE.Analysis.Evolution.ODE.FiniteContinuation

/-!
# A smooth full flow through the prescribed initial section

A supplied reference on `[0,H]` suffices for a jointly smooth family of
solutions of the full concrete flux equation. Local existence through its exact
initial state supplies a short left extension before applying finite parameter
flow. Pulling back the initial-state coordinate preserves `!₂[0,a,1]` for every
parameter. The thresholds and the smooth signed gate family remain fixed.
-/

@[expose] public noncomputable section

open Set PDE.Analysis
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The full field is jointly smooth in the fast-law parameter, signed gate
coefficients, speed, and state. The feedback thresholds are arbitrary fixed reals. -/
theorem contDiff_prescribed_clock_full_field (A B : ℝ)
    {b : (Fin 3 → ℝ) × ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun z : (((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3) ↦ concreteGatedFlux z.1.1.1
      (clockFeedback A B) (fun y ↦ b (z.1.1.2, y)) z.2 - z.1.2 • z.2) := by
  have hk (i : Fin 3) : ContDiff ℝ ∞
      (fun z : (((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3) ↦ fastLogCosh z.1.1.1 (z.2 i)) :=
    contDiff_fastLogCosh_joint.comp (contDiff_fst.fst.fst.prodMk
      ((contDiff_piLp_apply (2 : ENNReal)).comp contDiff_snd))
  have := hk 0; have := hk 2; have := MiddleClock.contDiff_g; have := contDiff_cutoff
  have := contDiff_clockFeedback A B
  refine ContDiff.sub ?_ (by fun_prop)
  unfold concreteGatedFlux GatedFlux.flux
  refine (contDiff_piLp (2 : ENNReal)).mpr fun i ↦ ?_
  fin_cases i
  · change ContDiff ℝ ∞ (fun z : (((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3) ↦
      -fastLogCosh z.1.1.1 (z.2 0) + b (z.1.1.2, z.2 1) * z.2 2)
    fun_prop
  · change ContDiff ℝ ∞ (fun z : (((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3) ↦
      MiddleClock.g (z.2 1) + cutoff (-z.2 1) * clockFeedback A B (z.2 2) +
        cutoff (z.2 1) * clockFeedback A B (z.2 0))
    fun_prop
  · change ContDiff ℝ ∞ (fun z : (((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3) ↦
      fastLogCosh z.1.1.1 (z.2 2) - b (z.1.1.2, -z.2 1) * z.2 0)
    fun_prop

/-- A supplied base solution gives one smooth full-flow family on the same
closed time slab. Parameters are `((δ,c),(μ,a))`; the initial identity holds for
all parameters, and the full ODE holds on one open neighborhood of the base.
The same reference curve is retained on every point of `[0,H]`. -/
theorem exists_prescribed_clock_full_flow (A B : ℝ) {b : (Fin 3 → ℝ) × ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (cStar : Fin 3 → ℝ) {H : ℝ} (hH : 0 < H) (γ : ℝ → ℝ^3)
    (hγode : ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt γ (concreteGatedFlux 0 (clockFeedback A B) (fun y ↦ b (cStar, y)) (γ t)) t)
    (hγzero : γ 0 = (!₂[0, 0, 1] : ℝ^3)) :
    ∃ (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
      (N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))),
      IsOpen N ∧ ((0, cStar), (0, 0)) ∈ N ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ p, Ψ (0, p) = (!₂[0, p.2.2, 1] : ℝ^3)) ∧
      EqOn (fun t ↦ Ψ (t, ((0, cStar), (0, 0)))) γ (Icc (0 : ℝ) H) ∧
      ∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) H,
        HasDerivAt (fun s ↦ Ψ (s, p))
          (concreteGatedFlux p.1.1 (clockFeedback A B)
            (fun y ↦ b (p.1.2, y)) (Ψ (t, p)) - p.2.1 • Ψ (t, p)) t := by
  let v : (((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3) → ℝ^3 := fun z ↦
    concreteGatedFlux z.1.1.1 (clockFeedback A B) (fun y ↦ b (z.1.1.2, y)) z.2 - z.1.2 • z.2
  let p₀ : (ℝ × (Fin 3 → ℝ)) × ℝ := ((0, cStar), 0)
  have hv : ContDiff ℝ ∞ v := contDiff_prescribed_clock_full_field A B hb
  have hγv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
      HasDerivAt γ (v (p₀, γ t)) t := by
    simpa only [v, p₀, zero_smul, sub_zero] using hγode t ht
  have hv₀ : ContDiffAt ℝ 1 (fun u : ℝ^3 ↦ v (p₀, u)) (!₂[0, 0, 1] : ℝ^3) :=
    (hv.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp)
  obtain ⟨α, hαzero, ε, hε, hαode⟩ :=
    hv₀.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (0 : ℝ)
  have hleft : -(ε / 2) < (0 : ℝ) := neg_lt_zero.mpr (half_pos hε)
  have hαleft : ∀ t ∈ Icc (-(ε / 2)) (0 : ℝ),
      HasDerivWithinAt α (v (p₀, α t)) (Icc (-(ε / 2)) 0) t := fun t ht ↦
    (hαode t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivWithinAt
  obtain ⟨γext, _, hext, hextode⟩ := PDE.Analysis.Evolution.glue_ode_solution_Icc
      (fun _ u ↦ v (p₀, u)) hleft.le hH.le α γ (hαzero.trans hγzero.symm) hαleft
      (fun t ht ↦ (hγv t ht).hasDerivWithinAt)
  obtain ⟨Φ, W, hW, hbaseW, hΦ, hΦzero, hΦsame, hΦode⟩ :=
    PDE.Analysis.ODE.exists_contDiff_infty_parameterized_family_near_solution_Icc
      v hv hleft hH p₀ γext (fun t ht ↦ (hextode t ht).continuousWithinAt)
      (fun t ht ↦ (hextode t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (!₂[0, 0, 1] : ℝ^3) ((hext 0 ⟨le_rfl, hH.le⟩).trans hγzero)
  let j : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ((ℝ × (Fin 3 → ℝ)) × ℝ) × ℝ^3 :=
    fun p ↦ ((p.1, p.2.1), !₂[0, p.2.2, 1])
  have hjstate : ContDiff ℝ ∞
      (fun p : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) ↦ (!₂[0, p.2.2, 1] : ℝ^3)) := by
    refine (contDiff_piLp (2 : ENNReal)).mpr fun i ↦ ?_
    fin_cases i
    exacts [contDiff_const, contDiff_snd.snd, contDiff_const]
  have hj : ContDiff ℝ ∞ j := (contDiff_fst.prodMk contDiff_snd.fst).prodMk hjstate
  let Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3 := fun z ↦ Φ (z.1, j z.2)
  let N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) := j ⁻¹' W
  have hΨ : ContDiff ℝ ∞ Ψ := hΦ.comp (contDiff_fst.prodMk (hj.comp contDiff_snd))
  exact ⟨Ψ, N, hW.preimage hj.continuous, hbaseW, hΨ, fun p ↦ hΦzero (j p),
    fun t ht ↦ (hΦsame ⟨hleft.le.trans ht.1, ht.2⟩).trans (hext t ht),
    fun p hp t ht ↦ hΦode (j p) hp t ⟨hleft.le.trans ht.1, ht.2⟩⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
