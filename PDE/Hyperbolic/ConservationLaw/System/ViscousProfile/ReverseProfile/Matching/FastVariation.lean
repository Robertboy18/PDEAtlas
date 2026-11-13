/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Events.Speed

import CAS.ExactTactic

/-!
# Fast terminal value and parameter derivatives

The fast component of the supplied family satisfies its constant-rate ODE.
The scalar representation identifies its value at the same terminal event throughout
an open parameter neighborhood. The chain rule then includes the motion of that
event in both ordinary parameter derivatives. The family and event are retained.
-/

@[expose] public noncomputable section

open Filter Set
open PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The fast terminal value and its speed and displacement derivatives.
The event is locally `C¹`; time continuity follows from the supplied ODE, including
at the closed slab endpoints. The unit initial value gives the exponential identity
on the neighborhood, and openness transfers its derivatives to the same terminal state. -/
theorem prescribed_clock_fast_terminal_variation {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L : ℝ × ℝ → ℝ}
    {N : Set (ℝ × ℝ)} {A B H : ℝ} (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hL : ContDiffOn ℝ 1 L N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hfastzero : ∀ p ∈ N, (F (0, p)).2 = 1) (hterminal : ∀ p ∈ N, L p ∈ Icc (0 : ℝ) H) :
    (∀ p ∈ N, (F (L p, p)).2 = Real.exp ((2 - p.1) * L p)) ∧
      HasDerivAt (fun μ : ℝ ↦ (F (L (μ, 0), (μ, 0))).2)
        ((F (L (0, 0), (0, 0))).2 *
          (2 * deriv (fun μ : ℝ ↦ L (μ, 0)) 0 - L (0, 0))) 0 ∧
      HasDerivAt (fun a : ℝ ↦ (F (L (0, a), (0, a))).2)
        (2 * (F (L (0, 0), (0, 0))).2 * deriv (fun a : ℝ ↦ L (0, a)) 0) 0 := by
  have hvalue (p : ℝ × ℝ) (hp : p ∈ N) :
      (F (L p, p)).2 = Real.exp ((2 - p.1) * L p) := by
    have hcontinuous : ContinuousOn (fun t : ℝ ↦ (F (t, p)).2)
        (Icc (0 : ℝ) (L p)) := by
      intro t ht
      exact (hode p hp t ⟨ht.1, ht.2.trans (hterminal p hp).2⟩).continuousAt.snd.continuousWithinAt
    have heq := eq_scalarLinearSolution_const_of_hasDerivAt
      (r := fun t ↦ (F (t, p)).2) (f := fun _ ↦ 0) (κ := -(2 - p.1))
      (hterminal p hp).1 hcontinuous continuousOn_const
      (fun t ht ↦ by
        have hpair := hode p hp t ⟨ht.1.le, ht.2.le.trans (hterminal p hp).2⟩
        simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', prescribedSpeedField,
          neg_neg, add_zero] using
          (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hpair)
    rw [scalarLinearSolution_const_eq_exp_mul_add_integral] at heq
    simpa only [hfastzero p hp, neg_neg, sub_zero, mul_one, mul_zero,
      intervalIntegral.integral_zero, add_zero] using heq
  have hbaseValue : (F (L (0, 0), (0, 0))).2 = Real.exp (2 * L (0, 0)) := by
    simpa only [sub_zero] using hvalue (0, 0) hbase
  have hLd : DifferentiableAt ℝ L (0, 0) := (hL.contDiffAt (hN.mem_nhds hbase)).differentiableAt_one
  have hspeedAxis : DifferentiableAt ℝ (fun μ : ℝ ↦ (μ, (0 : ℝ))) 0 :=
    differentiableAt_id.prodMk (differentiableAt_const 0)
  have hdisplacementAxis : DifferentiableAt ℝ (fun a : ℝ ↦ ((0 : ℝ), a)) 0 :=
    (differentiableAt_const 0).prodMk differentiableAt_id
  have hLspeed : HasDerivAt (fun μ : ℝ ↦ L (μ, 0)) (deriv (fun μ : ℝ ↦ L (μ, 0)) 0) 0 :=
    (hLd.comp (f := fun μ : ℝ ↦ (μ, (0 : ℝ))) 0 hspeedAxis).hasDerivAt
  have hLdisplacement : HasDerivAt (fun a : ℝ ↦ L (0, a)) (deriv (fun a : ℝ ↦ L (0, a)) 0) 0 :=
    (hLd.comp (f := fun a : ℝ ↦ ((0 : ℝ), a)) 0 hdisplacementAxis).hasDerivAt
  refine ⟨hvalue, ?_, ?_⟩
  · have hrate : HasDerivAt (fun μ : ℝ ↦ 2 - μ) (-1) 0 := (hasDerivAt_id 0).const_sub 2
    have hexp : HasDerivAt (fun μ : ℝ ↦ Real.exp ((2 - μ) * L (μ, 0))) ((F (L (0, 0), (0, 0))).2 *
          (2 * deriv (fun μ : ℝ ↦ L (μ, 0)) 0 - L (0, 0))) 0 := by
      apply (hrate.fun_mul hLspeed).exp.congr_deriv
      rw [hbaseValue]
      ring_nf
    apply hexp.congr_of_eventuallyEq
    have hmem : ∀ᶠ μ : ℝ in 𝓝 0, (μ, (0 : ℝ)) ∈ N :=
      hspeedAxis.continuousAt.eventually_mem (hN.mem_nhds hbase)
    exact hmem.mono (fun μ hμ ↦ hvalue (μ, 0) hμ)
  · have hexp : HasDerivAt (fun a : ℝ ↦ Real.exp (2 * L (0, a)))
        (2 * (F (L (0, 0), (0, 0))).2 * deriv (fun a : ℝ ↦ L (0, a)) 0) 0 := by
      apply (hLdisplacement.const_mul 2).exp.congr_deriv
      rw [hbaseValue]
      ring
    apply hexp.congr_of_eventuallyEq
    have hmem : ∀ᶠ a : ℝ in 𝓝 0, ((0 : ℝ), a) ∈ N :=
      hdisplacementAxis.continuousAt.eventually_mem (hN.mem_nhds hbase)
    exact hmem.mono (fun a ha ↦ by simpa only [sub_zero] using hvalue (0, a) ha)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
