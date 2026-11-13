/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.GateBounds

import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.CEGA
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Nonparallel speed variation on the upward gate

The middle and fast equations of the zero-speed, zero-delta upward gate already
exclude a speed variation that stays tangent to the orbit on an open interval.
The fast equation determines the derivative of the normalized variation. The
middle equation would then force a relation incompatible with the clock
bounds. A nonzero two-coordinate defect persists on a smaller open set.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- On any nonempty open part of the upward gate, the speed variation leaves
`span {v}` at some time and throughout an open neighborhood of that time.

Here `v` is the supplied orbit derivative. The hypotheses are the middle and fast
coordinate equations of the orbit and its speed variation at zero speed
and zero delta, including both forcing terms `-γ₁` and `-γ₂`. Ordinary local derivatives suffice; in
particular, the statement applies to the supplied smooth flow without selecting another curve. -/
theorem exists_prescribed_clock_gate_variation_nonparallel {γ v W : ℝ → ℝ^3} {I : Set ℝ}
    (hI : IsOpen I) (hne : I.Nonempty) (hγ : ∀ t ∈ I, HasDerivAt γ (v t) t)
    (hvy : ∀ t ∈ I, (v t) 1 = MiddleClock.g ((γ t) 1) + 1) (hvz : ∀ t ∈ I, (v t) 2 = 2 * (γ t) 2)
    (hWy : ∀ t ∈ I,
      HasDerivAt (fun s ↦ (W s) 1) (deriv MiddleClock.g ((γ t) 1) * (W t) 1 - (γ t) 1) t)
    (hWz : ∀ t ∈ I, HasDerivAt (fun s ↦ (W s) 2) (2 * (W t) 2 - (γ t) 2) t)
    (hgate : ∀ t ∈ I, (γ t) 1 ∈ Ioo (205 : ℝ) (2051 / 10)) (hpositive : ∀ t ∈ I, 0 < (γ t) 2) :
    ∃ t ∈ I, W t ∉ Submodule.span ℝ {v t} ∧ ∃ J : Set ℝ, IsOpen J ∧ t ∈ J ∧ J ⊆ I ∧ ∀ s ∈ J, W s ∉
      Submodule.span ℝ {v s} := by
  classical
  let u : ℝ → ℝ := fun t ↦ MiddleClock.g ((γ t) 1) + 1
  let c : ℝ → ℝ := fun t ↦ (W t) 2 / (2 * (γ t) 2)
  have hcoord (i : Fin 3) (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun s ↦ (γ s) i) ((v t) i) t :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (γ t) i).comp_hasDerivAt t (hγ t ht)
  have hy (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun s ↦ (γ s) 1) (u t) t :=
    (hcoord 1 t ht).congr_deriv (hvy t ht)
  have hz (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun s ↦ (γ s) 2) (2 * (γ t) 2) t :=
    (hcoord 2 t ht).congr_deriv (hvz t ht)
  have hu (t : ℝ) (ht : t ∈ I) : HasDerivAt u (deriv MiddleClock.g ((γ t) 1) * u t) t :=
    (((MiddleClock.contDiff_g.differentiable (by simp)) _).hasDerivAt.comp t (hy t ht)).add_const 1
  -- The fast variation fixes the multiplier's derivative, including its sign.
  have hc (t : ℝ) (ht : t ∈ I) : HasDerivAt c (-1 / 2 : ℝ) t := by
    have hden : 2 * (γ t) 2 ≠ 0 := mul_ne_zero two_ne_zero (hpositive t ht).ne'
    refine ((hWz t ht).fun_div (HasDerivAt.const_mul 2 (hz t ht)) hden).congr_deriv ?_
    change ((2 * (W t) 2 - (γ t) 2) * (2 * (γ t) 2) -
      (W t) 2 * (2 * (2 * (γ t) 2))) / (2 * (γ t) 2) ^ 2 = (-1 / 2 : ℝ)
    rw [div_eq_iff (pow_ne_zero 2 hden)]
    ring
  have hpoint : ∃ t ∈ I, (W t) 1 ≠ c t * u t := by
    by_contra! heq
    obtain ⟨t, ht⟩ := hne
    have hEqGerm : (fun s ↦ (W s) 1) =ᶠ[𝓝 t] (fun s ↦ c s * u s) := by
      filter_upwards [hI.mem_nhds ht] with s hs using heq s hs
    have hprod : HasDerivAt (fun s ↦ (W s) 1) ((-1 / 2 : ℝ) * u t +
          c t * (deriv MiddleClock.g ((γ t) 1) * u t)) t :=
      ((hc t ht).fun_mul (hu t ht)).congr_of_eventuallyEq hEqGerm
    have heqDeriv := (hWy t ht).unique hprod
    rw [heq t ht] at heqDeriv
    have hforced : 2 * (γ t) 1 = MiddleClock.g ((γ t) 1) + 1 := by
      change 2 * (γ t) 1 = u t
      linear_combination -2 * heqDeriv
    linarith [(MiddleClock.g_mem_Icc_gate ⟨(hgate t ht).1.le, (hgate t ht).2.le⟩).2, (hgate t ht).1]
  -- The normalized two-coordinate test detects membership in the full tangent line.
  have hnonparallel (s : ℝ) (hs : s ∈ I)
      (hneq : (W s) 1 ≠ c s * u s) : W s ∉ Submodule.span ℝ {v s} := by
    intro hspan
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hspan
    have hkz : k * (2 * (γ s) 2) = (W s) 2 := by
      simpa only [PiLp.smul_apply, smul_eq_mul, hvz s hs] using congrArg (fun w : ℝ^3 ↦ w 2) hk
    have hky : k * u s = (W s) 1 := by
      simpa only [PiLp.smul_apply, smul_eq_mul, hvy s hs] using congrArg (fun w : ℝ^3 ↦ w 1) hk
    apply hneq
    dsimp only [c]
    rw [← hky, ← hkz, mul_div_cancel_right₀ _ (mul_ne_zero two_ne_zero (hpositive s hs).ne')]
  obtain ⟨t, ht, htne⟩ := hpoint
  have hcont : ContinuousAt (fun s ↦ (W s) 1 - c s * u s) t := (hWy t ht).continuousAt.sub
      ((hc t ht).continuousAt.mul (hu t ht).continuousAt)
  have hevent : {s | s ∈ I ∧ (W s) 1 - c s * u s ≠ 0} ∈ 𝓝 t :=
    inter_mem (hI.mem_nhds ht) (hcont.eventually_ne (sub_ne_zero.mpr htne))
  obtain ⟨J, hJsub, hJopen, htJ⟩ := mem_nhds_iff.mp hevent
  exact ⟨t, ht, hnonparallel t ht htne, J, hJopen, htJ, fun s hs ↦ (hJsub hs).1,
    fun s hs ↦ hnonparallel s (hJsub hs).1 (sub_ne_zero.mp (hJsub hs).2)⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
