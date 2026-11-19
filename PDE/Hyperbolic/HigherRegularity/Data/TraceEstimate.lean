/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.InitialTrace
public import PDE.Analysis.Evolution.Time.WeakDerivative.L2Representative

/-!
# Quantitative forcing traces

Each nonterminal forcing derivative has a continuous representative after one
spatial restriction. Its initial value is the canonical compatibility trace.
The fundamental theorem holds on the closed interval, and the uniform bound
uses only the two adjacent Bochner norms and the interval length.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Spatial restriction also contracts the Bochner norm. -/
theorem norm_lowerOrderTimeLp_le (f : Lp (W^{(m + 1),2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    ‖lowerOrderTimeLp f‖ ≤ ‖f‖ :=
  ((lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (Nat.le_succ m)).norm_compLp_le f).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (norm_lowerOrderCLM_le_one (Nat.le_succ m)) (norm_nonneg f))

/-- Construct the forcing trace and its interval-only estimate. There is
no trace requirement on the terminal derivative of the jet. -/
theorem InitialTraceData.exists_head_representative_norm_le {F : SobolevTimeJet n (m + 1) Ω a b}
    (traces : InitialTraceData (F := F)) (hab : a < b) :
    ∃ R : ℝ → W^{m,2}(Ω),
      Continuous R ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (Nat.le_succ m) (F.head t) = R t) ∧
      R a = traces.head ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        R t = R s + ∫ r in s..t, F.timeDerivative.head r) ∧
      ∀ t ∈ Icc a b, ‖R t‖ ≤
        (((b - a)⁻¹ + 1) * max 1 (b - a)) * (‖F.head‖ + ‖F.timeDerivative.head‖) := by
  have hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (lowerOrderTimeLp F.head) F.timeDerivative.head := by
    cases F with
    | mk head derivatives =>
        cases derivatives with
        | succ _ df hderiv _ =>
            exact hderiv.identity_hasWeakTimeDerivativeOn
  obtain ⟨R, hR, hae, hFTC, hbound⟩ := hweak.exists_continuous_L2_representative_norm_le hab
  have hrep : (fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (Nat.le_succ m) (F.head t))
      =ᵐ[volume.restrict (Ioc a b)] R := (lowerOrderTimeLp_apply_ae F.head).symm.trans hae
  refine ⟨R, hR, hrep,
    traces.head_eq_of_continuousRepresentative R hR.continuousOn hrep.symm hab, hFTC, ?_⟩
  exact fun t ht ↦ (hbound t ht).trans (mul_le_mul_of_nonneg_left
    (add_le_add (norm_lowerOrderTimeLp_le F.head) le_rfl) (by
      have hlen := sub_pos.mpr hab
      positivity))

/-- Every canonical forcing trace is controlled by the two adjacent data norms. -/
theorem InitialTraceData.norm_head_le {F : SobolevTimeJet n (m + 1) Ω a b}
    (traces : InitialTraceData (F := F)) (hab : a < b) :
    ‖traces.head‖ ≤ (((b - a)⁻¹ + 1) * max 1 (b - a)) * (‖F.head‖ + ‖F.timeDerivative.head‖) := by
  obtain ⟨R, _, _, hRa, _, hbound⟩ := traces.exists_head_representative_norm_le hab
  simpa only [hRa] using hbound a ⟨le_rfl, hab.le⟩

end Hyperbolic.HigherRegularity
