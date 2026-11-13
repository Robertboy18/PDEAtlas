/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Uniqueness
public import PDE.Analysis.Calculus.PositivePartRpow

/-!
# Classical power waves before a terminal time

The solution class records the wave operator and both Cauchy traces.
Regularity is imposed on the open half-space before the endpoint, including
a neighborhood of the initial slice. Existence and boundedness of this class
are separate propositions; neither is built into a lifespan definition.
-/

@[expose] public noncomputable section

open PDE.Common Set

namespace WaveEquation.SmallData.Classical

variable {n : ℕ}

/-- A classical Cauchy solution before a positive time. The negative-time
extension is only a regular representative and need not satisfy the PDE. -/
structure IsSolutionBefore
    (f : ℝ → ℝ) (g h : ℝ^n → ℝ) (T : ℝ) (u : ℝ^(n + 1) → ℝ) : Prop where
  time_pos : 0 < T
  regular : ContDiffOn ℝ 2 u {p | p 0 < T}
  equation : ∀ p, p 0 ∈ Ico 0 T → waveOperator u p = -f (u p)
  position : ∀ x, u (timeSpaceCons 0 x) = g x
  velocity : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x

/-- Restriction of the PDE solution to a smaller positive interval. -/
theorem IsSolutionBefore.mono {f : ℝ → ℝ} {g h : ℝ^n → ℝ} {S T : ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : IsSolutionBefore f g h T u) (hS : 0 < S) (hST : S ≤ T) :
    IsSolutionBefore f g h S u :=
  ⟨hS, hu.regular.mono (fun _ hp ↦ lt_of_lt_of_le hp hST),
    fun p hp ↦ hu.equation p ⟨hp.1, hp.2.trans_le hST⟩, hu.position, hu.velocity⟩

/-- Classical solutions with common data agree on their forward overlap. -/
theorem IsSolutionBefore.eq_on_overlap [Fact (0 < n)] {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    {g h : ℝ^n → ℝ} {S T : ℝ} {u v : ℝ^(n + 1) → ℝ} (hu : IsSolutionBefore f g h S u)
    (hv : IsSolutionBefore f g h T v) :
    ∀ p, p 0 ∈ Ico 0 (min S T) → u p = v p := by
  have hU := hu.mono (lt_min hu.time_pos hv.time_pos) (min_le_left S T)
  have hV := hv.mono (lt_min hu.time_pos hv.time_pos) (min_le_right S T)
  exact eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz hf
    hU.regular hV.regular hU.equation hV.equation
    (fun x ↦ (hu.position x).trans (hv.position x).symm)
    (fun x ↦ (hu.velocity x).trans (hv.velocity x).symm)

/-- For every real exponent greater than one, the absolute power is C¹ at zero
as well as away from zero. -/
theorem contDiff_one_abs_rpow {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (fun x : ℝ ↦ |x| ^ p) := by
  have heq : (fun x : ℝ ↦ |x| ^ p) = fun x ↦ x⁺ ^ p + (-x)⁺ ^ p := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, posPart_eq_self.mpr hx,
        posPart_eq_zero.mpr (neg_nonpos.mpr hx), Real.zero_rpow (by linarith), add_zero]
    · rw [abs_of_nonpos hx, posPart_eq_zero.mpr hx,
        posPart_eq_self.mpr (neg_nonneg.mpr hx), Real.zero_rpow (by linarith), zero_add]
  rw [heq]
  exact (PDE.Analysis.contDiff_one_posPart_rpow hp).add
    ((PDE.Analysis.contDiff_one_posPart_rpow hp).comp contDiff_neg)

/-- The power reaction has precisely the local Lipschitz regularity required
by classical uniqueness for every `p > 1`. -/
theorem locallyLipschitz_neg_abs_rpow {p : ℝ} (hp : 1 < p) :
    LocallyLipschitz (fun x : ℝ ↦ -|x| ^ p) :=
  (contDiff_one_abs_rpow hp).neg.locallyLipschitz

/-- Durations for which a classical solution exists. This set is
allowed to be empty until a local construction has been proved. -/
def existenceTimes (f : ℝ → ℝ) (g h : ℝ^n → ℝ) : Set ℝ :=
  {T | ∃ u, IsSolutionBefore f g h T u}

end WaveEquation.SmallData.Classical
