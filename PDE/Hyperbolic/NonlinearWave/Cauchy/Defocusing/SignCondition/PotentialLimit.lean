/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.NonnegativeLimit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.ReactionConvergence

/-!
# Integrability of limiting sign-condition potentials

Agreement of reactions on amplitude balls also gives agreement of their
normalized potentials. Fatou's lemma then proves integrability of the original potential from a
uniform bound for the truncated energies.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open PDE.Analysis (primitive continuous_primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Reactions agreeing on a ball centered at zero have the same normalized
potential throughout that ball. -/
theorem potential_eqOn_of_eqOn_closedBall {f g : ℝ → ℝ} {r : ℝ}
    (h : EqOn f g (Metric.closedBall 0 r)) :
    EqOn (primitive f) (primitive g) (Metric.closedBall 0 r) := by
  intro z hz
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  apply h
  have hsz : |s| ≤ |z| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using
    hsz.trans (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hz)

/-- Nonnegative truncated potentials with an eventual integral bound yield an
integrable original potential along any almost-everywhere displacement limit.
No growth bound on the original reaction is required. -/
theorem integrable_potential_of_truncated_ae_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {r : ℕ → ℝ} (hf : Continuous f) (hg : ∀ i, Continuous (g i))
    (hs : ∀ i z, 0 ≤ z * g i z) (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i)))
    (hr : Tendsto r atTop atTop) {u : ℕ → α → ℝ} {v : α → ℝ} {C : ℝ}
    (hF : ∀ i, Integrable (fun x ↦ primitive (g i) (u i x)) μ)
    (hb : ∀ᶠ i in atTop, (∫ x, primitive (g i) (u i x) ∂μ) ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ u i x) atTop (𝓝 (v x))) :
    Integrable (fun x ↦ primitive f (v x)) μ ∧ (∫ x, primitive f (v x) ∂μ) ≤ C := by
  apply integrable_and_integral_le_of_nonnegative_limit hF
    (fun i ↦ Eventually.of_forall fun x ↦ primitive_nonneg (hg i) (hs i) (u i x)) hb
  filter_upwards [hlim] with x hx
  exact tendsto_reaction_of_expanding_agreement (continuous_primitive hf)
    (fun i ↦ potential_eqOn_of_eqOn_closedBall (hagree i)) hr hx


end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
