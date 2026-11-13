/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.Galerkin

/-!
# Autonomous monotone Galerkin equations

For the equation `-div a(Du) = f` with zero Sobolev boundary data, a continuous
monotone flux of linear growth satisfying `α |p|² - β ≤ ⟨a(p), p⟩`, `α > 0`,
admits Galerkin coefficients for every finite trial family. A single energy constant
controls all solutions of all these finite systems.

These are the construction and energy statements of Evans, §9.1, Theorems 1 and 2, for a
continuous flux and an arbitrary finite trial family. On bounded open domains the supported-core
space is `H¹₀`; its full Sobolev norm and the Dirichlet gradient norm both satisfy the estimate.
The proofs derive measurability, integrable growth offsets, and operator hypotheses
from the pointwise flux assumptions.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "V" => H¹₀(Ω)
local notation "μ" => domainMeasure n Ω
local notation "B₀" => baseCoordCLM (n := n) (Ω := Ω)

/-- Coefficients solve the finite autonomous Galerkin system for an arbitrary finite trial
family. The conclusion also supplies every test in the trial span. -/
theorem exists_galerkin_coefficients_autonomous
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (a : ℝ^n → ℝ^n) (ha : Continuous a) {C α β : ℝ}
    (hgrowth : ∀ p, ‖a p‖ ≤ C * (1 + ‖p‖))
    (hmono : ∀ p q, 0 ≤ inner ℝ (a p - a q) (p - q))
    (hα : 0 < α) (hlower : ∀ p, α * ‖p‖ ^ 2 - β ≤ inner ℝ (a p) p)
    (f : Lp ℝ 2 μ) {ι : Type*} [Fintype ι] (w : ι → V) :
    ∃ d : ι → ℝ,
      (∀ i, (∫ x, inner ℝ (a (∇ ((∑ j, d j • w j : H¹₀(Ω)) : H¹(Ω)) x))
        (∇ (w i : H¹(Ω)) x) ∂μ) =
        ∫ x, f x * B₀ (w i) x ∂μ) ∧
      (∀ v ∈ Submodule.span ℝ (range w),
        (∫ x, inner ℝ (a (∇ ((∑ j, d j • w j : H¹₀(Ω)) : H¹(Ω)) x))
          (∇ (v : H¹(Ω)) x) ∂μ) =
          ∫ x, f x * B₀ v x ∂μ) := by
  let : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hΩ
  have hmeas : Measurable (Function.uncurry (fun (_ : ℝ^n) p ↦ a p)) :=
    ha.measurable.comp measurable_snd
  have hgrowth' : ∀ᵐ x ∂μ, ∀ p, ‖a p‖ ≤ C + C * ‖p‖ :=
    ae_of_all μ fun _ p ↦ by simpa only [mul_add, mul_one] using hgrowth p
  have hhemi : ∀ᵐ x ∂μ, ∀ p q : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a (p + t • q)) q) (Ici 0) 0 := by
    apply ae_of_all
    intro _ p q
    exact ((ha.comp (continuous_const.add (continuous_id.smul continuous_const))).inner
      continuous_const).continuousWithinAt
  obtain ⟨d, hd⟩ := exists_galerkin_coefficients_gradientFlux
    (fun _ p ↦ a p) hmeas (memLp_const C) hgrowth' hn hΩ
    (ae_of_all μ fun _ ↦ hmono) hhemi hα (integrable_const β)
    (ae_of_all μ fun _ ↦ hlower) f w
  exact ⟨d, fun i ↦ hd (w i) (Submodule.subset_span (mem_range_self i)), hd⟩

/-- A constant depending only on the bounded domain and flux bounds controls every
finite autonomous Galerkin solution. It precedes the load, finite index type, family,
and coefficients. Both the full Sobolev norm and the Dirichlet norm are bounded.
Only the finite equations, not the full weak equation, are assumed. -/
theorem exists_pos_galerkin_bound_autonomous
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (a : ℝ^n → ℝ^n) (ha : Continuous a) {C α β : ℝ}
    (hgrowth : ∀ p, ‖a p‖ ≤ C * (1 + ‖p‖))
    (hα : 0 < α) (hlower : ∀ p, α * ‖p‖ ^ 2 - β ≤ inner ℝ (a p) p) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : Lp ℝ 2 μ) {ι : Type*} [Fintype ι]
      (w : ι → V) (d : ι → ℝ),
      (∀ i, (∫ x, inner ℝ (a (∇ ((∑ j, d j • w j : H¹₀(Ω)) : H¹(Ω)) x))
        (∇ (w i : H¹(Ω)) x) ∂μ) =
        ∫ x, f x * B₀ (w i) x ∂μ) →
      ‖∑ i, d i • w i‖ ≤ M * (1 + ‖f‖) ∧
        ‖∇ ((∑ i, d i • w i : H¹₀(Ω)) : H¹(Ω))‖ ≤ M * (1 + ‖f‖) := by
  let : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hΩ
  have hmeas : Measurable (Function.uncurry (fun (_ : ℝ^n) p ↦ a p)) :=
    ha.measurable.comp measurable_snd
  have hgrowth' : ∀ᵐ x ∂μ, ∀ p, ‖a p‖ ≤ C + C * ‖p‖ :=
    ae_of_all μ fun _ p ↦ by simpa only [mul_add, mul_one] using hgrowth p
  obtain ⟨M, hM, hbound⟩ := exists_pos_galerkin_bound_gradientFlux
    (fun _ p ↦ a p) hmeas (memLp_const C) hgrowth' hn hΩ hα
    (integrable_const β) (ae_of_all μ fun _ ↦ hlower)
  refine ⟨M, hM, ?_⟩
  intro f ι _ w d heq
  exact ⟨hbound f w d heq, (gradientCLM_norm_le _).trans (hbound f w d heq)⟩

end SobolevSpace.GraphSpace
