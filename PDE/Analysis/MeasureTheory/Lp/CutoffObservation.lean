/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Local Lp bounds from cutoff observations

If an Lp element represents a cutoff times a function, its norm controls the
function on every measurable set where the cutoff is one. The local measure
may be any measure dominated by the measure of the observation.

For observations available at every test function, this yields bounds on balls
and uniform convergence of local Lp distances. The bound is chosen before the
state.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Filter TopologicalSpace
open scoped ENNReal Distributions

/-- A cutoff equal to one on a measurable set transfers Lp membership and its
norm bound to that set, for any smaller measure. -/
theorem local_lpNorm_le_cutoff
    {X : Type*} [MeasurableSpace X] {p : ℝ≥0∞}
    {μ ν : Measure X} (hν : ν ≤ μ) {s : Set X} (hs : MeasurableSet s)
    (χ : X → ℝ) (hχ : ∀ x ∈ s, χ x = 1) (v : Lp ℝ p μ) (q : X → ℝ)
    (hrep : (v : X → ℝ) =ᵐ[μ] fun x ↦ χ x * q x) :
    MemLp q p (ν.restrict s) ∧ lpNorm q p (ν.restrict s) ≤ ‖v‖ := by
  have hmeasure : ν.restrict s ≤ μ := Measure.restrict_le_self.trans hν
  have hlocal : (v : X → ℝ) =ᵐ[ν.restrict s] q := by
    filter_upwards [ae_mono hmeasure hrep, ae_restrict_mem hs] with x hx hxs
    simpa only [hχ x hxs, one_mul] using hx
  have hv := Lp.memLp v
  refine ⟨(hv.mono_measure hmeasure).ae_eq hlocal, ?_⟩
  rw [← toReal_eLpNorm, ← eLpNorm_congr_ae hlocal, Lp.norm_def]
  exact ENNReal.toReal_mono hv.eLpNorm_ne_top (eLpNorm_mono_measure _ hmeasure)

/-- Uniform convergence of all cutoff observations gives uniform convergence
of local Lp distances on each ball. The state space need not carry any topology. -/
theorem tendstoUniformly_localLpNorm_of_cutoffs
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure (ℝ^n)}
    {E ι X : Type*} {l : Filter ι}
    (J : 𝓓((⊤ : Opens (ℝ^n)), ℝ) → E → Lp ℝ p μ)
    (q : E → (ℝ^n → ℝ))
    (hJ : ∀ χ U, (J χ U : ℝ^n → ℝ) =ᵐ[μ] fun x ↦ χ x * q U x)
    (u : ι → X → E) (uLimit : X → E)
    (hconv : ∀ χ, TendstoUniformly (fun k t ↦ J χ (u k t))
      (fun t ↦ J χ (uLimit t)) l)
    {ν : Measure (ℝ^n)} (hν : ν ≤ μ) (R : ℝ) :
    TendstoUniformly
      (fun k t ↦ lpNorm (fun x ↦ q (u k t) x - q (uLimit t) x) p
        (ν.restrict (Metric.ball 0 R))) (fun _ ↦ 0) l := by
  obtain ⟨χ, _, hχ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ (isCompact_closedBall (0 : ℝ^n) R) (Set.subset_univ _)
  have hχball : ∀ x ∈ Metric.ball (0 : ℝ^n) R, χ x = 1 :=
    fun x hx ↦ hχ x (Metric.ball_subset_closedBall hx)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp (hconv χ) ε hε] with k hk
  intro t
  have hsub : ((J χ (u k t) - J χ (uLimit t) : Lp ℝ p μ) : ℝ^n → ℝ)
      =ᵐ[μ] fun x ↦ χ x * (q (u k t) x - q (uLimit t) x) := by
    filter_upwards [Lp.coeFn_sub (J χ (u k t)) (J χ (uLimit t)),
      hJ χ (u k t), hJ χ (uLimit t)] with x hx h₁ h₂
    simpa only [Pi.sub_apply, h₁, h₂, mul_sub] using hx
  have hb := (local_lpNorm_le_cutoff hν Metric.isOpen_ball.measurableSet χ hχball
    (J χ (u k t) - J χ (uLimit t)) _ hsub).2
  rw [dist_zero_left, Real.norm_of_nonneg lpNorm_nonneg]
  apply hb.trans_lt
  have hkt := hk t
  rw [dist_eq_norm] at hkt
  exact (norm_sub_rev _ _).trans_lt hkt

/-- Bounded linear cutoff observations give one local Lp bound on each ball,
with its constant chosen before the state. -/
theorem exists_localLpNorm_bound_of_cutoffs
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure (ℝ^n)}
    {E : Type*} [NormedAddCommGroup E] [instE : NormedSpace ℝ E]
    (J : 𝓓((⊤ : Opens (ℝ^n)), ℝ) → E →L[ℝ] Lp ℝ p μ)
    (q : E → (ℝ^n → ℝ))
    (hJ : ∀ χ U, (J χ U : ℝ^n → ℝ) =ᵐ[μ] fun x ↦ χ x * q U x)
    {ν : Measure (ℝ^n)} (hν : ν ≤ μ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : E, MemLp (q U) p (ν.restrict (Metric.ball 0 R)) ∧
      lpNorm (q U) p (ν.restrict (Metric.ball 0 R)) ≤ C * ‖U‖ := by
  obtain ⟨χ, _, hχ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ (isCompact_closedBall (0 : ℝ^n) R) (Set.subset_univ _)
  refine ⟨‖J χ‖, norm_nonneg (J χ), fun U ↦ ?_⟩
  obtain ⟨hmem, hb⟩ := local_lpNorm_le_cutoff hν Metric.isOpen_ball.measurableSet χ
    (fun x hx ↦ hχ x (Metric.ball_subset_closedBall hx)) (J χ U) _ (hJ χ U)
  exact ⟨hmem, hb.trans ((J χ).le_opNorm U)⟩

end MeasureTheory
