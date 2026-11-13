/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Uniform convergence with a common finite-measure support

Uniform approximation on one finite-measure set controls every finite Lᵖ seminorm.
The measure may already contain a singular weight: finiteness on the common support
is enough, without a pointwise bound on its density. Eventual support and measurability
assumptions allow the first few terms of an approximation to use larger supports.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- Uniform approximation on a common finite-measure support gives convergence in every
finite Lᵖ seminorm. Only the differences must be eventually a.e. strongly measurable. -/
theorem tendsto_eLpNorm_sub_of_tendstoUniformlyOn
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {l : Filter ι} {s : Set α}
    {f : ι → α → E} {g : α → E}
    (hp : p ≠ ∞) (hs : NullMeasurableSet s μ) (hfinite : μ s ≠ ∞)
    (hfg : ∀ᶠ n in l, AEStronglyMeasurable (f n - g) μ)
    (hf : ∀ᶠ n in l, Function.support (f n) ⊆ s)
    (hg : Function.support g ⊆ s) (hconv : TendstoUniformlyOn f g l s) :
    Tendsto (fun n ↦ eLpNorm (f n - g) p μ) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  have hweight : μ s ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hfinite
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hweight hε.ne'
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv δ hδ, hfg, hf] with
    n hn hmeas hsupp
  have hdist (x : α) : dist (f n x) (g x) ≤ δ := by
    by_cases hx : x ∈ s
    · rw [dist_comm]
      exact (hn x hx).le
    · rw [Function.notMem_support.mp (mt (@hsupp x) hx),
        Function.notMem_support.mp (mt (@hg x) hx), dist_self]
      exact δ.coe_nonneg
  exact (eLpNorm_sub_le_of_dist_bdd μ hp hs δ.coe_nonneg hmeas hdist hsupp hg).trans
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hδε.le)

end MeasureTheory
