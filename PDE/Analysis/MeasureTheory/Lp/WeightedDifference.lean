/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closed graphs of weighted differences

A weighted difference sends `u` to `w (x, y) • (u x - u y)`. Its graph in the
product of two `L^p` spaces is closed: convergence in each coordinate gives a
common almost-everywhere convergent subsequence, and scalar multiplication
preserves its pointwise limit.

The weight need not be measurable for this closedness statement. The graph
only contains pairs whose second coordinate already belongs to `L^p`.
Fractional Sobolev spaces use a measurable power of the distance as the weight.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α}

/-- A weighted difference has closed graph in `L^p(μ) × L^p(μ × μ)`.
This includes `p = ∞` and arbitrary real weights. -/
theorem isClosed_graph_weightedDifference {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : α × α → ℝ) :
    IsClosed {z : Lp F p μ × Lp F p (μ.prod μ) |
      (z.2 : α × α → F) =ᵐ[μ.prod μ] fun x ↦ w x • (z.1 x.1 - z.1 x.2)} := by
  apply IsSeqClosed.isClosed
  intro z z₀ hz hzz₀
  have hu : Tendsto (fun k ↦ (z k).1) atTop (nhds z₀.1) :=
    (continuous_fst.tendsto z₀).comp hzz₀
  have hv : Tendsto (fun k ↦ (z k).2) atTop (nhds z₀.2) :=
    (continuous_snd.tendsto z₀).comp hzz₀
  obtain ⟨k, hk, hku⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  obtain ⟨l, hl, hlv⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hv.comp hk.tendsto_atTop)).exists_seq_tendsto_ae
  have hku' : ∀ᵐ x ∂μ,
      Tendsto (fun j ↦ (z (k (l j))).1 x) atTop (nhds (z₀.1 x)) :=
    hku.mono fun _ hx ↦ hx.comp hl.tendsto_atTop
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hku'
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hku'
  have hgraph : ∀ᵐ x ∂μ.prod μ, ∀ j,
      (z (k (l j))).2 x = w x • ((z (k (l j))).1 x.1 - (z (k (l j))).1 x.2) :=
    ae_all_iff.2 fun j ↦ hz (k (l j))
  filter_upwards [hlv, hfst, hsnd, hgraph] with x hx hx₁ hx₂ hgraph
  have hdiff : Tendsto
      (fun j ↦ w x • ((z (k (l j))).1 x.1 - (z (k (l j))).1 x.2))
      atTop (nhds (w x • (z₀.1 x.1 - z₀.1 x.2))) :=
    (hx₁.sub hx₂).const_smul (w x)
  exact tendsto_nhds_unique
    (hx.congr' (Filter.Eventually.of_forall hgraph)) hdiff

end MeasureTheory.Lp
