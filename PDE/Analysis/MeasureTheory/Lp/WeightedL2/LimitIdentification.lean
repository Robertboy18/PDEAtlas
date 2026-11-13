/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Identifying weighted and unweighted L² limits

The relation `v = (u - b) * w` is closed in the product of two L² spaces,
when the weighted space uses a smaller measure. A common almost-everywhere
convergent subsequence proves closedness. It then identifies limits along
arbitrary nontrivial filters, without requiring a countable filter basis.

No integrability assumption is imposed on the fixed reference or weight.
Only the weighted differences themselves must belong to L².
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- The graph of multiplication of a fixed-reference difference by any real
weight is closed, also when the weighted norm uses a smaller measure. -/
theorem isClosed_weighted_sub_graph (hν : ν ≤ μ) (b w : α → ℝ) :
    IsClosed {z : Lp ℝ 2 μ × Lp ℝ 2 ν |
      (z.2 : α → ℝ) =ᵐ[ν] fun x ↦ (z.1 x - b x) * w x} := by
  apply IsSeqClosed.isClosed
  intro z z₀ hz hzz₀
  have hu := (continuous_fst.tendsto z₀).comp hzz₀
  have hv := (continuous_snd.tendsto z₀).comp hzz₀
  obtain ⟨k, hk, hku⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  obtain ⟨j, hj, hjv⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hv.comp hk.tendsto_atTop)).exists_seq_tendsto_ae
  have hgraph : ∀ᵐ x ∂ν, ∀ n,
      (z (k (j n))).2 x = ((z (k (j n))).1 x - b x) * w x :=
    ae_all_iff.mpr fun n ↦ hz (k (j n))
  filter_upwards [hku.filter_mono (ae_mono hν), hjv, hgraph] with x hxu hxv hxgraph
  have hweighted :
      Tendsto (fun n ↦ ((z (k (j n))).1 x - b x) * w x) atTop
        (𝓝 ((z₀.1 x - b x) * w x)) :=
    ((hxu.comp hj.tendsto_atTop).sub_const (b x)).mul_const (w x)
  exact tendsto_nhds_unique (hxv.congr' (Eventually.of_forall hxgraph)) hweighted

/-- The unweighted and weighted L² limits satisfy the same weighted-difference
identity as the approximating family. -/
theorem ae_eq_weighted_sub_of_tendsto_L2
    {ι : Type*} {l : Filter ι} [l.NeBot] (hν : ν ≤ μ)
    {u : ι → Lp ℝ 2 μ} {v : ι → Lp ℝ 2 ν}
    {U : Lp ℝ 2 μ} {V : Lp ℝ 2 ν} {b w : α → ℝ}
    (hu : Tendsto u l (𝓝 U)) (hv : Tendsto v l (𝓝 V))
    (hgraph : ∀ᶠ i in l, (v i : α → ℝ) =ᵐ[ν] fun x ↦ (u i x - b x) * w x) :
    (V : α → ℝ) =ᵐ[ν] fun x ↦ (U x - b x) * w x :=
  (isClosed_weighted_sub_graph hν b w).mem_of_tendsto (hu.prodMk_nhds hv) hgraph

end MeasureTheory.Lp
