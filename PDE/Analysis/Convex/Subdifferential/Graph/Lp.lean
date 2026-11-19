/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Subdifferential.Graph.Closed
public import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Subdifferential graph limits in Bochner L²

On a finite measure space the resolvent acts on `L²`, including its possibly nonzero value
at zero. A single resolvent test proves almost-everywhere graph membership simultaneously
for all comparison points. This avoids intersecting uncountably many exceptional sets.

The resulting strong/weak closure theorem applies on nonseparable Hilbert spaces and along
arbitrary nontrivial filters. The subdifferential graph itself need not be convex.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace PDE.Analysis.Convex

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace α] {μ : Measure α} {I : H → EReal}

omit [CompleteSpace H] in
/-- Integrating pointwise subgradient monotonicity gives monotonicity in Bochner `L²`. -/
theorem subdifferential_monotone_L2 (hproper : IsProper I)
    {x y z v : Lp H 2 μ}
    (hxy : ∀ᵐ t ∂μ, y t ∈ subdifferential I (x t))
    (hzv : ∀ᵐ t ∂μ, v t ∈ subdifferential I (z t)) :
    0 ≤ inner ℝ (y - v) (x - z) := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hxy, hzv, Lp.coeFn_sub y v, Lp.coeFn_sub x z] with t ht hs hy hx
  simpa only [hy, hx, Pi.sub_apply, Pi.zero_apply] using subdifferential_monotone hproper ht hs

/-- The resolvent test characterizes graph membership in `L²` without a separability
hypothesis on the Hilbert space. Finite measure is needed only for the resolvent's offset. -/
theorem ae_mem_subdifferential_of_monotone_L2 [IsFiniteMeasure μ]
    (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
    (hlsc : LowerSemicontinuous I) {x y : Lp H 2 μ}
    (hmono : ∀ z v : Lp H 2 μ, (∀ᵐ t ∂μ, v t ∈ subdifferential I (z t)) →
      0 ≤ inner ℝ (y - v) (x - z)) :
    ∀ᵐ t ∂μ, y t ∈ subdifferential I (x t) := by
  let J := resolvent I hproper hconvex hlsc 1 zero_lt_one
  have hJ : LipschitzWith 1 J := lipschitzWith_resolvent hproper hconvex hlsc zero_lt_one
  have hmem : MemLp (fun t ↦ J ((x + y) t)) 2 μ :=
    hJ.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp (x + y))
  let z := hmem.toLp (fun t ↦ J ((x + y) t))
  let v := x + y - z
  have hv : ∀ᵐ t ∂μ, v t ∈ subdifferential I (z t) := by
    filter_upwards [Lp.coeFn_sub (x + y) z, hmem.coeFn_toLp] with t hvt hzt
    change (x + y - z) t ∈ subdifferential I (z t)
    rw [hvt, Pi.sub_apply, hzt]
    simpa only [inv_one, one_smul] using
      resolvent_residual_mem_subdifferential hproper hconvex hlsc zero_lt_one ((x + y) t)
  have h := hmono z v hv
  have hdiff : y - v = -(x - z) := by dsimp only [v]; abel
  rw [hdiff, inner_neg_left, real_inner_self_eq_norm_sq] at h
  have hxz : x = z := sub_eq_zero.1 (norm_eq_zero.1 (by
    nlinarith [norm_nonneg (x - z)]))
  have hvy : v = y := by dsimp only [v]; rw [← hxz]; abel
  rwa [hvy, ← hxz] at hv

/-- Strong `L²` convergence of states and bounded weak `L²` convergence of subgradients
preserve the full almost-everywhere supporting inequality. -/
theorem ae_mem_subdifferential_of_tendsto_strong_weak_L2 [IsFiniteMeasure μ]
    (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
    (hlsc : LowerSemicontinuous I)
    {ι : Type*} {l : Filter ι} [l.NeBot] {x y : ι → Lp H 2 μ} {x₀ y₀ : Lp H 2 μ}
    (hx : Tendsto x l (𝓝 x₀))
    (hy : Tendsto (fun i ↦ toWeakSpace ℝ (Lp H 2 μ) (y i)) l
      (𝓝 (toWeakSpace ℝ (Lp H 2 μ) y₀)))
    (R : ℝ) (hR : ∀ i, ‖y i‖ ≤ R)
    (hgraph : ∀ᶠ i in l, ∀ᵐ t ∂μ, y i t ∈ subdifferential I (x i t)) :
    ∀ᵐ t ∂μ, y₀ t ∈ subdifferential I (x₀ t) := by
  apply ae_mem_subdifferential_of_monotone_L2 hproper hconvex hlsc
  intro z v hv
  apply ge_of_tendsto
    (WeakCompactness.tendsto_inner_sub_of_tendsto_strong_weak hx hy R hR z v)
  filter_upwards [hgraph] with i hi
  exact subdifferential_monotone_L2 hproper hi hv

end PDE.Analysis.Convex
