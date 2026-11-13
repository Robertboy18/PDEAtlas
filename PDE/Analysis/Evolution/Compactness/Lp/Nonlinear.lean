/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Bochner.Duality
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Evolution.Compactness.Lp.Basic

/-!
# Nonlinear limit passages in Bochner spaces

Two limit passages recur in nonlinear evolution equations. The first is a
pure continuity fact: strong convergence in a Hölder pair of Bochner spaces
passes continuous bilinear products to strong convergence in the target
space. The second pairs weak convergence of a dual trajectory with strong
convergence of the state.

## Main results

* `tendsto_bilinear_product_Lr_of_tendsto_Lp_Lq`: strong convergence in `Lᵖ` and `L^q`
  passes a continuous bilinear map to strong convergence in `L^r`, for a Hölder triple
  `(p, q, r)`.
* `tendsto_bilinear_product_L1_of_tendsto_L2`, `tendsto_quadratic_product_L1_of_tendsto_L2`:
  the case `p = q = 2`, `r = 1`.
* `tendsto_integral_dual_pairing_of_tendsto_weak_strong`: if a uniformly bounded `L²` dual
  trajectory converges weakly through the Riesz map and the state converges strongly in `L²`,
  then the time integrals of the pairings converge.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace PDE.Analysis.Evolution

section Bilinear

variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Strong convergence in a Hölder pair of Bochner spaces passes a
continuous bilinear pointwise operation to strong convergence in the target
Bochner space. -/
theorem tendsto_bilinear_product_Lr_of_tendsto_Lp_Lq
    {p q r : ENNReal} [ENNReal.HolderTriple p q r]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (B : E →L[ℝ] F →L[ℝ] G)
    {ι : Type*} {l : Filter ι}
    {u : ι → Lp E p μ} {uLimit : Lp E p μ}
    {v : ι → Lp F q μ} {vLimit : Lp F q μ}
    (hu : Tendsto u l (nhds uLimit))
    (hv : Tendsto v l (nhds vLimit)) :
    Tendsto (fun i ↦ B.holder r (u i) (v i)) l
      (nhds (B.holder r uLimit vLimit)) := by
  simpa only [ContinuousLinearMap.holderL_apply_apply,
    Function.comp_def, Function.uncurry_apply_pair] using
    (B.holderL μ p q r).continuous₂.continuousAt.tendsto.comp
      (hu.prodMk_nhds hv)

/-- Strong `L²` convergence in both arguments of a continuous bilinear map
implies strong `L¹` convergence of its pointwise products. -/
theorem tendsto_bilinear_product_L1_of_tendsto_L2
    (B : E →L[ℝ] F →L[ℝ] G)
    {ι : Type*} {l : Filter ι}
    {u : ι → Lp E 2 μ} {uLimit : Lp E 2 μ}
    {v : ι → Lp F 2 μ} {vLimit : Lp F 2 μ}
    (hu : Tendsto u l (nhds uLimit))
    (hv : Tendsto v l (nhds vLimit)) :
    Tendsto (fun i ↦ B.holder 1 (u i) (v i)) l
      (nhds (B.holder 1 uLimit vLimit)) :=
  tendsto_bilinear_product_Lr_of_tendsto_Lp_Lq B hu hv

/-- Strong `L²` convergence carries a quadratic expression defined by a
continuous bilinear map to strong `L¹` convergence. -/
theorem tendsto_quadratic_product_L1_of_tendsto_L2
    (B : E →L[ℝ] E →L[ℝ] G)
    {ι : Type*} {l : Filter ι}
    {u : ι → Lp E 2 μ} {uLimit : Lp E 2 μ}
    (hu : Tendsto u l (nhds uLimit)) :
    Tendsto (fun i ↦ B.holder 1 (u i) (u i)) l
      (nhds (B.holder 1 uLimit uLimit)) :=
  tendsto_bilinear_product_L1_of_tendsto_L2 B hu hu

end Bilinear

section Duality

variable {α W : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- A weakly convergent `L²` dual trajectory may be paired with a strongly
convergent `L²` state trajectory inside the time integral. -/
theorem tendsto_integral_dual_pairing_of_tendsto_weak_strong
    {ι : Type*} {l : Filter ι}
    {g : ι → Lp (StrongDual ℝ W) 2 μ}
    {gLimit : Lp (StrongDual ℝ W) 2 μ}
    (hg : Tendsto
      (fun i ↦ toWeakSpace ℝ (Lp W 2 μ) (rieszFromDualLp (g i))) l
      (nhds (toWeakSpace ℝ (Lp W 2 μ) (rieszFromDualLp gLimit))))
    {u : ι → Lp W 2 μ} {uLimit : Lp W 2 μ}
    (hu : Tendsto u l (nhds uLimit))
    (R : ℝ) (hgR : ∀ i, ‖rieszFromDualLp (g i)‖ ≤ R) :
    Tendsto (fun i ↦ ∫ t, g i t (u i t) ∂μ) l
      (nhds (∫ t, gLimit t (uLimit t) ∂μ)) := by
  have hpair := tendsto_inner_of_tendsto_weak_of_tendsto_strong
    hg hu R hgR
  simpa only [integral_dual_pairing_eq_L2_inner, real_inner_comm] using hpair

end Duality

end PDE.Analysis.Evolution
