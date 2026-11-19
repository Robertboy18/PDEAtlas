/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Approximation.Resolvent
public import PDE.Analysis.Evolution.GradientFlow.Approximation.Velocity
public import PDE.Analysis.Convex.Subdifferential.Graph.Lp
public import PDE.Analysis.Evolution.Time.WeakDerivative.Limit.Primitive
public import PDE.Analysis.Evolution.Compactness.Lp.PointwiseBounds
public import PDE.Analysis.MeasureTheory.Lp.Convergence.Uniform

/-!
# Identifying the limiting velocity on a finite interval

Bounded Bochner L² velocities have a weak ultrafilter limit in every complete Hilbert
space. The primitive identity survives this limit at every time. Resolvent states
converge strongly in L², so the L² Minty argument gives the full subdifferential graph
almost everywhere. The original initial subgradient bound passes to the weak velocity.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Convex
open scoped Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- If the Yosida flows converge to `u` uniformly on `[0, T]` and `u` is `‖v‖`-Lipschitz
on `[0, ∞)`, then there is `g ∈ L²(0, T; H)` with `u(t) = x₀ + ∫₀ᵗ g` on `[0, T]`,
`‖g‖ ≤ ‖v‖` and `-g(t) ∈ ∂I(u(t))` almost everywhere. -/
theorem exists_velocity_of_yosidaFlow_limit (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) {u : ℝ → H}
    (hLip : LipschitzOnWith ‖v‖₊ u (Ici 0)) {T : ℝ}
    (hu : TendstoUniformlyOn
      (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
        (by positivity) x₀) u atTop (Icc 0 T)) :
    ∃ g : Lp H 2 (volume.restrict (Ioc 0 T)),
      (∀ t ∈ Icc 0 T, u t = x₀ + ∫ r in 0..t, g r) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ‖g t‖ ≤ ‖v‖) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), -g t ∈ subdifferential I (u t)) := by
  let parameter := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < parameter n := by dsimp [parameter]; positivity
  let f := fun n ↦ yosidaFlow I hproper hconvex hlsc (parameter n) (hpos n) x₀
  let velocity := fun n t ↦ -yosidaApproximation I hproper hconvex hlsc
    (parameter n) (hpos n) (f n t)
  let state := fun n t ↦ resolvent I hproper hconvex hlsc (parameter n) (hpos n) (f n t)
  have hvel (n : ℕ) : MemLp (velocity n) 2 (volume.restrict (Ioc 0 T)) :=
    memLp_yosidaFlow_velocity hproper hconvex hlsc (hpos n) x₀ T
  have hstate (n : ℕ) : MemLp (state n) 2 (volume.restrict (Ioc 0 T)) :=
    memLp_resolvent_yosidaFlow hproper hconvex hlsc (hpos n) x₀ T
  have humem : MemLp u 2 (volume.restrict (Ioc 0 T)) :=
    (hLip.continuousOn.mono Icc_subset_Ici_self).memLp_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  let G := fun n ↦ (hvel n).toLp (velocity n)
  let Z := fun n ↦ (hstate n).toLp (state n)
  let uLp := humem.toLp u
  have hbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ‖G n t‖ ≤ ‖v‖ := by
    filter_upwards [(hvel n).coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with t ht htime
    change ‖(hvel n).toLp (velocity n) t‖ ≤ _
    rw [ht]
    simpa only [velocity, norm_neg] using
      norm_yosidaFlow_velocity_le hproper hconvex hlsc (hpos n) hv htime.1.le
  let R := (measureUnivNNReal (volume.restrict (Ioc 0 T)) : ℝ) ^ (2 : ℝ)⁻¹ * ‖v‖
  have hR (n : ℕ) : ‖G n‖ ≤ R := by
    simpa only [ENNReal.toReal_ofNat] using Lp.norm_le_of_ae_bound (norm_nonneg v) (hbound n)
  obtain ⟨g, U, hU, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter atTop G
      (isBounded_iff_forall_norm_le.2 ⟨R, forall_mem_range.2 hR⟩)
  have hstrong : Tendsto Z atTop (𝓝 uLp) :=
    tendsto_Lp_of_tendstoUniformlyOn
      ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht ↦ Ioc_subset_Icc_self ht)
      (fun n ↦ (hstate n).coeFn_toLp) humem.coeFn_toLp
      (tendstoUniformlyOn_resolvent_yosidaFlow hproper hconvex hlsc hv hu)
  have hweakneg : Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp H 2 (volume.restrict (Ioc 0 T))) (-G n)) U
      (𝓝 (toWeakSpace ℝ (Lp H 2 (volume.restrict (Ioc 0 T))) (-g))) := by
    simpa only [map_neg] using hweak.neg
  have hgraph : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (-G n) t ∈ subdifferential I (Z n t) := by
    intro n
    filter_upwards [Lp.coeFn_neg (G n), (hvel n).coeFn_toLp,
      (hstate n).coeFn_toLp] with t hneg hgt hzt
    change (-G n) t ∈ subdifferential I ((hstate n).toLp (state n) t)
    rw [hneg, Pi.neg_apply, hgt, hzt]
    simpa only [velocity, neg_neg, state] using
      yosidaApproximation_mem_subdifferential hproper hconvex hlsc (hpos n) (f n t)
  have hlimitgraph := ae_mem_subdifferential_of_tendsto_strong_weak_L2
    hproper hconvex hlsc (hstrong.mono_left hU) hweakneg R
    (fun n ↦ by simpa only [norm_neg] using hR n) (Eventually.of_forall hgraph)
  refine ⟨g, ?_, ae_norm_le_of_tendsto_weak_Lp (fun _ ↦ ‖v‖) hweak
    (Eventually.of_forall hbound), ?_⟩
  · intro t ht
    apply eq_initial_add_integral_of_tendsto_strong_weak_L2
      (fun s hs ↦ (hu.tendsto_at hs).mono_left hU) hweak _ ht
    exact Eventually.of_forall fun n s hs ↦
      yosidaFlow_eq_initial_add_integral hproper hconvex hlsc (hpos n) x₀ hs
  · filter_upwards [hlimitgraph, Lp.coeFn_neg g, humem.coeFn_toLp] with t ht hneg hut
    change uLp t = u t at hut
    simpa only [hneg, Pi.neg_apply, hut] using ht

end PDE.Analysis.Evolution
