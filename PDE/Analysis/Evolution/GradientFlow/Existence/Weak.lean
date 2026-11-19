/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Limit.Velocity
public import PDE.Analysis.Evolution.GradientFlow.Solution.Basic
public import PDE.Analysis.Evolution.Time.WeakDerivative.Regularity.Integral
public import PDE.Analysis.Evolution.Time.WeakDerivative.Domain.HalfLine
public import PDE.Analysis.MeasureTheory.Measure.Restriction.HalfLine

/-!
# Global weak gradient flow of a signed energy

For proper convex lower semicontinuous `I` and `v ∈ ∂I(x₀)`, let `u` be the uniform
limit of the Yosida flows. On each `[0, T]` the weak velocity of `u` agrees almost
everywhere with `deriv u`. Exhausting `(0, ∞)` by countably many such intervals gives
`‖u'‖ ≤ ‖v‖` and `-u'(t) ∈ ∂I(u(t))` for almost every `t > 0`, so `u` is a weak
subgradient flow with velocity `deriv u`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Convex
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- For proper convex lower semicontinuous `I` and `v ∈ ∂I(x₀)`, there is a weak
subgradient flow `u` from `x₀` with velocity `deriv u`. It is `‖v‖`-Lipschitz on
`[0, ∞)`, satisfies `u' = deriv u` with `‖u'‖ ≤ ‖v‖` almost everywhere, stays in the
subdifferential domain for `t ≥ 0`, is absolutely continuous on every `[0, T]`, and is
the uniform limit of the Yosida flows on every `[0, T]`. -/
theorem exists_isSubgradientFlow_of_mem_subdifferential
    (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
    (hlsc : LowerSemicontinuous I) {x₀ v : H} (hv : v ∈ subdifferential I x₀) :
    ∃ u : ℝ → H, u 0 = x₀ ∧
      IsSubgradientFlow I u (deriv u) ∧
      LipschitzOnWith ‖v‖₊ u (Ici 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0), ‖deriv u t‖ ≤ ‖v‖) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt u (deriv u t) t) ∧
      (∀ t, 0 ≤ t → u t ∈ subdifferentialDomain I) ∧
      (∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval u 0 T) ∧
      (∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn
        (fun n : ℕ ↦ yosidaFlow I hproper hconvex hlsc (1 / ((n : ℝ) + 1))
          (by positivity) x₀) u atTop (Icc 0 T)) := by
  obtain ⟨u, hu0, hLip, hu⟩ := exists_yosidaFlow_limit hproper hconvex hlsc hv
  have hlocal (T : ℝ) (hT : 0 < T) :
      AEStronglyMeasurable (deriv u) (volume.restrict (Ioo 0 T)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 T),
        ‖deriv u t‖ ≤ ‖v‖ ∧ HasDerivAt u (deriv u t) t ∧
          -deriv u t ∈ subdifferential I (u t)) ∧
      HasWeakTimeDerivativeOn (Ioo 0 T) u (deriv u) := by
    obtain ⟨g, hFTC, hbound, hgraph⟩ :=
      exists_velocity_of_yosidaFlow_limit hproper hconvex hlsc hv hLip (hu T hT.le)
    obtain ⟨_, hd, hweak⟩ := regularity_of_eq_initial_add_integral hT.le
      ((Lp.memLp g).integrable (by norm_num)) hFTC
    have heq : (fun t ↦ g t) =ᵐ[volume.restrict (Ioo 0 T)] deriv u :=
      hd.mono fun t ht ↦ ht.deriv.symm
    have hmeasure := volume.restrict_mono_set (Ioo_subset_Ioc_self : Ioo 0 T ⊆ Ioc 0 T)
    refine ⟨((Lp.aestronglyMeasurable g).mono_measure hmeasure).congr heq, ?_,
      hweak.congr_ae_restrict measurableSet_Ioo EventuallyEq.rfl heq⟩
    filter_upwards [hd, heq, hbound.filter_mono (ae_mono hmeasure),
      hgraph.filter_mono (ae_mono hmeasure)] with t hdt heqt hbt hgt
    exact ⟨heqt ▸ hbt, heqt ▸ hdt, heqt ▸ hgt⟩
  have hmeas := aestronglyMeasurable_restrict_Ioi_of_forall_Ioo
    (fun T hT ↦ (hlocal T hT).1)
  have hall := ae_restrict_Ioi_of_forall_Ioo (fun T hT ↦ (hlocal T hT).2.1)
  have hbound := hall.mono fun _ ht ↦ ht.1
  have hflow : IsSubgradientFlow I u (deriv u) :=
    ⟨hLip.continuousOn, memLp_top_of_bound hmeas ‖v‖ hbound,
      HasWeakTimeDerivativeOn.of_forall_Ioo (fun T hT ↦ (hlocal T hT).2.2),
      hall.mono fun _ ht ↦ ht.2.2⟩
  refine ⟨u, hu0, hflow, hLip, hbound, hall.mono fun _ ht ↦ ht.2.1,
    fun t ht ↦ mem_subdifferentialDomain_of_yosidaFlow_limit hproper hconvex hlsc hv hu ht,
    ?_, hu⟩
  intro T hT
  exact (hLip.mono (by
    rw [uIcc_of_le hT]
    exact Icc_subset_Ici_self)).absolutelyContinuousOnInterval

end PDE.Analysis.Evolution
