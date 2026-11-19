/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Solution.Regularity
public import PDE.Analysis.Evolution.Monotone.Contraction

/-!
# Contraction and uniqueness of weak subdifferential flows

For two weak subgradient flows `u, v`, monotonicity of `∂I` makes `‖u - v‖²`
nonincreasing, so `‖u(t) - v(t)‖ ≤ ‖u(0) - v(0)‖` for `t ≥ 0`. Hence the initial
value determines a weak flow on `[0, ∞)`, and its velocity almost everywhere.
The argument uses that weak flows are absolutely continuous on bounded intervals,
since their velocity is a weak derivative.
-/

@[expose] public section

open MeasureTheory Set PDE.Analysis.Convex

namespace PDE.Analysis.Evolution.IsSubgradientFlow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal} {u v g h : ℝ → H}

/-- Contraction: two weak flows of a proper energy satisfy
`‖u(t) - v(t)‖ ≤ ‖u(0) - v(0)‖` for `t ≥ 0`. Only monotonicity of `∂I` is used, so
`I` need not be convex or lower semicontinuous. -/
theorem norm_sub_le_initial (hI : IsProper I)
    (hu : IsSubgradientFlow I u g) (hv : IsSubgradientFlow I v h)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖u 0 - v 0‖ := by
  rcases ht.eq_or_lt with rfl | ht
  · exact le_rfl
  obtain ⟨huAC, hdu⟩ := hu.regularity_Icc ht
  obtain ⟨hvAC, hdv⟩ := hv.regularity_Icc ht
  apply norm_sub_le_of_ae_dissipative_derivatives ht.le huAC hvAC hdu hdv
  have hmeasure := volume.restrict_mono_set (Ioo_subset_Ioi_self : Ioo 0 t ⊆ Ioi 0)
  filter_upwards [hu.inclusion.filter_mono (ae_mono hmeasure),
    hv.inclusion.filter_mono (ae_mono hmeasure)] with s hus hvs
  have hm := subdifferential_monotone hI hus hvs
  rw [show -g s - -h s = -(g s - h s) by abel, inner_neg_left] at hm
  exact neg_nonneg.1 hm

/-- The entire continuous weak class has at most one trajectory for each initial datum. -/
theorem eqOn_of_initial_eq (hI : IsProper I)
    (hu : IsSubgradientFlow I u g) (hv : IsSubgradientFlow I v h)
    (h0 : u 0 = v 0) : EqOn u v (Ici 0) := by
  intro t ht
  have hb := hu.norm_sub_le_initial hI hv ht
  rw [h0, sub_self, norm_zero] at hb
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hb)

/-- Velocities also agree almost everywhere when the initial data agree. -/
theorem velocity_ae_eq_of_initial_eq (hI : IsProper I)
    (hu : IsSubgradientFlow I u g) (hv : IsSubgradientFlow I v h)
    (h0 : u 0 = v 0) : g =ᵐ[volume.restrict (Ioi 0)] h := by
  have heq := hu.eqOn_of_initial_eq hI hv h0
  filter_upwards [hu.ae_hasDerivAt, hv.ae_hasDerivAt,
    ae_restrict_mem measurableSet_Ioi] with t hut hvt ht
  have hvt' : HasDerivAt u (h t) t := hvt.congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact heq (le_of_lt hs))
  exact hut.unique hvt'

end PDE.Analysis.Evolution.IsSubgradientFlow
