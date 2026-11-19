/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Uniqueness

/-!
# Maximal lifetimes of semilinear mild solutions

Finite-interval solutions from the same initial state agree on overlaps.
Local existence at the terminal state extends each such solution to a longer
interval. Their lifetimes therefore have a positive supremum in `ℝ≥0∞`.

`lt_mildLifespan_iff` identifies the attainable compact time intervals with
those strictly below the supremum. Local Lipschitz continuity suffices in any
real Banach space; no uniform bound on a whole norm ball is needed here.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Two finite-interval mild solutions with the same initial state agree wherever
their time intervals overlap. -/
theorem IsMildSolutionOn.eqOn_overlap {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} (hF : LocallyLipschitz F) {x₀ : E} {τ σ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)} {v : C(Icc (0 : ℝ) (σ : ℝ), E)}
    (hu : T.IsMildSolutionOn F x₀ τ u) (hv : T.IsMildSolutionOn F x₀ σ v) :
    EqOn (IccExtend τ.coe_nonneg u) (IccExtend σ.coe_nonneg v)
      (Icc (0 : ℝ) (min (τ : ℝ) (σ : ℝ))) := by
  intro t ht
  let η : NNReal := ⟨t, ht.1⟩
  have hητ : η ≤ τ := ht.2.trans (min_le_left _ _)
  have hησ : η ≤ σ := ht.2.trans (min_le_right _ _)
  have heq := (hu.restrict hητ).eq_of_locallyLipschitz hF (hv.restrict hησ)
  have hvalue := congrArg
    (fun w : C(Icc (0 : ℝ) (η : ℝ), E) ↦ w ⟨η, η.coe_nonneg, le_rfl⟩) heq
  rw [IccExtend_of_mem τ.coe_nonneg u ⟨ht.1, hητ⟩,
    IccExtend_of_mem σ.coe_nonneg v ⟨ht.1, hησ⟩]
  exact hvalue

/-- Every attained finite lifetime can be increased by solving from the terminal
state and gluing. The extension length may depend on that state. -/
theorem IsMildSolutionOn.exists_extension_of_locallyLipschitz
    {T : StronglyContinuousSemigroup E} {F : C(E, E)}
    (hF : LocallyLipschitz F) {x₀ : E} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)} (hu : T.IsMildSolutionOn F x₀ τ u) :
    ∃ σ : NNReal, ∃ hτσ : τ < σ,
      ∃ w : C(Icc (0 : ℝ) (σ : ℝ), E),
        T.IsMildSolutionOn F x₀ σ w ∧ restrictMildCurve hτσ.le w = u := by
  obtain ⟨δ, hδ, v, hv, _⟩ :=
    T.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted
      hF (u ⟨τ, τ.coe_nonneg, le_rfl⟩)
  refine ⟨τ + δ, lt_add_of_pos_right τ hδ,
    glueMildCurves u v hv.initial_value.symm, hu.glue hv, ?_⟩
  ext t
  change glueMildCurves u v hv.initial_value.symm
    ⟨t, t.property.1, t.property.2.trans (le_add_of_nonneg_right δ.coe_nonneg)⟩ = u t
  rw [glueMildCurves_apply_left u v hv.initial_value.symm _ t.property.2]
  exact IccExtend_val τ.coe_nonneg u t

omit [CompleteSpace E] in
/-- The supremum of finite lifetimes admitting a mild solution from `x₀`.
The value `∞` is allowed. -/
def mildLifespan (T : StronglyContinuousSemigroup E) (F : C(E, E)) (x₀ : E) : ℝ≥0∞ :=
  ⨆ (τ : NNReal) (_ : ∃ u : C(Icc (0 : ℝ) (τ : ℝ), E),
    T.IsMildSolutionOn F x₀ τ u), (τ : ℝ≥0∞)

omit [CompleteSpace E] in
/-- A time lies below the supremum exactly when a solution exists on a strictly
longer finite interval. This order-theoretic fact needs no Lipschitz assumption. -/
theorem lt_mildLifespan_iff_exists_longer (T : StronglyContinuousSemigroup E)
    (F : C(E, E)) (x₀ : E) {τ : NNReal} :
    (τ : ℝ≥0∞) < T.mildLifespan F x₀ ↔
      ∃ σ : NNReal, τ < σ ∧
        ∃ u : C(Icc (0 : ℝ) (σ : ℝ), E), T.IsMildSolutionOn F x₀ σ u := by
  change (τ : ℝ≥0∞) <
    (⨆ (σ : NNReal) (_ : ∃ u : C(Icc (0 : ℝ) (σ : ℝ), E),
      T.IsMildSolutionOn F x₀ σ u), (σ : ℝ≥0∞)) ↔ _
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := lt_iSup_iff.mp h
    obtain ⟨hsol, hlt⟩ := lt_iSup_iff.mp hσ
    exact ⟨σ, ENNReal.coe_lt_coe.mp hlt, hsol⟩
  · rintro ⟨σ, hτσ, hsol⟩
    exact (ENNReal.coe_lt_coe.mpr hτσ).trans_le
      (le_iSup_of_le σ (le_iSup_of_le hsol le_rfl))

/-- Local existence at terminal states makes the set of attained finite lifetimes
exactly the interval strictly below its supremum. -/
theorem lt_mildLifespan_iff (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E) {τ : NNReal} :
    (τ : ℝ≥0∞) < T.mildLifespan F x₀ ↔
      ∃ u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  constructor
  · intro h
    obtain ⟨σ, hτσ, u, hu⟩ := (T.lt_mildLifespan_iff_exists_longer F x₀).mp h
    exact ⟨restrictMildCurve hτσ.le u, hu.restrict hτσ.le⟩
  · rintro ⟨u, hu⟩
    obtain ⟨σ, hτσ, w, hw, _⟩ := hu.exists_extension_of_locallyLipschitz hF
    exact (T.lt_mildLifespan_iff_exists_longer F x₀).mpr ⟨σ, hτσ, w, hw⟩

/-- Every initial state has a positive maximal forward lifetime. -/
theorem mildLifespan_pos (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} (hF : LocallyLipschitz F) (x₀ : E) :
    0 < T.mildLifespan F x₀ := by
  obtain ⟨τ, hτ, u, hu, _⟩ :=
    T.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted hF x₀
  exact (ENNReal.coe_pos.mpr hτ).trans ((T.lt_mildLifespan_iff hF x₀).mpr ⟨u, hu⟩)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
