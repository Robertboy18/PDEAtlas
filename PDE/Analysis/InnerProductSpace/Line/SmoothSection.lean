/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Line.UnitCover
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Contractible

/-!
# Smooth unit sections of real line families

The sign relating two continuous unit generators is locally constant. Thus the
continuous section obtained by covering-space lifting has the same regularity as
the local generators. In particular one section is smooth to all orders.
-/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace ContDiff

namespace Submodule

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Continuous unit vectors in the same real line differ locally by a fixed sign. -/
theorem eventually_eq_inner_smul {u v : X → E} {x : X}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (h : ∀ᶠ y in 𝓝 x, ‖v y‖ = 1 ∧ u y ∈ ℝ ∙ v y ∧ ‖u y‖ = 1) :
    u =ᶠ[𝓝 x] fun y ↦ ⟪v x, u x⟫_ℝ • v y := by
  let S : Set ℝ := {a | |a| = 1}
  have hS : IsDiscrete S := ⟨inferInstanceAs (DiscreteTopology UnitTotal.Sign)⟩
  have hm : ∀ᶠ y in 𝓝 x, ⟪v y, u y⟫_ℝ ∈ S :=
    h.mono fun y hy ↦ abs_inner_eq_one_of_mem_span_singleton hy.1 hy.2.1 hy.2.2
  have ht : Tendsto (fun y ↦ ⟪v y, u y⟫_ℝ) (𝓝 x) (𝓝[S] ⟪v x, u x⟫_ℝ) :=
    tendsto_nhdsWithin_iff.mpr ⟨hv.inner hu, hm⟩
  rw [hS.nhdsWithin _ hm.self_of_nhds] at ht
  have he := tendsto_pure.mp ht
  filter_upwards [he, h] with y hy hyl
  rw [← hy]
  exact (inner_smul_eq_of_mem_span_singleton hyl.1 hyl.2.1).symm

end Submodule

namespace Submodule.UnitTotal

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {q : WithTop ℕ∞} (L : X → Submodule ℝ E)

/-- A continuous unit section inherits the regularity of local unit generators. -/
theorem contDiff_unit_section (u : C(X, E))
    (hu : ∀ x, u x ∈ L x ∧ ‖u x‖ = 1)
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ v : X → E,
      ContDiffOn ℝ q v U ∧ (∀ y ∈ U, ‖v y‖ = 1) ∧
        ∀ y ∈ U, L y = ℝ ∙ v y) :
    ContDiff ℝ q u := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨U, hU, hx, v, hv, hvn, hL⟩ := h x
  have hvx := hv.contDiffAt (hU.mem_nhds hx)
  have he := Submodule.eventually_eq_inner_smul u.continuous.continuousAt hvx.continuousAt
    (by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ⟨hvn y hy, (hL y hy) ▸ (hu y).1, (hu y).2⟩)
  exact (contDiffAt_const.smul hvx).congr_of_eventuallyEq he

/-- A locally smooth real line family on a real normed space has a global smooth
unit section, uniquely fixed by its value at one point. -/
theorem existsUnique_contDiff_unit_section
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ v : X → E,
      ContDiffOn ℝ q v U ∧ (∀ y ∈ U, ‖v y‖ = 1) ∧
        ∀ y ∈ U, L y = ℝ ∙ v y)
    (x₀ : X) (v₀ : E) (hv₀ : v₀ ∈ L x₀) (hn₀ : ‖v₀‖ = 1) :
    ∃! v : C(X, E), ContDiff ℝ q v ∧ v x₀ = v₀ ∧
      ∀ x, v x ∈ L x ∧ ‖v x‖ = 1 := by
  have hc : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ v : X → E,
      ContinuousOn v U ∧ (∀ y ∈ U, ‖v y‖ = 1) ∧
        ∀ y ∈ U, L y = ℝ ∙ v y := by
    intro x
    obtain ⟨U, hU, hx, v, hv, hvn, hL⟩ := h x
    exact ⟨U, hU, hx, v, hv.continuousOn, hvn, hL⟩
  obtain ⟨u, hu, huniq⟩ := existsUnique_continuous_unit_section L hc x₀ v₀ hv₀ hn₀
  exact ⟨u, ⟨contDiff_unit_section L u hu.2 h, hu⟩, fun v hv ↦ huniq v hv.2⟩

end Submodule.UnitTotal
