/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.ScalarBarrier
public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Connection

/-!
# Orientation of connections for strictly convex or concave scalar fields

Between two zeros, strict convexity makes the scalar field negative and
strict concavity makes it positive. The scalar connection construction gives
the corresponding orbit. Conversely, the barrier at an intermediate level
forces this orientation for every complete differentiable orbit with the
stated end limits, even if no range constraint is imposed.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution.Scalar

/-- A complete orbit between distinct zeros of a strictly convex field must
run from the larger zero to the smaller one. -/
theorem lt_of_heteroclinic_of_strictConvexOn
    {S : Set ℝ} {f u : ℝ → ℝ} {a b : ℝ}
    (hf : StrictConvexOn ℝ S f) (ha : a ∈ S) (hb : b ∈ S)
    (ha0 : f a = 0) (hb0 : f b = 0) (hne : a ≠ b)
    (hu : ∀ t, HasDerivAt u (f (u t)) t)
    (hleft : Tendsto u atBot (𝓝 a)) (hright : Tendsto u atTop (𝓝 b)) :
    b < a := by
  by_contra h
  have hab : a < b := lt_of_le_of_ne (le_of_not_gt h) hne
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  have hc : f c < 0 := by
    have hmem : c ∈ openSegment ℝ a b := by
      rw [openSegment_eq_Ioo hab]
      exact ⟨hac, hcb⟩
    simpa only [ha0, hb0, max_self] using hf.lt_on_openSegment ha hb hne hmem
  have hbound (t : ℝ) : u t ≤ c :=
    le_of_tendsto_atBot_of_deriv_neg_at_level hu hleft hac
      (fun s hs ↦ by simpa only [hs] using hc) t
  exact (not_le_of_gt hcb) (le_of_tendsto' hright hbound)

/-- A complete orbit between distinct zeros of a strictly concave field must
run from the smaller zero to the larger one. -/
theorem lt_of_heteroclinic_of_strictConcaveOn
    {S : Set ℝ} {f u : ℝ → ℝ} {a b : ℝ}
    (hf : StrictConcaveOn ℝ S f) (ha : a ∈ S) (hb : b ∈ S)
    (ha0 : f a = 0) (hb0 : f b = 0) (hne : a ≠ b)
    (hu : ∀ t, HasDerivAt u (f (u t)) t)
    (hleft : Tendsto u atBot (𝓝 a)) (hright : Tendsto u atTop (𝓝 b)) :
    a < b := by
  by_contra h
  have hba : b < a := lt_of_le_of_ne (le_of_not_gt h) hne.symm
  obtain ⟨c, hbc, hca⟩ := exists_between hba
  have hc : 0 < f c := by
    have hmem : c ∈ openSegment ℝ b a := by
      rw [openSegment_eq_Ioo hba]
      exact ⟨hbc, hca⟩
    simpa only [ha0, hb0, min_self] using hf.lt_on_openSegment hb ha hne.symm hmem
  have hbound (t : ℝ) : c ≤ u t :=
    le_of_tendsto_atBot_of_deriv_pos_at_level hu hleft hca
      (fun s hs ↦ by simpa only [hs] using hc) t
  exact (not_le_of_gt hbc) (ge_of_tendsto' hright hbound)

/-- Two zeros of a C¹ strictly convex field admit the decreasing C² connection
through any intermediate state, with state and velocity limits. -/
theorem exists_heteroclinic_of_strictConvexOn
    {S : Set ℝ} {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : StrictConvexOn ℝ S f) (hC1 : ContDiffOn ℝ 1 f S)
    (ha : a ∈ S) (hb : b ∈ S) (ha0 : f a = 0) (hb0 : f b = 0)
    (hx₀ : x₀ ∈ Ioo b a) :
    ∃ x : ℝ → ℝ, x 0 = x₀ ∧ ContDiff ℝ 2 x ∧
      (∀ t, HasDerivAt x (f (x t)) t) ∧
      (∀ t, x t ∈ Ioo b a) ∧ StrictAnti x ∧
      Tendsto x atBot (𝓝 a) ∧ Tendsto x atTop (𝓝 b) ∧
      Tendsto (deriv x) atBot (𝓝 0) ∧ Tendsto (deriv x) atTop (𝓝 0) := by
  have hba : b < a := hx₀.1.trans hx₀.2
  apply exists_heteroclinic_of_neg
    (hC1.mono (hf.1.ordConnected.out hb ha)) hb0 ha0 _ hx₀
  intro z hz
  have hmem : z ∈ openSegment ℝ b a := by
    rwa [openSegment_eq_Ioo hba]
  simpa only [ha0, hb0, max_self] using hf.lt_on_openSegment hb ha hba.ne hmem

/-- Two zeros of a C¹ strictly concave field admit the increasing C² connection
through any intermediate state, with state and velocity limits. -/
theorem exists_heteroclinic_of_strictConcaveOn
    {S : Set ℝ} {f : ℝ → ℝ} {a b x₀ : ℝ}
    (hf : StrictConcaveOn ℝ S f) (hC1 : ContDiffOn ℝ 1 f S)
    (ha : a ∈ S) (hb : b ∈ S) (ha0 : f a = 0) (hb0 : f b = 0)
    (hx₀ : x₀ ∈ Ioo a b) :
    ∃ x : ℝ → ℝ, x 0 = x₀ ∧ ContDiff ℝ 2 x ∧
      (∀ t, HasDerivAt x (f (x t)) t) ∧
      (∀ t, x t ∈ Ioo a b) ∧ StrictMono x ∧
      Tendsto x atBot (𝓝 a) ∧ Tendsto x atTop (𝓝 b) ∧
      Tendsto (deriv x) atBot (𝓝 0) ∧ Tendsto (deriv x) atTop (𝓝 0) := by
  have hab : a < b := hx₀.1.trans hx₀.2
  apply exists_heteroclinic_of_pos
    (hC1.mono (hf.1.ordConnected.out ha hb)) ha0 hb0 _ hx₀
  intro z hz
  have hmem : z ∈ openSegment ℝ a b := by
    rwa [openSegment_eq_Ioo hab]
  simpa only [ha0, hb0, min_self] using hf.lt_on_openSegment ha hb hab.ne hmem

end PDE.Analysis.Evolution.Scalar
