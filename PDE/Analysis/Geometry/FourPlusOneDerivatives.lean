/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Geometry.FourPlusOne
public import PDE.FDeriv.Calculus

/-!
# Finite local derivatives on the profile axis

Restricting a five-dimensional function to the profile plane sends radial
derivatives to coordinate zero and axial derivatives to coordinate four.
The identity needs only local regularity through the order being taken.
It therefore applies to a separated Newtonian tail, which is smooth near
the evaluation point even when its source has only finite regularity.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis

private theorem contDiffAt_iteratedPartialDeriv_add
    {n : ℕ} (indices : List (Fin n)) (m : ℕ) {F : ℝ^n → ℝ} {X : ℝ^n}
    (hF : ContDiffAt ℝ (m + indices.length) F X) :
    ContDiffAt ℝ m (iteratedPartialDeriv indices F) X := by
  induction indices generalizing m with
  | nil => simpa only [List.length_nil, Nat.cast_zero, add_zero, iteratedPartialDeriv] using hF
  | cons i rest ih =>
      apply contDiffAt_partialDeriv m
      apply ih (m + 1)
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
        add_left_comm, add_comm] using hF

/-- A derivative word commutes with restriction to the profile axis. Only
finite local regularity at the embedded evaluation point is required. -/
theorem iteratedPartialDeriv_comp_profileAxisEmbeddingFive_of_contDiffAt
    (indices : List (Fin 2)) (F : ℝ^5 → ℝ) (x : ℝ^2)
    (hF : ContDiffAt ℝ indices.length F (profileAxisEmbeddingFive x)) :
    iteratedPartialDeriv indices (F ∘ profileAxisEmbeddingFive) x =
      iteratedPartialDeriv (indices.map (fun i ↦ if i = 0 then (0 : Fin 5) else 4))
        F (profileAxisEmbeddingFive x) := by
  induction indices generalizing x with
  | nil => rfl
  | cons i rest ih =>
      have hrest : ContDiffAt ℝ rest.length F (profileAxisEmbeddingFive x) :=
        hF.of_le (by exact_mod_cast Nat.le_succ rest.length)
      have hnear : ∀ᶠ y in 𝓝 x,
          ContDiffAt ℝ rest.length F (profileAxisEmbeddingFive y) :=
        profileAxisEmbeddingFive.continuous.continuousAt.eventually
          (hrest.eventually (by simp))
      have heq :
          iteratedPartialDeriv rest (F ∘ profileAxisEmbeddingFive) =ᶠ[𝓝 x]
            (iteratedPartialDeriv
              (rest.map (fun j ↦ if j = 0 then (0 : Fin 5) else 4)) F) ∘
                profileAxisEmbeddingFive := by
        filter_upwards [hnear] with y hy
        exact ih y hy
      have hrow : ContDiffAt ℝ 1
          (iteratedPartialDeriv
            (rest.map (fun j ↦ if j = 0 then (0 : Fin 5) else 4)) F)
          (profileAxisEmbeddingFive x) := by
        apply contDiffAt_iteratedPartialDeriv_add _ 1
        simpa only [List.length_map, List.length_cons, Nat.cast_add, Nat.cast_one,
          add_comm] using hF
      simp only [List.map_cons, iteratedPartialDeriv]
      rw [partialDeriv_congr_nhds i heq]
      fin_cases i
      · exact partialDeriv_comp_profileAxisEmbeddingFive_zero _ x hrow.differentiableAt_one
      · exact partialDeriv_comp_profileAxisEmbeddingFive_one _ x hrow.differentiableAt_one

end PDE.Analysis
