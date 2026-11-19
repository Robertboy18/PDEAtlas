/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite-dimensional spaces of functions and point evaluations

A finite-dimensional space `V` of functions `X → 𝕜` is determined on a set `U ⊆ X` by finitely
many point values: the evaluations at the points of `U` span the dual of the restrictions of `V`
to `U`, so the coordinates of a basis of those restrictions are finite combinations of
evaluations. This gives a reproducing formula `g = ∑ᵢ (∑ᵤ cᵢ(u) g(u)) vᵢ` on `U` with `vᵢ ∈ V`,
which turns pointwise bounds at finitely many points into bounds in any seminorm that is finite
on `V`.

## Main results

* `Submodule.exists_eq_sum_eval`: the reproducing formula `g = ∑ᵢ (∑ᵤ cᵢ(u) g(u)) vᵢ` on `U`,
  with finitely many points `u ∈ U`.
-/

@[expose] public noncomputable section

open Module

namespace Submodule

/-- **A finite-dimensional space of functions is reproduced from finitely many point values**: for
a finite-dimensional subspace `V` of the functions `X → 𝕜` and a set `U ⊆ X` there are
`v₁, …, vₙ ∈ V` and finitely supported weights `cᵢ` on `U` such that every `g ∈ V` satisfies
`g y = ∑ᵢ (∑_{u ∈ U} cᵢ(u) g(u)) vᵢ(y)` at every `y ∈ U`. -/
theorem exists_eq_sum_eval {𝕜 X : Type*} [Field 𝕜] (V : Submodule 𝕜 (X → 𝕜))
    [FiniteDimensional 𝕜 V] (U : Set X) :
    ∃ (n : ℕ) (v : Fin n → X → 𝕜) (c : Fin n → U →₀ 𝕜), (∀ i, v i ∈ V) ∧
      ∀ g ∈ V, ∀ y ∈ U, g y = ∑ i, ((c i).sum fun u a ↦ a * g u) * v i y := by
  set ρ : (X → 𝕜) →ₗ[𝕜] (U → 𝕜) := LinearMap.funLeft 𝕜 𝕜 ((↑) : U → X) with hρ
  set W := V.map ρ with hW
  set b := Module.finBasis 𝕜 W with hb
  have hv : ∀ i, ∃ v ∈ V, ρ v = (b i : U → 𝕜) := fun i ↦ (Submodule.mem_map).1 (b i).2
  choose v hvV hvρ using hv
  set ev : U → Module.Dual 𝕜 W := fun u ↦ (LinearMap.proj u).comp W.subtype with hev
  have htop : span 𝕜 (Set.range ev) = ⊤ := by
    have hbot : (span 𝕜 (Set.range ev)).dualCoannihilator = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun w hw ↦ ?_
      rw [Submodule.mem_dualCoannihilator] at hw
      ext u
      exact hw (ev u) (subset_span ⟨u, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := span 𝕜 (Set.range ev)), hbot,
      Submodule.dualAnnihilator_bot]
  have hc : ∀ i, ∃ c : U →₀ 𝕜, (c.sum fun u a ↦ a • ev u) = b.coord i := fun i ↦
    (Finsupp.mem_span_range_iff_exists_finsupp).1 (htop ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨finrank 𝕜 W, v, c, hvV, fun g hg y hy ↦ ?_⟩
  set w : W := ⟨ρ g, Submodule.mem_map_of_mem hg⟩ with hw
  have hcoord : ∀ i, b.coord i w = (c i).sum fun u a ↦ a * g u := by
    intro i
    rw [← hc i, Finsupp.sum, LinearMap.sum_apply, Finsupp.sum]
    rfl
  have hsum := congrArg (fun f : W ↦ (f : U → 𝕜) ⟨y, hy⟩) (b.sum_repr w)
  simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hsum
  calc g y = (w : U → 𝕜) ⟨y, hy⟩ := rfl
    _ = ∑ i, b.repr w i * (b i : U → 𝕜) ⟨y, hy⟩ := hsum.symm
    _ = ∑ i, ((c i).sum fun u a ↦ a * g u) * v i y := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Basis.coord_apply, hcoord i, ← hvρ i]
        rfl

end Submodule
