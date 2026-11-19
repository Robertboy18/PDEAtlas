/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Implicit.Regularity
public import PDE.Analysis.Calculus.ImplicitRay

/-!
# Higher regularity of implicit rays

For a continuous curve satisfying `S(t) - x₀ = t • r(S(t))`, the state derivative
of the residual at zero strength is the identity. The existing curve therefore
inherits the regularity of the vector field on one open parameter neighborhood.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Set
open scoped ContDiff Topology

/-- A continuous implicit ray inherits the field's regularity near zero
strength, including infinite differentiability on a single neighborhood. -/
theorem exists_contDiffOn_implicit_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ∞ω} {r : E → E} {S : ℝ → E} {x₀ : E}
    {U : Set E} {I : Set ℝ}
    (hn : n ≠ 0) (hU : IsOpen U) (hr : ContDiffOn ℝ n r U)
    (hI : IsOpen I) (hI₀ : 0 ∈ I) (hS : ContinuousOn S I)
    (hS₀ : S 0 = x₀) (hSU : ∀ t ∈ I, S t ∈ U)
    (heq : ∀ t ∈ I, S t - x₀ = t • r (S t)) :
    ∃ J : Set ℝ, IsOpen J ∧ 0 ∈ J ∧ J ⊆ I ∧ ContDiffOn ℝ n S J := by
  let G : ℝ × E → E := fun z ↦ z.2 - x₀ - z.1 • r z.2
  have hG : ContDiffOn ℝ n G (univ ×ˢ U) :=
    (contDiffOn_snd.sub contDiffOn_const).sub
      (contDiffOn_fst.smul (hr.comp contDiffOn_snd fun _ hz ↦ hz.2))
  have hU₀ : x₀ ∈ U := hS₀ ▸ hSU 0 hI₀
  have hG₀ : ContDiffAt ℝ n G (0, x₀) :=
    hG.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hU₀⟩)
  have hpartial :
      (fderiv ℝ G (0, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
        ContinuousLinearMap.id ℝ E := by
    have hd : HasFDerivAt (fun x ↦ G (0, x))
        (ContinuousLinearMap.id ℝ E) x₀ := by
      simpa only [G, id, zero_smul, sub_zero] using (hasFDerivAt_id x₀).sub_const x₀
    exact ((hG₀.differentiableAt hn).hasFDerivAt.comp x₀
      (hasFDerivAt_prodMk_right (0 : ℝ) x₀)).unique hd
  have hinv : ((fderiv ℝ G (0, S 0)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible := by
    rw [hS₀, hpartial]
    exact ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.id ℝ E) (by ext x; rfl) (by ext x; rfl)
  apply hG.exists_contDiffOn_of_implicit_eq hn (isOpen_univ.prod hU)
    hI hI₀ hS (fun t ht ↦ ⟨mem_univ _, hSU t ht⟩) (c := 0) ?_ hinv
  intro t ht
  exact sub_eq_zero.mpr (heq t ht)

end PDE.Analysis
