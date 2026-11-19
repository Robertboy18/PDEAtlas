/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.CompactConvergence
public import PDE.CalculusOfVariations.DirectMethod

/-!
# Nonlinear constraints through a compact embedding

A continuous constraint on the image of a compact linear map is weakly
continuous on bounded sets. Intersecting one bounded energy sublevel with
the constraint therefore gives the compact set needed by the direct method.
The full nonlinear admissible set need not be globally weakly closed.
-/

@[expose] public section

open Set

namespace PDE.CalculusOfVariations

/-- A weakly lower semicontinuous energy attains its minimum under a continuous
constraint on a compactly embedded coordinate. Only the energy sublevel through
one feasible point must be norm bounded. -/
theorem exists_isMinOn_of_compact_constraint
    {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [TopologicalSpace Y]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (T : E →L[ℝ] H) (hT : IsCompactOperator T)
    (Ψ : H → Y) (hΨ : Continuous Ψ) {C : Set Y} (hC : IsClosed C)
    (F : E → ℝ)
    (hF : LowerSemicontinuous
      (fun w : WeakSpace ℝ E ↦ F ((toWeakSpace ℝ E).symm w)))
    {x₀ : E} (hx₀ : Ψ (T x₀) ∈ C)
    (hbounded : Bornology.IsBounded {x | F x ≤ F x₀}) :
    ∃ u, Ψ (T u) ∈ C ∧ IsMinOn F {x | Ψ (T x) ∈ C} u := by
  let f : WeakSpace ℝ E → ℝ := fun w ↦ F ((toWeakSpace ℝ E).symm w)
  let K := f ⁻¹' Iic (F x₀)
  let J : WeakSpace ℝ E → Y := fun w ↦ Ψ (T ((toWeakSpace ℝ E).symm w))
  have hKclosed : IsClosed K := hF.isClosed_preimage (F x₀)
  have hKbounded : Bornology.IsBounded ((toWeakSpace ℝ E) ⁻¹' K) := by
    have heq : (toWeakSpace ℝ E) ⁻¹' K = {x | F x ≤ F x₀} := by
      ext x
      simp only [K, f, mem_preimage, mem_Iic, mem_ofPred_eq, LinearEquiv.symm_apply_apply]
    rwa [heq]
  have hKcompact : IsCompact K := by
    rw [← hKclosed.closure_eq]
    exact PDE.Analysis.WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
      hreflexive K hKbounded
  have himage : toWeakSpace ℝ E '' {x | F x ≤ F x₀} = K := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [K, f, mem_preimage, mem_Iic, mem_ofPred_eq,
        LinearEquiv.symm_apply_apply] using hu
    · intro hw
      exact ⟨(toWeakSpace ℝ E).symm w, hw, LinearEquiv.apply_symm_apply _ _⟩
  have hJ : ContinuousOn J K := by
    rw [← himage]
    exact hΨ.comp_continuousOn
      (PDE.Analysis.continuousOn_compactOperator_weak_of_bounded T hT hbounded)
  have hclosed : IsClosed (K ∩ J ⁻¹' C) :=
    hJ.preimage_isClosed_of_isClosed hKclosed hC
  have hcompact : IsCompact (K ∩ J ⁻¹' C) :=
    hKcompact.of_isClosed_subset hclosed inter_subset_left
  have hnonempty : (K ∩ J ⁻¹' C).Nonempty := by
    refine ⟨toWeakSpace ℝ E x₀, ?_⟩
    simpa [K, f, J] using hx₀
  obtain ⟨w, hw, hmin⟩ :=
    (hF.lowerSemicontinuousOn _).exists_isMinOn hnonempty hcompact
  refine ⟨(toWeakSpace ℝ E).symm w, hw.2, fun v hv ↦ ?_⟩
  by_cases hvF : F v ≤ F x₀
  · have hvK : toWeakSpace ℝ E v ∈ K ∩ J ⁻¹' C := by
      simpa [K, f, J] using And.intro hvF hv
    simpa [f] using hmin hvK
  · exact (show f w ≤ F x₀ from hw.1).trans (le_of_not_ge hvF)

end PDE.CalculusOfVariations
