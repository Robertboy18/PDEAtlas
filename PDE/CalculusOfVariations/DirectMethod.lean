/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import PDE.Analysis.Convex.Differentiable.Supporting
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import PDE.Analysis.WeakCompactness

/-!
# The direct method of the calculus of variations

This is the functional-analytic form of the direct method of Evans, §8.2.1 and §8.2.2.
In a reflexive space, a functional attains its minimum on
a weakly closed admissible set if it is weakly lower semicontinuous there and
one nonempty sublevel is norm bounded. Coercivity need hold only along the
admissible set. Reflexivity is expressed by surjectivity of the canonical
double-dual map; for real Hilbert spaces we prove this hypothesis from Riesz
representation.

The lower-semicontinuity hypothesis uses the full weak topology. Applying
these results to a particular integral energy still requires proving its
lower semicontinuity and coercivity, and weak closedness of its admissible set.

The first-variation results characterize constrained minimizers and give
sufficient conditions under convexity. Strict convexity gives uniqueness,
which is combined with the direct method in the final theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.1 and §8.2.2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set

namespace PDE.CalculusOfVariations

section ReflexiveDirectMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The direct method on a weakly closed admissible set in a reflexive space.
Only one nonempty sublevel must be bounded, and lower semicontinuity is needed
only on the admissible set. -/
theorem exists_isMinOn_of_weak_lowerSemicontinuousOn_of_bounded_sublevel
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (F : E → ℝ) {A : Set E}
    (hA : IsClosed (toWeakSpace ℝ E '' A))
    (hF : LowerSemicontinuousOn
      (fun w : WeakSpace ℝ E ↦ F ((toWeakSpace ℝ E).symm w))
      (toWeakSpace ℝ E '' A))
    {x₀ : E} (hx₀ : x₀ ∈ A)
    (hbounded : Bornology.IsBounded {x | x ∈ A ∧ F x ≤ F x₀}) :
    ∃ u ∈ A, IsMinOn F A u := by
  let f : WeakSpace ℝ E → ℝ := fun w ↦ F ((toWeakSpace ℝ E).symm w)
  let S := toWeakSpace ℝ E '' A
  let K := S ∩ f ⁻¹' Iic (F x₀)
  have hclosed : IsClosed K := by
    obtain ⟨C, hC, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hF (F x₀)
    change IsClosed (S ∩ f ⁻¹' Iic (F x₀))
    rw [heq]
    exact hA.inter hC
  have hbounded' : Bornology.IsBounded ((toWeakSpace ℝ E) ⁻¹' K) := by
    have heq : (toWeakSpace ℝ E) ⁻¹' K = {x | x ∈ A ∧ F x ≤ F x₀} := by
      ext x
      simp [K, S, f]
    rwa [heq]
  have hcompact : IsCompact K := by
    rw [← hclosed.closure_eq]
    exact PDE.Analysis.WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
      hreflexive K hbounded'
  have hnonempty : K.Nonempty := by
    refine ⟨toWeakSpace ℝ E x₀, ⟨⟨x₀, hx₀, rfl⟩, ?_⟩⟩
    simp [f]
  obtain ⟨w, hw, hmin⟩ :=
    (hF.mono inter_subset_left).exists_isMinOn hnonempty hcompact
  refine ⟨(toWeakSpace ℝ E).symm w, ?_, fun v hv ↦ ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hw.1
    simpa using hu
  · by_cases hvF : F v ≤ F x₀
    · have hvK : toWeakSpace ℝ E v ∈ K := by
        exact ⟨⟨v, hv, rfl⟩, by simpa [f] using hvF⟩
      simpa [f] using hmin hvK
    · exact (show f w ≤ F x₀ from hw.2).trans (le_of_not_ge hvF)

/-- Coercivity along a nonempty weakly closed admissible set gives a minimizer
of every weakly lower semicontinuous functional on that set. The ambient space
is reflexive; no condition is imposed on the energy outside the set. -/
theorem exists_isMinOn_of_weak_lowerSemicontinuousOn_of_coercive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (F : E → ℝ) {A : Set E}
    (hA : IsClosed (toWeakSpace ℝ E '' A)) (hne : A.Nonempty)
    (hF : LowerSemicontinuousOn
      (fun w : WeakSpace ℝ E ↦ F ((toWeakSpace ℝ E).symm w))
      (toWeakSpace ℝ E '' A))
    (hcoercive : Tendsto F (Bornology.cobounded E ⊓ 𝓟 A) atTop) :
    ∃ u ∈ A, IsMinOn F A u := by
  obtain ⟨x₀, hx₀⟩ := hne
  apply exists_isMinOn_of_weak_lowerSemicontinuousOn_of_bounded_sublevel
    hreflexive F hA hF hx₀
  rw [Bornology.isBounded_def]
  have h := eventually_inf_principal.mp (hcoercive.eventually (Ioi_mem_atTop (F x₀)))
  filter_upwards [h] with x hx
  simpa only [mem_compl_iff, mem_ofPred_eq, not_and, not_le] using hx

end ReflexiveDirectMethod

section DirectMethod

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- A weakly lower semicontinuous functional on a real Hilbert space attains
its global minimum if one of its nonempty sublevel sets is norm bounded. -/
theorem exists_global_minimizer_of_weak_lowerSemicontinuous_of_bounded_sublevel
    (F : H → ℝ)
    (hF : LowerSemicontinuous
      (fun w : WeakSpace ℝ H ↦ F ((toWeakSpace ℝ H).symm w)))
    (x₀ : H)
    (hbounded : Bornology.IsBounded {x | F x ≤ F x₀}) :
    ∃ u, ∀ v, F u ≤ F v := by
  obtain ⟨u, _, hu⟩ :=
    exists_isMinOn_of_weak_lowerSemicontinuousOn_of_bounded_sublevel
      PDE.Analysis.inclusionInDoubleDual_surjective F
      (A := univ) (by simp) (hF.lowerSemicontinuousOn _)
      (mem_univ x₀) (by simpa using hbounded)
  exact ⟨u, fun v ↦ hu (mem_univ v)⟩

/-- Coercivity with respect to the bornological cobounded filter makes every
real sublevel bounded, so the direct method produces a global minimizer. -/
theorem exists_global_minimizer_of_weak_lowerSemicontinuous_of_coercive
    (F : H → ℝ)
    (hF : LowerSemicontinuous
      (fun w : WeakSpace ℝ H ↦ F ((toWeakSpace ℝ H).symm w)))
    (hcoercive : Tendsto F (Bornology.cobounded H) atTop) :
    ∃ u, ∀ v, F u ≤ F v := by
  apply
    exists_global_minimizer_of_weak_lowerSemicontinuous_of_bounded_sublevel
      F hF 0
  rw [Bornology.isBounded_def]
  have hset : {x | F x ≤ F 0}ᶜ = {x | F 0 < F x} := by
    ext x
    simp
  rw [hset]
  exact hcoercive.eventually (Ioi_mem_atTop (F 0))

end DirectMethod

section FirstVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point minimizes a differentiable convex functional on a convex
admissible set exactly when its first variation is nonnegative in every
feasible direction. At a boundary point the derivative need not vanish. -/
theorem isMinOn_iff_forall_fderiv_sub_nonneg
    {F : E → ℝ} {A : Set E} {u : E} {DF : E →L[ℝ] ℝ}
    (hconvex : ConvexOn ℝ A F) (hu : u ∈ A) (hF : HasFDerivAt F DF u) :
    IsMinOn F A u ↔ ∀ v ∈ A, 0 ≤ DF (v - u) := by
  constructor
  · intro hmin v hv
    exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hF.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hconvex.1.segment_subset hu hv))
  · intro hfirst v hv
    exact sub_nonneg.mp ((hfirst v hv).trans
      (PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hconvex hF v hu hv))

/-- A zero first variation is sufficient for global minimality when the
functional is convex. -/
theorem global_minimizer_of_convex_of_hasFDerivAt_zero
    {F : E → ℝ} {u : E}
    (hconvex : ConvexOn ℝ Set.univ F)
    (hF : HasFDerivAt F (0 : E →L[ℝ] ℝ) u) :
    ∀ v, F u ≤ F v := by
  intro v
  simpa only [zero_apply, sub_nonneg] using
    PDE.Analysis.fderiv_apply_sub_le_sub_of_convex hconvex hF v (mem_univ _) (mem_univ _)

end FirstVariation

section UniqueDirectMethod

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- A weakly lower semicontinuous, coercive, strictly convex functional on a
real Hilbert space has a unique global minimizer. -/
theorem existsUnique_global_minimizer_of_weak_lowerSemicontinuous_of_coercive_of_strictConvex
    (F : H → ℝ)
    (hF : LowerSemicontinuous
      (fun w : WeakSpace ℝ H ↦ F ((toWeakSpace ℝ H).symm w)))
    (hcoercive : Tendsto F (Bornology.cobounded H) atTop)
    (hstrict : StrictConvexOn ℝ Set.univ F) :
    ∃! u, ∀ v, F u ≤ F v := by
  obtain ⟨u, hu⟩ :=
    exists_global_minimizer_of_weak_lowerSemicontinuous_of_coercive
      F hF hcoercive
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  exact hstrict.eq_of_isMinOn (fun w _ ↦ hv w) (fun w _ ↦ hu w)
    (mem_univ v) (mem_univ u)

end UniqueDirectMethod

end PDE.CalculusOfVariations
