/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import PDE.CalculusOfVariations.DirectMethod

/-!
# Weak lower semicontinuity of convex functionals

A convex set that is closed in the norm topology is closed in the weak
topology. Applying this fact to every sublevel set shows that a convex,
norm-lower-semicontinuous real functional is lower semicontinuous for the full
weak topology, not only sequentially weakly lower semicontinuous. In a
reflexive space, the direct method then gives a minimizer on a nonempty closed
convex admissible set under coercivity along that set. Strict convexity makes
the minimizer unique.

The closedness fact is Mazur's theorem (Evans, Appendix D.4), which Evans uses for
the admissible set in the proof of §8.2.2, Theorem 2. His Theorem 1 proves weak
lower semicontinuity of integral functionals by a different route, through
Egoroff's theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorems 1 and 2, and Appendix D.4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set

namespace PDE.CalculusOfVariations

section WeakLowerSemicontinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex norm-closed subset of a real normed space is closed for the weak
topology. This is the closed-set form of Mathlib's `Convex.toWeakSpace_closure`. -/
theorem isClosed_toWeakSpace_image_of_convex
    {S : Set E} (hconvex : Convex ℝ S) (hclosed : IsClosed S) :
    IsClosed ((toWeakSpace ℝ E) '' S) := by
  rw [← hclosed.closure_eq, hconvex.toWeakSpace_closure ℝ]
  exact isClosed_closure

/-- A convex functional that is norm-lower-semicontinuous on a closed convex
admissible set is weakly lower semicontinuous there. No behavior outside the
admissible set enters the proof. -/
theorem lowerSemicontinuousOn_weakSpace_of_convex
    (F : E → ℝ) {A : Set E} (hconvex : ConvexOn ℝ A F)
    (hclosed : IsClosed A) (hlsc : LowerSemicontinuousOn F A) :
    LowerSemicontinuousOn
      (fun w : WeakSpace ℝ E ↦ F ((toWeakSpace ℝ E).symm w))
      (toWeakSpace ℝ E '' A) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  intro r
  let K := A ∩ F ⁻¹' Iic r
  have hKclosed : IsClosed K := by
    obtain ⟨C, hC, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hlsc r
    change IsClosed (A ∩ F ⁻¹' Iic r)
    rw [heq]
    exact hclosed.inter hC
  have hKconvex : Convex ℝ K := hconvex.convex_le r
  refine ⟨toWeakSpace ℝ E '' K,
    isClosed_toWeakSpace_image_of_convex hKconvex hKclosed, ?_⟩
  rw [(toWeakSpace ℝ E).image_eq_preimage_symm A,
    (toWeakSpace ℝ E).image_eq_preimage_symm K]
  ext w
  simp [K]

/-- A convex real functional that is lower semicontinuous in the norm
topology is lower semicontinuous in the weak topology. -/
theorem lowerSemicontinuous_weakSpace_of_convex
    (F : E → ℝ)
    (hconvex : ConvexOn ℝ Set.univ F)
    (hlsc : LowerSemicontinuous F) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ E ↦ F ((toWeakSpace ℝ E).symm w)) := by
  simpa [lowerSemicontinuousOn_univ_iff] using
    lowerSemicontinuousOn_weakSpace_of_convex F hconvex
    isClosed_univ (hlsc.lowerSemicontinuousOn univ)

/-- A norm-lower-semicontinuous convex energy attains its minimum on a nonempty
closed convex set in a reflexive space if it is coercive along that set. -/
theorem exists_isMinOn_of_convex_lowerSemicontinuousOn_of_coercive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (F : E → ℝ) {A : Set E} (hconvex : ConvexOn ℝ A F)
    (hclosed : IsClosed A) (hne : A.Nonempty)
    (hlsc : LowerSemicontinuousOn F A)
    (hcoercive : Tendsto F (Bornology.cobounded E ⊓ 𝓟 A) atTop) :
    ∃ u ∈ A, IsMinOn F A u :=
  exists_isMinOn_of_weak_lowerSemicontinuousOn_of_coercive hreflexive F
    (isClosed_toWeakSpace_image_of_convex hconvex.1 hclosed) hne
    (lowerSemicontinuousOn_weakSpace_of_convex F hconvex hclosed hlsc) hcoercive

/-- Strict convexity makes the constrained direct-method minimizer unique. -/
theorem existsUnique_isMinOn_of_strictConvex_lowerSemicontinuousOn_of_coercive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (F : E → ℝ) {A : Set E} (hstrict : StrictConvexOn ℝ A F)
    (hclosed : IsClosed A) (hne : A.Nonempty)
    (hlsc : LowerSemicontinuousOn F A)
    (hcoercive : Tendsto F (Bornology.cobounded E ⊓ 𝓟 A) atTop) :
    ∃! u, u ∈ A ∧ IsMinOn F A u := by
  obtain ⟨u, huA, hu⟩ := exists_isMinOn_of_convex_lowerSemicontinuousOn_of_coercive
    hreflexive F hstrict.convexOn hclosed hne hlsc hcoercive
  exact ⟨u, ⟨huA, hu⟩, fun v ⟨hvA, hv⟩ ↦ hstrict.eq_of_isMinOn hv hu hvA huA⟩

end WeakLowerSemicontinuity

section ConvexDirectMethod

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- A convex, norm-lower-semicontinuous, coercive functional on a real
Hilbert space attains its global minimum. -/
theorem exists_global_minimizer_of_convex_lowerSemicontinuous_of_coercive
    (F : H → ℝ)
    (hconvex : ConvexOn ℝ Set.univ F)
    (hlsc : LowerSemicontinuous F)
    (hcoercive : Tendsto F (Bornology.cobounded H) atTop) :
    ∃ u, ∀ v, F u ≤ F v := by
  exact
    exists_global_minimizer_of_weak_lowerSemicontinuous_of_coercive F
      (lowerSemicontinuous_weakSpace_of_convex F hconvex hlsc) hcoercive

/-- A strictly convex, norm-lower-semicontinuous, coercive functional on a
real Hilbert space has a unique global minimizer. -/
theorem existsUnique_global_minimizer_of_strictConvex_lowerSemicontinuous_of_coercive
    (F : H → ℝ)
    (hstrict : StrictConvexOn ℝ Set.univ F)
    (hlsc : LowerSemicontinuous F)
    (hcoercive : Tendsto F (Bornology.cobounded H) atTop) :
    ∃! u, ∀ v, F u ≤ F v := by
  exact
    existsUnique_global_minimizer_of_weak_lowerSemicontinuous_of_coercive_of_strictConvex
      F (lowerSemicontinuous_weakSpace_of_convex F hstrict.convexOn hlsc)
      hcoercive hstrict

end ConvexDirectMethod

end PDE.CalculusOfVariations
