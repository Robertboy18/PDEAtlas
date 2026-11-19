/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.LinearImage.Basic
public import PDE.Analysis.WeakCompactness

/-!
# Lower semicontinuity after inclusion in an ambient space

A weakly lower-semicontinuous energy with bounded sublevels on a Hilbert
space has weakly compact sublevels. Their images under a continuous
linear inclusion are weakly compact, hence closed in the ambient norm
topology. Extension by `+∞` therefore gives an ambient lower-semicontinuous
energy. No compactness of the inclusion or separability is required.
-/

@[expose] public section

namespace PDE.Analysis.Convex

open Set

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Weak lower semicontinuity and bounded sublevels in the included
Hilbert space give norm lower semicontinuity of the extended energy. -/
theorem lowerSemicontinuous_linearImageEnergy
    (j : V →L[ℝ] H) (hj : Function.Injective j) (J : V → ℝ)
    (hJ : LowerSemicontinuous (fun u : WeakSpace ℝ V ↦ J ((toWeakSpace ℝ V).symm u)))
    (hbounded : ∀ r : ℝ, Bornology.IsBounded {u | J u ≤ r}) :
    LowerSemicontinuous (linearImageEnergy j J) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun r ↦ ?_
  induction r with
  | bot =>
      have hproper := isProper_linearImageEnergy j J
      have hempty : (linearImageEnergy j J) ⁻¹' Iic ⊥ = ∅ := by
        ext x
        simp [hproper.1 x]
      rw [hempty]
      exact isClosed_empty
  | top => simp
  | coe r =>
      let S : Set (WeakSpace ℝ V) := {u | J ((toWeakSpace ℝ V).symm u) ≤ r}
      have hS : IsCompact S :=
        WeakCompactness.isCompact_of_isClosed_of_isBounded
          (hJ.isClosed_preimage r) (hbounded r)
      have hT : IsClosed ((WeakSpace.map j) '' S) :=
        (hS.image (WeakSpace.map j).continuous).isClosed
      have hclosed := hT.preimage (toWeakSpaceCLM ℝ H).continuous
      convert hclosed using 1
      rw [show (linearImageEnergy j J) ⁻¹' Iic (r : EReal) =
        {x | linearImageEnergy j J x ≤ (r : EReal)} from rfl,
        sublevel_linearImageEnergy j hj]
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨toWeakSpace ℝ V u, hu, rfl⟩
      · rintro ⟨u, hu, hux⟩
        exact ⟨(toWeakSpace ℝ V).symm u, hu,
          congrArg (toWeakSpace ℝ H).symm hux⟩

end PDE.Analysis.Convex
