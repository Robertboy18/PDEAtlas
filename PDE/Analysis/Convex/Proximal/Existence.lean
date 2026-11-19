/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Energy
public import PDE.Analysis.WeakCompactness

/-!
# Attainment of the extended proximal energy

A finite proximal sublevel is nonempty, norm bounded by the derived affine minorant, and
weakly closed by convex lower semicontinuity. Weak compactness in a complete real Hilbert
space therefore yields a minimizer of the signed extended energy.

The compactness argument is topological and requires no countable dense set. Finiteness of
the minimizing energy is derived by comparison with the finite point supplied by properness.
-/

@[expose] public section

open Set

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Every positive quadratic perturbation of a proper convex lower-semicontinuous energy
attains its global minimum at a finite-energy point. -/
theorem exists_minimizer_proximalEnergy {I : H → EReal} (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {lambda : ℝ} (hlambda : 0 < lambda) (w : H) :
    ∃ u, I u ≠ ⊤ ∧ ∀ z, proximalEnergy I lambda w u ≤ proximalEnergy I lambda w z := by
  let F := proximalEnergy I lambda w
  have hFproper : IsProper F := isProper_proximalEnergy hproper lambda w
  have hFconvex : Convex ℝ (realEpigraph F) :=
    convex_realEpigraph_proximalEnergy hproper hconvex hlambda.le w
  have hFlsc : LowerSemicontinuous F := lowerSemicontinuous_proximalEnergy hlsc lambda w
  have hFweak := lowerSemicontinuous_weak hFproper.1 hFconvex hFlsc
  obtain ⟨u₀, r₀, hu₀⟩ := hFproper.exists_eq_coe
  obtain ⟨L, b, hminorant⟩ := exists_affine_minorant hproper hconvex hlsc
  let S : Set (WeakSpace ℝ H) :=
    {u | F ((toWeakSpace ℝ H).symm u) ≤ (r₀ : EReal)}
  have hSclosed : IsClosed S := hFweak.isClosed_preimage (r₀ : EReal)
  have hSbounded : Bornology.IsBounded ((toWeakSpace ℝ H) ⁻¹' S) := by
    have h := isBounded_proximal_sublevel_of_affine_minorant L b hminorant hlambda w r₀
    simpa only [S, F, Set.preimage_ofPred_eq, LinearEquiv.symm_apply_apply] using h
  have hScompact := WeakCompactness.isCompact_of_isClosed_of_isBounded hSclosed hSbounded
  have hSne : S.Nonempty := ⟨toWeakSpace ℝ H u₀, by simpa [S] using hu₀.le⟩
  obtain ⟨u, hu, hmin⟩ := (hFweak.lowerSemicontinuousOn S).exists_isMinOn hSne hScompact
  have hminAll (z : H) : F ((toWeakSpace ℝ H).symm u) ≤ F z := by
    by_cases hz : F z ≤ (r₀ : EReal)
    · exact hmin (show toWeakSpace ℝ H z ∈ S by simpa [S] using hz)
    · exact hu.trans (le_of_not_ge hz)
  refine ⟨(toWeakSpace ℝ H).symm u, ?_, hminAll⟩
  intro htop
  have hfinite : F ((toWeakSpace ℝ H).symm u) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top r₀) hu
  apply hfinite
  change I ((toWeakSpace ℝ H).symm u) + _ = ⊤
  rw [htop, EReal.top_add_coe]

end PDE.Analysis.Convex
