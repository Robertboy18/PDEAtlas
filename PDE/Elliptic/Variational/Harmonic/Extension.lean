/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Variational.DirichletData

/-!
# Harmonic extension of H¹ boundary data

For a prescribed H¹ lifting there is a weak harmonic field in the prescribed affine Sobolev
class, written as the lifting plus a zero-boundary correction. This is the existence half of
`existsUnique_weak_harmonic_extension`, the Dirichlet problem with data for the Laplacian,
and is proved from it.

Only boundedness and positive ambient dimension enter the coercivity argument.
No boundary regularity, trace right inverse, or solution is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Variational
open scoped InnerProductSpace

/-- Every H¹ lifting on a bounded set has a weak harmonic extension
in its affine H¹₀ class. The zero-boundary correction is the difference of the unique weakly
harmonic field of the class and the lifting. -/
theorem exists_weak_harmonic_extension
    {n : ℕ} {Ω : Set ℝ^n} (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (G : H¹(Ω)) :
    ∃ w : H¹₀(Ω), ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) (G + (w : H¹(Ω))))
        (derivCoordCLM i t)) = 0 := by
  obtain ⟨u, ⟨hu, heq⟩, -⟩ := existsUnique_weak_harmonic_extension hn hbounded G
  refine ⟨⟨u - G, hu⟩, fun t ↦ ?_⟩
  have h : G + ((⟨u - G, hu⟩ : H¹₀(Ω)) : H¹(Ω)) = u := add_sub_cancel G u
  rw [h]
  exact heq t

end SobolevSpace.GraphSpace
