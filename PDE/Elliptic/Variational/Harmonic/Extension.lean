/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PoissonDirichlet

/-!
# Harmonic extension of H¹ boundary data

For a prescribed H¹ lifting, the negative Dirichlet pairing with that lifting
is a bounded functional on H¹₀. The unshifted Lax–Milgram solver
constructs the correction. Adding it to the lifting gives a weak harmonic
field in the prescribed affine Sobolev class.

Only boundedness and positive ambient dimension enter the coercivity argument.
No boundary regularity, trace right inverse, or solution is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Variational
open scoped InnerProductSpace

/-- Every H¹ lifting on a bounded set has a weak harmonic extension
in its affine H¹₀ class. The zero-boundary correction is obtained from
the coercive Dirichlet form. -/
theorem exists_weak_harmonic_extension
    {n : ℕ} {Ω : Set ℝ^n} (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (G : H¹(Ω)) :
    ∃ w : H¹₀(Ω), ∀ t : H¹₀(Ω),
      (∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) (G + (w : H¹(Ω))))
        (derivCoordCLM i t)) = 0 := by
  let ℓ : H¹₀(Ω) →L[ℝ] ℝ :=
    -(∑ i : Fin n, (innerSL ℝ (wkpCoordinateCLM (singleDerivIndex n i) G)).comp
      (derivCoordCLM i))
  have hB : IsCoercive (dirichletForm (n := n) (Ω := Ω)) :=
    dirichletForm_isCoercive (n := n) (Ω := Ω) hn hbounded
  let w : H¹₀(Ω) :=
    solve (V := H¹₀(Ω)) (dirichletForm (n := n) (Ω := Ω)) hB ℓ
  have hw := solve.isWeakSolution (V := H¹₀(Ω))
    (dirichletForm (n := n) (Ω := Ω)) hB ℓ
  refine ⟨w, fun t ↦ ?_⟩
  have ht :
      (∑ i, inner ℝ (derivCoordCLM i w) (derivCoordCLM i t)) =
        -(∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) G)
          (derivCoordCLM i t)) := by
    simpa only [dirichletForm_apply, ℓ, neg_apply, sum_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hw t
  have hD (i : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n i) (w : H¹(Ω)) = derivCoordCLM i w := by
    rw [wkpCoordinateCLM_apply, derivCoordCLM_apply]
  simp only [map_add, hD, inner_add_left, Finset.sum_add_distrib, ht, add_neg_cancel]

end SobolevSpace.GraphSpace
