/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime

/-!
# Spatial differentiation of translated spacetime kernels

Differentiating a kernel in its source variable introduces the negative of
the corresponding target derivative. This identity is useful when moving
derivatives from a source onto a convolution kernel.
-/

@[expose] public section

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- A spatial derivative in the source of a translated joint kernel is the
negative joint derivative in that spatial direction. -/
theorem partialDeriv_sub_prod
    (i : Fin n) {G : ℝ^n × ℝ → E} (p : ℝ^n × ℝ) (y : ℝ^n) (s : ℝ)
    (hG : DifferentiableAt ℝ G (p - (y, s))) :
    (∂[i] (fun z ↦ G (p - (z, s)))) y =
      -fderiv ℝ G (p - (y, s)) (EuclideanSpace.single i 1, 0) := by
  have hsub : HasFDerivAt (fun q : ℝ^n × ℝ ↦ p - q)
      (-(ContinuousLinearMap.id ℝ (ℝ^n × ℝ))) (y, s) :=
    (hasFDerivAt_id (y, s)).const_sub p
  have hd := hG.hasFDerivAt.comp (y, s) hsub
  rw [partialDeriv_prod_spaceSlice i (fun q ↦ G (p - q)) y s hd.differentiableAt]
  simpa [Function.comp_def] using
    congrArg (fun L : ℝ^n × ℝ →L[ℝ] E ↦ L (EuclideanSpace.single i 1, 0)) hd.fderiv

end PDE

end
