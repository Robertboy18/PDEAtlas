/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Particle paths in incompressible flow

Eulerian velocity fields determine Lagrangian particle trajectories. A spatial
curve `X` is a particle path for `u` when

```text
X'(t) = u(t, X(t)).
```

The chain rule then differentiates a spacetime field along that path in the
spacetime direction `(1, u)`. Coordinate expansion of this directional
derivative gives the material derivative `∂ₜ + u · ∇`.

Particle paths are predicates (`IsParticlePathAt`, `IsParticlePathOn`) rather than a
separate data structure; `IsParticlePathAt.hasDerivAt_comp_scalar` is the chain rule.

Particle trajectories and the evolution of quantities carried by the fluid are treated in
Majda and Bertozzi, Section 1.3.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, Section 1.3.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

namespace IncompressibleFlow

open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- A spatial curve follows the Eulerian velocity field at time `t`. -/
def IsParticlePathAt {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (X : ℝ → ℝ^n) (t : ℝ) : Prop :=
  HasDerivAt X (u (timeSpaceCons t (X t))) t

/-- A spatial curve follows the Eulerian velocity field at every time in `s`. -/
def IsParticlePathOn {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (X : ℝ → ℝ^n) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsParticlePathAt u X t

/-- Restrict a particle-path identity on a set to one time in that set. -/
theorem IsParticlePathOn.at {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}
    {X : ℝ → ℝ^n} {s : Set ℝ} (hX : IsParticlePathOn u X s)
    {t : ℝ} (ht : t ∈ s) :
    IsParticlePathAt u X t :=
  hX t ht

/-- If `X` has velocity `v`, then the spacetime curve `t ↦ (t, X(t))`
has velocity `(1, v)`. -/
theorem hasDerivAt_spacetimeCurve {n : ℕ} {X : ℝ → ℝ^n}
    {t : ℝ} {v : ℝ^n} (hX : HasDerivAt X v t) :
    HasDerivAt (fun s ↦ timeSpaceCons s (X s))
      (timeSpaceCons 1 v) t := by
  let e₀ : ℝ^(n + 1) :=
    EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
  have htime : HasDerivAt (fun s : ℝ ↦ s • e₀) e₀ t := by
    simpa using (hasDerivAt_id t).smul_const e₀
  have hspace :
      HasDerivAt (fun s ↦ embedWithTimeZeroCLM n (X s))
        (embedWithTimeZeroCLM n v) t :=
    (embedWithTimeZeroCLM n).hasFDerivAt.comp_hasDerivAt t hX
  have hcurve :
      (fun s ↦ timeSpaceCons s (X s)) =
        fun s ↦ s • e₀ + embedWithTimeZeroCLM n (X s) := by
    funext s
    ext i
    cases i using Fin.cases <;> simp [e₀]
  have hvelocity :
      timeSpaceCons 1 v = e₀ + embedWithTimeZeroCLM n v := by
    ext i
    cases i using Fin.cases <;> simp [e₀]
  rw [hcurve, hvelocity]
  exact htime.add hspace

/-- The chain rule along a particle path differentiates in the spacetime
direction `(1, u(t, X(t)))`. -/
theorem IsParticlePathAt.hasDerivAt_comp
    {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {X : ℝ → ℝ^n} {t : ℝ}
    (hX : IsParticlePathAt u X t)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : ℝ^(n + 1) → E}
    (hw : DifferentiableAt ℝ w (timeSpaceCons t (X t))) :
    HasDerivAt (fun s ↦ w (timeSpaceCons s (X s)))
      (fderiv ℝ w (timeSpaceCons t (X t))
        (timeSpaceCons 1 (u (timeSpaceCons t (X t))))) t := by
  exact hw.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_spacetimeCurve hX)

/-- Along a particle path, the derivative of a scalar field is its material
derivative `∂ₜw + u · ∇w`. -/
theorem IsParticlePathAt.hasDerivAt_comp_scalar
    {n : ℕ} {u : ℝ^(n + 1) → ℝ^n} {X : ℝ → ℝ^n} {t : ℝ}
    (hX : IsParticlePathAt u X t) {w : ℝ^(n + 1) → ℝ}
    (hw : DifferentiableAt ℝ w (timeSpaceCons t (X t))) :
    HasDerivAt (fun s ↦ w (timeSpaceCons s (X s)))
      (scalarMaterialDerivative n u w (timeSpaceCons t (X t))) t := by
  have hcoordinate :
      fderiv ℝ w (timeSpaceCons t (X t))
          (timeSpaceCons 1 (u (timeSpaceCons t (X t)))) =
        scalarMaterialDerivative n u w (timeSpaceCons t (X t)) := by
    rw [scalarMaterialDerivative_apply]
    rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_succ]
    simp [mul_comm]
  rw [← hcoordinate]
  exact hX.hasDerivAt_comp hw

end

end IncompressibleFlow
