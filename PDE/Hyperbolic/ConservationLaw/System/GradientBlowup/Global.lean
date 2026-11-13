/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.GradientBlowup.Lifespan

/-!
# Gradient blowup from compact initial compression

This is Theorem 2 of Evans, §11.3.2: under global Riemann coordinates and the condition (27),
a negative initial slope (28) of an invariant excludes a global classical solution. Evans
takes smooth data with compact support; our data are continuous with compact support, and we
exclude even C² closure solutions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.3.2, Theorem 2, equations (27)-(28).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Manifold
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Compact initial compression prevents global closure-C² existence.
The given global coordinate diffeomorphism is the standing Riemann coordinate
data; it is not a consequence assumed of strict hyperbolicity alone. -/
theorem not_exists_global_of_compressive_invariant {flux : ℝ^2 → ℝ^2} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ))
    (hcoord : ∀ i q v, fderiv ℝ (fun z ↦ Φ z i) q (fderiv ℝ flux q v) =
      characteristicSpeed flux i.rev q * fderiv ℝ (fun z ↦ Φ z i) q v)
    (hpos : ∀ i z, 0 < fderiv ℝ (invariantSpeed flux Φ i) z (Pi.single i 1)) {g : ℝ → ℝ^2}
    (hg : Continuous g) (hcompact : HasCompactSupport g) {i : Fin 2} {x₀ : ℝ}
    (hneg : deriv (fun x ↦ Φ (g x) i) x₀ < 0) :
    ¬ ∃ u : ℝ^2 → ℝ^2, Nonempty (ContinuousSecondJetOn u PDE.Common.positiveTimeDomain) ∧
      (∀ x, u !₂[0, x] = g x) ∧
      (∀ p ∈ PDE.Common.positiveTimeDomain, fluxResidual flux u p = 0) := by
  rintro ⟨u, ⟨hu⟩, hinit, hpde⟩
  obtain ⟨κ, hκ, hbound⟩ := exists_uniform_lifespan_constants hflux hhyper Φ hcoord hpos hg hcompact
  let T := (κ i * (-deriv (fun x ↦ Φ (g x) i) x₀))⁻¹
  have hT : 0 < T := inv_pos.mpr (mul_pos (hκ i) (neg_pos.mpr hneg))
  have hsub : {p : ℝ^2 | p 0 ∈ Ioo 0 T} ⊆ PDE.Common.positiveTimeDomain := fun _ hp ↦ hp.1
  exact (lt_irrefl T) (hbound T hT u (hu.mono hsub) hinit (fun p hp ↦ hpde p hp.1) i x₀ hneg)

end PDE.Hyperbolic.ConservationLaw.System
