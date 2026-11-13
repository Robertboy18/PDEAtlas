/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.GradientBlowup.Coordinates
public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Lifespan

/-!
# Uniform lifespan bound for a conservative two-system

Compact initial data give a bounded invariant rectangle even when the coordinate
map does not fix zero. The constants are chosen from this rectangle before the
candidate solution and its time interval. The initial invariant slopes in the
conclusion are derivatives of the given data; their identification with
the candidate's first-jet trace is part of the diagonal argument.

This is a quantitative form of the proof of Theorem 2 in Evans, §11.3.2, which follows the
slope of an invariant along a characteristic and solves the resulting Riccati equation,
(29)-(35). We take a C² flux and continuous compactly supported initial data. The candidate
supplies the initial differentiability through its closure jet.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.3.2, proof of Theorem 2, equations (29)-(35).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Manifold
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System

/-- A continuous compactly supported datum has bounded global Riemann
coordinates. The rectangle includes the possibly nonzero state `Φ 0`. -/
theorem exists_bound_invariant_initial (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ)) {g : ℝ → ℝ^2} (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    ∃ R : ℝ, ∀ x i, -R ≤ Φ (g x) i ∧ Φ (g x) i ≤ R := by
  have hK := (hcompact.isCompact_range hg).image Φ.contDiff.continuous
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨R, fun x i ↦ ?_⟩
  have hb := (norm_le_pi_norm (Φ (g x)) i).trans (hR _ ⟨g x, ⟨x, rfl⟩, rfl⟩)
  exact abs_le.mp hb

/-- A strictly hyperbolic conservative two-system with positive opposite
speed derivatives in global Riemann coordinates has a uniform finite lifespan
bound at every compressive initial point. The constants precede both the
original candidate and the terminal time. -/
theorem exists_uniform_lifespan_constants {flux : ℝ^2 → ℝ^2} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ))
    (hcoord : ∀ i q v, fderiv ℝ (fun z ↦ Φ z i) q (fderiv ℝ flux q v) =
      characteristicSpeed flux i.rev q * fderiv ℝ (fun z ↦ Φ z i) q v)
    (hpos : ∀ i z, 0 < fderiv ℝ (invariantSpeed flux Φ i) z (Pi.single i 1)) {g : ℝ → ℝ^2}
    (hg : Continuous g) (hcompact : HasCompactSupport g) :
    ∃ κ : Fin 2 → ℝ, (∀ i, 0 < κ i) ∧
      ∀ T : ℝ, 0 < T → ∀ (u : ℝ^2 → ℝ^2)
        (_ : ContinuousSecondJetOn u {p : ℝ^2 | p 0 ∈ Ioo 0 T}),
        (∀ x, u !₂[0, x] = g x) →
        (∀ p : ℝ^2, p 0 ∈ Ioo 0 T → fluxResidual flux u p = 0) →
        ∀ i x₀, deriv (fun x ↦ Φ (g x) i) x₀ < 0 →
          T < (κ i * (-deriv (fun x ↦ Φ (g x) i) x₀))⁻¹ := by
  obtain ⟨R, hR⟩ := exists_bound_invariant_initial Φ hg hcompact
  obtain ⟨κ, hκ, hbound⟩ := Quasilinear.Diagonal.exists_uniform_lifespan_constants
      (contDiff_invariantSpeed hflux hhyper Φ) (invariantSpeed_ne_rev hhyper Φ) hpos R
  refine ⟨κ, hκ, fun T hT u hu hinit hpde i x₀ hneg ↦ ?_⟩
  apply hbound (fun x ↦ Φ (g x)) hR T hT (fun p : ℝ × ℝ ↦ Φ (u !₂[p.1, p.2]))
    (invariantJet isOpen_Ioo hu Φ) (fun x ↦ congrArg Φ (hinit x)) _ i x₀ hneg
  intro p hp j
  apply invariant_transport (hflux.differentiable (by norm_num)) Φ hcoord (hu.hasFDerivAt
      (isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous) hp).differentiableAt (hpde _ hp) j

end PDE.Hyperbolic.ConservationLaw.System
