/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Osgood
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import PDE.Fluid.Incompressible.HalfPlane.VelocityBoundary

/-!
# Velocity laws of half-plane transport systems

The local theory of the two-dimensional Boussinesq system in the half-plane uses the Biot-Savart law
only through a few estimates of the velocity in terms of the vorticity. Stated as a class of maps
from vorticities to velocities, they give one local theory for every system with the same transport
structure, among them the axisymmetric Euler equations near the wall of a cylinder. This module
defines that class and the class of forcing coefficients.

The local theory of `HalfPlaneSystem` concerns systems on the closed upper half-plane
`H̄ = {x₁ ≥ 0}` of the form

```text
θ_t + u · ∇θ = 0,     ω_t + u · ∇ω = b(x) ∂₀θ,     u(t) = U (ω t),
```

where the velocity law `U` takes a vorticity on `H̄` to a velocity field on `H̄` and the forcing
coefficient `b` is smooth with bounded derivatives. For the two-dimensional Boussinesq system `U` is
the half-plane Biot-Savart law and `b = 1`; for the axisymmetric Euler equations near the wall of a
cylinder, in the wall coordinates `(z, 1 - r)`, `U` is the meridional velocity of the cylinder
stream function, cut off away from the support, and `b = r⁻⁴`.

`IsVelocityLaw U R₀ C` collects the properties of the law that the local theory uses, for data
continuous on `H̄` and vanishing there outside a disc of radius `R ≤ R₀`, with the constants `C k α`
(`k` the order, `α` the Hölder exponent):

* the field on `H̄` depends only on the datum on `H̄`, and the law is linear there;
* `‖U f‖ ≤ C 0 0 · B` for data bounded by `B`;
* for `α`-Hölder data the field is `C¹` within `H̄` with the Kato bound
  `‖DU f‖ ≤ C 0 α (1 + B log (2 + M) + B)` and the homogeneous form
  `‖DU f‖ ≤ C 0 α (φ_{2A+M}(η) + η)` for data bounded by `η ≤ A`, with `φ` the Osgood modulus;
* the normal component of the field vanishes on the boundary line;
* for data `C¹` within `H̄` with gradient bounded by `B₁` the derivative of the field is
  log-Lipschitz: `‖DU f(y) - DU f(z)‖ ≤ C 0 0 · B₁ |y - z| (1 + log⁺ (1 / |y - z|))`;
* for data of class `C^{k,α}` within `H̄`, `k ≥ 1`, with norms at most `N`, the field is `C^{k+1}`
  within `H̄`, its derivatives of order at most `k + 1` are at most `C k α · N` and the derivative
  of order `k + 1` is `α`-Hölder with constant `C k α · N`.

These are the estimates of the half-plane Biot-Savart law of `IncompressibleFlow`
(`norm_halfPlaneVelocity_le_of_abs_le`, `katoBound`, `norm_sub_fderivWithin_halfPlaneVelocity_le`,
`dist_fderivWithin_halfPlaneVelocity_le_log_of_support`,
`norm_iteratedFDerivWithin_halfPlaneVelocity_le_mul`,
`norm_iteratedFDerivWithin_halfPlaneVelocity_sub_le`) in a form without the explicit constants; the
constants `C k α` are not specified. The Schauder estimate of the derivative of the field for Hölder
data is not a field of `IsVelocityLaw`: it is the separate class `IsHolderVelocityLaw` of
`APrioriHolder.lean`, needed for the continuation criterion only, which is part of the maximal
well-posedness theorem. `IsForcingCoefficient b Bb` asks that `b` be smooth with `‖Dᵏ b‖ ≤ Bb k`
everywhere.

## Main results

* `IsVelocityLaw`: the velocity law. Its fields are the properties listed above.
* `IsForcingCoefficient`: the forcing coefficient.
* `IsVelocityLaw.norm_sub_le`: the fields of two continuous data supported in a disc of radius
  `R ≤ R₀` that differ by at most `β` on `H̄` differ by at most `C 0 0 · β` there.
* `IsVelocityLaw.norm_fderivWithin_sub_le_osgood`: for `0 < α < 1`, the derivatives of the fields of
  two `α`-Hölder data that differ by at most `β ≤ A` differ by at most
  `C 0 α (φ_{2A + M_f + M_g}(β) + β)`.

## The modules of the folder

* `Field.lean`, `FieldHigher.lean`, `FieldHigherFlow.lean`, `FieldPair.lean`: the field of a
  vorticity history, extended across the boundary, its regularity and its flow, and the comparison
  of the flows of two close fields.
* `Forcing.lean`, `CarriedVorticity.lean`, `CarriedTemperature.lean`, `CarriedHigherForcing.lean`,
  `CarriedHigher.lean`: the fields that a frozen velocity carries from the data, with their bounds;
  the carried vorticity is the iteration map.
* `Iteration.lean`, `Convergence.lean`, `FixedPoint.lean`, `Solution.lean`, `LocalExistence.lean`:
  the iteration keeps a class of histories for a short time, satisfies a difference estimate of
  Osgood type and converges, and its fixed point is a classical solution
  (`exists_isSolutionOn_Ioo`).
* `Lagrangian.lean`, `Uniqueness.lean`: a solution along its trajectories, and forward uniqueness on
  the closed half-plane.
* `Canonical.lean`, `Maximal.lean`: canonical representatives, the maximal solution and the blow-up
  alternative.
* `VorticityBound.lean`, `APrioriLower.lean`, `APrioriHolder.lean`, `APrioriTop.lean`,
  `APrioriTopBounds.lean`, `APriori.lean`, `APrioriEstimate.lean`, `Continuation.lean`: the a priori
  estimate and the continuation criterion.
* `LevelK.lean`, `IterationHigher.lean`, `Persistence.lean`, `PersistenceCanonical.lean`,
  `RegularField.lean`: regular solutions of order `k`, the propagation of regularity and the
  regularity of the velocity field.
* `PersistenceMaximal.lean`: the theorem of the folder, `exists_maximalSolutionOf`, local
  well-posedness at level `k ≥ 2` on the maximal life span.
* `BiotSavartLaw.lean`, `BoussinesqInstance.lean`: the half-plane Biot-Savart law with a constant
  coefficient as an instance, and the link to `PDE/Fluid/Boussinesq/HalfPlane`.

Two instances of the hypotheses are proved. In this library: the half-plane Biot-Savart law
(`isVelocityLaw_halfPlaneVelocity` in `BiotSavartLaw.lean`) with a constant coefficient
(`isForcingCoefficient_const` in `BoussinesqInstance.lean`). In BlowupZoo: the velocity law of the
wall (`isVelocityLaw_wall` in `Euler/BoundaryBlowup/LocalTheory/WallLawRegularity.lean`) with the
coefficient `r⁻⁴` (`isForcingCoefficient_wallCoefficient` in `LocalTheory/WallCoefficient.lean`).
There `wallWellPosedness` (`Euler/BoundaryBlowup/LocalTheory/WellPosedness.lean`), the local theory
of the Euler equations near the wall of the cylinder in the boundary blowup (question `bb-steps` of
BlowupZoo), is proved from `exists_maximalSolutionOf`, and the estimates of the velocity near the
wall use the fields of `IsVelocityLaw` for the Biot-Savart law.

`PDE/Fluid/Boussinesq/HalfPlane` has the local theory of the Boussinesq system for its own class of
solutions. No theorem of this library derives the theorems of that folder from the theorems of this
one, or the reverse; `BoussinesqInstance.lean` says what is proved about the relation.
-/

@[expose] public section

noncomputable section

open Set

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- **A velocity law** for data supported in the disc of radius `R₀`, with the constants
`C k α`. The data are functions continuous on the closed upper half-plane `H̄` that vanish there
outside a disc of radius `R ≤ R₀`; only the values of the data and of the fields on `H̄` matter.
See the module docstring for the meaning of each field. -/
structure IsVelocityLaw (U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2) (R₀ : ℝ) (C : ℕ → ℝ → ℝ) : Prop where
  /-- The constants are nonnegative. -/
  const_nonneg : ∀ k α, 0 ≤ C k α
  /-- The field on `H̄` depends only on the datum on `H̄`. -/
  congr : ∀ {f g : ℝ^2 → ℝ}, (∀ y : ℝ^2, 0 ≤ y 1 → f y = g y) →
    ∀ x : ℝ^2, 0 ≤ x 1 → U f x = U g x
  /-- Linearity on the data. -/
  sub : ∀ {f g : ℝ^2 → ℝ} {R : ℝ}, R ≤ R₀ → ContinuousOn f H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) → ContinuousOn g H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) →
    ∀ x : ℝ^2, 0 ≤ x 1 → U (f - g) x = U f x - U g x
  /-- The size of the field. -/
  norm_le : ∀ {f : ℝ^2 → ℝ} {R B : ℝ}, R ≤ R₀ → ContinuousOn f H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) → (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) →
    ∀ x : ℝ^2, 0 ≤ x 1 → ‖U f x‖ ≤ C 0 0 * B
  /-- The field of a Hölder datum is `C¹` within `H̄`. -/
  contDiffOn_one : ∀ {f : ℝ^2 → ℝ} {R M α : ℝ}, 0 < α → α < 1 → R ≤ R₀ → ContinuousOn f H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) →
    ContDiffOn ℝ 1 (U f) H̄
  /-- The Kato bound of the derivative of the field. -/
  norm_fderivWithin_le : ∀ {f : ℝ^2 → ℝ} {R B M α : ℝ}, 0 < α → α < 1 → R ≤ R₀ →
    ContinuousOn f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) → 0 ≤ M →
    (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) →
    ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderivWithin ℝ (U f) H̄ x‖ ≤ C 0 α * (1 + B * Real.log (2 + M) + B)
  /-- The homogeneous Kato bound of the derivative of the field, for small data. -/
  norm_fderivWithin_le_osgood : ∀ {f : ℝ^2 → ℝ} {R M α η A : ℝ}, 0 < α → α < 1 → R ≤ R₀ →
    ContinuousOn f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) → 0 ≤ M →
    (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ η) → η ≤ A →
    ∀ x : ℝ^2, 0 ≤ x 1 → ‖fderivWithin ℝ (U f) H̄ x‖ ≤
      C 0 α * (PDE.Analysis.osgoodModulus (2 * A + M) η + η)
  /-- The normal component of the field vanishes on the boundary line. -/
  normal_eq_zero : ∀ {f : ℝ^2 → ℝ} {R : ℝ}, R ≤ R₀ → ContinuousOn f H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) → ∀ x : ℝ^2, x 1 = 0 → U f x 1 = 0
  /-- The derivative of the field of a `C¹` datum is log-Lipschitz on `H̄`. -/
  norm_fderivWithin_sub_le_log : ∀ {f : ℝ^2 → ℝ} {R B₁ : ℝ}, R ≤ R₀ → ContDiffOn ℝ 1 f H̄ →
    (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ f H̄ y‖ ≤ B₁) →
    ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (U f) H̄ y - fderivWithin ℝ (U f) H̄ z‖ ≤
        C 0 0 * B₁ * ‖y - z‖ * (1 + Real.posLog (1 / ‖y - z‖))
  /-- The field of a `C^{k,α}` datum, `k ≥ 1`, is `C^{k+1}` within `H̄`. -/
  contDiffOn_succ : ∀ {k : ℕ} {f : ℝ^2 → ℝ} {R N α : ℝ}, 1 ≤ k → 0 < α → α < 1 → R ≤ R₀ →
    ContDiffOn ℝ k f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ N * ‖y - z‖ ^ α) →
    ContDiffOn ℝ (k + 1) (U f) H̄
  /-- The derivatives of order at most `k + 1` of the field of a `C^{k,α}` datum. -/
  norm_iteratedFDerivWithin_le : ∀ {k : ℕ} {f : ℝ^2 → ℝ} {R N α : ℝ}, 1 ≤ k → 0 < α → α < 1 →
    R ≤ R₀ → ContDiffOn ℝ k f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ N * ‖y - z‖ ^ α) →
    ∀ j ≤ k + 1, ∀ x : ℝ^2, 0 ≤ x 1 → ‖iteratedFDerivWithin ℝ j (U f) H̄ x‖ ≤ C k α * N
  /-- The Hölder bound of the derivative of order `k + 1` of the field of a `C^{k,α}` datum. -/
  holder_iteratedFDerivWithin : ∀ {k : ℕ} {f : ℝ^2 → ℝ} {R N α : ℝ}, 1 ≤ k → 0 < α → α < 1 →
    R ≤ R₀ → ContDiffOn ℝ k f H̄ → (∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) →
    (∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N) →
    (∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ N * ‖y - z‖ ^ α) →
    ∀ x x' : ℝ^2, 0 ≤ x 1 → 0 ≤ x' 1 →
      ‖iteratedFDerivWithin ℝ (k + 1) (U f) H̄ x - iteratedFDerivWithin ℝ (k + 1) (U f) H̄ x'‖ ≤
        C k α * N * ‖x - x'‖ ^ α

/-- **A forcing coefficient**: a smooth function on the plane whose derivatives of order `k` are
bounded by `Bb k` everywhere. -/
structure IsForcingCoefficient (b : ℝ^2 → ℝ) (Bb : ℕ → ℝ) : Prop where
  /-- Smoothness. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) b
  /-- The bounds of the derivatives. -/
  norm_iteratedFDeriv_le : ∀ (k : ℕ) (x : ℝ^2), ‖iteratedFDeriv ℝ k b x‖ ≤ Bb k

namespace IsVelocityLaw

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ}

/-- **The fields of two data differ by `C 0 0` times the bound of the difference.** It is the
Lipschitz dependence of the velocity on the vorticity in the sup norm, which compares two
solutions or two iterates. Proof: the law is linear on the data, and the size bound applies to
the difference. -/
theorem norm_sub_le (hU : IsVelocityLaw U R₀ C) {f g : ℝ^2 → ℝ} {R β : ℝ} (hR : R ≤ R₀)
    (hf : ContinuousOn f H̄) (hfR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    (hg : ContinuousOn g H̄) (hgR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0)
    (hβ : ∀ y : ℝ^2, 0 ≤ y 1 → |f y - g y| ≤ β) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖U f x - U g x‖ ≤ C 0 0 * β := by
  rw [← hU.sub hR hf hfR hg hgR x hx]
  exact hU.norm_le hR (hf.sub hg) (fun y hy hyR ↦ by simp [hfR y hy hyR, hgR y hy hyR])
    (fun y hy ↦ hβ y hy) x hx

/-- **The derivatives of the fields of two Hölder data differ by the homogeneous Kato bound** of
the difference: by at most `C 0 α (φ_{2A + M_f + M_g}(β) + β)` when the data differ by at most
`β ≤ A`. The velocity gradient depends on the vorticity with a logarithmic loss, which is why
the comparison of two flows has the Osgood modulus. Proof: the law is linear, the difference of
the data is `α`-Hölder with constant `M_f + M_g`, and the homogeneous Kato bound applies. -/
theorem norm_fderivWithin_sub_le_osgood (hU : IsVelocityLaw U R₀ C) {f g : ℝ^2 → ℝ}
    {R Mf Mg α β A : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : R ≤ R₀) (hf : ContinuousOn f H̄)
    (hfR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hg : ContinuousOn g H̄)
    (hgR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0)
    (hMf : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ Mf * ‖y - z‖ ^ α)
    (hMg : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ Mg * ‖y - z‖ ^ α)
    (hMf0 : 0 ≤ Mf) (hMg0 : 0 ≤ Mg) (hβ : ∀ y : ℝ^2, 0 ≤ y 1 → |f y - g y| ≤ β) (hβA : β ≤ A)
    {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (U f) H̄ x - fderivWithin ℝ (U g) H̄ x‖ ≤
      C 0 α * (PDE.Analysis.osgoodModulus (2 * A + (Mf + Mg)) β + β) := by
  have hfR' : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → (f - g) y = 0 := fun y hy hyR ↦ by
    simp [hfR y hy hyR, hgR y hy hyR]
  have hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      |(f - g) y - (f - g) z| ≤ (Mf + Mg) * ‖y - z‖ ^ α := fun y z hy hz ↦ by
    have h1 := hMf y z hy hz
    have h2 := hMg y z hy hz
    simp only [Pi.sub_apply]
    calc |f y - g y - (f z - g z)| = |(f y - f z) - (g y - g z)| := by ring_nf
      _ ≤ |f y - f z| + |g y - g z| := abs_sub _ _
      _ ≤ (Mf + Mg) * ‖y - z‖ ^ α := by linarith
  have hd := hU.contDiffOn_one hα hα1 hR (hf.sub hg) hfR' hM
  have hdf := hU.contDiffOn_one hα hα1 hR hf hfR hMf
  have hdg := hU.contDiffOn_one hα hα1 hR hg hgR hMg
  have heq : fderivWithin ℝ (U (f - g)) H̄ x =
      fderivWithin ℝ (U f) H̄ x - fderivWithin ℝ (U g) H̄ x := by
    have hcongr : fderivWithin ℝ (U (f - g)) H̄ x = fderivWithin ℝ (U f - U g) H̄ x :=
      fderivWithin_congr (fun y hy ↦ hU.sub hR hf hfR hg hgR y hy) (hU.sub hR hf hfR hg hgR x hx)
    rw [hcongr]
    exact fderivWithin_sub (IncompressibleFlow.uniqueDiffOn_closedUpper x hx)
      (hdf.differentiableOn one_ne_zero x hx) (hdg.differentiableOn one_ne_zero x hx)
  rw [← heq]
  exact hU.norm_fderivWithin_le_osgood hα hα1 hR (hf.sub hg) hfR' hM (by positivity)
    (fun y hy ↦ hβ y hy) hβA x hx

end IsVelocityLaw

end HalfPlaneSystem
