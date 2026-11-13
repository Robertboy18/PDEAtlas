/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric.Isometry
public import PDE.Fluid.Incompressible.Solenoidal
public import PDE.Fluid.NavierStokes.Stationary.Representative
public import PDE.Spaces.Sobolev.Calculus.Divergence.ZeroBoundary

/-!
# Axisymmetry with swirl and equatorial parity

Write `R_θ` for the rotation `PDE.CoordinateSystems.axialRotation θ` about the third coordinate
axis and `σ` for the equatorial reflection `diag(1, 1, -1)`. A vector field `u` on `ℝ^3` is
even axisymmetric when `R_θ u(R_θ⁻¹ x) = u(x)` for every angle and `σ u(σ x) = u(x)`, and odd
axisymmetric when the reflection identity is `σ u(σ x) = -u(x)` instead. Both identities are
imposed almost everywhere, so they apply to equivalence classes through any representative.
Rotation equivariance allows swirl.

Hou, Wang and Yang impose even symmetry in the axial variable on the profile and odd symmetry on
the eigenfunction (Sections 1.3 and 5.2). Componentwise, under the reflection
`z ↦ -z` of the axial coordinate, an even axisymmetric field has even radial and swirl
components and an odd axial component, and an odd axisymmetric field the reverse.

The sectors are the corresponding linear subspaces: `evenSector ρ` and `oddSector ρ` in the
solenoidal zero-boundary space on the ball `B(0,ρ)`, through the zero extension `ballField ρ`,
and `evenSectorH1` and `oddSectorH1` in the whole-space `H¹` velocity space, through
`Stationary.representative`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.3, p. 5, and Section 5.2,
  p. 39.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.CoordinateSystems (axialRotation equatorialReflection
  measurePreserving_equatorialReflection)
open scoped ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- Even axisymmetry with swirl, almost everywhere: `R_θ u(R_θ⁻¹ x) = u(x)` for every angle `θ`
and `σ u(σ x) = u(x)` for the equatorial reflection `σ = diag(1, 1, -1)`. -/
def IsEvenAxisymmetric (u : ℝ^3 → ℝ^3) : Prop :=
  (∀ θ : ℝ, (fun x ↦ axialRotation θ (u ((axialRotation θ).symm x))) =ᵐ[volume] u) ∧
    (fun x ↦ equatorialReflection (u (equatorialReflection x))) =ᵐ[volume] u

/-- Odd axisymmetry with swirl, almost everywhere: `R_θ u(R_θ⁻¹ x) = u(x)` for every angle `θ`
and `σ u(σ x) = -u(x)` for the equatorial reflection `σ = diag(1, 1, -1)`. -/
def IsOddAxisymmetric (u : ℝ^3 → ℝ^3) : Prop :=
  (∀ θ : ℝ, (fun x ↦ axialRotation θ (u ((axialRotation θ).symm x))) =ᵐ[volume] u) ∧
    (fun x ↦ equatorialReflection (u (equatorialReflection x))) =ᵐ[volume] -u

/-- Composing with a measure-preserving isometry on the inside and an isometry on the outside
respects almost-everywhere equality. -/
private theorem conj_ae_eq {u v : ℝ^3 → ℝ^3} (h : u =ᵐ[volume] v) (L : ℝ^3 ≃ₗᵢ[ℝ] ℝ^3)
    (M : ℝ^3 ≃ₗᵢ[ℝ] ℝ^3) (hM : MeasurePreserving M volume volume) :
    (fun x ↦ L (u (M x))) =ᵐ[volume] fun x ↦ L (v (M x)) := by
  have hcomp : u ∘ M =ᵐ[volume] v ∘ M := hM.quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [hcomp] with x hx
  simp only [Function.comp_apply] at hx
  rw [hx]

/-- Even axisymmetry depends only on the almost-everywhere class of the field. -/
theorem IsEvenAxisymmetric.congr_ae {u v : ℝ^3 → ℝ^3} (hu : IsEvenAxisymmetric u)
    (h : u =ᵐ[volume] v) : IsEvenAxisymmetric v := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · exact (conj_ae_eq h.symm (axialRotation θ) (axialRotation θ).symm
      (axialRotation θ).symm.measurePreserving).trans ((hu.1 θ).trans h)
  · exact (conj_ae_eq h.symm equatorialReflection equatorialReflection
      measurePreserving_equatorialReflection).trans (hu.2.trans h)

/-- Odd axisymmetry depends only on the almost-everywhere class of the field. -/
theorem IsOddAxisymmetric.congr_ae {u v : ℝ^3 → ℝ^3} (hu : IsOddAxisymmetric u)
    (h : u =ᵐ[volume] v) : IsOddAxisymmetric v := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · exact (conj_ae_eq h.symm (axialRotation θ) (axialRotation θ).symm
      (axialRotation θ).symm.measurePreserving).trans ((hu.1 θ).trans h)
  · exact (conj_ae_eq h.symm equatorialReflection equatorialReflection
      measurePreserving_equatorialReflection).trans (hu.2.trans h.neg)

/-- The zero field is even axisymmetric. -/
theorem isEvenAxisymmetric_zero : IsEvenAxisymmetric 0 :=
  ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ by simp,
    Filter.Eventually.of_forall fun _ ↦ by simp⟩

/-- The zero field is odd axisymmetric. -/
theorem isOddAxisymmetric_zero : IsOddAxisymmetric 0 :=
  ⟨fun _ ↦ Filter.Eventually.of_forall fun _ ↦ by simp,
    Filter.Eventually.of_forall fun _ ↦ by simp⟩

/-- Even axisymmetric fields are closed under addition. -/
theorem IsEvenAxisymmetric.add {u v : ℝ^3 → ℝ^3} (hu : IsEvenAxisymmetric u)
    (hv : IsEvenAxisymmetric v) : IsEvenAxisymmetric (u + v) := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · filter_upwards [hu.1 θ, hv.1 θ] with x hux hvx
    simp only [Pi.add_apply, map_add] at hux hvx ⊢
    rw [hux, hvx]
  · filter_upwards [hu.2, hv.2] with x hux hvx
    simp only [Pi.add_apply, map_add] at hux hvx ⊢
    rw [hux, hvx]

/-- Odd axisymmetric fields are closed under addition. -/
theorem IsOddAxisymmetric.add {u v : ℝ^3 → ℝ^3} (hu : IsOddAxisymmetric u)
    (hv : IsOddAxisymmetric v) : IsOddAxisymmetric (u + v) := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · filter_upwards [hu.1 θ, hv.1 θ] with x hux hvx
    simp only [Pi.add_apply, map_add] at hux hvx ⊢
    rw [hux, hvx]
  · filter_upwards [hu.2, hv.2] with x hux hvx
    simp only [Pi.add_apply, Pi.neg_apply, map_add] at hux hvx ⊢
    rw [hux, hvx, neg_add]

/-- Even axisymmetric fields are closed under scalar multiplication. -/
theorem IsEvenAxisymmetric.smul {u : ℝ^3 → ℝ^3} (c : ℝ) (hu : IsEvenAxisymmetric u) :
    IsEvenAxisymmetric (c • u) := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · filter_upwards [hu.1 θ] with x hux
    simp only [Pi.smul_apply, map_smul] at hux ⊢
    rw [hux]
  · filter_upwards [hu.2] with x hux
    simp only [Pi.smul_apply, map_smul] at hux ⊢
    rw [hux]

/-- Odd axisymmetric fields are closed under scalar multiplication. -/
theorem IsOddAxisymmetric.smul {u : ℝ^3 → ℝ^3} (c : ℝ) (hu : IsOddAxisymmetric u) :
    IsOddAxisymmetric (c • u) := by
  refine ⟨fun θ ↦ ?_, ?_⟩
  · filter_upwards [hu.1 θ] with x hux
    simp only [Pi.smul_apply, map_smul] at hux ⊢
    rw [hux]
  · filter_upwards [hu.2] with x hux
    simp only [Pi.smul_apply, Pi.neg_apply, map_smul] at hux ⊢
    rw [hux, smul_neg]

/-- A field that is equivariant at every point under the rotations and the reflection is even
axisymmetric. -/
theorem IsEvenAxisymmetric.of_forall {u : ℝ^3 → ℝ^3}
    (hrot : ∀ θ x, u (axialRotation θ x) = axialRotation θ (u x))
    (hrefl : ∀ x, u (equatorialReflection x) = equatorialReflection (u x)) :
    IsEvenAxisymmetric u := by
  refine ⟨fun θ ↦ Filter.Eventually.of_forall fun x ↦ ?_,
    Filter.Eventually.of_forall fun x ↦ ?_⟩
  · have h := hrot θ ((axialRotation θ).symm x)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  · simp only [hrefl, PDE.CoordinateSystems.equatorialReflection_equatorialReflection]

/-- A field that is rotation equivariant and reflection antiequivariant at every point is odd
axisymmetric. -/
theorem IsOddAxisymmetric.of_forall {u : ℝ^3 → ℝ^3}
    (hrot : ∀ θ x, u (axialRotation θ x) = axialRotation θ (u x))
    (hrefl : ∀ x, u (equatorialReflection x) = -equatorialReflection (u x)) :
    IsOddAxisymmetric u := by
  refine ⟨fun θ ↦ Filter.Eventually.of_forall fun x ↦ ?_,
    Filter.Eventually.of_forall fun x ↦ ?_⟩
  · have h := hrot θ ((axialRotation θ).symm x)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  · simp only [hrefl, map_neg, PDE.CoordinateSystems.equatorialReflection_equatorialReflection,
      Pi.neg_apply]

/-! ### Sectors on a ball -/

/-- The zero extension to `ℝ^3` of the value of a zero-boundary vector field on the ball
`B(0,ρ)`: the chosen `L²` representative on the ball and zero outside it. -/
def ballField (ρ : ℝ) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3 :=
  (Metric.ball (0 : ℝ^3) ρ).indicator (ZeroBoundaryVectorSpace.toLp u)

/-- The zero extension of a sum is the sum of the zero extensions, almost everywhere. -/
theorem ballField_add_ae (ρ : ℝ) (u v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ballField ρ (u + v) =ᵐ[volume] ballField ρ u + ballField ρ v := by
  have h := Lp.coeFn_add (ZeroBoundaryVectorSpace.toLp u) (ZeroBoundaryVectorSpace.toLp v)
  rw [ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet] at h
  filter_upwards [h] with x hx
  by_cases hb : x ∈ Metric.ball (0 : ℝ^3) ρ
  · simpa only [ballField, map_add, Pi.add_apply, Set.indicator_of_mem hb] using hx
  · simp only [ballField, Pi.add_apply, Set.indicator_of_notMem hb, add_zero]

/-- The zero extension of a scalar multiple is the multiple of the zero extension, almost
everywhere. -/
theorem ballField_smul_ae (ρ c : ℝ) (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ballField ρ (c • u) =ᵐ[volume] c • ballField ρ u := by
  have h := Lp.coeFn_smul c (ZeroBoundaryVectorSpace.toLp u)
  rw [ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet] at h
  filter_upwards [h] with x hx
  by_cases hb : x ∈ Metric.ball (0 : ℝ^3) ρ
  · simpa only [ballField, map_smul, Pi.smul_apply, Set.indicator_of_mem hb] using hx
  · simp only [ballField, Pi.smul_apply, Set.indicator_of_notMem hb, smul_zero]

/-- The zero extension of the zero field vanishes almost everywhere. -/
theorem ballField_zero_ae (ρ : ℝ) : ballField ρ 0 =ᵐ[volume] 0 := by
  have h := Lp.coeFn_zero (ℝ^3) 2 (domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ))
  rw [ae_eq_restrict_iff_indicator_ae_eq Metric.isOpen_ball.measurableSet] at h
  filter_upwards [h] with x hx
  by_cases hb : x ∈ Metric.ball (0 : ℝ^3) ρ
  · simpa only [ballField, map_zero, Pi.zero_apply, Set.indicator_of_mem hb] using hx
  · simp only [ballField, Pi.zero_apply, Set.indicator_of_notMem hb]

/-- The even axisymmetric sector of the solenoidal zero-boundary space on `B(0,ρ)`: the fields
whose zero extension `ballField ρ u` is even axisymmetric. -/
def evenSector (ρ : ℝ) : Submodule ℝ (IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))) where
  carrier := {u | IsEvenAxisymmetric (ballField ρ u)}
  zero_mem' := isEvenAxisymmetric_zero.congr_ae (ballField_zero_ae ρ).symm
  add_mem' {u v} hu hv := (IsEvenAxisymmetric.add hu hv).congr_ae
    (ballField_add_ae ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) v).symm
  smul_mem' c u hu := (IsEvenAxisymmetric.smul c hu).congr_ae
    (ballField_smul_ae ρ c (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))).symm

/-- The odd axisymmetric sector of the solenoidal zero-boundary space on `B(0,ρ)`: the fields
whose zero extension `ballField ρ u` is odd axisymmetric. -/
def oddSector (ρ : ℝ) : Submodule ℝ (IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))) where
  carrier := {u | IsOddAxisymmetric (ballField ρ u)}
  zero_mem' := isOddAxisymmetric_zero.congr_ae (ballField_zero_ae ρ).symm
  add_mem' {u v} hu hv := (IsOddAxisymmetric.add hu hv).congr_ae
    (ballField_add_ae ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) v).symm
  smul_mem' c u hu := (IsOddAxisymmetric.smul c hu).congr_ae
    (ballField_smul_ae ρ c (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))).symm

/-- Membership in the even sector on a ball is even axisymmetry of the zero extension. -/
theorem mem_evenSector_iff {ρ : ℝ} {u : IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))} :
    u ∈ evenSector ρ ↔ IsEvenAxisymmetric (ballField ρ u) :=
  Iff.rfl

/-- Membership in the odd sector on a ball is odd axisymmetry of the zero extension. -/
theorem mem_oddSector_iff {ρ : ℝ} {u : IncompressibleFlow.SolenoidalSpace
    (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))} :
    u ∈ oddSector ρ ↔ IsOddAxisymmetric (ballField ρ u) :=
  Iff.rfl

/-! ### Sectors of whole-space `H¹` velocities -/

/-- The even axisymmetric sector of the whole-space `H¹` velocity space: the fields whose
representative `Stationary.representative w` is even axisymmetric. -/
def evenSectorH1 : Submodule ℝ (PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) where
  carrier := {w | IsEvenAxisymmetric (Stationary.representative w)}
  zero_mem' := isEvenAxisymmetric_zero.congr_ae Stationary.representative_zero_ae.symm
  add_mem' {v w} hv hw := (IsEvenAxisymmetric.add hv hw).congr_ae
    (Stationary.representative_add_ae v w).symm
  smul_mem' c w hw := (IsEvenAxisymmetric.smul c hw).congr_ae
    (Stationary.representative_smul_ae c w).symm

/-- The odd axisymmetric sector of the whole-space `H¹` velocity space: the fields whose
representative `Stationary.representative w` is odd axisymmetric. -/
def oddSectorH1 : Submodule ℝ (PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) where
  carrier := {w | IsOddAxisymmetric (Stationary.representative w)}
  zero_mem' := isOddAxisymmetric_zero.congr_ae Stationary.representative_zero_ae.symm
  add_mem' {v w} hv hw := (IsOddAxisymmetric.add hv hw).congr_ae
    (Stationary.representative_add_ae v w).symm
  smul_mem' c w hw := (IsOddAxisymmetric.smul c hw).congr_ae
    (Stationary.representative_smul_ae c w).symm

/-- Membership in the even whole-space sector is even axisymmetry of the representative. -/
theorem mem_evenSectorH1_iff {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} :
    w ∈ evenSectorH1 ↔ IsEvenAxisymmetric (Stationary.representative w) :=
  Iff.rfl

/-- Membership in the odd whole-space sector is odd axisymmetry of the representative. -/
theorem mem_oddSectorH1_iff {w : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} :
    w ∈ oddSectorH1 ↔ IsOddAxisymmetric (Stationary.representative w) :=
  Iff.rfl

end NavierStokes.Nonuniqueness
