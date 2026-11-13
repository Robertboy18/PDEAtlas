/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Complex.CircleIntegral.Conjugation
public import PDE.Analysis.InnerProductSpace.Complexification.Spectrum
public import PDE.Analysis.Spectral.RieszProjection.Idempotent

/-!
# Riesz integrals of complexified operators

Conjugation of operators is a continuous real-linear equivalence of the bounded complex operators
on `Complexification H`, and it conjugates complex scalars. If an operator `A` is fixed by
conjugation, then conjugation carries the resolvent `(z - A)⁻¹` to the resolvent at the
conjugate point, so it fixes the weighted resolvent integral

```text
rieszIntegral A R g = (2 π i)⁻¹ ∮ z in C(0, R), g z (z - A)⁻¹
```

whenever `g (conj z) = conj (g z)` on the circle. The weights `1` and `z⁻¹` give the Riesz
projection `rieszInner A R` and the outer inverse `rieszOuterInverse A R`, so for
`A = complexify T` both are complexifications of bounded real operators.
-/

@[expose] public noncomputable section

open Real PDE.Analysis.Spectral

namespace PDE.Analysis.Complexification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Conjugation of operators as a continuous real-linear equivalence. -/
def conjOpCLE :
    (Complexification H →L[ℂ] Complexification H) ≃L[ℝ]
      (Complexification H →L[ℂ] Complexification H) where
  toFun := conjOp
  invFun := conjOp
  map_add' := map_add conjOp
  map_smul' r A := by ext z <;> simp
  left_inv := conjOp_conjOp
  right_inv := conjOp_conjOp
  continuous_toFun := (AddMonoidHomClass.isometry_of_norm conjOp norm_conjOp).continuous
  continuous_invFun := (AddMonoidHomClass.isometry_of_norm conjOp norm_conjOp).continuous

@[simp]
theorem conjOpCLE_apply (A : Complexification H →L[ℂ] Complexification H) :
    conjOpCLE A = conjOp A := rfl

/-- Conjugation reverses the circle integral of an operator family that it intertwines with
complex conjugation. -/
theorem conjOp_circleIntegral {f : ℂ → Complexification H →L[ℂ] Complexification H} {R : ℝ}
    (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, conjOp (f z) = f (starRingEnd ℂ z)) :
    conjOp (∮ z in C(0, R), f z) = -∮ z in C(0, R), f z :=
  map_circleIntegral_conj (L := conjOpCLE) (fun c A ↦ conjOp_smul c A) hf

/-- Conjugation fixes `(2 π i)⁻¹ ∮ z in C(0, R), f z` for an operator family that it intertwines
with complex conjugation. -/
theorem conjOp_two_pi_I_inv_smul_circleIntegral
    {f : ℂ → Complexification H →L[ℂ] Complexification H} {R : ℝ}
    (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, conjOp (f z) = f (starRingEnd ℂ z)) :
    conjOp ((2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), f z) =
      (2 * π * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), f z :=
  map_two_pi_I_inv_smul_circleIntegral_conj (L := conjOpCLE) (fun c A ↦ conjOp_smul c A) hf

/-- If `A` is fixed by conjugation and `g (conj z) = conj (g z)` on the circle `|z| = R`, then
conjugation fixes the weighted resolvent integral `rieszIntegral A R g`. -/
theorem conjOp_rieszIntegral {A : Complexification H →L[ℂ] Complexification H}
    (hA : conjOp A = A) {g : ℂ → ℂ} {R : ℝ}
    (hg : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) :
    conjOp (rieszIntegral A R g) = rieszIntegral A R g :=
  conjOp_two_pi_I_inv_smul_circleIntegral fun z hz ↦ by
    rw [conjOp_smul, conjOp_resolvent, hA, hg z hz]

/-- The Riesz projection of an operator fixed by conjugation is fixed by conjugation. -/
theorem conjOp_rieszInner {A : Complexification H →L[ℂ] Complexification H}
    (hA : conjOp A = A) (R : ℝ) : conjOp (rieszInner A R) = rieszInner A R := by
  rw [rieszInner_eq_rieszIntegral]
  exact conjOp_rieszIntegral hA fun z _ ↦ (map_one (starRingEnd ℂ)).symm

/-- The outer inverse of an operator fixed by conjugation is fixed by conjugation. -/
theorem conjOp_rieszOuterInverse {A : Complexification H →L[ℂ] Complexification H}
    (hA : conjOp A = A) (R : ℝ) : conjOp (rieszOuterInverse A R) = rieszOuterInverse A R := by
  rw [rieszOuterInverse, map_neg, conjOp_rieszIntegral hA fun z _ ↦ (map_inv₀ _ z).symm]

/-- The Riesz projection of a complexified real operator is fixed by conjugation. -/
theorem conjOp_rieszInner_complexify (T : H →L[ℝ] H) (R : ℝ) :
    conjOp (rieszInner (complexify T) R) = rieszInner (complexify T) R :=
  conjOp_rieszInner (conjOp_complexify T) R

/-- The outer inverse of a complexified real operator is fixed by conjugation. -/
theorem conjOp_rieszOuterInverse_complexify (T : H →L[ℝ] H) (R : ℝ) :
    conjOp (rieszOuterInverse (complexify T) R) = rieszOuterInverse (complexify T) R :=
  conjOp_rieszOuterInverse (conjOp_complexify T) R

end PDE.Analysis.Complexification
