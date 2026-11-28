/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import PDE.CalculusOfVariations.SlopeField.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Slope fields with a closed form

## Motivation

Which slope fields `p(x, y)` have an invariant integral that is independent of the path, and
what does this have to do with the Euler–Lagrange equation?

## The idea

Write the form of the field as `ω = A dy - B dx`, with the momentum `A = L_q(x, y, p)` and the
energy `B = A p - L(x, y, p)`. The form is closed when its derivative is symmetric. In terms of
`A` and `B` this is two conditions: `D_y A` is symmetric, and `∂A/∂x + D_y B = 0`. For one
unknown function the first condition is empty and the second is a first-order partial
differential equation for `p`. On a convex open region a closed form is the differential of a
function, by the Poincaré lemma, so the field has an eikonal and its invariant integral is
independent of the path.

Differentiating `B = A p - L(x, y, p)` in `y`, the terms with the derivative of `p` cancel,
because `A` is the derivative of `L` in the slope: `D_y B = (D_y A) p - L_y`. Along a curve
`y' = p(x, y)` of the field, `d/dx A(x, y(x)) = ∂A/∂x + (D_y A) p`. So, given the symmetry,
`∂A/∂x + D_y B = 0` at a point says exactly that the curve of the field through the point
satisfies the Euler–Lagrange equation `d/dx L_q = L_y` there.

## Main results

* `exists_isEikonal_of_convex` (all fields on convex open regions): a field whose form is
  differentiable and closed has an eikonal.
* `isClosedAt_iff` (all): closedness in terms of the momentum and the energy.
* `isClosedAt_iff_real`, `isClosedAt_iff_deriv` (one unknown function): closedness is the
  single equation `∂A/∂x + ∂B/∂y = 0`, with Fréchet derivatives and with partial derivatives.
* `IsClosedAt.hasDerivAt_momentum` (all): on a closed field, along a curve that is tangent to
  the field at a point the momentum of the field has the derivative `L_y` there. For a curve
  that follows the field near the point this is the Euler–Lagrange equation.
* `isClosedAt_of_hasDerivAt_momentum` (all fields with symmetric `D_y A`),
  `isClosedAt_iff_hasDerivAt_momentum_real` and `isClosedAt_iff_hasDerivAt_deriv` (one unknown
  function): the converse, and the equivalence for one unknown function.

## Relations

* `exists_isEikonal_of_convex` is Mathlib's
  `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric` for the form of a slope field. Its
  conclusion is the premise `IsEikonal` of every theorem of
  `PDE.CalculusOfVariations.SlopeField.Basic`.
* `isClosedAt_iff_real` is `isClosedAt_iff` for `E = ℝ`, and
  `isClosedAt_iff_hasDerivAt_momentum_real` joins `IsClosedAt.hasDerivAt_momentum` and
  `isClosedAt_of_hasDerivAt_momentum` for `E = ℝ`. `isClosedAt_iff_deriv` and
  `isClosedAt_iff_hasDerivAt_deriv` restate these two with the partial derivatives of real
  functions.
* `PDE.CalculusOfVariations.eulerLagrange_of_curveAction_min` derives the same Euler–Lagrange
  equation for a minimizing curve when `L` does not depend on `x`.

## What stays open

An eikonal on a region that is simply connected but not convex. Mathlib's Poincaré lemma for
1-forms is for convex sets.
-/

@[expose] public noncomputable section

open Set

namespace PDE.CalculusOfVariations.SlopeField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : ℝ × E → E → ℝ} {p : ℝ × E → E} {D : Set (ℝ × E)} {z : ℝ × E}

/-- The form of the slope field `p` is closed at `z`: its derivative there is symmetric. -/
def IsClosedAt (L : ℝ × E → E → ℝ) (p : ℝ × E → E) (z : ℝ × E) : Prop :=
  ∀ u v : ℝ × E, fderiv ℝ (beltramiForm L p) z u v = fderiv ℝ (beltramiForm L p) z v u

/-- A slope field on a convex open region whose form is differentiable and closed has an
eikonal. This is the Poincaré lemma for the form of the field. -/
theorem exists_isEikonal_of_convex (hD : Convex ℝ D) (hDo : IsOpen D)
    (hω : DifferentiableOn ℝ (beltramiForm L p) D) (hclosed : ∀ z ∈ D, IsClosedAt L p z) :
    ∃ S, IsEikonal L p D S :=
  hD.exists_forall_hasFDerivAt_of_fderiv_symmetric hDo hω hclosed

/-- The derivative of the form of the field, from the derivatives of the momentum and of the
energy. -/
theorem hasFDerivAt_beltramiForm {A' : ℝ × E →L[ℝ] E →L[ℝ] ℝ} {B' : ℝ × E →L[ℝ] ℝ}
    (hA : HasFDerivAt (momentum L p) A' z) (hB : HasFDerivAt (energy L p) B' z) :
    HasFDerivAt (beltramiForm L p)
      (((ContinuousLinearMap.compL ℝ (ℝ × E) E ℝ).flip (ContinuousLinearMap.snd ℝ ℝ E)).comp A' -
        (ContinuousLinearMap.toSpanSingleton ℝ (ContinuousLinearMap.fst ℝ ℝ E)).comp B') z := by
  have h1 := ((ContinuousLinearMap.compL ℝ (ℝ × E) E ℝ).flip
    (ContinuousLinearMap.snd ℝ ℝ E)).hasFDerivAt.comp z hA
  have h2 := (ContinuousLinearMap.toSpanSingleton ℝ
    (ContinuousLinearMap.fst ℝ ℝ E)).hasFDerivAt.comp z hB
  exact h1.sub h2

/-- The form of the field is differentiable where the momentum and the energy are. -/
theorem differentiableAt_beltramiForm (hA : DifferentiableAt ℝ (momentum L p) z)
    (hB : DifferentiableAt ℝ (energy L p) z) : DifferentiableAt ℝ (beltramiForm L p) z :=
  (hasFDerivAt_beltramiForm hA.hasFDerivAt hB.hasFDerivAt).differentiableAt

/-- The derivative of the form of the field on two vectors. -/
theorem fderiv_beltramiForm_apply (hA : DifferentiableAt ℝ (momentum L p) z)
    (hB : DifferentiableAt ℝ (energy L p) z) (u v : ℝ × E) :
    fderiv ℝ (beltramiForm L p) z u v =
      fderiv ℝ (momentum L p) z u v.2 - fderiv ℝ (energy L p) z u * v.1 := by
  rw [(hasFDerivAt_beltramiForm hA.hasFDerivAt hB.hasFDerivAt).fderiv]
  simp

/-- Closedness of the form of a slope field in terms of the momentum `A` and the energy `B`:
the derivative of `A` in `y` is symmetric, and `∂A/∂x + D_y B = 0`. -/
theorem isClosedAt_iff (hA : DifferentiableAt ℝ (momentum L p) z)
    (hB : DifferentiableAt ℝ (energy L p) z) :
    IsClosedAt L p z ↔
      (∀ w₁ w₂ : E, fderiv ℝ (momentum L p) z (0, w₁) w₂ =
        fderiv ℝ (momentum L p) z (0, w₂) w₁) ∧
      ∀ w : E, fderiv ℝ (momentum L p) z (1, 0) w + fderiv ℝ (energy L p) z (0, w) = 0 := by
  constructor
  · intro h
    refine ⟨fun w₁ w₂ ↦ ?_, fun w ↦ ?_⟩
    · have h' := h (0, w₁) (0, w₂)
      rw [fderiv_beltramiForm_apply hA hB, fderiv_beltramiForm_apply hA hB] at h'
      simpa using h'
    · have h' := h (1, 0) (0, w)
      rw [fderiv_beltramiForm_apply hA hB, fderiv_beltramiForm_apply hA hB] at h'
      simp only [mul_zero, sub_zero, map_zero, mul_one, zero_sub] at h'
      linarith
  · rintro ⟨hsymm, hx⟩ u v
    have hA' (w : ℝ × E) : fderiv ℝ (momentum L p) z w =
        w.1 • fderiv ℝ (momentum L p) z (1, 0) + fderiv ℝ (momentum L p) z (0, w.2) := by
      rw [← map_smul, ← map_add]
      simp
    have hB' (w : ℝ × E) : fderiv ℝ (energy L p) z w =
        w.1 * fderiv ℝ (energy L p) z (1, 0) + fderiv ℝ (energy L p) z (0, w.2) := by
      rw [← smul_eq_mul, ← map_smul, ← map_add]
      simp
    rw [fderiv_beltramiForm_apply hA hB, fderiv_beltramiForm_apply hA hB, hA' u, hA' v,
      hB' u, hB' v]
    simp only [add_apply, smul_apply, smul_eq_mul]
    linear_combination u.1 * hx v.2 - v.1 * hx u.2 + hsymm u.2 v.2

/-- The derivative of the energy of a slope field: `B' v = (A' v) p - L_z v`. The terms with the
derivative of `p` cancel because the momentum is the derivative of `L` in the slope. -/
theorem hasFDerivAt_energy {A' : ℝ × E →L[ℝ] E →L[ℝ] ℝ} {p' : ℝ × E →L[ℝ] E}
    {ℓ : (ℝ × E) × E →L[ℝ] ℝ}
    (hL : HasFDerivAt (fun w : (ℝ × E) × E ↦ L w.1 w.2) ℓ (z, p z))
    (hp : HasFDerivAt p p' z) (hA : HasFDerivAt (momentum L p) A' z) :
    HasFDerivAt (energy L p)
      (A'.flip (p z) - ℓ.comp (ContinuousLinearMap.inl ℝ (ℝ × E) E)) z := by
  have h1 : HasFDerivAt (fun z ↦ momentum L p z (p z))
      ((momentum L p z).comp p' + A'.flip (p z)) z := hA.clm_apply hp
  have hpair : HasFDerivAt (fun z ↦ (z, p z)) ((ContinuousLinearMap.id ℝ (ℝ × E)).prod p') z :=
    (hasFDerivAt_id z).prodMk hp
  have h2 : HasFDerivAt (fun z ↦ L z (p z))
      (ℓ.comp ((ContinuousLinearMap.id ℝ (ℝ × E)).prod p')) z :=
    HasFDerivAt.comp (g := fun w : (ℝ × E) × E ↦ L w.1 w.2) z hL hpair
  have hslope : HasFDerivAt (L z) (ℓ.comp (ContinuousLinearMap.inr ℝ (ℝ × E) E)) (p z) :=
    HasFDerivAt.comp (g := fun w : (ℝ × E) × E ↦ L w.1 w.2) (f := fun q ↦ (z, q)) (p z) hL
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z (p z))
  have hmom : momentum L p z = ℓ.comp (ContinuousLinearMap.inr ℝ (ℝ × E) E) := hslope.fderiv
  refine (h1.sub h2).congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  have hsplit : ℓ (v, p' v) = ℓ (v, 0) + ℓ (0, p' v) := by
    rw [← map_add]
    simp
  simp only [hmom, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.inl_apply, hsplit]
  ring

/-- The energy of a slope field is differentiable where the Lagrangian, the field and the
momentum are. -/
theorem differentiableAt_energy
    (hL : DifferentiableAt ℝ (fun w : (ℝ × E) × E ↦ L w.1 w.2) (z, p z))
    (hp : DifferentiableAt ℝ p z) (hA : DifferentiableAt ℝ (momentum L p) z) :
    DifferentiableAt ℝ (energy L p) z :=
  (hasFDerivAt_energy hL.hasFDerivAt hp.hasFDerivAt hA.hasFDerivAt).differentiableAt

/-- The derivative of the energy of a slope field on a vector `v`: the derivative of the
momentum on `v`, evaluated at the slope, minus the derivative of `L` in the point at the fixed
slope `p z`. -/
theorem fderiv_energy_apply
    (hL : DifferentiableAt ℝ (fun w : (ℝ × E) × E ↦ L w.1 w.2) (z, p z))
    (hp : DifferentiableAt ℝ p z) (hA : DifferentiableAt ℝ (momentum L p) z) (v : ℝ × E) :
    fderiv ℝ (energy L p) z v =
      fderiv ℝ (momentum L p) z v (p z) - fderiv ℝ (fun z' ↦ L z' (p z)) z v := by
  have hz : HasFDerivAt (fun z' ↦ L z' (p z))
      ((fderiv ℝ (fun w : (ℝ × E) × E ↦ L w.1 w.2) (z, p z)).comp
        (ContinuousLinearMap.inl ℝ (ℝ × E) E)) z :=
    HasFDerivAt.comp (g := fun w : (ℝ × E) × E ↦ L w.1 w.2) (f := fun z' ↦ (z', p z)) z
      hL.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) z (p z))
  rw [(hasFDerivAt_energy hL.hasFDerivAt hp.hasFDerivAt hA.hasFDerivAt).fderiv, hz.fderiv]
  rfl

section FieldCurve

variable {x₀ : ℝ} {y₀ : ℝ → E}

/-- The derivative of the momentum along a curve of the field, on a vector `w`. -/
private theorem hasDerivAt_momentum_curve
    (hA : DifferentiableAt ℝ (momentum L p) (x₀, y₀ x₀))
    (hy₀ : HasDerivAt y₀ (p (x₀, y₀ x₀)) x₀) (w : E) :
    HasDerivAt (fun x ↦ momentum L p (x, y₀ x) w)
      (fderiv ℝ (momentum L p) (x₀, y₀ x₀) (1, 0) w +
        fderiv ℝ (momentum L p) (x₀, y₀ x₀) (0, p (x₀, y₀ x₀)) w) x₀ := by
  have hγ : HasDerivAt (fun x ↦ (x, y₀ x)) (1, p (x₀, y₀ x₀)) x₀ :=
    (hasDerivAt_id x₀).prodMk hy₀
  have h1 : HasDerivAt (fun x ↦ momentum L p (x, y₀ x))
      (fderiv ℝ (momentum L p) (x₀, y₀ x₀) (1, p (x₀, y₀ x₀))) x₀ :=
    HasFDerivAt.comp_hasDerivAt (l := momentum L p) (f := fun x ↦ (x, y₀ x)) x₀
      hA.hasFDerivAt hγ
  have h2 := h1.clm_apply (hasDerivAt_const x₀ w)
  have hsplit : fderiv ℝ (momentum L p) (x₀, y₀ x₀) (1, p (x₀, y₀ x₀)) =
      fderiv ℝ (momentum L p) (x₀, y₀ x₀) (1, 0) +
        fderiv ℝ (momentum L p) (x₀, y₀ x₀) (0, p (x₀, y₀ x₀)) := by
    rw [← map_add]
    simp
  simpa only [hsplit, map_zero, add_zero, add_apply] using h2

/-- On a slope field with a closed form, a curve `y₀` that is tangent to the field at a point
satisfies `d/dx L_q(x, y₀, p) w = L_y(x, y₀, p) w` there, for every direction `w`, where `p`
is the slope of the field along the curve. Only tangency at the point is assumed. For a curve
that follows the field near the point, `p` is its own slope and this is the Euler–Lagrange
equation. The derivative of the momentum along the curve is `∂A/∂x + (D_y A) p`; closedness
and the formula for the derivative of the energy turn it into `L_y`. -/
theorem IsClosedAt.hasDerivAt_momentum (hclosed : IsClosedAt L p (x₀, y₀ x₀))
    (hL : DifferentiableAt ℝ (fun w : (ℝ × E) × E ↦ L w.1 w.2)
      ((x₀, y₀ x₀), p (x₀, y₀ x₀)))
    (hp : DifferentiableAt ℝ p (x₀, y₀ x₀))
    (hA : DifferentiableAt ℝ (momentum L p) (x₀, y₀ x₀))
    (hy₀ : HasDerivAt y₀ (p (x₀, y₀ x₀)) x₀) (w : E) :
    HasDerivAt (fun x ↦ momentum L p (x, y₀ x) w)
      (fderiv ℝ (fun z ↦ L z (p (x₀, y₀ x₀))) (x₀, y₀ x₀) (0, w)) x₀ := by
  obtain ⟨hsymm, hx⟩ := (isClosedAt_iff hA (differentiableAt_energy hL hp hA)).mp hclosed
  convert hasDerivAt_momentum_curve hA hy₀ w using 1
  have h := hx w
  rw [fderiv_energy_apply hL hp hA] at h
  rw [hsymm (p (x₀, y₀ x₀)) w]
  linarith

/-- If the derivative of the momentum in `y` is symmetric at a point and, along a curve that
is tangent to the field at the point, the momentum of the field has the derivative `L_y`
there, the form of the field is closed at the point. For a curve that follows the field near
the point the hypothesis is the Euler–Lagrange equation. -/
theorem isClosedAt_of_hasDerivAt_momentum
    (hsymm : ∀ w₁ w₂ : E, fderiv ℝ (momentum L p) (x₀, y₀ x₀) (0, w₁) w₂ =
      fderiv ℝ (momentum L p) (x₀, y₀ x₀) (0, w₂) w₁)
    (hL : DifferentiableAt ℝ (fun w : (ℝ × E) × E ↦ L w.1 w.2)
      ((x₀, y₀ x₀), p (x₀, y₀ x₀)))
    (hp : DifferentiableAt ℝ p (x₀, y₀ x₀))
    (hA : DifferentiableAt ℝ (momentum L p) (x₀, y₀ x₀))
    (hy₀ : HasDerivAt y₀ (p (x₀, y₀ x₀)) x₀)
    (hEL : ∀ w : E, HasDerivAt (fun x ↦ momentum L p (x, y₀ x) w)
      (fderiv ℝ (fun z ↦ L z (p (x₀, y₀ x₀))) (x₀, y₀ x₀) (0, w)) x₀) :
    IsClosedAt L p (x₀, y₀ x₀) := by
  refine (isClosedAt_iff hA (differentiableAt_energy hL hp hA)).mpr ⟨hsymm, fun w ↦ ?_⟩
  have h := (hEL w).unique (hasDerivAt_momentum_curve hA hy₀ w)
  rw [fderiv_energy_apply hL hp hA, hsymm w (p (x₀, y₀ x₀))]
  linarith

end FieldCurve

section Real

variable {L : ℝ × ℝ → ℝ → ℝ} {p : ℝ × ℝ → ℝ} {z : ℝ × ℝ}

/-- For one unknown function the form of a slope field is closed exactly when
`∂A/∂x + ∂B/∂y = 0`, with the momentum `A` and the energy `B` of the field. -/
theorem isClosedAt_iff_real (hA : DifferentiableAt ℝ (momentum L p) z)
    (hB : DifferentiableAt ℝ (energy L p) z) :
    IsClosedAt L p z ↔
      fderiv ℝ (momentum L p) z (1, 0) 1 + fderiv ℝ (energy L p) z (0, 1) = 0 := by
  have hy (w : ℝ) : ((0 : ℝ), w) = w • ((0 : ℝ), (1 : ℝ)) := by simp
  have hone (f : ℝ →L[ℝ] ℝ) (w : ℝ) : f w = w * f 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [isClosedAt_iff hA hB]
  constructor
  · exact fun h ↦ h.2 1
  · intro h
    refine ⟨fun w₁ w₂ ↦ ?_, fun w ↦ ?_⟩
    · rw [hy w₁, hy w₂, map_smul, map_smul, smul_apply,
        smul_apply, hone _ w₂, hone _ w₁, smul_eq_mul, smul_eq_mul]
      ring
    · rw [hy w, map_smul, hone _ w, smul_eq_mul]
      linear_combination w * h

variable {x₀ : ℝ} {y₀ : ℝ → ℝ}

/-- For one unknown function and a curve that is tangent to the slope field at a point, the
form of the field is closed at the point exactly when the momentum of the field along the
curve has the derivative `L_y` there. For a curve that follows the field near the point this
is the Euler–Lagrange equation. -/
theorem isClosedAt_iff_hasDerivAt_momentum_real
    (hL : DifferentiableAt ℝ (fun w : (ℝ × ℝ) × ℝ ↦ L w.1 w.2)
      ((x₀, y₀ x₀), p (x₀, y₀ x₀)))
    (hp : DifferentiableAt ℝ p (x₀, y₀ x₀))
    (hA : DifferentiableAt ℝ (momentum L p) (x₀, y₀ x₀))
    (hy₀ : HasDerivAt y₀ (p (x₀, y₀ x₀)) x₀) :
    IsClosedAt L p (x₀, y₀ x₀) ↔
      HasDerivAt (fun x ↦ momentum L p (x, y₀ x) 1)
        (fderiv ℝ (fun z ↦ L z (p (x₀, y₀ x₀))) (x₀, y₀ x₀) (0, 1)) x₀ := by
  have hy (w : ℝ) : ((0 : ℝ), w) = w • ((0 : ℝ), (1 : ℝ)) := by simp
  have hone (f : ℝ →L[ℝ] ℝ) (w : ℝ) : f w = w * f 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  refine ⟨fun h ↦ h.hasDerivAt_momentum hL hp hA hy₀ 1, fun h ↦ ?_⟩
  refine isClosedAt_of_hasDerivAt_momentum (fun w₁ w₂ ↦ ?_) hL hp hA hy₀ fun w ↦ ?_
  · rw [hy w₁, hy w₂, map_smul, map_smul, smul_apply,
      smul_apply, hone _ w₂, hone _ w₁, smul_eq_mul, smul_eq_mul]
    ring
  · have h' := h.const_mul w
    rw [hy w, map_smul, smul_eq_mul]
    exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ hone _ w)

/-- For one unknown function the momentum of a slope field is multiplication by
`L_q(z, p z)`. -/
theorem momentum_apply_real (z : ℝ × ℝ) (w : ℝ) :
    momentum L p z w = w * deriv (L z) (p z) := by
  rw [momentum, fderiv_eq_smul_deriv, smul_eq_mul]

/-- For one unknown function the energy of a slope field is `p L_q(z, p) - L(z, p)`. -/
theorem energy_eq_real (z : ℝ × ℝ) :
    energy L p z = p z * deriv (L z) (p z) - L z (p z) := by
  rw [energy, momentum_apply_real]

/-- For one unknown function the momentum, as a linear map, is the image of the number
`L_q(z, p z)` under a fixed continuous linear map. -/
private theorem momentum_eq_smulRightL :
    momentum L p = fun z ↦ ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
      (deriv (L z) (p z)) := by
  funext z
  ext
  simp [momentum_apply_real]

/-- For one unknown function the momentum is differentiable where `z ↦ L_q(z, p z)` is. -/
theorem differentiableAt_momentum_real
    (hA : DifferentiableAt ℝ (fun z ↦ deriv (L z) (p z)) z) :
    DifferentiableAt ℝ (momentum L p) z := by
  rw [momentum_eq_smulRightL]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).differentiableAt.comp z hA

/-- For one unknown function the derivative of the momentum is the derivative of
`z ↦ L_q(z, p z)`. -/
theorem fderiv_momentum_apply_real
    (hA : DifferentiableAt ℝ (fun z ↦ deriv (L z) (p z)) z) (u : ℝ × ℝ) (w : ℝ) :
    fderiv ℝ (momentum L p) z u w = w * fderiv ℝ (fun z ↦ deriv (L z) (p z)) z u := by
  have h := (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt.comp z
    hA.hasFDerivAt
  rw [momentum_eq_smulRightL]
  rw [show (fun z ↦ ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
    (deriv (L z) (p z))) = (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)) ∘
      fun z ↦ deriv (L z) (p z) from rfl, h.fderiv]
  simp

/-- The derivative of a differentiable function of two real variables in the first variable. -/
private theorem fderiv_apply_one_zero {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z (1, 0) = deriv (fun x ↦ f (x, z.2)) z.1 :=
  (HasFDerivAt.comp_hasDerivAt (l := f) (f := fun x ↦ (x, z.2)) z.1 hf.hasFDerivAt
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv.symm

/-- The derivative of a differentiable function of two real variables in the second variable. -/
private theorem fderiv_apply_zero_one {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z (0, 1) = deriv (fun y ↦ f (z.1, y)) z.2 :=
  (HasFDerivAt.comp_hasDerivAt (l := f) (f := fun y ↦ (z.1, y)) z.2 hf.hasFDerivAt
    ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv.symm

/-- For one unknown function, with `A(x, y) = L_q(x, y, p(x, y))` and `B = p A - L(x, y, p)`
differentiable at a point, the form of the slope field is closed there exactly when
`∂A/∂x + ∂B/∂y = 0`. -/
theorem isClosedAt_iff_deriv (hA : DifferentiableAt ℝ (fun z ↦ deriv (L z) (p z)) z)
    (hB : DifferentiableAt ℝ (fun z ↦ p z * deriv (L z) (p z) - L z (p z)) z) :
    IsClosedAt L p z ↔
      deriv (fun x ↦ deriv (L (x, z.2)) (p (x, z.2))) z.1 +
        deriv (fun y ↦ p (z.1, y) * deriv (L (z.1, y)) (p (z.1, y)) -
          L (z.1, y) (p (z.1, y))) z.2 = 0 := by
  have hB' : DifferentiableAt ℝ (energy L p) z := by
    rwa [show energy L p = fun z ↦ p z * deriv (L z) (p z) - L z (p z) from
      funext energy_eq_real]
  rw [isClosedAt_iff_real (differentiableAt_momentum_real hA) hB',
    fderiv_momentum_apply_real hA, one_mul, fderiv_apply_one_zero hA,
    show energy L p = fun z ↦ p z * deriv (L z) (p z) - L z (p z) from funext energy_eq_real,
    fderiv_apply_zero_one hB]

/-- For one unknown function and a curve that is tangent to the slope field at a point, the
form of the field is closed at the point exactly when the derivative along the curve of the
momentum of the field, `x ↦ L_q(x, y(x), p(x, y(x)))`, equals `L_y` there. Only tangency at
the point is assumed. For a curve that follows the field near the point, the momentum of the
field along it is `L_q` at its own slope, and the condition is the Euler–Lagrange equation
`d/dx L_q = L_y`. -/
theorem isClosedAt_iff_hasDerivAt_deriv
    (hL : DifferentiableAt ℝ (fun w : (ℝ × ℝ) × ℝ ↦ L w.1 w.2)
      ((x₀, y₀ x₀), p (x₀, y₀ x₀)))
    (hp : DifferentiableAt ℝ p (x₀, y₀ x₀))
    (hA : DifferentiableAt ℝ (fun z ↦ deriv (L z) (p z)) (x₀, y₀ x₀))
    (hy₀ : HasDerivAt y₀ (p (x₀, y₀ x₀)) x₀) :
    IsClosedAt L p (x₀, y₀ x₀) ↔
      HasDerivAt (fun x ↦ deriv (L (x, y₀ x)) (p (x, y₀ x)))
        (deriv (fun y ↦ L (x₀, y) (p (x₀, y₀ x₀))) (y₀ x₀)) x₀ := by
  have hz : DifferentiableAt ℝ (fun z' ↦ L z' (p (x₀, y₀ x₀))) (x₀, y₀ x₀) :=
    (HasFDerivAt.comp (g := fun w : (ℝ × ℝ) × ℝ ↦ L w.1 w.2)
      (f := fun z' ↦ (z', p (x₀, y₀ x₀))) (x₀, y₀ x₀) hL.hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (x₀, y₀ x₀) (p (x₀, y₀ x₀)))).differentiableAt
  rw [isClosedAt_iff_hasDerivAt_momentum_real hL hp (differentiableAt_momentum_real hA) hy₀,
    fderiv_apply_zero_one hz]
  simp only [momentum_apply_real, one_mul]

end Real

end PDE.CalculusOfVariations.SlopeField
