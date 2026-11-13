/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D.Noncharacteristic
public import PDE.Hyperbolic.Classical.CanonicalForm2D.Shear

/-!
# Characteristic maps for a general strictly hyperbolic principal part

A fixed shear first makes the initial line noncharacteristic. The two scalar ODE
families then construct coordinates in that plane, and their pullbacks give the
coordinates in the original variables. The pure coefficients may vanish in the original coordinates.

`exists_characteristic_map` constructs the map `Φ = (Φ¹, Φ²)` of Evans, §7.2.5, for a
hyperbolic equation (89), with `DΦ` invertible and `ã¹¹ = ã²² = 0` as in (86)-(87). Evans
assumes that the components can be chosen as solutions of the factors (91₁) and (91₂) of the
characteristic equation (88), constant along the characteristics (92) and (93); we build them
from the two families of characteristic curves, after a shear that makes `a¹¹ ≠ 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.5, equations (86)-(93).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter
open scoped Topology
open PDE.Analysis

namespace Hyperbolic.CanonicalForm2D

/-- Local C² coefficients and strict hyperbolicity construct independent
characteristic coordinates. The identities hold on a neighborhood of the base point. -/
theorem exists_characteristic_map {A : ℝ^2 → PrincipalPart} {x : ℝ^2}
    (h₁₁ : ContDiffAt ℝ 2 (fun y ↦ (A y).a11) x) (h₁₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a12) x)
    (h₂₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a22) x) (hA : (A x).IsHyperbolic) :
    ∃ Φ : ℝ^2 → ℝ^2, ContDiffAt ℝ 2 Φ x ∧ (jacobianMatrix Φ x).det ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, (transformedPrincipal A Φ y).a11 = 0 ∧
        (transformedPrincipal A Φ y).a22 = 0) := by
  obtain ⟨k, hk⟩ := (A x).exists_shear_a11_ne_zero hA
  let B : ℝ^2 → PrincipalPart := fun z ↦ (A (shearCoordinates (-k) z)).shear k
  have hraw₁₁ : ContDiffAt ℝ 2 (fun z ↦ (A (shearCoordinates (-k) z)).a11)
      (shearCoordinates k x) := by
    have h : ContDiffAt ℝ 2 (fun z ↦ (A z).a11)
        (shearCoordinates (-k) (shearCoordinates k x)) := by
      simpa only [shearCoordinates_neg_apply] using h₁₁
    exact h.comp _ (contDiffAt_shearCoordinates (-k) _)
  have hraw₁₂ : ContDiffAt ℝ 2 (fun z ↦ (A (shearCoordinates (-k) z)).a12)
      (shearCoordinates k x) := by
    have h : ContDiffAt ℝ 2 (fun z ↦ (A z).a12)
        (shearCoordinates (-k) (shearCoordinates k x)) := by
      simpa only [shearCoordinates_neg_apply] using h₁₂
    exact h.comp _ (contDiffAt_shearCoordinates (-k) _)
  have hraw₂₂ : ContDiffAt ℝ 2 (fun z ↦ (A (shearCoordinates (-k) z)).a22)
      (shearCoordinates k x) := by
    have h : ContDiffAt ℝ 2 (fun z ↦ (A z).a22)
        (shearCoordinates (-k) (shearCoordinates k x)) := by
      simpa only [shearCoordinates_neg_apply] using h₂₂
    exact h.comp _ (contDiffAt_shearCoordinates (-k) _)
  have hB₁₁ : ContDiffAt ℝ 2 (fun z ↦ (B z).a11) (shearCoordinates k x) :=
    (hraw₁₁.add (contDiffAt_const.mul hraw₁₂)).add (contDiffAt_const.mul hraw₂₂)
  have hB₁₂ : ContDiffAt ℝ 2 (fun z ↦ (B z).a12) (shearCoordinates k x) :=
    hraw₁₂.add (contDiffAt_const.mul hraw₂₂)
  have hBa : (B (shearCoordinates k x)).a11 ≠ 0 := by
    simpa only [B, shearCoordinates_neg_apply] using hk
  have hB : (B (shearCoordinates k x)).IsHyperbolic := by
    rw [PrincipalPart.isHyperbolic_iff_discriminant_pos]
    simpa only [B, shearCoordinates_neg_apply, PrincipalPart.discriminant_shear] using
      (A x).isHyperbolic_iff_discriminant_pos.mp hA
  obtain ⟨F, hF, hdet, hnull⟩ := exists_characteristic_map_of_a11_ne_zero hB₁₁ hB₁₂ hraw₂₂ hBa hB
  refine ⟨F ∘ shearCoordinates k, hF.comp x (contDiffAt_shearCoordinates k x), ?_, ?_⟩
  · rwa [det_jacobianMatrix_comp_shearCoordinates k F x
      (hF.differentiableAt (by norm_num))]
  · have ht : ContinuousAt (shearCoordinates k) x :=
      (contDiffAt_shearCoordinates k x (r := 1)).continuousAt
    filter_upwards [ht.eventually hnull, ht.eventually (hF.eventually (by norm_num))] with y hy hFy
    have hquadratic (j : Fin 2) : (A y).quadratic ((∂[0] (fun z ↦ F (shearCoordinates k z) j)) y)
            ((∂[1] (fun z ↦ F (shearCoordinates k z) j)) y) = (B (shearCoordinates k y)).quadratic
            ((∂[0] (fun z ↦ F z j)) (shearCoordinates k y))
            ((∂[1] (fun z ↦ F z j)) (shearCoordinates k y)) := by
      have hj : DifferentiableAt ℝ (fun z ↦ F z j) (shearCoordinates k y) :=
        (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).differentiableAt.comp _
          (hFy.differentiableAt (by norm_num))
      change (A y).quadratic ((∂[0] ((fun z ↦ F z j) ∘ shearCoordinates k)) y)
          ((∂[1] ((fun z ↦ F z j) ∘ shearCoordinates k)) y) = _
      rw [partialDeriv_zero_comp_shearCoordinates k _ y hj,
        partialDeriv_one_comp_shearCoordinates k _ y hj]
      simp only [B, shearCoordinates_neg_apply, PrincipalPart.quadratic_shear]
    exact ⟨(hquadratic 0).trans hy.1, (hquadratic 1).trans hy.2⟩

end Hyperbolic.CanonicalForm2D
