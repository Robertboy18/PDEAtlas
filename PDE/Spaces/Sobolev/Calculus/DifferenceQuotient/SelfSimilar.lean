/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Pointwise
public import PDE.Analysis.Integration.ConvolutionDrift
import PDE.Elliptic.Regularity.Interior.Weyl.SecondOrder
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Translates and difference quotients of the tested self-similar equation

A function `g` solves `(1 - n/2) g - ½ x·∇g - Δg + Σⱼ ∂ⱼNⱼ + ∂ᵢP = F` on `ℝⁿ` in the weak sense.
The drift `x·∇` does not commute with translations, so the difference quotient
`D_h g = h⁻¹ (g(· + h eₗ) - g)` solves the same equation only up to one more term. For locally
integrable data in every dimension, with `g` having a weak derivative `∂ₗg`, the difference
quotients `D_h g`, `D_h Nⱼ`, `D_h P` satisfy the tested equation with the right side
`D_h F + ½ (∂ₗg)(· + h eₗ)`. This is the identity `D_h(x·∇g) = x·∇(D_h g) + (∂ₗg)(· + h eₗ)` in
weak form. The tested equation is the hypothesis of `PDE.Analysis.mollified_similarity_eq`, so
the mollifications of the difference quotients satisfy the self-similar equation at every point.
Hou, Wang and Yang test the equation with difference quotients in this way in the proof of their
Proposition 3.

## Main results

* `integral_tested_similarity_comp_add_right`: the translates by `a` satisfy the tested
  equation with the drift direction `y + a` in place of `y`.
* `integral_tested_similarity_forwardDifference`: the difference quotients satisfy the tested
  equation with the right side `D_h F + ½ (∂ₗg)(· + h eₗ)`, for every `h ≠ 0`.

## How it works

Test with the translate `ψ(· - a)` and change variables. Every term is translated, and the drift
gives one more term, `½ g(· + a) a·∇ψ`. Subtract the equation itself and divide by `h`, with
`a = h eₗ`. The extra term is `½ g(· + h eₗ) ∂ₗψ`, which is `-½ (∂ₗg)(· + h eₗ) ψ` after an
integration by parts against the weak derivative of `g`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, the difference quotients in the
  proof of Proposition 3. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory
open PDE (laplacian)
open PDE.Analysis

namespace SobolevSpace.GraphSpace.DifferenceQuotient

variable {n : ℕ}

/-- **Translation of the tested self-similar equation.** If `(g, N, F, P)` satisfy

`∫ (g ψ + ½ g (y·∇ψ) - g Δψ - Σⱼ Nⱼ ∂ⱼψ) = ∫ F ψ + ∫ P ∂ᵢψ` for every test function `ψ`,

then the translates by `a` satisfy the same identity with `(y + a)·∇ψ` in the place of
`y·∇ψ`. -/
theorem integral_tested_similarity_comp_add_right {g F P : ℝ^n → ℝ} {N : Fin n → ℝ^n → ℝ}
    (i : Fin n)
    (htest : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y, (g y * ψ y + (1 / 2 : ℝ) * (g y * fderiv ℝ ψ y y) - g y * laplacian ψ y -
        ∑ j, N j y * ∂[j] ψ y) = (∫ y, F y * ψ y) + ∫ y, P y * ∂[i] ψ y)
    (a : ℝ^n) {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, (g (y + a) * ψ y + (1 / 2 : ℝ) * (g (y + a) * fderiv ℝ ψ y (y + a)) -
        g (y + a) * laplacian ψ y - ∑ j, N j (y + a) * ∂[j] ψ y) =
      (∫ y, F (y + a) * ψ y) + ∫ y, P (y + a) * ∂[i] ψ y := by
  have hψa : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ ψ (y - a)) :=
    hψ.comp (contDiff_id.sub contDiff_const)
  have hψac : HasCompactSupport (fun y ↦ ψ (y - a)) :=
    hψc.comp_homeomorph (Homeomorph.subRight a)
  have h := htest _ hψa hψac
  have hfd : ∀ y, fderiv ℝ (fun z ↦ ψ (z - a)) y = fderiv ℝ ψ (y - a) := fun y ↦ by
    have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := ψ) (x := y) (-a)
    simpa only [← sub_eq_add_neg] using h1
  have hpd : ∀ (j : Fin n) y, ∂[j] (fun z ↦ ψ (z - a)) y = ∂[j] ψ (y - a) := fun j y ↦
    congrFun (PDE.partialDeriv_comp_sub j ψ a) y
  have hlap : ∀ y, laplacian (fun z ↦ ψ (z - a)) y = laplacian ψ (y - a) := fun y ↦
    PDE.laplacian_comp_sub_right ψ a y (hψ.of_le (by simp)).contDiffAt
  simp only [hfd, hpd, hlap] at h
  have e1 := integral_add_right_eq_self (μ := (volume : Measure (ℝ^n)))
    (fun y ↦ g y * ψ (y - a) + (1 / 2 : ℝ) * (g y * fderiv ℝ ψ (y - a) y) -
      g y * laplacian ψ (y - a) - ∑ j, N j y * ∂[j] ψ (y - a)) a
  have e2 := integral_add_right_eq_self (μ := (volume : Measure (ℝ^n)))
    (fun y ↦ F y * ψ (y - a)) a
  have e3 := integral_add_right_eq_self (μ := (volume : Measure (ℝ^n)))
    (fun y ↦ P y * ∂[i] ψ (y - a)) a
  simp only [add_sub_cancel_right] at e1 e2 e3
  rw [e1, e2, e3]
  exact h

/-- **The difference quotient of the tested self-similar equation.** Let `g`, `F`, `P` and
`N₁, …, Nₙ` be locally integrable with

`∫ (g ψ + ½ g (y·∇ψ) - g Δψ - Σⱼ Nⱼ ∂ⱼψ) = ∫ F ψ + ∫ P ∂ᵢψ` for every test function `ψ`,

and let `gl` be a weak derivative `∂ₗg`. Then for `h ≠ 0` the forward difference quotients in
the direction `eₗ` satisfy

`∫ (D_h g ψ + ½ D_h g (y·∇ψ) - D_h g Δψ - Σⱼ D_h Nⱼ ∂ⱼψ)
  = ∫ (D_h F + ½ gl(· + h eₗ)) ψ + ∫ D_h P ∂ᵢψ`.

The term `½ gl(· + h eₗ)` is the commutator of the drift with the translation:
`D_h(y·∇g) = y·∇D_h g + (∂ₗg)(· + h eₗ)`. -/
theorem integral_tested_similarity_forwardDifference {g gl F P : ℝ^n → ℝ}
    {N : Fin n → ℝ^n → ℝ} (i l : Fin n) (hg : LocallyIntegrable g volume)
    (hgl : LocallyIntegrable gl volume) (hF : LocallyIntegrable F volume)
    (hP : LocallyIntegrable P volume) (hN : ∀ j, LocallyIntegrable (N j) volume)
    (htest : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y, (g y * ψ y + (1 / 2 : ℝ) * (g y * fderiv ℝ ψ y y) - g y * laplacian ψ y -
        ∑ j, N j y * ∂[j] ψ y) = (∫ y, F y * ψ y) + ∫ y, P y * ∂[i] ψ y)
    (hweak : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ y, g y * ∂[l] ψ y = -∫ y, gl y * ψ y)
    {h : ℝ} (hh : h ≠ 0) {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ y, (forwardDifference l h g y * ψ y +
        (1 / 2 : ℝ) * (forwardDifference l h g y * fderiv ℝ ψ y y) -
        forwardDifference l h g y * laplacian ψ y -
        ∑ j, forwardDifference l h (N j) y * ∂[j] ψ y) =
      (∫ y, (forwardDifference l h F y + (1 / 2 : ℝ) * gl (y + coordinateStep l h)) * ψ y) +
        ∫ y, forwardDifference l h P y * ∂[i] ψ y := by
  set a : ℝ^n := coordinateStep l h with ha
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have c0 : Continuous ψ := hψ.continuous
  have cE : Continuous fun y ↦ fderiv ℝ ψ y y := continuous_fderiv_apply_self hψ1
  have sE : HasCompactSupport fun y ↦ fderiv ℝ ψ y y := hasCompactSupport_fderiv_apply_self hψc
  have cL : Continuous (laplacian ψ) := (PDE.contDiff_laplacian_coord hψ).continuous
  have sL : HasCompactSupport (laplacian ψ) := hψc.coordinate_laplacian
  have cD : ∀ j : Fin n, Continuous (∂[j] ψ) := fun j ↦ hψ1.continuous_partialDeriv j
  have sD : ∀ j : Fin n, HasCompactSupport (∂[j] ψ) := fun j ↦ hψc.partialDeriv j
  -- A locally integrable function, or its translate, times a continuous compactly supported
  -- function is integrable.
  have I : ∀ {f φ : ℝ^n → ℝ}, LocallyIntegrable f volume → Continuous φ →
      HasCompactSupport φ → Integrable fun y ↦ f y * φ y := fun hf hφ hφc ↦
    hf.integrable_smul_right_of_hasCompactSupport hφ hφc
  have Iτ : ∀ {f φ : ℝ^n → ℝ}, LocallyIntegrable f volume → Continuous φ →
      HasCompactSupport φ → Integrable fun y ↦ f (y + a) * φ y := fun {f φ} hf hφ hφc ↦ by
    have h1 : Integrable fun y ↦ f y * φ (y - a) :=
      I hf (hφ.comp (continuous_id.sub continuous_const))
        (hφc.comp_homeomorph (Homeomorph.subRight a))
    have h2 := h1.comp_add_right a
    simpa only [add_sub_cancel_right] using h2
  -- The integrands of the equation and of its translate.
  have iA : Integrable fun y ↦ g y * ψ y + (1 / 2 : ℝ) * (g y * fderiv ℝ ψ y y) -
      g y * laplacian ψ y - ∑ j, N j y * ∂[j] ψ y :=
    (((I hg c0 hψc).add ((I hg cE sE).const_mul _)).sub (I hg cL sL)).sub
      (integrable_finsetSum _ fun j _ ↦ I (hN j) (cD j) (sD j))
  have iAτ : Integrable fun y ↦ g (y + a) * ψ y +
      (1 / 2 : ℝ) * (g (y + a) * fderiv ℝ ψ y y) - g (y + a) * laplacian ψ y -
      ∑ j, N j (y + a) * ∂[j] ψ y :=
    (((Iτ hg c0 hψc).add ((Iτ hg cE sE).const_mul _)).sub (Iτ hg cL sL)).sub
      (integrable_finsetSum _ fun j _ ↦ Iτ (hN j) (cD j) (sD j))
  have iX : Integrable fun y ↦ g (y + a) * ∂[l] ψ y := Iτ hg (cD l) (sD l)
  -- The translated equation, with the extra term of the drift.
  have hT := integral_tested_similarity_comp_add_right i htest a hψ hψc
  have hstep : ∀ y, fderiv ℝ ψ y a = h * ∂[l] ψ y := fun y ↦ by
    rw [ha, coordinateStep, map_smul, smul_eq_mul]
    rfl
  have hsplit : (fun y ↦ g (y + a) * ψ y +
      (1 / 2 : ℝ) * (g (y + a) * fderiv ℝ ψ y (y + a)) - g (y + a) * laplacian ψ y -
      ∑ j, N j (y + a) * ∂[j] ψ y) = fun y ↦ (g (y + a) * ψ y +
      (1 / 2 : ℝ) * (g (y + a) * fderiv ℝ ψ y y) - g (y + a) * laplacian ψ y -
      ∑ j, N j (y + a) * ∂[j] ψ y) + h / 2 * (g (y + a) * ∂[l] ψ y) := funext fun y ↦ by
    rw [map_add, hstep]
    ring
  rw [hsplit, integral_add iAτ (iX.const_mul _), integral_const_mul] at hT
  -- The extra term, by the weak derivative of `g`.
  have hX : ∫ y, g (y + a) * ∂[l] ψ y = -∫ y, gl (y + a) * ψ y := by
    have hψa : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ ψ (y - a)) :=
      hψ.comp (contDiff_id.sub contDiff_const)
    have hψac : HasCompactSupport (fun y ↦ ψ (y - a)) :=
      hψc.comp_homeomorph (Homeomorph.subRight a)
    have h1 := hweak _ hψa hψac
    have hpd : ∀ y, ∂[l] (fun z ↦ ψ (z - a)) y = ∂[l] ψ (y - a) := fun y ↦
      congrFun (PDE.partialDeriv_comp_sub l ψ a) y
    simp only [hpd] at h1
    have e1 := integral_add_right_eq_self (μ := (volume : Measure (ℝ^n)))
      (fun y ↦ g y * ∂[l] ψ (y - a)) a
    have e2 := integral_add_right_eq_self (μ := (volume : Measure (ℝ^n)))
      (fun y ↦ gl y * ψ (y - a)) a
    simp only [add_sub_cancel_right] at e1 e2
    rw [e1, e2]
    exact h1
  rw [hX] at hT
  have hA := htest ψ hψ hψc
  -- The difference quotients, term by term.
  have eL : (fun y ↦ forwardDifference l h g y * ψ y +
      (1 / 2 : ℝ) * (forwardDifference l h g y * fderiv ℝ ψ y y) -
      forwardDifference l h g y * laplacian ψ y -
      ∑ j, forwardDifference l h (N j) y * ∂[j] ψ y) = fun y ↦ h⁻¹ * ((g (y + a) * ψ y +
      (1 / 2 : ℝ) * (g (y + a) * fderiv ℝ ψ y y) - g (y + a) * laplacian ψ y -
      ∑ j, N j (y + a) * ∂[j] ψ y) - (g y * ψ y + (1 / 2 : ℝ) * (g y * fderiv ℝ ψ y y) -
      g y * laplacian ψ y - ∑ j, N j y * ∂[j] ψ y)) := funext fun y ↦ by
    have hs : ∑ j, forwardDifference l h (N j) y * ∂[j] ψ y =
        h⁻¹ * ((∑ j, N j (y + a) * ∂[j] ψ y) - ∑ j, N j y * ∂[j] ψ y) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        simp only [forwardDifference]
        ring
    rw [hs]
    simp only [forwardDifference]
    ring
  have eF : (fun y ↦ (forwardDifference l h F y + (1 / 2 : ℝ) * gl (y + a)) * ψ y) =
      fun y ↦ h⁻¹ * (F (y + a) * ψ y - F y * ψ y) + (1 / 2 : ℝ) * (gl (y + a) * ψ y) :=
    funext fun y ↦ by
      simp only [forwardDifference]
      ring
  have eP : (fun y ↦ forwardDifference l h P y * ∂[i] ψ y) =
      fun y ↦ h⁻¹ * (P (y + a) * ∂[i] ψ y - P y * ∂[i] ψ y) := funext fun y ↦ by
    simp only [forwardDifference]
    ring
  have iFd : Integrable fun y ↦ h⁻¹ * (F (y + a) * ψ y - F y * ψ y) :=
    ((Iτ hF c0 hψc).sub (I hF c0 hψc)).const_mul _
  have iG : Integrable fun y ↦ (1 / 2 : ℝ) * (gl (y + a) * ψ y) := (Iτ hgl c0 hψc).const_mul _
  rw [eL, eF, eP, integral_const_mul, integral_sub iAτ iA, integral_add iFd iG]
  simp only [integral_const_mul]
  rw [integral_sub (Iτ hF c0 hψc) (I hF c0 hψc),
    integral_sub (Iτ hP (cD i) (sD i)) (I hP (cD i) (sD i)), hA]
  have e : h⁻¹ * h = 1 := inv_mul_cancel₀ hh
  linear_combination h⁻¹ * hT + ((∫ y, gl (y + a) * ψ y) / 2) * e

end SobolevSpace.GraphSpace.DifferenceQuotient
