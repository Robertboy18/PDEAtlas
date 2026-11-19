/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv

import PDE.Analysis.Calculus.Prod.SliceDerivative
import CAS.ExactTactic

/-!
# Raw reflected matching jets

For arbitrary jointly differentiable terminal coordinates `x,z`, the raw value
mismatch and the two reflected discrepancy derivatives are expressed in terms of
the quotient residual. The identity retains every off-match term and allows any
real reflection slope. It can be applied separately at each fixed coefficient
and external parameter, with both terminal coordinates depending on them.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

private theorem hasDerivAt_reflected_parameter_line
    {f : ℝ × ℝ → ℝ} (hf : DifferentiableAt ℝ f (0, 0)) (h : ℝ) :
    HasDerivAt (fun μ : ℝ ↦ f (-μ, -h * μ))
      (-deriv (fun μ : ℝ ↦ f (μ, 0)) 0 -
        h * deriv (fun a : ℝ ↦ f (0, a)) 0) 0 := by
  have hfirst : fderiv ℝ f (0, 0) (1, 0) = deriv (fun μ : ℝ ↦ f (μ, 0)) 0 := by
    simpa only [fderiv_apply_one_eq_deriv] using
      (fderiv_prod_firstSlice f 0 1 0 hf).symm
  have hsecond : fderiv ℝ f (0, 0) (0, 1) = deriv (fun a : ℝ ↦ f (0, a)) 0 :=
    (deriv_prod_timeSlice f 0 0 hf).symm
  have hneg : HasDerivAt (fun μ : ℝ ↦ -μ) (-1) 0 := by cas
  have hmul : HasDerivAt (fun μ : ℝ ↦ -h * μ) (-h) 0 := by cas
  have hline : HasDerivAt (fun μ : ℝ ↦ (-μ, -h * μ)) (-1, -h) 0 :=
    hneg.prodMk hmul
  have hchain : HasDerivAt (fun μ : ℝ ↦ f (-μ, -h * μ))
      (fderiv ℝ f (0, 0) (-1, -h)) 0 := by
    simpa only [Function.comp_def] using
      hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  apply hchain.congr_deriv
  have hdir : ((-1 : ℝ), -h) =
      (-1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + (-h) • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> dsimp <;> cas
  rw [hdir, map_add, map_smul, map_smul, hfirst, hsecond]
  simp only [smul_eq_mul]
  ring

/-- The raw reflected matching jet is the stated transformation of the quotient
residual. Joint differentiability at the base point justifies the reflected-line
derivatives; nonvanishing of the base denominator justifies the quotient rules. -/
theorem raw_matching_jet_eq
    {x z : ℝ × ℝ → ℝ}
    (hx : DifferentiableAt ℝ x (0, 0)) (hz : DifferentiableAt ℝ z (0, 0))
    (hz0 : z (0, 0) ≠ 0) (h : ℝ) :
    let ρ : ℝ × ℝ → ℝ := fun p ↦ x p / z p
    let H₁ : ℝ → ℝ := fun μ ↦ x (μ, 0) - z (-μ, -h * μ)
    let H₂ : ℝ → ℝ := fun μ ↦ z (μ, 0) - x (-μ, -h * μ)
    let G : Fin 3 → ℝ :=
      ![ρ (0, 0) - 1,
        deriv (fun a ↦ ρ (0, a)) 0,
        z (0, 0) * deriv (fun μ ↦ ρ (μ, 0)) 0 +
          2 * deriv (fun μ ↦ z (μ, 0)) 0 + h * deriv (fun a ↦ z (0, a)) 0]
    let K : Fin 3 → ℝ := ![x (0, 0) - z (0, 0), deriv H₁ 0, deriv H₂ 0]
    K = ![z (0, 0) * G 0,
      G 2 + deriv (fun μ ↦ z (μ, 0)) 0 * G 0,
      G 2 + h * z (0, 0) * G 1 +
        (deriv (fun μ ↦ z (μ, 0)) 0 + h * deriv (fun a ↦ z (0, a)) 0) * G 0] := by
  intro ρ H₁ H₂ G K
  have hspeedAxis : DifferentiableAt ℝ (fun μ : ℝ ↦ (μ, (0 : ℝ))) 0 :=
    differentiableAt_id.prodMk (differentiableAt_const 0)
  have hdisplacementAxis : DifferentiableAt ℝ (fun a : ℝ ↦ ((0 : ℝ), a)) 0 :=
    (differentiableAt_const 0).prodMk differentiableAt_id
  have hxμ : HasDerivAt (fun μ : ℝ ↦ x (μ, 0))
      (deriv (fun μ : ℝ ↦ x (μ, 0)) 0) 0 :=
    (hx.comp (f := fun μ : ℝ ↦ (μ, (0 : ℝ))) 0 hspeedAxis).hasDerivAt
  have hxa : HasDerivAt (fun a : ℝ ↦ x (0, a))
      (deriv (fun a : ℝ ↦ x (0, a)) 0) 0 :=
    (hx.comp (f := fun a : ℝ ↦ ((0 : ℝ), a)) 0 hdisplacementAxis).hasDerivAt
  have hzμ : HasDerivAt (fun μ : ℝ ↦ z (μ, 0))
      (deriv (fun μ : ℝ ↦ z (μ, 0)) 0) 0 :=
    (hz.comp (f := fun μ : ℝ ↦ (μ, (0 : ℝ))) 0 hspeedAxis).hasDerivAt
  have hza : HasDerivAt (fun a : ℝ ↦ z (0, a))
      (deriv (fun a : ℝ ↦ z (0, a)) 0) 0 :=
    (hz.comp (f := fun a : ℝ ↦ ((0 : ℝ), a)) 0 hdisplacementAxis).hasDerivAt
  have hH₁ : HasDerivAt H₁
      (deriv (fun μ : ℝ ↦ x (μ, 0)) 0 -
        (-deriv (fun μ : ℝ ↦ z (μ, 0)) 0 -
          h * deriv (fun a : ℝ ↦ z (0, a)) 0)) 0 :=
    hxμ.sub (hasDerivAt_reflected_parameter_line hz h)
  have hH₂ : HasDerivAt H₂
      (deriv (fun μ : ℝ ↦ z (μ, 0)) 0 -
        (-deriv (fun μ : ℝ ↦ x (μ, 0)) 0 -
          h * deriv (fun a : ℝ ↦ x (0, a)) 0)) 0 :=
    hzμ.sub (hasDerivAt_reflected_parameter_line hx h)
  have hρμ : HasDerivAt (fun μ : ℝ ↦ ρ (μ, 0))
      ((deriv (fun μ : ℝ ↦ x (μ, 0)) 0 * z (0, 0) -
        x (0, 0) * deriv (fun μ : ℝ ↦ z (μ, 0)) 0) / z (0, 0) ^ 2) 0 :=
    hxμ.fun_div hzμ hz0
  have hρa : HasDerivAt (fun a : ℝ ↦ ρ (0, a))
      ((deriv (fun a : ℝ ↦ x (0, a)) 0 * z (0, 0) -
        x (0, 0) * deriv (fun a : ℝ ↦ z (0, a)) 0) / z (0, 0) ^ 2) 0 :=
    hxa.fun_div hza hz0
  change ![x (0, 0) - z (0, 0), deriv H₁ 0, deriv H₂ 0] =
    ![z (0, 0) * (ρ (0, 0) - 1),
      z (0, 0) * deriv (fun μ ↦ ρ (μ, 0)) 0 +
        2 * deriv (fun μ ↦ z (μ, 0)) 0 +
        h * deriv (fun a ↦ z (0, a)) 0 +
        deriv (fun μ ↦ z (μ, 0)) 0 * (ρ (0, 0) - 1),
      z (0, 0) * deriv (fun μ ↦ ρ (μ, 0)) 0 +
        2 * deriv (fun μ ↦ z (μ, 0)) 0 +
        h * deriv (fun a ↦ z (0, a)) 0 +
        h * z (0, 0) * deriv (fun a ↦ ρ (0, a)) 0 +
        (deriv (fun μ ↦ z (μ, 0)) 0 +
          h * deriv (fun a ↦ z (0, a)) 0) * (ρ (0, 0) - 1)]
  rw [hH₁.deriv, hH₂.deriv, hρμ.deriv, hρa.deriv]
  dsimp only [ρ]
  generalize deriv (fun μ : ℝ ↦ x (μ, 0)) 0 = xμ
  generalize deriv (fun a : ℝ ↦ x (0, a)) 0 = xa
  generalize deriv (fun μ : ℝ ↦ z (μ, 0)) 0 = zμ
  generalize deriv (fun a : ℝ ↦ z (0, a)) 0 = za
  generalize x (0, 0) = x₀
  generalize z (0, 0) = z₀ at hz0 ⊢
  ext i
  fin_cases i <;> dsimp <;> cas

end PDE.Analysis
