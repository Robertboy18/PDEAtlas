/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.Spectrum

import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Genuine nonlinearity of reflected gated fluxes

The derivatives of the three explicit speeds in their displayed eigenvector
directions are `-k'' (x)`, `middleCurvature g C φ q`, and `k'' (z)`.
For the middle family, the gate partition removes the transverse derivative
terms: both cutoff derivatives vanish in either gate, while both transverse
coordinates of the middle eigenvector vanish outside the gates.

Scalar second-derivative positivity, middle-curvature positivity, and the two
ordered speed gaps therefore imply genuine nonlinearity of every canonical
family. The characteristic-field equivalence transfers the calculation
to every nonzero eigenvector, using the complete simple eigenbasis.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.GatedFlux

open Set
open scoped ContDiff

/-- Differentiating the middle speed requires first derivatives of the scalar
feedback and second derivatives of the clock and cutoff. -/
theorem differentiable_middleSpeed {g C φ : ℝ → ℝ} (hg : Differentiable ℝ (deriv g))
    (hC : Differentiable ℝ (deriv C)) (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (middleSpeed g C φ) := by
  unfold middleSpeed
  fun_prop

/-- The middle-speed derivative retains both transverse feedback terms.
The reflected cutoff contributes positively to the middle curvature. -/
theorem fderiv_middleSpeed_apply {g C φ : ℝ → ℝ} {q v : ℝ^3}
    (hg : DifferentiableAt ℝ (deriv g) (q 1)) (hCy : DifferentiableAt ℝ (deriv C) (q 1))
    (hCny : DifferentiableAt ℝ (deriv C) (-q 1)) (hφx : DifferentiableAt ℝ φ (q 0))
    (hφz : DifferentiableAt ℝ φ (q 2)) :
    fderiv ℝ (middleSpeed g C φ) q v = deriv C (q 1) * deriv φ (q 0) * v 0 +
      middleCurvature g C φ q * v 1 - deriv C (-q 1) * deriv φ (q 2) * v 2 := by
  have hx := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (0 : Fin 3)
  have hy := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (1 : Fin 3)
  have hz := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (2 : Fin 3)
  have hmiddle := ((hg.hasDerivAt.comp_hasFDerivAt q hy).sub
    ((hCny.hasDerivAt.comp_hasFDerivAt q hy.neg).mul (hφz.hasDerivAt.comp_hasFDerivAt q hz))).add
        ((hCy.hasDerivAt.comp_hasFDerivAt q hy).mul (hφx.hasDerivAt.comp_hasFDerivAt q hx))
  rw [show fderiv ℝ (middleSpeed g C φ) q = _ from hmiddle.fderiv]
  simp only [Fin.isValue, Function.comp_apply, Pi.neg_apply, smul_neg, add_apply, sub_apply,
    smul_apply, PiLp.proj_apply, smul_eq_mul, neg_apply, middleCurvature]
  ring

/-- Each displayed speed is differentiable from the scalar derivative data. -/
theorem differentiable_speed {k g C φ : ℝ → ℝ} (hk : Differentiable ℝ (deriv k))
    (hg : Differentiable ℝ (deriv g)) (hC : Differentiable ℝ (deriv C)) (hφ : Differentiable ℝ φ)
    (i : Fin 3) :
    Differentiable ℝ (fun q : ℝ^3 ↦ speed k g C φ q i) := by
  fin_cases i
  · change Differentiable ℝ (fun q : ℝ^3 ↦ -deriv k (q 0))
    fun_prop
  · exact differentiable_middleSpeed hg hC hφ
  · change Differentiable ℝ (fun q : ℝ^3 ↦ deriv k (q 2))
    fun_prop

/-- The full directional derivatives of the three displayed speeds. -/
theorem fderiv_speed_apply {k g C φ : ℝ → ℝ} {q v : ℝ^3} (hk : Differentiable ℝ (deriv k))
    (hg : Differentiable ℝ (deriv g)) (hC : Differentiable ℝ (deriv C)) (hφ : Differentiable ℝ φ)
    (i : Fin 3) :
    fderiv ℝ (fun p : ℝ^3 ↦ speed k g C φ p i) q v = ![-deriv (deriv k) (q 0) * v 0,
      deriv C (q 1) * deriv φ (q 0) * v 0 + middleCurvature g C φ q * v 1 - deriv C (-q 1) *
      deriv φ (q 2) * v 2, deriv (deriv k) (q 2) * v 2] i := by
  fin_cases i
  · change fderiv ℝ (fun p : ℝ^3 ↦ -deriv k (p 0)) q v = -deriv (deriv k) (q 0) * v 0
    have h := ((hk (q 0)).hasDerivAt.comp_hasFDerivAt q
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (0 : Fin 3))).neg
    rw [show fderiv ℝ (fun p : ℝ^3 ↦ -deriv k (p 0)) q = _ from h.fderiv]
    simp [PiLp.proj_apply, smul_eq_mul]
  · exact fderiv_middleSpeed_apply (hg _) (hC _) (hC _) (hφ _) (hφ _)
  · change fderiv ℝ (fun p : ℝ^3 ↦ deriv k (p 2)) q v = deriv (deriv k) (q 2) * v 2
    have h := (hk (q 2)).hasDerivAt.comp_hasFDerivAt q
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) q (2 : Fin 3))
    rw [show fderiv ℝ (fun p : ℝ^3 ↦ deriv k (p 2)) q = _ from h.fderiv]
    simp [PiLp.proj_apply, smul_eq_mul]

/-- The gate geometry removes the transverse derivative terms for the middle
eigenvector. -/
theorem fderiv_middleSpeed_rightEigenvector_one {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hg : Differentiable ℝ (deriv g)) (hC : Differentiable ℝ (deriv C)) (hφ : Differentiable ℝ φ)
    (ha : 0 < a) (had : a < d) (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0)
    (hsupport : tsupport b ⊆ Ioo d e) :
    fderiv ℝ (middleSpeed g C φ) q (rightEigenvector k g C φ b q 1) = middleCurvature g C φ q := by
  rw [fderiv_middleSpeed_apply (hg _) (hC _) (hC _) (hφ _) (hφ _)]
  rcases gate_partition ha had hleft hright hsupport (q 1) with
    ⟨-, -, h₁, -, h₂, -, -⟩ | ⟨-, -, h₁, -, h₂, -, -⟩ | ⟨-, h₁, -, h₂⟩ <;>
  simp [rightEigenvector, h₁, h₂]

/-- Along the displayed vectors, the three speed derivatives are exactly the
two signed fast curvatures and the middle curvature. -/
theorem fderiv_speed_rightEigenvector {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hk : Differentiable ℝ (deriv k)) (hg : Differentiable ℝ (deriv g))
    (hC : Differentiable ℝ (deriv C)) (hφ : Differentiable ℝ φ) (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (i : Fin 3) :
    fderiv ℝ (fun p : ℝ^3 ↦ speed k g C φ p i) q (rightEigenvector k g C φ b q i) =
      ![-deriv (deriv k) (q 0), middleCurvature g C φ q, deriv (deriv k) (q 2)] i := by
  fin_cases i
  · rw [fderiv_speed_apply hk hg hC hφ]
    simp
  · exact fderiv_middleSpeed_rightEigenvector_one hg hC hφ ha had hleft hright hsupport
  · rw [fderiv_speed_apply hk hg hC hφ]
    simp

/-- Nonzero scalar curvatures give nonzero derivatives along all three
displayed vectors, independently of the sign or amplitude of the gate. -/
theorem fderiv_speed_rightEigenvector_ne_zero {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hk : Differentiable ℝ (deriv k)) (hg : Differentiable ℝ (deriv g))
    (hC : Differentiable ℝ (deriv C)) (hφ : Differentiable ℝ φ) (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hfastx : deriv (deriv k) (q 0) ≠ 0) (hfastz : deriv (deriv k) (q 2) ≠ 0)
    (hmiddle : middleCurvature g C φ q ≠ 0) (i : Fin 3) :
    fderiv ℝ (fun p : ℝ^3 ↦ speed k g C φ p i) q (rightEigenvector k g C φ b q i) ≠ 0 := by
  rw [fderiv_speed_rightEigenvector hk hg hC hφ ha had hleft hright hsupport]
  fin_cases i
  exacts [neg_ne_zero.mpr hfastx, hmiddle, hfastz]

/-- Positive scalar fast curvature and middle curvature make every ordered
family genuinely nonlinear on the whole state space. The conclusion quantifies
over every nonzero eigenvector of the Jacobian, via the
characteristic-field equivalence and the constructed simple eigenbasis. -/
theorem isGenuinelyNonlinearFamily {k g C φ b : ℝ → ℝ} {a d e : ℝ} (hk : ContDiff ℝ 2 k)
    (hg : ContDiff ℝ 2 g) (hC : ContDiff ℝ 2 C) (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b)
    (ha : 0 < a) (had : a < d) (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0)
    (hsupport : tsupport b ⊆ Ioo d e) (hlow : ∀ q : ℝ^3, -deriv k (q 0) < middleSpeed g C φ q)
    (hhigh : ∀ q : ℝ^3, middleSpeed g C φ q < deriv k (q 2)) (hfast : ∀ s, 0 < deriv (deriv k) s)
    (hmiddle : ∀ q : ℝ^3, 0 < middleCurvature g C φ q) (i : Fin 3) :
    System.IsGenuinelyNonlinearFamily (flux k g C φ b) i := by
  have hk' : Differentiable ℝ k := hk.differentiable (by simp)
  have hg' : Differentiable ℝ g := hg.differentiable (by simp)
  have hC' : Differentiable ℝ C := hC.differentiable (by simp)
  let field : CharacteristicField (flux k g C φ b) :=
    { flux_differentiable := differentiable_flux hk' hg' hC' hφ hb
      speed := fun q ↦ speed k g C φ q i
      rightEigenvector := fun q ↦ rightEigenvector k g C φ b q i
      eigenvector := fun q ↦
        hasEigenvector_fderiv_flux hk' hg' hC' hφ hb ha had hleft hright hsupport
          (hlow q) (hhigh q) i }
  have hhyper : ∀ q, IsStrictlyHyperbolicAt (flux k g C φ b) q :=
    fun q ↦ isStrictlyHyperbolicAt hk' hg' hC' hφ hb ha had hleft hright hsupport (hlow q) (hhigh q)
  have hspeed : field.speed = System.characteristicSpeed (flux k g C φ b) i :=
    (characteristicSpeed_eq_fun hk' hg' hC' hφ hb ha had hleft hright hsupport hlow hhigh i).symm
  exact (System.isGenuinelyNonlinearFamily_iff hhyper i field hspeed).2 fun q ↦
    ⟨differentiable_speed hk.differentiable_deriv_two hg.differentiable_deriv_two
      hC.differentiable_deriv_two hφ i q,
    fderiv_speed_rightEigenvector_ne_zero hk.differentiable_deriv_two
      hg.differentiable_deriv_two hC.differentiable_deriv_two hφ ha had hleft hright
      hsupport (hfast (q 0)).ne' (hfast (q 2)).ne' (hmiddle q).ne' i⟩

end PDE.Hyperbolic.ConservationLaw.System.GatedFlux
