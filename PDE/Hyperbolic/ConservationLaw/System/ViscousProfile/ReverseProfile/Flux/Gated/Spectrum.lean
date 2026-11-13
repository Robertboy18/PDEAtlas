/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.Basic

import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The complete spectrum of a reflected gated flux

The two adjacent scalar gaps order three explicit speeds. Plateau and support
conditions split the Jacobian into three triangular patterns, with the same
rational eigenvector formulas valid in every pattern. Distinct eigenvalues give
linear independence, and the three vectors form a Euclidean basis.

The canonical characteristic speeds and strict hyperbolicity are conclusions.
Scalar gap estimates and genuine nonlinearity are proved separately.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.GatedFlux

open Set

/-- The candidate speeds in increasing order when the two adjacent gaps hold. -/
def speed (k g C φ : ℝ → ℝ) (q : ℝ^3) : Fin 3 → ℝ :=
  ![-deriv k (q 0), middleSpeed g C φ q, deriv k (q 2)]

/-- The first speed is the derivative of the negative fast law. -/
@[simp]
theorem speed_zero (k g C φ : ℝ → ℝ) (q : ℝ^3) :
    speed k g C φ q 0 = -deriv k (q 0) := rfl

/-- The middle speed is the middle diagonal entry of the full Jacobian. -/
@[simp]
theorem speed_one (k g C φ : ℝ → ℝ) (q : ℝ^3) :
    speed k g C φ q 1 = middleSpeed g C φ q := rfl

/-- The last speed is the derivative of the positive fast law. -/
@[simp]
theorem speed_two (k g C φ : ℝ → ℝ) (q : ℝ^3) :
    speed k g C φ q 2 = deriv k (q 2) := rfl

/-- Rational eigenvector formulas retaining both shear-derivative columns.
The vector for family `i` has coordinate `i` equal to one. -/
def rightEigenvector (k g C φ b : ℝ → ℝ) (q : ℝ^3) : Fin 3 → ℝ^3 :=
  let p := -deriv k (q 0)
  let m := middleSpeed g C φ q
  let l := deriv k (q 2)
  let B := deriv b (q 1) * q 2
  let D := deriv b (-q 1) * q 0
  let shearPos := b (q 1)
  let shearNeg := -b (-q 1)
  let P := C (q 1) * deriv φ (q 0)
  let Q := C (-q 1) * deriv φ (q 2)
  ![!₂[1, P / (p - m), shearNeg / (p - l) + D * P / ((p - m) * (p - l))],
    !₂[B / (m - p) + shearPos * D / ((m - p) * (m - l)), 1,
      D / (m - l) + shearNeg * B / ((m - p) * (m - l))],
    !₂[shearPos / (l - p) + B * Q / ((l - p) * (l - m)), Q / (l - m), 1]]

/-- The chosen normalization holds even before imposing nonzero gaps. -/
@[simp]
theorem rightEigenvector_self (k g C φ b : ℝ → ℝ) (q : ℝ^3) (i : Fin 3) :
    rightEigenvector k g C φ b q i i = 1 := by
  fin_cases i <;> simp [rightEigenvector]

/-- Every displayed eigenvector is nonzero by its normalized coordinate. -/
theorem rightEigenvector_ne_zero (k g C φ b : ℝ → ℝ) (q : ℝ^3) (i : Fin 3) :
    rightEigenvector k g C φ b q i ≠ 0 :=
  fun h ↦ by simpa using congrArg (fun v : ℝ^3 ↦ v i) h

/-- Two adjacent inequalities order the complete candidate speed list. -/
theorem speed_strictMono {k g C φ : ℝ → ℝ} {q : ℝ^3} (hlow : -deriv k (q 0) < middleSpeed g C φ q)
    (hhigh : middleSpeed g C φ q < deriv k (q 2)) :
    StrictMono (speed k g C φ q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [speed] at hij ⊢ <;> linarith

/-- Differentiable scalar ingredients give a differentiable flux. -/
theorem differentiable_flux {k g C φ b : ℝ → ℝ} (hk : Differentiable ℝ k) (hg : Differentiable ℝ g)
    (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b) :
    Differentiable ℝ (flux k g C φ b) := by
  rw [differentiable_piLp]
  intro i
  fin_cases i
  · change Differentiable ℝ (fun q : ℝ^3 ↦ -k (q 0) + b (q 1) * q 2)
    fun_prop
  · change Differentiable ℝ
      (fun q : ℝ^3 ↦ g (q 1) + C (-q 1) * φ (q 2) + C (q 1) * φ (q 0))
    fun_prop
  · change Differentiable ℝ (fun q : ℝ^3 ↦ k (q 2) - b (-q 1) * q 0)
    fun_prop

/-- The explicit vectors are eigenvectors of the full flux Jacobian.
The support partition removes cyclic products before denominators are cleared. -/
theorem fderiv_flux_rightEigenvector {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hk : Differentiable ℝ k) (hg : Differentiable ℝ g) (hC : Differentiable ℝ C)
    (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2))
    (i : Fin 3) :
    fderiv ℝ (flux k g C φ b) q (rightEigenvector k g C φ b q i) =
      speed k g C φ q i • rightEigenvector k g C φ b q i := by
  have hpm := sub_ne_zero.mpr hlow.ne
  have hmp := sub_ne_zero.mpr hlow.ne'
  have hml := sub_ne_zero.mpr hhigh.ne
  have hlm := sub_ne_zero.mpr hhigh.ne'
  have hpl := sub_ne_zero.mpr (hlow.trans hhigh).ne
  have hlp := sub_ne_zero.mpr (hlow.trans hhigh).ne'
  simp only [sub_neg_eq_add] at hmp hlp
  rw [fderiv_flux_apply (hk _) (hk _) (hg _) (hC _) (hC _) (hφ _) (hφ _) (hb _) (hb _)]
  rcases gate_partition ha had hleft hright hsupport (q 1) with
    ⟨-, h₁, -, h₂, -, h₃, h₄⟩ | ⟨-, h₁, -, h₂, -, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩ <;>
  · ext j
    fin_cases i <;> fin_cases j <;>
      simp [rightEigenvector, speed, h₁, h₂, h₃, h₄, smul_eq_mul] <;>
      field_simp [hpm, hmp, hml, hlm, hpl, hlp] <;> ring

/-- The rational vectors are nonzero eigenvectors of the derivative. -/
theorem hasEigenvector_fderiv_flux {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hk : Differentiable ℝ k) (hg : Differentiable ℝ g) (hC : Differentiable ℝ C)
    (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2))
    (i : Fin 3) :
    Module.End.HasEigenvector (fderiv ℝ (flux k g C φ b) q).toLinearMap
      (speed k g C φ q i) (rightEigenvector k g C φ b q i) := by
  exact ⟨Module.End.mem_eigenspace_iff.mpr
    (fderiv_flux_rightEigenvector hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh i),
    rightEigenvector_ne_zero k g C φ b q i⟩

/-- Distinct ordered speeds make the three explicit vectors linearly independent. -/
theorem rightEigenvector_linearIndependent {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hk : Differentiable ℝ k) (hg : Differentiable ℝ g) (hC : Differentiable ℝ C)
    (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2)) :
    LinearIndependent ℝ (rightEigenvector k g C φ b q) := by
  exact Module.End.eigenvectors_linearIndependent'
    (fderiv ℝ (flux k g C φ b) q).toLinearMap (speed k g C φ q)
    (speed_strictMono hlow hhigh).injective (rightEigenvector k g C φ b q)
    (hasEigenvector_fderiv_flux hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh)

/-- The displayed eigenvectors form a complete basis of the three-dimensional state space. -/
def eigenbasis
    {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3}
    (hk : Differentiable ℝ k) (hg : Differentiable ℝ g)
    (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b)
    (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0)
    (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q)
    (hhigh : middleSpeed g C φ q < deriv k (q 2)) :
    Module.Basis (Fin 3) ℝ (ℝ^3) :=
  basisOfLinearIndependentOfCardEqFinrank
    (rightEigenvector_linearIndependent hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh)
    (by simp)

/-- The constructed basis has exactly the displayed rational vectors. -/
@[simp]
theorem eigenbasis_apply {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3} (hk : Differentiable ℝ k)
    (hg : Differentiable ℝ g) (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ)
    (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d) (hleft : ∀ s, s ≤ a → C s = 1)
    (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2))
    (i : Fin 3) :
    eigenbasis hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh i =
      rightEigenvector k g C φ b q i :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

/-- The basis diagonalizes the full derivative. -/
theorem fderiv_flux_eigenbasis {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3} (hk : Differentiable ℝ k)
    (hg : Differentiable ℝ g) (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ)
    (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d) (hleft : ∀ s, s ≤ a → C s = 1)
    (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2))
    (i : Fin 3) :
    fderiv ℝ (flux k g C φ b) q (eigenbasis hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh
      i) = speed k g C φ q i •
      eigenbasis hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh i := by
  simpa only [eigenbasis_apply] using
    fderiv_flux_rightEigenvector hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh i

/-- Scalar gaps and the gate geometry imply strict hyperbolicity at the state. -/
theorem isStrictlyHyperbolicAt {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3} (hk : Differentiable ℝ k)
    (hg : Differentiable ℝ g) (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ)
    (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d) (hleft : ∀ s, s ≤ a → C s = 1)
    (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2)) :
    IsStrictlyHyperbolicAt (flux k g C φ b) q := by
  refine ⟨differentiable_flux hk hg hC hφ hb q,
    eigenbasis hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh,
    speed k g C φ q, (speed_strictMono hlow hhigh).injective, fun i ↦ ?_⟩
  simpa only [eigenbasis_apply] using
    hasEigenvector_fderiv_flux hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh i

/-- The repository's canonical ordered speeds equal the explicit scalar formulas. -/
theorem characteristicSpeed_eq {k g C φ b : ℝ → ℝ} {a d e : ℝ} {q : ℝ^3} (hk : Differentiable ℝ k)
    (hg : Differentiable ℝ g) (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ)
    (hb : Differentiable ℝ b) (ha : 0 < a) (had : a < d) (hleft : ∀ s, s ≤ a → C s = 1)
    (hright : ∀ s, d ≤ s → C s = 0) (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : -deriv k (q 0) < middleSpeed g C φ q) (hhigh : middleSpeed g C φ q < deriv k (q 2)) :
    (fun i ↦ System.characteristicSpeed (flux k g C φ b) i q) = speed k g C φ q := by
  exact System.characteristicSpeed_eq_of_eigenbasis
    (eigenbasis hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh)
    (speed_strictMono hlow hhigh)
    (fderiv_flux_eigenbasis hk hg hC hφ hb ha had hleft hright hsupport hlow hhigh)

/-- Global scalar gaps imply strict hyperbolicity on the whole state space. -/
theorem isStrictlyHyperbolicOn_univ
    {k g C φ b : ℝ → ℝ} {a d e : ℝ}
    (hk : Differentiable ℝ k) (hg : Differentiable ℝ g)
    (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b)
    (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0)
    (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : ∀ q : ℝ^3, -deriv k (q 0) < middleSpeed g C φ q)
    (hhigh : ∀ q : ℝ^3, middleSpeed g C φ q < deriv k (q 2)) :
    IsStrictlyHyperbolicOn (flux k g C φ b) univ := fun q _ ↦
  isStrictlyHyperbolicAt hk hg hC hφ hb ha had hleft hright hsupport (hlow q) (hhigh q)

/-- Global gap bounds identify each canonical speed as a function of the state.
This equality can be differentiated in the later genuine-nonlinearity proof. -/
theorem characteristicSpeed_eq_fun
    {k g C φ b : ℝ → ℝ} {a d e : ℝ}
    (hk : Differentiable ℝ k) (hg : Differentiable ℝ g)
    (hC : Differentiable ℝ C) (hφ : Differentiable ℝ φ) (hb : Differentiable ℝ b)
    (ha : 0 < a) (had : a < d)
    (hleft : ∀ s, s ≤ a → C s = 1) (hright : ∀ s, d ≤ s → C s = 0)
    (hsupport : tsupport b ⊆ Ioo d e)
    (hlow : ∀ q : ℝ^3, -deriv k (q 0) < middleSpeed g C φ q)
    (hhigh : ∀ q : ℝ^3, middleSpeed g C φ q < deriv k (q 2)) (i : Fin 3) :
    System.characteristicSpeed (flux k g C φ b) i = fun q ↦ speed k g C φ q i :=
  funext fun q ↦ congrFun (characteristicSpeed_eq hk hg hC hφ hb ha had hleft hright hsupport
    (hlow q) (hhigh q)) i

end PDE.Hyperbolic.ConservationLaw.System.GatedFlux
