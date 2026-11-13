/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SymmetricSystem
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Plane waves for constant-coefficient first-order systems

We treat the plane waves (4) of Evans, §7.3.1, for constant coefficients. A spatial covector
`xi`, temporal frequency `omega`, and vector profile `psi` determine the plane wave

`u(t,x) = psi(-omega * t + <xi,x>)`.

Evans's substitution says that this is a solution precisely when `psi'`
lies in the `omega`-eigenspace of the principal symbol. We prove this
equivalence pointwise and the induced initial trace. As a formal corollary,
a fixed polarization satisfying the symbol eigenvalue equation gives waves
for arbitrary differentiable scalar profiles.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.1, equations (3)-(4) and the computation after them.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE.Common
open scoped InnerProductSpace

namespace PDE.Hyperbolic.FirstOrder

namespace LinearFirstOrderSystem

variable {n m : ℕ}

/-- A homogeneous first-order system with coefficients independent of spacetime. -/
def homogeneousConstant
    (B : Fin n → ℝ^m →L[ℝ] ℝ^m) :
    LinearFirstOrderSystem n m where
  coefficient := fun j _ ↦ B j
  forcing := fun _ ↦ 0
  domain := Set.univ

/-- The coefficient family of `homogeneousConstant B` is `B`. -/
@[simp]
theorem homogeneousConstant_coefficient (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (j : Fin n) (p : SpaceTime n) :
    (homogeneousConstant B).coefficient j p = B j :=
  rfl

/-- A homogeneous constant-coefficient system has zero forcing. -/
@[simp]
theorem homogeneousConstant_forcing (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (p : SpaceTime n) :
    (homogeneousConstant B).forcing p = 0 :=
  rfl

/-- A homogeneous constant-coefficient system is defined on all spacetime. -/
@[simp]
theorem homogeneousConstant_domain (B : Fin n → ℝ^m →L[ℝ] ℝ^m) :
    (homogeneousConstant B).domain = Set.univ :=
  rfl

/-- The principal symbol of a constant coefficient family. -/
def constantPrincipalSymbol
    (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (xi : ℝ^n) :
    ℝ^m →L[ℝ] ℝ^m :=
  (homogeneousConstant B).principalSymbol (0 : SpaceTime n) xi

/-- The principal symbol of a constant-coefficient system is independent of spacetime. -/
@[simp]
theorem homogeneousConstant_principalSymbol (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (p : SpaceTime n)
    (xi : ℝ^n) :
    (homogeneousConstant B).principalSymbol p xi = constantPrincipalSymbol B xi :=
  rfl

/-- The spacetime phase `-omega t + <xi,x>`, as a continuous linear map. -/
def phaseMap (omega : ℝ) (xi : ℝ^n) : SpaceTime n →L[ℝ] ℝ :=
  (-omega) • EuclideanSpace.proj (0 : Fin (n + 1)) +
    (innerSL ℝ xi).comp (spatialPartCLM n)

/-- Evaluation formula for the plane-wave phase. -/
theorem phaseMap_apply (omega : ℝ) (xi : ℝ^n) (p : SpaceTime n) :
    phaseMap omega xi p = -omega * p 0 + ⟪xi, spatialPartCLM n p⟫_ℝ := by
  simp [phaseMap, innerSL_apply_apply, smul_eq_mul]

/-- The time coordinate derivative of the phase is `-omega`. -/
@[simp]
theorem phaseMap_single_zero (omega : ℝ) (xi : ℝ^n) :
    phaseMap omega xi (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = -omega := by
  rw [phaseMap_apply, spatialPartCLM_single_zero]
  simp

/-- The `j`th spatial coordinate derivative of the phase is `xi j`. -/
@[simp]
theorem phaseMap_single_succ (omega : ℝ) (xi : ℝ^n) (j : Fin n) :
    phaseMap omega xi (EuclideanSpace.single (j.succ : Fin (n + 1)) (1 : ℝ)) = xi j := by
  rw [phaseMap_apply, spatialPartCLM_single_succ]
  simpa using (EuclideanSpace.inner_single_right
      (𝕜 := ℝ) (ι := Fin n) (i := j) (a := (1 : ℝ)) (v := xi))

/-- Evans's plane wave with vector-valued profile `psi`. -/
def planeWave
    (omega : ℝ) (xi : ℝ^n) (psi : ℝ → ℝ^m) :
    SpaceTime n → ℝ^m :=
  fun p ↦ psi (phaseMap omega xi p)

/-- Coordinate derivative of a differentiable vector-profile plane wave. -/
theorem partialDeriv_planeWave (omega : ℝ) (xi : ℝ^n) (psi : ℝ → ℝ^m) (p : SpaceTime n)
    (i : Fin (n + 1)) (hpsi : DifferentiableAt ℝ psi (phaseMap omega xi p)) :
    (∂[i] (planeWave omega xi psi)) p =
      phaseMap omega xi (EuclideanSpace.single i (1 : ℝ)) • deriv psi (phaseMap omega xi p) := by
  unfold partialDeriv planeWave
  have hchain : fderiv ℝ (fun q ↦ psi (phaseMap omega xi q)) p =
        (fderiv ℝ psi (phaseMap omega xi p)).comp
          (phaseMap omega xi) := by
    exact (hpsi.hasFDerivAt.comp p (phaseMap omega xi).hasFDerivAt).fderiv
  rw [hchain]
  simp [ContinuousLinearMap.comp_apply]

/-- Substitution of Evans's vector-profile plane wave into the homogeneous operator. -/
theorem homogeneousConstant_operator_planeWave (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (omega : ℝ) (xi : ℝ^n)
    (psi : ℝ → ℝ^m) (p : SpaceTime n) (hpsi : DifferentiableAt ℝ psi (phaseMap omega xi p)) :
    (homogeneousConstant B).operator (planeWave omega xi psi) p = (-omega) • deriv psi
      (phaseMap omega xi p) + constantPrincipalSymbol B xi (deriv psi (phaseMap omega xi p)) := by
  rw [operator]
  rw [partialDeriv_planeWave omega xi psi p 0 hpsi]
  simp_rw [partialDeriv_planeWave omega xi psi p _ hpsi]
  rw [phaseMap_single_zero]
  simp_rw [phaseMap_single_succ]
  simp only [constantPrincipalSymbol, principalSymbol,
    homogeneousConstant_coefficient, map_smul, _root_.sum_apply, _root_.smul_apply]

/-- Evans's vector-profile plane wave solves the equation at `p` exactly
when its profile derivative there satisfies the symbol eigenvalue equation. -/
theorem homogeneousConstant_operator_planeWave_eq_zero_iff (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (omega : ℝ)
    (xi : ℝ^n) (psi : ℝ → ℝ^m) (p : SpaceTime n)
    (hpsi : DifferentiableAt ℝ psi (phaseMap omega xi p)) :
    (homogeneousConstant B).operator (planeWave omega xi psi) p = 0 ↔ constantPrincipalSymbol B xi
      (deriv psi (phaseMap omega xi p)) = omega • deriv psi (phaseMap omega xi p) := by
  rw [homogeneousConstant_operator_planeWave B omega xi psi p hpsi]
  constructor
  · intro h
    simpa using eq_neg_of_add_eq_zero_right h
  · intro h
    rw [h]
    simp

/-- Evans's eigenvalue equation for `psi'` makes the vector-profile plane wave a solution. -/
theorem homogeneousConstant_operator_planeWave_eq_zero (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (omega : ℝ)
    (xi : ℝ^n) (psi : ℝ → ℝ^m) (p : SpaceTime n)
    (hpsi : DifferentiableAt ℝ psi (phaseMap omega xi p))
    (heigen : constantPrincipalSymbol B xi (deriv psi (phaseMap omega xi p)) =
      omega • deriv psi (phaseMap omega xi p)) :
    (homogeneousConstant B).operator (planeWave omega xi psi) p = 0 :=
  (homogeneousConstant_operator_planeWave_eq_zero_iff B omega xi psi p hpsi).2 heigen

/-- Initial data induced by a vector-profile plane wave. -/
def planeWaveVectorInitialData
    (xi : ℝ^n) (psi : ℝ → ℝ^m) :
    ℝ^n → ℝ^m :=
  fun x ↦ psi ⟪xi, x⟫_ℝ

/-- A differentiable vector profile whose derivative lies pointwise in one
symbol eigenspace solves Evans's homogeneous initial-value problem. -/
theorem planeWave_satisfies_initialValueProblem (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (omega : ℝ) (xi : ℝ^n)
    (psi : ℝ → ℝ^m) (hpsi : Differentiable ℝ psi)
    (heigen : ∀ s, constantPrincipalSymbol B xi (deriv psi s) = omega • deriv psi s) :
    SatisfiesPDEProblem ((homogeneousConstant B).initialValueProblem
      (planeWaveVectorInitialData xi psi)) (planeWave omega xi psi) := by
  apply initialValueProblem.of_operator_initial
  · intro p _
    rw [homogeneousConstant_forcing]
    exact homogeneousConstant_operator_planeWave_eq_zero B omega xi psi p (hpsi _) (heigen _)
  · intro p hp
    unfold planeWave planeWaveVectorInitialData
    rw [phaseMap_apply]
    change p 0 = 0 at hp
    rw [hp]
    simp

/-- A scalar profile traveling in the direction `xi`, with polarization `v`. -/
def profilePlaneWave
    (omega : ℝ) (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m) :
    SpaceTime n → ℝ^m :=
  planeWave omega xi (fun s ↦ phi s • v)

/-- Coordinate derivative of a differentiable scalar-profile plane wave. -/
theorem partialDeriv_profilePlaneWave (omega : ℝ) (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m)
    (p : SpaceTime n) (i : Fin (n + 1)) (hphi : DifferentiableAt ℝ phi (phaseMap omega xi p)) :
    (∂[i] (profilePlaneWave omega xi phi v)) p = (deriv phi (phaseMap omega xi p) *
      phaseMap omega xi (EuclideanSpace.single i (1 : ℝ))) • v := by
  simpa [profilePlaneWave, deriv_smul_const hphi v, smul_smul, mul_comm] using
    partialDeriv_planeWave omega xi (fun s ↦ phi s • v) p i (hphi.smul_const v)

/-- Substituting a profile plane wave reduces the PDE operator to the
principal-symbol eigenvalue residual. -/
theorem homogeneousConstant_operator_profilePlaneWave (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (omega : ℝ)
    (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m) (p : SpaceTime n)
    (hphi : DifferentiableAt ℝ phi (phaseMap omega xi p)) :
    (homogeneousConstant B).operator (profilePlaneWave omega xi phi v) p =
      deriv phi (phaseMap omega xi p) • ((-omega) • v + constantPrincipalSymbol B xi v) := by
  simpa [profilePlaneWave, deriv_smul_const hphi v, map_smul, smul_add,
    smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    homogeneousConstant_operator_planeWave B omega xi (fun s ↦ phi s • v) p (hphi.smul_const v)

/-- A scalar-profile wave solves the equation at `p` exactly when the
profile is stationary there or its polarization satisfies the symbol
eigenvalue equation. -/
theorem homogeneousConstant_operator_profilePlaneWave_eq_zero_iff (B : Fin n → ℝ^m →L[ℝ] ℝ^m)
    (omega : ℝ) (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m) (p : SpaceTime n)
    (hphi : DifferentiableAt ℝ phi (phaseMap omega xi p)) :
    (homogeneousConstant B).operator (profilePlaneWave omega xi phi v) p = 0 ↔
      deriv phi (phaseMap omega xi p) = 0 ∨ constantPrincipalSymbol B xi v = omega • v := by
  rw [homogeneousConstant_operator_profilePlaneWave B omega xi phi v p hphi]
  rw [smul_eq_zero]
  constructor
  · rintro (hderiv | hresidual)
    · exact Or.inl hderiv
    · right
      simpa using eq_neg_of_add_eq_zero_right hresidual
  · rintro (hderiv | heigen)
    · exact Or.inl hderiv
    · right
      rw [heigen]
      simp

/-- The dispersion relation `B(xi)v = omega v` makes every differentiable
profile wave solve the homogeneous constant-coefficient equation. -/
theorem homogeneousConstant_operator_profilePlaneWave_eq_zero (B : Fin n → ℝ^m →L[ℝ] ℝ^m)
    (omega : ℝ) (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m) (p : SpaceTime n)
    (hphi : DifferentiableAt ℝ phi (phaseMap omega xi p))
    (heigen : constantPrincipalSymbol B xi v = omega • v) :
    (homogeneousConstant B).operator (profilePlaneWave omega xi phi v) p = 0 :=
  (homogeneousConstant_operator_profilePlaneWave_eq_zero_iff
    B omega xi phi v p hphi).2 (Or.inr heigen)

/-- The spatial profile induced by a plane wave on the initial slice. -/
def planeWaveInitialData
    (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m) :
    ℝ^n → ℝ^m :=
  planeWaveVectorInitialData xi (fun s ↦ phi s • v)

/-- A polarization satisfying the symbol eigenvalue equation produces a
solution of the bundled initial-value problem, including its exact trace at
`t = 0`. -/
theorem profilePlaneWave_satisfies_initialValueProblem (B : Fin n → ℝ^m →L[ℝ] ℝ^m) (omega : ℝ)
    (xi : ℝ^n) (phi : ℝ → ℝ) (v : ℝ^m) (hphi : Differentiable ℝ phi)
    (heigen : constantPrincipalSymbol B xi v = omega • v) :
    SatisfiesPDEProblem ((homogeneousConstant B).initialValueProblem
      (planeWaveInitialData xi phi v)) (profilePlaneWave omega xi phi v) := by
  apply planeWave_satisfies_initialValueProblem
  · exact hphi.smul_const v
  · intro s
    simp [deriv_smul_const (hphi s) v, map_smul, heigen, smul_smul, mul_comm]

end LinearFirstOrderSystem

end PDE.Hyperbolic.FirstOrder
