/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.System
public import PDE.FDeriv.Operators
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Two instances of the analytic regularity theorem for systems

## Motivation

Are the hypotheses of the analytic regularity theorem for autonomous diagonal systems, and of
its local setting `SolutionOnBall`, satisfied by concrete systems and concrete solutions, also
when the forcing is not zero?

## The idea

Take the identity matrix as coefficients. Without forcing, the flux of the component `l` in the
direction `i` is `∂ᵢ v_l`, so the system says that every component of `v` is harmonic. The
coefficients are constant, hence analytic, and the quadratic form of the identity matrix is
`|ξ|²`. So every smooth family of harmonic functions satisfies the hypotheses, and constant
families do so on the whole space.

With the forcing `f_{l i}(w) = bᵢ w_l`, for a fixed vector `b`, the system is
`Δ v_l - b · ∇v_l = 0`. The family `v_l(x) = c_l exp⟨b, x⟩` solves it: its flux
`∂ᵢ v_l - bᵢ v_l` vanishes at every point. The forcing is linear, hence analytic, and it is not
zero when `b ≠ 0`.

## Main results

* `sum_partialDeriv_flux_identity`: for the identity coefficients and zero forcing the left side
  of the system is the Laplacian of the component. All families, all points.
* `analyticOnNhd_of_laplacian_eq_zero` (one system, all dimensions, all finite families, all
  open sets): a smooth family of harmonic functions is real-analytic.
* `exists_solutionOnBall_const` (one system, all constant families, all centres): the local
  setting `SolutionOnBall` has an instance.
* `flux_identity_exponentialFamily` and `analyticOnNhd_exponentialFamily` (a family of systems:
  all dimensions, all vectors `b`, all finite families of constants `c`): the family
  `c_l exp⟨b, x⟩` satisfies the hypotheses of the theorem for the forcing `bᵢ w_l`.

## Relations

`analyticOnNhd_of_laplacian_eq_zero` and `analyticOnNhd_exponentialFamily` are
`PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_autonomous_system` for these systems, and
`exists_solutionOnBall_const` is `PDE.Elliptic.Regularity.Analytic.exists_solutionOnBall` for a
constant family. For one function, `LaplacianEquation.IsHarmonicPDE.analyticOnNhd` proves more
in positive dimension: it starts from a `C²` harmonic function. The conclusion of
`analyticOnNhd_exponentialFamily` also follows from the analyticity of the exponential. The
theorem is stated to show that the hypotheses hold together with a forcing that is not zero.

## What stays open

Both systems have constant coefficients. Coefficients that depend on the solution occur in the
gradient system of `PDE.Elliptic.Regularity.Analytic.GradientDensity`. No example has a flux
that does not vanish together with a forcing that is not zero.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff
open SobolevSpace.GraphSpace.BoundaryRegularity (principalEnergy)

namespace PDE.Examples.AnalyticSystem

open PDE.Elliptic.Regularity.Analytic

variable {n : ℕ} {I : Type*}

/-- For the identity coefficients and zero forcing, the left side of the autonomous diagonal
system is the Laplacian of the component: `∑ᵢ ∂ᵢ (∂ᵢ v_l) = Δ v_l`. -/
theorem sum_partialDeriv_flux_identity (v : ℝ^n → I → ℝ) (l : I) (x : ℝ^n) :
    ∑ i, (∂[i] (flux (fun i j _ ↦ if i = j then (1 : ℝ) else 0) (fun _ _ _ ↦ 0) v l i)) x =
      PDE.laplacian (fun y ↦ v y l) x := by
  have hflux (i : Fin n) :
      flux (fun i j _ ↦ if i = j then (1 : ℝ) else 0) (fun _ _ _ ↦ 0) v l i =
        ∂[i] (fun y ↦ v y l) := by
    funext y
    simp [flux]
  simp only [hflux, PDE.laplacian]

/-- The coordinate derivatives of an exponential of a linear functional:
`∂ᵢ (c exp⟨b, ·⟩) = bᵢ c exp⟨b, ·⟩`. -/
theorem partialDeriv_const_mul_exp_inner (b : ℝ^n) (c : ℝ) (i : Fin n) (x : ℝ^n) :
    (∂[i] (fun y : ℝ^n ↦ c * Real.exp (inner ℝ b y))) x = b i * (c * Real.exp (inner ℝ b x)) := by
  have h1 : HasFDerivAt (fun y : ℝ^n ↦ inner ℝ b y) (innerSL ℝ b) x := (innerSL ℝ b).hasFDerivAt
  have h2 := (h1.exp).const_mul c
  change fderiv ℝ (fun y : ℝ^n ↦ c * Real.exp (inner ℝ b y)) x (EuclideanSpace.single i 1) = _
  rw [h2.fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial,
    one_mul, smul_eq_mul]
  ring

/-- **The flux of the exponential family vanishes.** For the identity coefficients and the
forcing `f_{l i}(w) = bᵢ w_l`, the flux `∂ᵢ v_l - bᵢ v_l` of the family
`v_l(x) = c_l exp⟨b, x⟩` is zero at every point. All dimensions, all vectors `b`, all families
of constants `c`. -/
theorem flux_identity_exponentialFamily (b : ℝ^n) (c : I → ℝ) (l : I) (i : Fin n) (y : ℝ^n) :
    flux (fun i j _ ↦ if i = j then (1 : ℝ) else 0) (fun l i w ↦ b i * w l)
      (fun x l ↦ c l * Real.exp (inner ℝ b x)) l i y = 0 := by
  simp [flux, partialDeriv_const_mul_exp_inner]

variable [Fintype I]

/-- The quadratic form of the identity matrix is `|ξ|²`. -/
theorem principalEnergy_identity (ξ : Fin n → ℝ) :
    principalEnergy (fun i j ↦ if i = j then (1 : ℝ) else 0) ξ = ∑ i, ξ i ^ 2 := by
  simp [principalEnergy, sq]

/-- **Smooth harmonic families are analytic.** Let `Ω ⊆ ℝ^n` be open and let `v = (v_l)` be a
smooth family on `Ω` with `Δ v_l = 0` at every point of `Ω`, for every `l`. Then `v` is
real-analytic on `Ω`. This is the analytic regularity theorem for autonomous diagonal systems
with the identity matrix as coefficients and no forcing. -/
theorem analyticOnNhd_of_laplacian_eq_zero {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {v : ℝ^n → I → ℝ}
    (hv : ContDiffOn ℝ ∞ v Ω) (hharm : ∀ x ∈ Ω, ∀ l, PDE.laplacian (fun y ↦ v y l) x = 0) :
    AnalyticOnNhd ℝ v Ω :=
  analyticOnNhd_of_autonomous_system hΩ hv (fun _ _ _ _ ↦ analyticAt_const)
    (fun _ _ _ _ ↦ analyticAt_const)
    (fun _ _ ↦ ⟨1, one_pos, fun ξ ↦ by rw [principalEnergy_identity, one_mul]⟩)
    (fun x hx l ↦ by rw [sum_partialDeriv_flux_identity]; exact hharm x hx l)

/-- **The local setting has an instance.** For every constant family `c` and every centre `x₀`
there are an open set, a radius and constants for which `SolutionOnBall` holds, with the
identity matrix as coefficients and no forcing. -/
theorem exists_solutionOnBall_const (c : I → ℝ) (x₀ : ℝ^n) :
    ∃ (U : Set (ℝ^n)) (R lam Lam C K : ℝ),
      SolutionOnBall (fun i j _ ↦ if i = j then (1 : ℝ) else 0) (fun _ _ _ ↦ 0)
        (fun _ : ℝ^n ↦ c) U x₀ R lam Lam C K := by
  obtain ⟨U, R, lam, Lam, C, K, -, hS⟩ := exists_solutionOnBall (Ω := univ) isOpen_univ
    (contDiffOn_const (c := c)) (fun _ _ _ _ ↦ analyticAt_const)
    (fun _ _ _ _ ↦ analyticAt_const)
    (fun _ _ ↦ ⟨1, one_pos, fun ξ ↦ by rw [principalEnergy_identity, one_mul]⟩)
    (fun x _ l ↦ by
      rw [sum_partialDeriv_flux_identity]
      simp [PDE.laplacian, partialDeriv_const])
    (mem_univ x₀)
  exact ⟨U, R, lam, Lam, C, K, hS⟩

/-- **An instance with a forcing that is not zero.** For every vector `b` and every finite
family of constants `c`, the family `v_l(x) = c_l exp⟨b, x⟩` on `ℝ^n` satisfies the hypotheses
of the analytic regularity theorem for the system with the identity matrix as coefficients and
the forcing `f_{l i}(w) = bᵢ w_l`, that is `Δ v_l - b · ∇v_l = 0`. The theorem then gives that
the family is real-analytic. The equation holds because the flux vanishes
(`flux_identity_exponentialFamily`). -/
theorem analyticOnNhd_exponentialFamily (b : ℝ^n) (c : I → ℝ) :
    AnalyticOnNhd ℝ (fun (x : ℝ^n) (l : I) ↦ c l * Real.exp (inner ℝ b x)) univ :=
  analyticOnNhd_of_autonomous_system (f := fun l i w ↦ b i * w l) isOpen_univ
    (contDiff_pi.mpr fun l ↦
      contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.inner ℝ contDiff_id))).contDiffOn
    (fun _ _ _ _ ↦ analyticAt_const)
    (fun _ _ l _ ↦ analyticAt_const.mul
      (show AnalyticAt ℝ (fun w : I → ℝ ↦ w l) _ from
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I ↦ ℝ) l).analyticAt _))
    (fun _ _ ↦ ⟨1, one_pos, fun ξ ↦ by rw [principalEnergy_identity, one_mul]⟩)
    (fun x _ l ↦ by
      have h (i : Fin n) :
          flux (fun i j _ ↦ if i = j then (1 : ℝ) else 0) (fun l i w ↦ b i * w l)
            (fun x l ↦ c l * Real.exp (inner ℝ b x)) l i = fun _ ↦ 0 :=
        funext (flux_identity_exponentialFamily b c l i)
      simp [h, partialDeriv_const])

end PDE.Examples.AnalyticSystem
