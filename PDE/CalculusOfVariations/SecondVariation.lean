/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.QuadraticEnergy
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.Module.ModuleTopology
import PDE.CalculusOfVariations.SecondOrderNecessaryCondition

/-!
# Second variations of abstract quadratic energies

For a symmetric bounded bilinear form `B` and load `ell`, we compute both
Fréchet derivatives of `energy B ell`, prove its exact quadratic expansion, and
derive the first- and second-order necessary conditions at a local minimum.
This is a bounded quadratic specialization of the first- and second-variation
arguments of Evans, §8.1.2 and §8.1.3.

The differentiation rules come from Mathlib.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.2 and §8.1.3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set
open PDE.Analysis.Variational

namespace PDE.CalculusOfVariations

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The first Fréchet derivative of a symmetric quadratic energy is `B u - ell`. -/
theorem quadraticEnergy_hasFDerivAt
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) (u : V) :
    HasFDerivAt (energy B ell) (B u - ell) u := by
  -- The bilinear derivative rule produces two mixed terms, which symmetry combines.
  have hquadraticRaw :=
    B.hasFDerivAt_of_bilinear
      (hasFDerivAt_id (𝕜 := ℝ) (x := u))
      (hasFDerivAt_id (𝕜 := ℝ) (x := u))
  have hquadratic :
      HasFDerivAt (fun w : V ↦ (1 / 2 : ℝ) * B w w) (B u) u := by
    apply (hquadraticRaw.const_mul (1 / 2 : ℝ)).congr_fderiv
    ext v
    simp [hBsymm v u]
    ring
  change HasFDerivAt (fun w : V ↦ (1 / 2 : ℝ) * B w w - ell w) (B u - ell) u
  exact hquadratic.sub ell.hasFDerivAt

/-- The quadratic first variation is a strict Fréchet derivative; its
derivative field is continuous because the bilinear form is bounded. -/
theorem quadraticEnergy_hasStrictFDerivAt
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) (u : V) :
    HasStrictFDerivAt (energy B ell) (B u - ell) u :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Eventually.of_forall (quadraticEnergy_hasFDerivAt B hBsymm ell))
    (B.continuous.sub continuous_const).continuousAt

/-- Formula for the first variation of a symmetric quadratic energy. -/
theorem quadraticEnergy_fderiv
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) (u : V) :
    fderiv ℝ (energy B ell) u = B u - ell :=
  (quadraticEnergy_hasFDerivAt B hBsymm ell u).fderiv

/-- A local minimizer of a symmetric quadratic energy satisfies its weak Euler equation. -/
theorem quadraticEnergy_isWeakSolution_of_isLocalMin
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) {u : V}
    (hmin : IsLocalMin (energy B ell) u) :
    IsWeakSolution (V := V) B ell u := by
  have hzero : B u - ell = 0 :=
    hmin.hasFDerivAt_eq_zero
      (quadraticEnergy_hasFDerivAt B hBsymm ell u)
  exact fun v ↦ DFunLike.congr_fun (sub_eq_zero.mp hzero) v

/-- The derivative of the first-variation map is the original bilinear form. -/
theorem quadraticEnergy_firstVariation_hasFDerivAt
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) (u : V) :
    HasFDerivAt (fun w ↦ fderiv ℝ (energy B ell) w) B u := by
  rw [fderiv_eq fun w ↦ quadraticEnergy_hasFDerivAt B hBsymm ell w]
  exact B.hasFDerivAt.sub_const ell

/-- The second variation of a symmetric quadratic energy is constant and equal to `B`. -/
theorem quadraticEnergy_secondVariation_eq
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) (u : V) :
    fderiv ℝ (fun w ↦ fderiv ℝ (energy B ell) w) u = B :=
  (quadraticEnergy_firstVariation_hasFDerivAt B hBsymm ell u).fderiv

/-- Exact second-order Taylor formula for a symmetric quadratic energy. -/
theorem quadraticEnergy_add_eq
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) (u v : V) :
    energy B ell (u + v) =
      energy B ell u + (B u - ell) v + (1 / 2 : ℝ) * B v v := by
  simp only [energy, map_add, add_apply, sub_apply]
  rw [hBsymm v u]
  ring

/-- The second variation of a symmetric quadratic energy is nonnegative in every direction
at a local minimum. -/
theorem quadraticEnergy_secondVariation_nonneg_of_isLocalMin
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ v w, B v w = B w v)
    (ell : StrongDual ℝ V) {u : V}
    (hmin : IsLocalMin (energy B ell) u) (v : V) :
    0 ≤ B v v := by
  have hsmooth : ContDiffAt ℝ 2 (energy B ell) u := by
    unfold energy
    fun_prop
  rw [← quadraticEnergy_secondVariation_eq B hBsymm ell u]
  exact hmin.fderiv_fderiv_apply_self_nonneg hsmooth v

end

end PDE.CalculusOfVariations
