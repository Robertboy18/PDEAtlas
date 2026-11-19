/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.TestPairing
public import PDE.Spaces.Sobolev.Periodic.ClassicalLift
public import PDE.Analysis.Calculus.Gradient

/-!
# Periodic potentials from Euclidean compact tests

Periodization commutes with the classical gradient. A compactly supported C¹
function therefore gives an actual periodic differentiable potential whose
gradient is the periodization of its Euclidean gradient.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Gradient

namespace SobolevSpace.Periodic

/-- Periodization commutes with the classical gradient. -/
theorem gradient_periodize {n : ℕ} {f : ℝ^n → ℝ}
    (hf : Differentiable ℝ f) (hfc : HasCompactSupport f) (x : ℝ^n) :
    ∇ (periodize f) x = periodize (∇ f) x := by
  change (InnerProductSpace.toDual ℝ (ℝ^n)).symm (fderiv ℝ (periodize f) x) = _
  rw [(hasFDerivAt_periodize hf hfc x).fderiv]
  exact map_periodize
    (InnerProductSpace.toDual ℝ (ℝ^n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    (hfc.fderiv ℝ) x

/-- A compactly supported C¹ Euclidean test periodizes to a genuine differentiable
potential on the torus, with gradient equal to its periodized Euclidean gradient. -/
theorem hasDerivAt_periodizeTorus {n : ℕ} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (y : UnitAddTorus (Fin n)) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s ↦ periodizeTorus f hf.continuous hfc (y + coordinateShift i s))
      (periodizeTorus (∇ f) (PDE.Analysis.continuous_gradient_of_contDiff hf)
        hfc.gradient (y + coordinateShift i t) i) t := by
  obtain ⟨x, rfl⟩ := (isOpenQuotientMap_toTorus n).surjective y
  have hfd := hf.differentiable (by simp)
  have hl : HasDerivAt (fun s ↦ x + s • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
  have hd := (hasFDerivAt_periodize hfd hfc _).comp_hasDerivAt t hl
  have he : periodize (fderiv ℝ f) (x + t • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) = periodize (∇ f) (x + t • EuclideanSpace.single i 1) i := by
    rw [← (hasFDerivAt_periodize hfd hfc _).fderiv,
      ← inner_gradient_left, gradient_periodize hfd hfc]
    simpa only [one_mul, conj_trivial] using EuclideanSpace.inner_single_right i (1 : ℝ)
      (periodize (∇ f) (x + t • EuclideanSpace.single i 1))
  simp only [← toTorus_add_single, periodizeTorus_toTorus]
  simpa only [Function.comp_def, he] using hd

end SobolevSpace.Periodic
