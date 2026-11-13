/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Bridge to Mathlib harmonic functions

LeanPDE's `LaplacianEquation.IsHarmonicPDE` uses the coordinate Laplacian and permits
relative `C²` regularity on an arbitrary set. Mathlib's
`InnerProductSpace.HarmonicOnNhd` uses the canonical inner-product-space Laplacian
and requires harmonicity in a neighborhood of every point.

Mathlib harmonicity therefore always implies LeanPDE harmonicity. The converse is
valid on open sets, where relative regularity and pointwise vanishing promote to
neighborhood statements. These equivalences let the classical elliptic theory use
Mathlib's harmonic functions while keeping LeanPDE's predicate on arbitrary sets.
-/

@[expose] public section

open PDE (laplacian)

namespace InnerProductSpace

/-- Mathlib harmonicity implies LeanPDE's coordinate formulation on any set. -/
theorem HarmonicOnNhd.isHarmonicPDE {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : HarmonicOnNhd u U) :
    LaplacianEquation.IsHarmonicPDE n u U := by
  refine ⟨hu.contDiffOn, ?_⟩
  intro x hx
  rw [(hu x hx).1.coordinate_laplacian_eq_laplacian]
  simpa using (hu x hx).2.eq_of_nhds

end InnerProductSpace

namespace LaplacianEquation

/-- On an open set, LeanPDE harmonicity gives Mathlib harmonicity in a neighborhood. -/
theorem IsHarmonicPDE.harmonicOnNhd {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U) :
    InnerProductSpace.HarmonicOnNhd u U := by
  intro x hx
  have huReg : ContDiffAt ℝ 2 u x :=
    hu.contDiffAt_of_isOpen hU hx
  refine ⟨huReg, ?_⟩
  filter_upwards [
      huReg.eventually (by norm_num),
      hu.eventually_laplacian_eq_zero_of_isOpen hU hx
    ] with y hyReg hyLaplacian
  calc
    Laplacian.laplacian u y = laplacian u y :=
      hyReg.coordinate_laplacian_eq_laplacian.symm
    _ = 0 := hyLaplacian
    _ = (0 : ℝ^n → ℝ) y := rfl

/-- On an open set, LeanPDE and Mathlib harmonicity are equivalent. -/
theorem isHarmonicPDE_iff_harmonicOnNhd {n : ℕ}
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)} (hU : IsOpen U) :
    IsHarmonicPDE n u U ↔ InnerProductSpace.HarmonicOnNhd u U :=
  ⟨fun hu ↦ hu.harmonicOnNhd hU,
    InnerProductSpace.HarmonicOnNhd.isHarmonicPDE⟩

end LaplacianEquation
