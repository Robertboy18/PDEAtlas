/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Nonzero supported functions in H¹₀

A nonzero value of a smooth supported function inside an open domain remains
nonzero in its `L²` coordinate. A smooth bump therefore supplies a
nonzero `H¹₀` element on every nonempty open domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonzero pointwise value of a supported test function in an open domain
cannot vanish after passage to the `L²` coordinate. -/
theorem baseCoordCLM_testFunction_ne_zero
    (hΩ : IsOpen Ω) (φ : TestFunctionOn n Ω) {x : ℝ^n}
    (hx : x ∈ Ω) (hφ : φ.1.toFun x ≠ 0) :
    baseCoordCLM (testFunctionToH10 φ) ≠ 0 := by
  intro hz
  have hae := baseCoordCLM_testFunction_apply_ae φ
  rw [hz] at hae
  have hzero : φ.1.toFun =ᵐ[volume.restrict Ω] 0 :=
    hae.symm.trans (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω))
  exact hφ (Measure.eqOn_open_of_ae_eq hzero hΩ
    φ.1.contDiff.continuous.continuousOn continuous_const.continuousOn hx)

/-- A nonempty open domain contains a supported smooth bump whose
`L²` base coordinate is nonzero. No boundary regularity is needed. -/
theorem exists_testFunction_baseCoord_ne_zero
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ φ : TestFunctionOn n Ω, baseCoordCLM (testFunctionToH10 φ) ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, hsupp, hcompact, hsmooth, _, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hΩ.mem_nhds hx)
  let φ : TestFunctionOn n Ω :=
    ⟨_root_.TestFunction.mk f hsmooth hcompact (subset_univ _), hsupp⟩
  refine ⟨φ, baseCoordCLM_testFunction_ne_zero hΩ φ hx ?_⟩
  change f x ≠ 0
  rw [hfx]
  exact one_ne_zero

end SobolevSpace.GraphSpace
