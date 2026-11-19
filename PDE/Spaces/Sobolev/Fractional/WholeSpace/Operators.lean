/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Definitions

/-!
# Operators on fractional Sobolev spaces

We record how the standard operators move between the fractional scales
`H^s(ℝ^n; ℂ)`:

* the inclusion `H^s ⊆ H^t` for `t ≤ s`;
* a directional derivative lowers the order by one;
* the Laplacian lowers the order by two.

Each is a `ℂ`-linear map.  The underlying membership facts are
Mathlib's `TemperedDistribution.MemSobolev.mono`, `.lineDerivOp`, and
`.laplacian`.

## Operator norms

For the inclusion,
`Fractional.WholeSpace.Embedding` proves
`norm_inclLinear_le : ‖inclLinear n h u‖ ≤ ‖u‖` and bundles the inclusion as a
continuous linear map `inclCLM` of operator norm at most one.

The derivative and Laplacian maps are bounded too; see
`Fractional.WholeSpace.OperatorBounds`, which supplies
`lineDerivCLM` and `laplacianCLM` with operator norms at most `2π‖m‖` and
`(2π)²`.  Those constants are not `1`, unlike the inclusion, because Mathlib's
Fourier convention gives `∂_{m}` the symbol `2πi⟪ξ,m⟫`.
-/

@[expose] public section

open TemperedDistribution MeasureTheory
open scoped BesselPotentialSpace ENNReal SchwartzMap LineDeriv Laplacian

namespace SobolevSpace.Fractional

variable {n : ℕ} {s t : ℝ}

open BesselPotentialSpace

/-- The inclusion `H^s ⊆ H^t` for `t ≤ s`, as a `ℂ`-linear map. -/
noncomputable def inclLinear (n : ℕ) (h : t ≤ s) : H^{s}(ℝ^n) →ₗ[ℂ] H^{t}(ℝ^n) where
  toFun u := ((memSobolev_toDistr u).mono h).toBesselPotentialSpace
  map_add' u v := by
    refine ext ?_
    simp
  map_smul' c u := by
    refine ext ?_
    simp

/-- The inclusion `H^s ⊆ H^t` does not change the underlying distribution. -/
@[simp] theorem toDistr_inclLinear (h : t ≤ s) (u : H^{s}(ℝ^n)) :
    toDistr (inclLinear n h u) = toDistr u :=
  ((memSobolev_toDistr u).mono h).toBesselPotentialSpace_toDistr

/-- The inclusion `H^s ⊆ H^t` is injective: it is the identity on the underlying
distributions, and `H^s` elements are determined by those. -/
theorem inclLinear_injective (h : t ≤ s) :
    Function.Injective (inclLinear n h) := by
  intro u v huv
  refine ext ?_
  have hd := congrArg toDistr huv
  simpa using hd

/-- A directional derivative maps `H^s` into `H^{s-1}`. -/
noncomputable def lineDerivLinear (n : ℕ) (s : ℝ) (m : ℝ^n) :
    H^{s}(ℝ^n) →ₗ[ℂ] H^{s - 1}(ℝ^n) where
  toFun u := ((memSobolev_toDistr u).lineDerivOp (m := m)).toBesselPotentialSpace
  map_add' u v := by
    refine ext ?_
    simp [LineDerivAdd.lineDerivOp_add]
  map_smul' c u := by
    refine ext ?_
    simp [LineDerivSMul.lineDerivOp_smul]

/-- The distribution underlying `lineDerivLinear n s m u` is the distributional derivative
`∂_m` of the one underlying `u`. -/
@[simp] theorem toDistr_lineDerivLinear (m : ℝ^n) (u : H^{s}(ℝ^n)) :
    toDistr (lineDerivLinear n s m u) = ∂_{m} (toDistr u) := by
  simp [lineDerivLinear]

/-- The Laplacian maps `H^s` into `H^{s-2}`. -/
noncomputable def laplacianLinear (n : ℕ) (s : ℝ) :
    H^{s}(ℝ^n) →ₗ[ℂ] H^{s - 2}(ℝ^n) where
  toFun u := (memSobolev_toDistr u).laplacian.toBesselPotentialSpace
  map_add' u v := by
    refine ext ?_
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, toDistr_add]
    exact map_add (LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓢'(ℝ^n, ℂ)) _ _
  map_smul' c u := by
    refine ext ?_
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, toDistr_smul, RingHom.id_apply]
    simpa only [TemperedDistribution.laplacianCLM_apply] using
      map_smul (LineDeriv.laplacianCLM ℂ (ℝ^n) 𝓢'(ℝ^n, ℂ)) c (toDistr u)

/-- The distribution underlying `laplacianLinear n s u` is the distributional Laplacian of
the one underlying `u`. -/
@[simp] theorem toDistr_laplacianLinear (u : H^{s}(ℝ^n)) :
    toDistr (laplacianLinear n s u) = Δ (toDistr u) := by
  simp [laplacianLinear]

/-- Every Schwartz function determines an element of `H^s`, `ℂ`-linearly. -/
noncomputable def ofSchwartzLinear (n : ℕ) (s : ℝ) :
    𝓢(ℝ^n, ℂ) →ₗ[ℂ] H^{s}(ℝ^n) where
  toFun f := (SchwartzMap.memSobolev f).toBesselPotentialSpace
  map_add' f g := by refine ext ?_; simp [map_add]
  map_smul' c f := by refine ext ?_; simp [map_smul]

end SobolevSpace.Fractional
