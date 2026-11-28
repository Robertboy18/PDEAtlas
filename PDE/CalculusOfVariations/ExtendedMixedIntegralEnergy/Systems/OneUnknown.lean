/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Functional
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent

/-!
# A scalar variational problem as a system with one unknown

## Motivation

The theorems for coupled systems take a system `Fin m → W^{1,p}(Ω)`, with its value in `ℝᵐ` and
its matrix of weak derivatives in `ℝ^(m * n)`. The scalar theorems take one function, with
its value in `ℝ` and its gradient in `ℝⁿ`. Is a scalar problem the case `m = 1` of the systems,
so that a theorem of either kind applies to the other?

## The idea

Yes. The matrix of derivatives of one unknown has one row, and `rowEquiv` reads this row as a
vector of `ℝⁿ`; it is a linear isometry. A scalar density `f(x, s, ξ)` becomes the density
`oneUnknownDensity f` of a system with one unknown. On a system `U` with one component, the
value and the row of the gradient are the value and the gradient of `U 0` almost everywhere,
so the two integrals are equal, and every system with one component is determined by `U 0`.
So `U` minimizes the integral of the system in the class of a datum `G` exactly when `U 0`
minimizes the scalar integral in the class of `G 0`.

## Main results

All are for all dimensions, all sets, all exponents `p ≥ 1` and all scalar densities.

* `oneUnknown_jet_ae`: the value and the row of the gradient of a system with one unknown are
  the value and the gradient of its component.
* `integral_oneUnknownDensity`: the integral of the system is the scalar integral.
* `forall_integral_oneUnknownDensity_le_iff`: minimality in a boundary class for the system
  with one unknown is minimality of the component in the scalar boundary class.
* `measurable_oneUnknownDensity`: measurability passes to the density of the system.

## Relations

* The identities come from `vectorWkpValueCLM_apply_ae` and `vectorWkpGradientCLM_apply_ae`.
* `PDE.CalculusOfVariations.exists_minimizer_integral_vectorWkp_prescribed_boundary` for the
  density `oneUnknownDensity f` is, through these results, an existence theorem for the scalar
  integral of `f`.

## What stays open

The same passage for the first variation and for the bilinear forms of linear equations.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The matrix of derivatives of one unknown, read as a vector: the linear isometry
`ℝ^(1 * n) ≃ ℝⁿ` that sends the entry `(0, j)` to the coordinate `j`. -/
def rowEquiv (n : ℕ) : ℝ^(1 * n) ≃ₗᵢ[ℝ] ℝ^n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finProdFinEquiv.symm.trans (Equiv.uniqueProd (Fin n) (Fin 1)))

/-- The coordinate `j` of the row is the entry `(0, j)` of the matrix. -/
theorem rowEquiv_apply (ξ : ℝ^(1 * n)) (j : Fin n) :
    rowEquiv n ξ j = ξ (finProdFinEquiv (0, j)) :=
  rfl

/-- The density of the system with one unknown that corresponds to the scalar density
`f(x, s, ξ)`: it takes the value in `ℝ¹` and the matrix of derivatives in `ℝ^(1 * n)`. -/
def oneUnknownDensity (f : ℝ^n → ℝ × ℝ^n → ℝ) (x : ℝ^n) (z : ℝ^1 × ℝ^(1 * n)) : ℝ :=
  f x (z.1 0, rowEquiv n z.2)

/-- The density of the system is jointly measurable when the scalar density is. -/
theorem measurable_oneUnknownDensity {f : ℝ^n → ℝ × ℝ^n → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry (oneUnknownDensity f)) := by
  have hc : Continuous fun q : ℝ^n × (ℝ^1 × ℝ^(1 * n)) ↦
      (q.1, ((EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ) q.2.1, rowEquiv n q.2.2)) :=
    continuous_fst.prodMk
      (((EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ).continuous.comp
        continuous_snd.fst).prodMk ((rowEquiv n).continuous.comp continuous_snd.snd))
  exact hf.comp hc.measurable

/-- On a system with one unknown, the value and the row of the matrix of weak derivatives are
the value and the weak gradient of the component, almost everywhere. -/
theorem oneUnknown_jet_ae (U : Fin 1 → W^{1,p}(Ω)) :
    ∀ᵐ x ∂domainMeasure n Ω, (vectorWkpValueCLM U x 0, rowEquiv n (∇ U x)) =
      (wkpBaseCoordinateCLM (U 0) x, ∇ (U 0) x) := by
  filter_upwards [vectorWkpValueCLM_apply_ae U, vectorWkpGradientCLM_apply_ae U] with x hv hg
  refine Prod.ext (hv 0) ?_
  ext j
  exact hg 0 j

/-- The integral of the system with one unknown is the scalar integral of its component. -/
theorem integral_oneUnknownDensity (f : ℝ^n → ℝ × ℝ^n → ℝ) (U : Fin 1 → W^{1,p}(Ω)) :
    (∫ x, oneUnknownDensity f x (vectorWkpValueCLM U x, ∇ U x) ∂domainMeasure n Ω) =
      ∫ x, f x (wkpBaseCoordinateCLM (U 0) x, ∇ (U 0) x) ∂domainMeasure n Ω :=
  integral_congr_ae ((oneUnknown_jet_ae U).mono fun x hx ↦ congrArg (f x) hx)

/-- A system with one unknown minimizes its integral in the boundary class of `G` exactly when
its component minimizes the scalar integral in the boundary class of `G 0`. -/
theorem forall_integral_oneUnknownDensity_le_iff (f : ℝ^n → ℝ × ℝ^n → ℝ)
    (G U : Fin 1 → W^{1,p}(Ω)) :
    (∀ V : Fin 1 → W^{1,p}(Ω),
        (∀ i, V i - G i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)) →
        (∫ x, oneUnknownDensity f x (vectorWkpValueCLM U x, ∇ U x) ∂domainMeasure n Ω) ≤
          ∫ x, oneUnknownDensity f x (vectorWkpValueCLM V x, ∇ V x) ∂domainMeasure n Ω) ↔
      ∀ w : W^{1,p}(Ω), w - G 0 ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω) →
        (∫ x, f x (wkpBaseCoordinateCLM (U 0) x, ∇ (U 0) x) ∂domainMeasure n Ω) ≤
          ∫ x, f x (wkpBaseCoordinateCLM w x, ∇ w x) ∂domainMeasure n Ω := by
  constructor
  · intro h w hw
    have hV := h (fun _ ↦ w) (fun i ↦ by rwa [Subsingleton.elim i 0])
    rwa [integral_oneUnknownDensity, integral_oneUnknownDensity] at hV
  · intro h V hV
    rw [integral_oneUnknownDensity, integral_oneUnknownDensity]
    exact h (V 0) (hV 0)

end PDE.CalculusOfVariations
