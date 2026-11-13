/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator

/-!
# Smooth nondivergence coefficients in the weak form

The operator `-aᵢⱼ ∂ᵢ∂ⱼ + bⱼ ∂ⱼ + c` has divergence-form drift
`bⱼ + ∑ᵢ ∂ᵢaᵢⱼ`. Derivatives of the coefficients are taken in the open
domain; their closure regularity follows from the derivative-word
criterion. No ambient smooth extension or boundary derivative identification
is assumed.

The resulting data use the full variational form and higher load maps.
The classical identification is local and does not require ellipticity or symmetry.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open Set

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The drift left after expanding the divergence of the principal flux. -/
def nondivergenceDrift (P : SmoothFullCoefficients n Ω) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 (fun j ↦ P.drift j x -
    ∑ i, (∂[i] (fun y ↦ P.principal y i j)) x)

/-- The effective nondivergence drift inherits smooth closure regularity
from the coefficients, using only their interior derivatives. -/
theorem nondivergenceDrift_regular (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (r : ℕ) (j : Fin n) :
    ContDiffUpToBoundary r (fun x ↦ P.nondivergenceDrift x j) Ω :=
  (P.drift_smooth r j).sub
    (ContDiffUpToBoundary.sum Finset.univ
      (fun i _ ↦ (P.principal_smooth (r + 1) i j).partialDeriv_of_succ hopen i)
      hopen) hopen

/-- Expanding a smooth divergence-form load gives the matrix operator
with the derivative-corrected drift. This equality is entirely local. -/
theorem classicalLoad_eq_matrixOperator (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) {u : ℝ^n → ℝ} {x : ℝ^n}
    (hx : x ∈ Ω) (hu : ContDiffAt ℝ 2 u x) :
    P.classicalLoad u x =
      EllipticMaximum.matrixOperator P.principal P.nondivergenceDrift P.potential u x := by
  have hflux := EllipticMaximum.matrixOperator_eq_neg_sum_partialDeriv_flux
    (fun i j y ↦ P.principal y i j)
    (fun i j ↦ (P.principal_smooth 1 i j).contDiffOn.contDiffAt (hopen.mem_nhds hx)) hu
  change -(∑ i, ∑ j, P.principal x i j * (∂[i] (∂[j] u)) x) +
      fderiv ℝ u x (WithLp.toLp 2
        (fun j ↦ -(∑ i, (∂[i] (fun y ↦ P.principal y i j)) x))) +
      0 * u x = _ at hflux
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul] at hflux
  change -(∑ i, ∑ j, P.principal x i j * (∂[i] (∂[j] u)) x) +
      (∑ j, (∂[j] u) x * -(∑ i, (∂[i] (fun y ↦ P.principal y i j)) x)) +
      0 * u x =
    -(∑ i, ∑ j, (∂[i] (fun y ↦ P.principal y i j * (∂[j] u) y)) x)
      at hflux
  change -(∑ i, ∑ j, (∂[i] (fun y ↦ P.principal y i j * (∂[j] u) y)) x) +
      (∑ j, P.drift j x * (∂[j] u) x) + P.potential x * u x = _
  rw [← hflux]
  change _ = -(∑ i, ∑ j, P.principal x i j * (∂[i] (∂[j] u)) x) +
    fderiv ℝ u x (P.nondivergenceDrift x) + P.potential x * u x
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul]
  change _ = -(∑ i, ∑ j, P.principal x i j * (∂[i] (∂[j] u)) x) +
    (∑ j, (∂[j] u) x * (P.drift j x -
      ∑ i, (∂[i] (fun y ↦ P.principal y i j)) x)) + P.potential x * u x
  simp only [zero_mul, add_zero, mul_sub, Finset.sum_sub_distrib, mul_neg,
    Finset.sum_neg_distrib, mul_comm (P.drift _ x) ((∂[_] u) x)]
  ring

/-- Convert smooth nondivergence coefficients to the divergence-form data.
The first principal index is differentiated in the correction to the drift. -/
def ofNondivergence (hopen : IsOpen Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (ha : ∀ r i j, ContDiffUpToBoundary r (fun x ↦ a x i j) Ω)
    (hb : ∀ r i, ContDiffUpToBoundary r (fun x ↦ b x i) Ω)
    (hc : ∀ r, ContDiffUpToBoundary r c Ω) :
    SmoothFullCoefficients n Ω where
  principal := a
  drift j x := b x j + ∑ i, (∂[i] (fun y ↦ a y i j)) x
  potential := c
  principal_smooth := ha
  drift_smooth r j := (hb r j).add
    (ContDiffUpToBoundary.sum Finset.univ
      (fun i _ ↦ (ha (r + 1) i j).partialDeriv_of_succ hopen i) hopen) hopen
  potential_smooth := hc

/-- The converted full classical load is exactly the original nondivergence
operator at every interior point of classical input. -/
theorem classicalLoad_ofNondivergence_eq_matrixOperator
    (hopen : IsOpen Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    (ha : ∀ r i j, ContDiffUpToBoundary r (fun x ↦ a x i j) Ω)
    (hb : ∀ r i, ContDiffUpToBoundary r (fun x ↦ b x i) Ω)
    (hc : ∀ r, ContDiffUpToBoundary r c Ω)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hx : x ∈ Ω) (hu : ContDiffAt ℝ 2 u x) :
    (ofNondivergence hopen a b c ha hb hc).classicalLoad u x =
      EllipticMaximum.matrixOperator a b c u x := by
  rw [classicalLoad_eq_matrixOperator _ hopen hx hu]
  have hdrift : (ofNondivergence hopen a b c ha hb hc).nondivergenceDrift = b := by
    funext y
    ext j
    simp [nondivergenceDrift, ofNondivergence]
  rw [hdrift]
  rfl

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
