/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram.AffineClass
public import PDE.Elliptic.Variational.InteriorLowerOrder
public import PDE.Elliptic.Variational.NonnegativePotential
import PDE.Elliptic.Variational.Comparison.Locality

/-!
# The linear Dirichlet problem with Sobolev boundary data

## Motivation

For `-div(a ∇u) + c u = f` in `Ω` with `u = g` on the boundary: given a datum `g ∈ H¹(Ω)`,
bounded measurable coefficients and a load in the dual of `H¹₀(Ω)`, is there exactly one weak
solution `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)`?

## The idea

Yes, on every bounded set of positive dimension, for a uniformly elliptic matrix `a` and a
potential `c ≥ 0`. The weak form pairs a state in `H¹(Ω)` with a test function in `H¹₀(Ω)`.
On states in `H¹₀(Ω)` it is the coercive form of the problem with zero data, by Poincaré's
inequality, so `PDE.Analysis.Variational.existsUnique_eq_add_and_forall_eq` applies:
the correction `u - g` is the Lax–Milgram solution for the load `ell - B g`. No regularity of
the boundary, no trace operator and no symmetry of the coefficients is used. The condition
`u - g ∈ H¹₀(Ω)` is the weak form of `u = g` on the boundary.

## Main results

All are for every bounded set in positive dimension, every datum `g ∈ H¹(Ω) = W^{1,2}(Ω)` and
every load in the dual of `H¹₀(Ω)`.

* `existsUnique_interiorVariableCoeffForm_prescribed_boundary` (all operator coefficients
  with integrated ellipticity): exactly one `u` with `u - g ∈ H¹₀` solves the principal
  equation.
* `existsUnique_interiorFullDivergenceOperator_prescribed_boundary` (all bounded measurable
  matrices that are uniformly elliptic almost everywhere, all bounded potentials `c ≥ 0`): the
  same with the zero-order term.
* `existsUnique_isInteriorWeakDivergenceSolution_prescribed_boundary`,
  `existsUnique_isInteriorWeakFullDivergenceSolution_prescribed_boundary`: the two statements
  for an `L²` source on an open set, in terms of the weak solution predicates.
* `existsUnique_weak_harmonic_extension` (one operator, all data): the Laplacian.

## Relations

* Each result is `PDE.Analysis.Variational.existsUnique_eq_add_and_forall_eq` for the
  inclusion `h10SubtypeL : H¹₀(Ω) → H¹(Ω)`; coercivity is `variableCoeffForm_isCoercive` or
  `fullDivergenceForm_zero_drift_isCoercive`.
* `exists_weak_harmonic_extension` is the existence half of
  `existsUnique_weak_harmonic_extension`, and is proved from it.
* For `g = 0` the first result is `existsUnique_variableCoeff_weakSolution`; the solution of
  the problem with data is `g` plus the solution with zero data for the load `ell - B g`.

## What stays open

A drift term or a potential without sign, where coercivity can fail and
`fullDivergenceForm.fredholmAlternative_of_bounded` replaces uniqueness. Attainment of the
boundary values in the classical sense needs regularity of the boundary and of `g`.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Variational
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- The class of a datum: `u = g + w` for some `w ∈ H¹₀(Ω)` exactly when `u - g` lies in the
zero-boundary subspace. -/
theorem exists_eq_add_h10SubtypeL_iff (g u : H¹(Ω)) :
    (∃ w : H¹₀(Ω), u = g + h10SubtypeL w) ↔ u - g ∈ h10Submodule (n := n) (Ω := Ω) := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [add_sub_cancel_left]
    exact w.2
  · intro hu
    exact ⟨⟨u - g, hu⟩, (add_sub_cancel g u).symm⟩

/-- The principal Dirichlet problem with data. On a bounded set of positive dimension, for
operator coefficients with integrated ellipticity, every load `ell` on `H¹₀(Ω)` and every
datum `g ∈ H¹(Ω)`, there is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and
`∑ ⟪Aᵢⱼ ∂ⱼu, ∂ᵢv⟫ = ell v` for every `v ∈ H¹₀(Ω)`.

The correction `u - g` is the Lax–Milgram solution for the load `ell - B g`. -/
theorem existsUnique_interiorVariableCoeffForm_prescribed_boundary
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → (L2 →L[ℝ] L2)) {α : ℝ} (hA : IntegratedElliptic A α)
    (ell : StrongDual ℝ H¹₀(Ω)) (g : H¹(Ω)) :
    ∃! u : H¹(Ω), u - g ∈ h10Submodule (n := n) (Ω := Ω) ∧
      ∀ v : H¹₀(Ω), interiorVariableCoeffForm A u v = ell v := by
  have h := existsUnique_eq_add_and_forall_eq (U := H¹(Ω)) (V := H¹₀(Ω))
    (fun w ↦ h10SubtypeL w) (fun u v ↦ interiorVariableCoeffForm A u v)
    (fun u u' v ↦ by rw [map_add]; rfl)
    (variableCoeffForm A) (variableCoeffForm_isCoercive hn hbounded A hA)
    (fun _ _ ↦ rfl) ell (interiorVariableCoeffForm A g) g (fun _ ↦ rfl)
  simpa only [exists_eq_add_h10SubtypeL_iff] using h

/-- The Dirichlet problem with data and a nonnegative potential. On a bounded set of positive
dimension, for a bounded measurable matrix `a` that is uniformly elliptic almost everywhere, a
bounded potential `c ≥ 0`, every load `ell` on `H¹₀(Ω)` and every datum `g ∈ H¹(Ω)`, there is
exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` that solves `-div(a ∇u) + c u = ell` weakly. -/
theorem existsUnique_interiorFullDivergenceOperator_prescribed_boundary
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (c : DerivLp n ∞ Ω) (hc : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ c x)
    (ell : StrongDual ℝ H¹₀(Ω)) (g : H¹(Ω)) :
    ∃! u : H¹(Ω), u - g ∈ h10Submodule (n := n) (Ω := Ω) ∧
      ∀ v : H¹₀(Ω), interiorFullDivergenceOperator a 0 c u v = ell v := by
  let B₀ : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    fullDivergenceForm (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator 0) (multiplicationZeroOrderOperator c)
  have hB₀ : IsCoercive B₀ := fullDivergenceForm_zero_drift_isCoercive hn hbounded
    (multiplicationCoefficientOperator a) (integratedElliptic_multiplication_of_ae a ha) c hc
  -- on zero-boundary states the operator is the coercive form
  have hι : ∀ w v : H¹₀(Ω),
      interiorFullDivergenceOperator a 0 c (h10SubtypeL w) v = B₀ w v :=
    fun w v ↦ interiorFullDivergenceOperator_coe_H10 a 0 c w v
  have h := existsUnique_eq_add_and_forall_eq (U := H¹(Ω)) (V := H¹₀(Ω))
    (fun w ↦ h10SubtypeL w) (fun u v ↦ interiorFullDivergenceOperator a 0 c u v)
    (fun u u' v ↦ by rw [map_add]; rfl) B₀ hB₀ hι ell
    (interiorFullDivergenceOperator a 0 c g) g (fun _ ↦ rfl)
  simpa only [exists_eq_add_h10SubtypeL_iff] using h

/-- On a bounded open set of positive dimension, for a bounded measurable matrix that is
uniformly elliptic almost everywhere, a source `f ∈ L²` and a datum `g ∈ H¹(Ω)`, the problem
`-div(a ∇u) = f` in `Ω`, `u = g` on the boundary has exactly one weak solution: one
`u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` that is an interior weak solution. -/
theorem existsUnique_isInteriorWeakDivergenceSolution_prescribed_boundary
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (f : L2) (g : H¹(Ω)) :
    ∃! u : H¹(Ω), u - g ∈ h10Submodule (n := n) (Ω := Ω) ∧
      IsInteriorWeakDivergenceSolution a f u := by
  simpa only [IsInteriorWeakDivergenceSolution, hopen, true_and] using
    existsUnique_interiorVariableCoeffForm_prescribed_boundary hn hbounded
      (multiplicationCoefficientOperator a) (integratedElliptic_multiplication_of_ae a ha)
      (loadFunctional f) g

/-- The same with a bounded potential `c ≥ 0`: the problem `-div(a ∇u) + c u = f` in `Ω`,
`u = g` on the boundary has exactly one weak solution in `H¹(Ω)`. -/
theorem existsUnique_isInteriorWeakFullDivergenceSolution_prescribed_boundary
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ} (ha : AEUniformlyElliptic a α)
    (c : DerivLp n ∞ Ω) (hc : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ c x)
    (f : L2) (g : H¹(Ω)) :
    ∃! u : H¹(Ω), u - g ∈ h10Submodule (n := n) (Ω := Ω) ∧
      IsInteriorWeakFullDivergenceSolution a 0 c f u := by
  simpa only [IsInteriorWeakFullDivergenceSolution, hopen, true_and,
    ContinuousLinearMap.ext_iff] using
    existsUnique_interiorFullDivergenceOperator_prescribed_boundary hn hbounded a ha c hc
      (loadFunctional f) g

/-- The Laplacian: every datum `G ∈ H¹(Ω)` on a bounded set of positive dimension has exactly
one weakly harmonic field in its class `G + H¹₀(Ω)`. This is the case of identity
coefficients and zero load. -/
theorem existsUnique_weak_harmonic_extension
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω) (G : H¹(Ω)) :
    ∃! u : H¹(Ω), u - G ∈ h10Submodule (n := n) (Ω := Ω) ∧
      ∀ t : H¹₀(Ω),
        (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i) u, derivCoordCLM i t⟫_ℝ) = 0 := by
  classical
  have h := existsUnique_interiorVariableCoeffForm_prescribed_boundary hn hbounded
    identityCoefficientOperator integratedElliptic_identity 0 G
  have hform (u : H¹(Ω)) (t : H¹₀(Ω)) :
      interiorVariableCoeffForm identityCoefficientOperator u t =
        ∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n i) u, derivCoordCLM i t⟫_ℝ := by
    simp only [interiorVariableCoeffForm_apply, identityCoefficientOperator]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  simpa only [hform, zero_apply] using h

end SobolevSpace.GraphSpace
