/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fredholm.WeakForm.Adjoint
public import PDE.Analysis.Variational.LaxMilgram

/-!
# Shifted-coercive reduction to a compact perturbation

A weak equation whose form becomes coercive after adding `λ` times a mass form `M` is
equivalent to an equation `u - K u = h` with `K = λ (B + λM)⁻¹ M`. We prove both the
equivalence of solutions and the factorization of the operator through the Lax–Milgram
solution equivalence and the Riesz map.

## Main definitions

* `fredholmOperator`: the operator `K = λ (B + λM)⁻¹ M`.
* `coerciveSolveEquiv`: the Lax–Milgram solution map of a coercive form.
* `fredholmHilbertEquiv`: the change of coordinates from the reduced equation to the Riesz
  representative of the form.

## Main results

* `isCompactOperator_fredholmOperator`: `K` is compact when the mass form is.
* `isWeakSolution_iff_sub_fredholmOperator_eq`: the weak equation is equivalent to `u - K u = h`.
* `hilbertOperator_eq_fredholmHilbertEquiv_comp_one_sub`: the Riesz representative of the form
  is an isomorphism composed with `1 - K`.

## How it works

The reduction is Evans's, steps 1-3 of the proof of §6.2.3, Theorem 4: with
`B_γ[u, v] = B[u, v] + γ (u, v)` coercive, `u` is a weak solution of `Lu = f` exactly when
`u = L_γ⁻¹ (γ u + f)`, that is `u - K u = h` with `K = γ L_γ⁻¹` and `h = L_γ⁻¹ f`. Evans takes
`K` on `L²(U)` and gets its compactness from the Rellich–Kondrachov theorem. We stay in one
Hilbert space `V`, replace `(u, v)` by an abstract mass form `massForm` assumed compact, and
invert the shifted form with the Lax–Milgram solution operator `solveCLM`. The factorization
`coerciveSolveEquiv_comp_form_eq_one_sub_fredholmOperator` then carries kernels, ranges and
adjoints between the weak operator and `1 - K`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, steps 1-3 of the proof of Theorem 4, (13)-(19),
  pp. 321-322. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Function Filter
open scoped Topology InnerProductSpace
open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The operator `K = λ (B + λM)⁻¹ M` of the shifted-form reduction, Evans's
`K = γ L_γ⁻¹`. -/
def fredholmOperator
    (shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ) :
    V →L[ℝ] V :=
  lambda • ((solveCLM shiftedForm coercive).comp massForm)

/-- The Lax–Milgram solution map for a coercive form, as a continuous
linear equivalence. It is the change of coordinates that turns
the original weak operator into `I-K`. -/
def coerciveSolveEquiv
    (form : V →L[ℝ] StrongDual ℝ V) (coercive : IsCoercive form) :
    StrongDual ℝ V ≃L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.trans
    coercive.continuousLinearEquivOfBilin.symm

/-- The underlying continuous linear map of the coercive solution equivalence
is the Lax–Milgram solution operator. -/
@[simp]
theorem coerciveSolveEquiv_toContinuousLinearMap
    (form : V →L[ℝ] StrongDual ℝ V) (coercive : IsCoercive form) :
    (coerciveSolveEquiv form coercive).toContinuousLinearMap = solveCLM form coercive := by
  rfl

/-- The Hilbert-space change of coordinates from the normalized Fredholm
equation back to the Riesz representative of the original weak operator. -/
def fredholmHilbertEquiv
    (shiftedForm : V →L[ℝ] StrongDual ℝ V) (coercive : IsCoercive shiftedForm) :
    V ≃L[ℝ] V :=
  (coerciveSolveEquiv shiftedForm coercive).symm.trans
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv

/-- `fredholmOperator` is compact when the mass operator is; Evans obtains this compactness,
step 3 of his proof, from the Rellich–Kondrachov theorem. -/
theorem isCompactOperator_fredholmOperator
    (shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hcompactMass : IsCompactOperator massForm) :
    IsCompactOperator (fredholmOperator shiftedForm massForm coercive lambda) := by
  exact (hcompactMass.clm_comp (solveCLM shiftedForm coercive)).smul lambda

/-- If the shifted form differs from the original form by `λM`, `u` solves the
weak equation with right side `ell` exactly when `u - K u` is the shifted solution of `ell`,
Evans's (15)-(19). -/
theorem isWeakSolution_iff_sub_fredholmOperator_eq
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (ell : StrongDual ℝ V) (u : V) :
    IsWeakSolution form ell u ↔
      u - fredholmOperator shiftedForm massForm coercive lambda u =
        solveCLM shiftedForm coercive ell := by
  constructor
  · intro hu
    have huShifted : IsWeakSolution shiftedForm (ell + lambda • massForm u) u := by
      intro v
      rw [hshift u v, hu v]
      simp
    have hsolved : u = solveCLM shiftedForm coercive (ell + lambda • massForm u) :=
      IsWeakSolution.unique shiftedForm coercive (ell + lambda • massForm u)
        huShifted (solveCLM.isWeakSolution shiftedForm coercive _)
    apply sub_eq_iff_eq_add.mpr
    calc
      u = solveCLM shiftedForm coercive (ell + lambda • massForm u) := hsolved
      _ = solveCLM shiftedForm coercive ell +
          solveCLM shiftedForm coercive (lambda • massForm u) := by rw [map_add]
      _ = solveCLM shiftedForm coercive ell +
          lambda • solveCLM shiftedForm coercive (massForm u) := by rw [map_smul]
      _ = solveCLM shiftedForm coercive ell +
          fredholmOperator shiftedForm massForm coercive lambda u := rfl
  · intro hu
    have hsolved :
        u = solveCLM shiftedForm coercive (ell + lambda • massForm u) := by
      calc
        u = solveCLM shiftedForm coercive ell +
            fredholmOperator shiftedForm massForm coercive lambda u :=
          sub_eq_iff_eq_add.mp hu
        _ = solveCLM shiftedForm coercive ell +
            lambda • solveCLM shiftedForm coercive (massForm u) := rfl
        _ = solveCLM shiftedForm coercive ell +
            solveCLM shiftedForm coercive (lambda • massForm u) := by rw [map_smul]
        _ = solveCLM shiftedForm coercive (ell + lambda • massForm u) := by
          rw [map_add]
    have huShifted : IsWeakSolution shiftedForm (ell + lambda • massForm u) u := by
      intro v
      calc
        shiftedForm u v = shiftedForm
            (solveCLM shiftedForm coercive (ell + lambda • massForm u)) v := by
          exact congrArg (fun w ↦ shiftedForm w v) hsolved
        _ = (ell + lambda • massForm u) v :=
          solveCLM.isWeakSolution shiftedForm coercive _ v
    intro v
    have hv := huShifted v
    rw [hshift u v] at hv
    simpa using hv

/-- Composed with the shifted solution map, the original weak operator is
`I-K`, the reduction in step 2 of Evans's proof of §6.2.3, Theorem 4. -/
theorem coerciveSolveEquiv_comp_form_eq_one_sub_fredholmOperator
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v) :
    (coerciveSolveEquiv shiftedForm coercive).toContinuousLinearMap.comp form =
      (1 : V →L[ℝ] V) -
        fredholmOperator shiftedForm massForm coercive lambda := by
  ext u
  have hu : IsWeakSolution form (form u) u := fun v ↦ rfl
  have heq := (isWeakSolution_iff_sub_fredholmOperator_eq
    form shiftedForm massForm coercive lambda hshift (form u) u).1 hu
  simpa [coerciveSolveEquiv_toContinuousLinearMap, solveCLM_apply] using heq.symm

/-- The Riesz representative of the original operator is an isomorphism
composed with `I-K`. -/
theorem hilbertOperator_eq_fredholmHilbertEquiv_comp_one_sub
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v) :
    hilbertOperator form =
      (fredholmHilbertEquiv shiftedForm coercive).toContinuousLinearMap.comp
        ((1 : V →L[ℝ] V) -
          fredholmOperator shiftedForm massForm coercive lambda) := by
  rw [← coerciveSolveEquiv_comp_form_eq_one_sub_fredholmOperator
    form shiftedForm massForm coercive lambda hshift]
  ext u
  apply (InnerProductSpace.toDual ℝ V).injective
  simp [hilbertOperator, fredholmHilbertEquiv, coerciveSolveEquiv]

end PDE.Analysis
