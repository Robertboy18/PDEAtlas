/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fredholm.WeakForm.Reduction
import Mathlib.Analysis.InnerProductSpace.Spectrum
import PDE.Analysis.Fredholm.CompactAdjoint
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Nullspaces in the compact Fredholm reduction

The nullspaces of a compact perturbation of the identity and of its adjoint are
finite-dimensional and have equal dimension. The shifted-coercive reduction
transports both facts to the primal and adjoint nullspaces of a variational weak
operator.

## Main results

* `finrank_ker_eq_adjoint_ker_compact`: for compact `K`, the kernels of `K - 1` and of its
  adjoint have the same `finrank`.
* `finiteDimensional_ker_form`, `finiteDimensional_ker_adjointForm_of_compact_mass`: the primal
  and adjoint homogeneous weak-solution spaces are finite-dimensional.
* `finrank_ker_form_eq_ker_adjointForm_of_compact_mass`: the two spaces have the same `finrank`.

## How it works

Both facts are classical: they are parts (i) and (v) of the Fredholm alternative, Evans,
Appendix D.5, Theorem 5, and in Evans's setting they give §6.2.3, Theorem 4(ii). Finite
dimension is Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace`. For the inequality
`finrank_adjoint_ker_le_ker_compact` we follow step 7 of Evans's proof: if the adjoint kernel
were larger, an injective map from the kernel into it that is not onto, composed with the
orthogonal projection onto the kernel, is a finite-rank operator `A` with `1 - (K + A)`
injective; Mathlib's `IsCompactOperator.hasEigenvalue_or_mem_resolventSet` makes it surjective,
which is impossible. Applied to `K.adjoint` the inequality gives equality, as in step 8. The
factorization `hilbertOperator_eq_fredholmHilbertEquiv_comp_one_sub` carries both kernels to
the weak operator.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, Theorem 4(ii), p. 321, with step 4 of its proof,
  pp. 322-323, and Appendix D.5, Theorem 5(i) and (v), p. 725, with steps 1, 7 and 8 of its
  proof, pp. 725-726. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Function Filter
open scoped Topology InnerProductSpace
open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- For compact `K` the kernel of `K - 1` is finite-dimensional: Mathlib's
`ContinuousLinearMap.finite_dimensional_eigenspace` in the kernel form used here. -/
private theorem finiteDimensional_ker_compact_sub_one
    (K : V →L[ℝ] V) (hK : IsCompactOperator K) :
    FiniteDimensional ℝ ↥((K - (1 : V →L[ℝ] V)).ker) := by
  have hker : (K - (1 : V →L[ℝ] V)).ker =
      Module.End.eigenspace (K : Module.End ℝ V) 1 := by
    ext x
    simp [sub_eq_zero]
  rw [hker]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK (1 : ℝ) one_ne_zero

/-- For a compact operator, the adjoint nullity of `K-I` is at most its
primal nullity.  This is Evans, Appendix D.5, Theorem 5(v), step 7.

The proof is the finite-rank-correction argument from Evans: if the adjoint
nullspace were larger, inject the primal kernel into it, extend this map by
orthogonal projection, and add the resulting finite-rank operator to `K`.
The corrected `I-(K+A)` is injective, hence surjective by the compact
Fredholm alternative, contradicting the choice of a vector outside the
finite-rank correction's range. -/
theorem finrank_adjoint_ker_le_ker_compact
    (K : V →L[ℝ] V) (hK : IsCompactOperator K) :
    Module.finrank ℝ ↥((K - (1 : V →L[ℝ] V)).adjoint.ker) ≤
      Module.finrank ℝ ↥((K - (1 : V →L[ℝ] V)).ker) := by
  let S : V →L[ℝ] V := (1 : V →L[ℝ] V) - K
  let N : Submodule ℝ V := S.ker
  let M : Submodule ℝ V := S.adjoint.ker
  have hSneg : S = -(K - (1 : V →L[ℝ] V)) := by ext x; simp [S]
  have hN : N = (K - (1 : V →L[ℝ] V)).ker := by
    rw [show N = S.ker from rfl, hSneg]
    exact LinearMap.ker_neg _
  have hM : M = (K - (1 : V →L[ℝ] V)).adjoint.ker := by
    rw [show M = S.adjoint.ker from rfl, hSneg, map_neg]
    exact LinearMap.ker_neg _
  let : FiniteDimensional ℝ N := hN ▸ finiteDimensional_ker_compact_sub_one K hK
  let : FiniteDimensional ℝ M := by
    rw [hM, map_sub, ContinuousLinearMap.adjoint_one]
    exact finiteDimensional_ker_compact_sub_one K.adjoint
      (PDE.Analysis.isCompactOperator_adjoint hK)
  rw [← hM, ← hN]
  by_contra hle
  have hlt : Module.finrank ℝ N < Module.finrank ℝ M := Nat.lt_of_not_ge hle
  obtain ⟨A0, hA0inj⟩ := finrank_le_iff_exists_linearMap.mp hlt.le
  let A0c : N →L[ℝ] M := A0.toContinuousLinearMap
  let A : V →L[ℝ] V := M.subtypeL.comp (A0c.comp N.orthogonalProjectionOnto)
  have hAcompact : IsCompactOperator A :=
    ((isCompactOperator_of_locallyCompactSpace_dom A0c).comp_clm
      N.orthogonalProjectionOnto).clm_comp M.subtypeL
  -- `S u ∈ range S` and `A u + w ∈ M = (range S)ᗮ` can only agree when `S u = 0`
  have horth {u w : V} (hw : w ∈ M) (h : S u = A u + w) :
      ∃ huN : u ∈ N, (A0 ⟨u, huN⟩ : V) = -w := by
    have hSu : S u = 0 := by
      refine (Submodule.mem_bot ℝ).mp ((Submodule.inf_orthogonal_eq_bot S.range).le
        ⟨LinearMap.mem_range_self S.toLinearMap u, ?_⟩)
      rw [h, S.orthogonal_range]
      exact M.add_mem (A0c (N.orthogonalProjectionOnto u)).property hw
    have hproj : N.orthogonalProjectionOnto u = ⟨u, hSu⟩ :=
      Subtype.ext (N.starProjection_eq_self_iff.mpr hSu)
    have hAu : A u = -w := eq_neg_of_add_eq_zero_left (hSu ▸ h).symm
    exact ⟨hSu, by simpa [A, A0c, hproj] using hAu⟩
  -- `I - (K + A)` is injective, hence surjective by the Fredholm alternative
  have hker : (K + A - (1 : V →L[ℝ] V)).ker = ⊥ := by
    refine eq_bot_iff.2 fun u hu ↦ ?_
    have hraw : K u + A u - u = 0 := LinearMap.mem_ker.mp hu
    obtain ⟨huN, hA⟩ := horth M.zero_mem (u := u) (by
      change u - K u = A u + 0
      linear_combination (norm := module) -hraw)
    exact congrArg Subtype.val (hA0inj (Subtype.ext (by simpa using hA)) : (⟨u, huN⟩ : N) = 0)
  have hsurj : Function.Surjective ((1 : V →L[ℝ] V) - (K + A)) := by
    have hKA : IsCompactOperator (K + A) := hK.add hAcompact
    rcases hKA.hasEigenvalue_or_mem_resolventSet
      (by norm_num : (1 : ℝ) ≠ 0) with heigen | hres
    · obtain ⟨u, hu⟩ := heigen.exists_hasEigenvector
      have huker : u ∈ (K + A - (1 : V →L[ℝ] V)).ker :=
        LinearMap.mem_ker.mpr (sub_eq_zero.mpr (by simpa using hu.apply_eq_smul))
      rw [hker] at huker
      exact (hu.2 (by simpa using huker)).elim
    · rw [spectrum.mem_resolventSet_iff, ContinuousLinearMap.isUnit_iff_bijective] at hres
      simpa using hres.2
  obtain ⟨v, hv⟩ : ∃ v : M, v ∉ LinearMap.range A0 := by
    by_contra! h
    exact hlt.not_ge (A0.finrank_le_finrank_of_surjective fun v ↦ LinearMap.mem_range.mp (h v))
  obtain ⟨u, hu⟩ := hsurj (v : V)
  obtain ⟨huN, hA⟩ := horth v.property (u := u) (by
    change u - (K u + A u) = (v : V) at hu
    change u - K u = A u + (v : V)
    linear_combination (norm := module) hu)
  exact hv ⟨-⟨u, huN⟩, Subtype.ext (by simpa using congrArg Neg.neg hA)⟩

/-- **Fredholm index zero for compact perturbations of the identity.**
The kernels of `K - 1` and of its adjoint have the same `finrank`. This is
Evans, Appendix D.5, Theorem 5(v), and is the equality used in
§6.2.3, Theorem 4(ii). -/
theorem finrank_ker_eq_adjoint_ker_compact
    (K : V →L[ℝ] V) (hK : IsCompactOperator K) :
    Module.finrank ℝ ↥((K - (1 : V →L[ℝ] V)).ker) =
      Module.finrank ℝ ↥((K - (1 : V →L[ℝ] V)).adjoint.ker) := by
  have hsubAdj : (K - (1 : V →L[ℝ] V)).adjoint = K.adjoint - (1 : V →L[ℝ] V) := by
    rw [map_sub, ContinuousLinearMap.adjoint_one]
  have hdouble : (K.adjoint - (1 : V →L[ℝ] V)).adjoint = K - (1 : V →L[ℝ] V) := by
    rw [map_sub, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_one]
  refine le_antisymm ?_ (finrank_adjoint_ker_le_ker_compact K hK)
  have := finrank_adjoint_ker_le_ker_compact K.adjoint (PDE.Analysis.isCompactOperator_adjoint hK)
  rwa [hdouble, ← hsubAdj] at this

/-- The kernel of the original weak operator is the kernel of
`fredholmOperator - 1`. -/
theorem ker_form_eq_ker_fredholmOperator_sub_one
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v) :
    form.ker =
      (fredholmOperator shiftedForm massForm coercive lambda -
        (1 : V →L[ℝ] V)).ker := by
  ext u
  have h := isWeakSolution_iff_sub_fredholmOperator_eq
    form shiftedForm massForm coercive lambda hshift 0 u
  rw [map_zero, sub_eq_zero, eq_comm, ← sub_eq_zero] at h
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ContinuousLinearMap.ext_iff]
  exact h

/-- The adjoint nullspace of the weak operator is the preimage of the adjoint nullspace of
`K - I` under the adjoint of the coercive Riesz equivalence. -/
private theorem ker_adjoint_hilbertOperator_eq_comap
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v) :
    (hilbertOperator form).adjoint.ker =
      ((fredholmOperator shiftedForm massForm coercive lambda - 1).adjoint.ker).comap
        (fredholmHilbertEquiv shiftedForm coercive).toContinuousLinearMap.adjoint.toLinearMap := by
  rw [hilbertOperator_eq_fredholmHilbertEquiv_comp_one_sub
    form shiftedForm massForm coercive lambda hshift, ContinuousLinearMap.adjoint_comp, ← neg_sub,
    map_neg]
  ext v
  simp only [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, neg_apply, neg_eq_zero]

/-- The adjoint of the coercive Riesz equivalence is bijective. -/
private theorem bijective_adjoint_fredholmHilbertEquiv
    (shiftedForm : V →L[ℝ] StrongDual ℝ V) (coercive : IsCoercive shiftedForm) :
    Function.Bijective
      (fredholmHilbertEquiv shiftedForm coercive).toContinuousLinearMap.adjoint := by
  rw [← ContinuousLinearMap.isUnit_iff_bijective, ← ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.isUnit_iff_bijective.2
    (fredholmHilbertEquiv shiftedForm coercive).bijective).star

/-- The homogeneous adjoint weak-solution space is finite-dimensional under
the shifted-coercive, compact-mass hypotheses. Together with
`finiteDimensional_ker_form`, this is the finiteness of both nullspaces in
Evans, §6.2.3, Theorem 4(ii). -/
theorem finiteDimensional_ker_adjoint_hilbertOperator_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    FiniteDimensional ℝ ↥((hilbertOperator form).adjoint.ker) := by
  have : FiniteDimensional ℝ
      ↥(fredholmHilbertEquiv shiftedForm coercive).toContinuousLinearMap.adjoint.ker := by
    rw [LinearMap.ker_eq_bot.mpr (bijective_adjoint_fredholmHilbertEquiv shiftedForm coercive).1]
    infer_instance
  have := finiteDimensional_ker_compact_sub_one _ (PDE.Analysis.isCompactOperator_adjoint
    (isCompactOperator_fredholmOperator shiftedForm massForm coercive lambda hcompactMass))
  rw [ker_adjoint_hilbertOperator_eq_comap form shiftedForm massForm coercive lambda hshift,
    map_sub, ContinuousLinearMap.adjoint_one]
  infer_instance

/-- Evans §6.2.3, Theorem 4(ii), nullity equality. Under the
shifted-coercive and compact-mass hypotheses, the primal weak operator and
the Hilbert adjoint of its Riesz representative have equal `finrank`.
Finiteness is supplied separately by `finiteDimensional_ker_form` and
`finiteDimensional_ker_adjoint_hilbertOperator_of_compact_mass`.

The equality is transported from `I-K` through the invertible coercive/Riesz
change of coordinates; it ultimately rests on the Fredholm index-zero theorem
`finrank_ker_eq_adjoint_ker_compact`. -/
theorem finrank_ker_form_eq_ker_adjoint_hilbertOperator_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    Module.finrank ℝ ↥form.ker =
      Module.finrank ℝ ↥((hilbertOperator form).adjoint.ker) := by
  have hQ := bijective_adjoint_fredholmHilbertEquiv shiftedForm coercive
  rw [ker_adjoint_hilbertOperator_eq_comap form shiftedForm massForm coercive lambda hshift,
    ker_form_eq_ker_fredholmOperator_sub_one form shiftedForm massForm coercive lambda hshift,
    finrank_ker_eq_adjoint_ker_compact _
      (isCompactOperator_fredholmOperator shiftedForm massForm coercive lambda hcompactMass)]
  exact (LinearEquiv.finrank_eq ((LinearEquiv.ofBijective _ hQ).ofSubmodule' _)).symm

/-- The adjoint-form homogeneous solution space is finite-dimensional under
the shifted-coercive, compact-mass hypotheses. -/
theorem finiteDimensional_ker_adjointForm_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    FiniteDimensional ℝ ↥((adjointForm form).ker) := by
  rw [ker_adjointForm_eq_ker_adjoint_hilbertOperator]
  exact finiteDimensional_ker_adjoint_hilbertOperator_of_compact_mass
    form shiftedForm massForm coercive lambda hshift hcompactMass

/-- Evans §6.2.3, Theorem 4(ii), weak-form statement. The primal
and adjoint homogeneous weak-solution spaces have equal `finrank`.
Use `finiteDimensional_ker_form` and
`finiteDimensional_ker_adjointForm_of_compact_mass` for their finiteness. -/
theorem finrank_ker_form_eq_ker_adjointForm_of_compact_mass
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    Module.finrank ℝ ↥form.ker =
      Module.finrank ℝ ↥((adjointForm form).ker) := by
  rw [ker_adjointForm_eq_ker_adjoint_hilbertOperator]
  exact finrank_ker_form_eq_ker_adjoint_hilbertOperator_of_compact_mass
    form shiftedForm massForm coercive lambda hshift hcompactMass

/-- The homogeneous weak-solution space in Evans's shifted compact
reduction is finite-dimensional.  This proves the finiteness assertion for
the primal nullspace in §6.2.3, Theorem 4(ii). -/
theorem finiteDimensional_ker_form
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + lambda * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    FiniteDimensional ℝ ↥form.ker := by
  rw [ker_form_eq_ker_fredholmOperator_sub_one
    form shiftedForm massForm coercive lambda hshift]
  exact finiteDimensional_ker_compact_sub_one
    (fredholmOperator shiftedForm massForm coercive lambda)
    (isCompactOperator_fredholmOperator
      shiftedForm massForm coercive lambda hcompactMass)

end PDE.Analysis
