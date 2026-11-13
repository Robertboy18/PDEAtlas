/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
import PDE.LinearAlgebra.Eigenbasis

/-!
# Normalized eigenpairs near a simple real eigenvalue

An eigenvector can be rescaled without changing its eigenvalue. Fixing one coordinate removes
that freedom: in a chosen eigenbasis, require the coordinate along the selected eigenvector
to equal one. The derivative of the eigenvalue equation together with this normalization
then has an explicit inverse. Transverse coordinates are divided by eigenvalue gaps; the
selected coordinate determines the change in eigenvalue.

The construction starts with a finite real eigenbasis of the operator. Only separation of the
selected eigenvalue from the other basis eigenvalues is needed. Mathlib's implicit function
theorem produces a locally analytic normalized eigenpair as the operator varies, with local
uniqueness near the original pair. No inner product or eigenvector field is assumed.

The implicit equation is polynomial in the operator, vector, and scalar. Its analytic
regularity gives a single neighborhood with smooth dependence, rather than only separate
finite-order regularity neighborhoods. The finite basis also supplies completeness.

## Main results

* `bordered`, `borderedInverse`, `isInvertible_bordered`: the partial derivative of the
  normalized equation in the vector and the eigenvalue, and its explicit inverse.
* `exists_normalized_eigenpair`: near an operator with a finite real eigenbasis and a selected
  eigenvalue different from the other basis eigenvalues, there is a locally unique normalized
  eigenpair, analytic in the operator.

## How it works

Evans, §11.1.2, Theorem 2, states that the eigenvalues and eigenvectors of a smooth strictly
hyperbolic matrix function `B(z)` depend smoothly on `z`, and steps 1-3 of his proof are the
local argument. He normalizes `|r| = 1`, applies the implicit function theorem to
`Φ(r, λ, z) = (B(z) r - λ r, |r|²)` and checks the nondegeneracy condition (39) with the
determinant computation based on (40). We use the linear normalization that fixes the `k`-th
basis coordinate of the vector (`normalizedEquation`), so the partial derivative is
`bordered` (`fderiv_normalizedEquation_comp_inr`), and we write down its inverse
`borderedInverse` in place of the determinant computation. Mathlib's
`ContDiffAt.implicitFunction` then gives the eigenpair. Evans's step 4, which extends the
eigenpair from a neighborhood to all of `ℝ^m`, is not part of this statement.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.2, Theorem 2 and steps 1-3 of its proof,
  (37)-(40), pp. 618-619. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter
open scoped ContDiff Topology

namespace PDE.Analysis.Calculus.SimpleEigenpair

variable {ι E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative of the eigenvalue equation and coordinate normalization at `(b k, eig k)`.
It sends `(v, a)` to `(A v - (eig k • v + a • b k), b.repr v k)`. -/
def bordered (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) (eig : ι → ℝ) (k : ι) :
    E × ℝ →L[ℝ] E × ℝ :=
  ((A.comp (ContinuousLinearMap.fst ℝ E ℝ)) -
    (eig k • ContinuousLinearMap.fst ℝ E ℝ +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (b k))).prod
    ((ContinuousLinearMap.proj k).comp
      (b.equivFunL.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E ℝ)))

open Classical in
/-- Inverse candidate for the bordered derivative. For input `(w, c)`, its vector has
coordinate `c` at `k` and coordinate `(b.repr w j) / (eig j - eig k)` elsewhere.
Its scalar is `-b.repr w k`. The inverse identities require the nonzero gaps explicitly. -/
def borderedInverse (b : Module.Basis ι ℝ E) (eig : ι → ℝ) (k : ι) :
    E × ℝ →L[ℝ] E × ℝ :=
  (b.equivFunL.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j ↦
      if j = k then ContinuousLinearMap.snd ℝ E ℝ
      else (eig j - eig k)⁻¹ •
        ((ContinuousLinearMap.proj j).comp
          (b.equivFunL.toContinuousLinearMap.comp
            (ContinuousLinearMap.fst ℝ E ℝ))))).prod
    (-((ContinuousLinearMap.proj k).comp
      (b.equivFunL.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E ℝ))))

/-- The vector coordinates of the constructed inverse separate the normalization coordinate
from the transverse eigenvalue-gap divisions. -/
theorem equivFun_borderedInverse_fst [DecidableEq ι] (b : Module.Basis ι ℝ E) (eig : ι → ℝ)
    (k : ι) (q : E × ℝ) (j : ι) :
    b.equivFun (borderedInverse b eig k q).1 j =
      if j = k then q.2 else b.equivFun q.1 j / (eig j - eig k) := by
  classical
  change b.equivFunL (b.equivFunL.symm _) j = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  by_cases hj : j = k
  · simp [hj]
  · simp [hj, div_eq_mul_inv, mul_comm]

/-- The scalar component of the inverse is minus the selected coordinate of its vector input. -/
theorem borderedInverse_snd (b : Module.Basis ι ℝ E) (eig : ι → ℝ)
    (k : ι) (q : E × ℝ) :
    (borderedInverse b eig k q).2 = -b.equivFun q.1 k := rfl

/-- In basis coordinates, the bordered map is diagonal except for the selected scalar column. -/
private theorem equivFun_bordered_fst [DecidableEq ι] (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (eig : ι → ℝ) (k : ι) (hA : ∀ j, A (b j) = eig j • b j)
    (q : E × ℝ) (j : ι) :
    b.equivFun (bordered b A eig k q).1 j =
      eig j * b.equivFun q.1 j -
        (eig k * b.equivFun q.1 j + q.2 * (if k = j then 1 else 0)) := by
  classical
  change b.equivFun (A q.1 - (eig k • q.1 + q.2 • b k)) j = _
  have hdiag := b.equivFun_apply_of_apply_basis_eq_smul A.toLinearMap eig hA q.1 j
  change b.equivFun (A q.1) j = eig j * b.equivFun q.1 j at hdiag
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Module.Basis.equivFun_self]
  rw [hdiag]

/-- The constructed map is a right inverse of the bordered derivative. Only the gaps from
the chosen eigenvalue must be nonzero; other eigenvalues may coincide with each other. -/
theorem bordered_comp_inverse (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (eig : ι → ℝ) (k : ι) (hA : ∀ j, A (b j) = eig j • b j)
    (hsep : ∀ j, j ≠ k → eig j ≠ eig k) :
    (bordered b A eig k).comp (borderedInverse b eig k) =
      ContinuousLinearMap.id ℝ (E × ℝ) := by
  classical
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext
  · apply b.equivFun.injective
    funext j
    change b.equivFun (bordered b A eig k (borderedInverse b eig k q)).1 j =
      b.equivFun q.1 j
    rw [equivFun_bordered_fst b A eig k hA, equivFun_borderedInverse_fst,
      borderedInverse_snd]
    by_cases hj : j = k
    · subst j
      simp only [ite_true, mul_one]
      abel
    · simp only [hj, Ne.symm hj, ite_false, mul_zero, add_zero]
      rw [← sub_mul, mul_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr (hsep j hj))]
  · change b.equivFun (borderedInverse b eig k q).1 k = q.2
    rw [equivFun_borderedInverse_fst, ite_eq_left rfl]

/-- The same explicit formula is a left inverse, so it also recovers the vector and
eigenvalue increments from their linearized equation and normalization. -/
theorem inverse_comp_bordered (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (eig : ι → ℝ) (k : ι) (hA : ∀ j, A (b j) = eig j • b j)
    (hsep : ∀ j, j ≠ k → eig j ≠ eig k) :
    (borderedInverse b eig k).comp (bordered b A eig k) =
      ContinuousLinearMap.id ℝ (E × ℝ) := by
  classical
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext
  · apply b.equivFun.injective
    funext j
    change b.equivFun (borderedInverse b eig k (bordered b A eig k q)).1 j =
      b.equivFun q.1 j
    rw [equivFun_borderedInverse_fst]
    by_cases hj : j = k
    · subst j
      rw [ite_eq_left rfl]
      rfl
    · rw [ite_eq_right hj, equivFun_bordered_fst b A eig k hA]
      simp only [Ne.symm hj, ite_false, mul_zero, add_zero]
      rw [← sub_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr (hsep j hj))]
  · change (borderedInverse b eig k (bordered b A eig k q)).2 = q.2
    rw [borderedInverse_snd, equivFun_bordered_fst b A eig k hA]
    simp only [ite_true, mul_one]
    abel

/-- A finite eigenbasis and separation of the selected eigenvalue give the invertibility
needed by the implicit-function theorem, via the two constructed inverse identities. -/
theorem isInvertible_bordered (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (eig : ι → ℝ) (k : ι) (hA : ∀ j, A (b j) = eig j • b j)
    (hsep : ∀ j, j ≠ k → eig j ≠ eig k) :
    (bordered b A eig k).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (bordered_comp_inverse b A eig k hA hsep)
    (inverse_comp_bordered b A eig k hA hsep)

/-! ## The implicit eigenpair equation -/

/-- The eigenvalue residual and the selected basis coordinate. Its value `(0, 1)` expresses
the eigenvalue equation with the normalization fixing the eigenvector's scale. -/
def normalizedEquation (b : Module.Basis ι ℝ E) (k : ι) :
    (E →L[ℝ] E) × (E × ℝ) → E × ℝ :=
  fun z ↦ (z.1 z.2.1 - z.2.2 • z.2.1, b.equivFun z.2.1 k)

/-- The normalized equation is polynomial in the operator, vector, and eigenvalue, hence
analytic. The coordinate functional is continuous because the basis is finite. -/
theorem contDiff_normalizedEquation (b : Module.Basis ι ℝ E) (k : ι) :
    ContDiff ℝ ω (normalizedEquation b k) := by
  let c : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  exact (contDiff_fst.clm_apply contDiff_snd.fst |>.sub
    (contDiff_snd.snd.smul contDiff_snd.fst)).prodMk
    (c.contDiff.comp contDiff_snd.fst)

/-- Differentiating only the vector and eigenvalue variables gives the bordered operator.
This is the partial derivative to which Mathlib's implicit function theorem is applied. -/
theorem fderiv_normalizedEquation_comp_inr (b : Module.Basis ι ℝ E)
    (A : E →L[ℝ] E) (eig : ι → ℝ) (k : ι) :
    (fderiv ℝ (normalizedEquation b k) (A, (b k, eig k))).comp
      (ContinuousLinearMap.inr ℝ (E →L[ℝ] E) (E × ℝ)) = bordered b A eig k := by
  let p : E × ℝ := (b k, eig k)
  let c : E →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  have hfst := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt (x := p)
  have hsnd := (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt (x := p)
  have hpartial : HasFDerivAt (fun q ↦ normalizedEquation b k (A, q))
      (bordered b A eig k) p := by
    exact ((A.hasFDerivAt.comp p hfst).sub (hsnd.smul hfst)).prodMk
      (c.hasFDerivAt.comp p hfst)
  have hfull : DifferentiableAt ℝ (normalizedEquation b k) (A, p) :=
    (contDiff_normalizedEquation b k).contDiffAt.differentiableAt
      (by simp : (ω : ℕ∞ω) ≠ 0)
  exact (hfull.hasFDerivAt.comp p (hasFDerivAt_prodMk_right A p)).unique hpartial

/-- Construct a normalized eigenpair near an operator with a finite real eigenbasis and a
selected simple eigenvalue. The pair is analytic at the base operator and on a neighborhood
of it; its vector is nonzero there. Uniqueness is local in both the operator and the pair.

Only gaps from the selected eigenvalue are assumed nonzero. The analytic order refers to
dependence on the operator itself. -/
theorem exists_normalized_eigenpair (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (eig : ι → ℝ) (k : ι) (hA : ∀ j, A (b j) = eig j • b j)
    (hsep : ∀ j, j ≠ k → eig j ≠ eig k) :
    ∃ ψ : (E →L[ℝ] E) → E × ℝ,
      ψ A = (b k, eig k) ∧
      ContDiffAt ℝ ω ψ A ∧
      (∀ᶠ B in 𝓝 A, ContDiffAt ℝ ω ψ B ∧
        B (ψ B).1 = (ψ B).2 • (ψ B).1 ∧
        b.equivFun (ψ B).1 k = 1 ∧ (ψ B).1 ≠ 0) ∧
      (∀ᶠ z in 𝓝 (A, (b k, eig k)),
        (z.1 z.2.1 = z.2.2 • z.2.1 ∧ b.equivFun z.2.1 k = 1) ↔
          ψ z.1 = z.2) := by
  classical
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hbase : normalizedEquation b k (A, (b k, eig k)) = (0, 1) := by
    simp [normalizedEquation, hA]
  have hcd := (contDiff_normalizedEquation b k).contDiffAt
    (x := (A, (b k, eig k)))
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hinv : ((fderiv ℝ (normalizedEquation b k) (A, (b k, eig k))).comp
      (ContinuousLinearMap.inr ℝ (E →L[ℝ] E) (E × ℝ))).IsInvertible := by
    rw [fderiv_normalizedEquation_comp_inr]
    exact isInvertible_bordered b A eig k hA hsep
  let ψ := hcd.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ ω ψ A := hcd.contDiffAt_implicitFunction hn hinv
  refine ⟨ψ, hcd.implicitFunction_apply_self hn hinv, hψ, ?_, ?_⟩
  · filter_upwards [hcd.eventually_apply_implicitFunction hn hinv,
      hψ.eventually (by simp)] with B hB hs
    have heq : B (ψ B).1 = (ψ B).2 • (ψ B).1 ∧
        b.equivFun (ψ B).1 k = 1 := by
      change normalizedEquation b k (B, ψ B) =
        normalizedEquation b k (A, (b k, eig k)) at hB
      rw [hbase] at hB
      simpa only [normalizedEquation, Prod.mk.injEq, sub_eq_zero] using hB
    refine ⟨hs, heq.1, heq.2, ?_⟩
    intro hz
    simpa [hz] using heq.2
  · filter_upwards [hcd.eventually_apply_eq_iff_implicitFunction hn hinv] with z hz
    change (normalizedEquation b k z = normalizedEquation b k (A, (b k, eig k)) ↔
      ψ z.1 = z.2) at hz
    rw [hbase] at hz
    simpa only [normalizedEquation, Prod.mk.injEq, sub_eq_zero] using hz

end PDE.Analysis.Calculus.SimpleEigenpair
