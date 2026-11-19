/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# Hilbert eigenbases of compact self-adjoint operators

Mathlib proves that the eigenspaces of a compact self-adjoint operator have trivial orthogonal
complement, `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`. Choosing a
Hilbert basis in each closed eigenspace and joining these orthogonal families gives a Hilbert
basis of the ambient space. The kernel is included as the zero eigenspace, so neither
injectivity nor separability is required.

The index type records an eigenvalue and a basis vector in its eigenspace. No ordering of the
eigenvalues, or enumeration by natural numbers, is asserted.

This is Evans, App. D.6, Theorem 7, over `ℝ` or `ℂ` and without his separability hypothesis,
which makes the basis countable. His step 2, the orthogonality of the eigenspaces, is
`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`; his step 3, `H̃^⊥ = {0}` for the span
`H̃` of the eigenspaces, is the Mathlib theorem above; and for his step 4 we choose a basis of
each eigenspace with `exists_hilbertBasis` and join them with
`OrthogonalFamily.orthonormal_sigma_orthonormal` and `HilbertBasis.mkOfOrthogonalEqBot`.

## Main results

* `exists_hilbertBasis_eigenvectors`: a compact self-adjoint operator on a complete inner
  product space has a Hilbert basis of eigenvectors.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. D.6, Theorem 7 (Eigenvectors of a compact,
  symmetric operator) and its proof, pp. 728-729. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

universe u v

namespace PDE.Analysis.Spectral

open Module.End

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A compact self-adjoint operator admits a Hilbert basis of eigenvectors, including a basis
of its kernel. The basis may have an arbitrary index type when the kernel is not separable. -/
theorem exists_hilbertBasis_eigenvectors
    (T : H →L[𝕜] H) (hcompact : IsCompactOperator T) (hsymm : T.IsSymmetric) :
    ∃ (ι : Type (max u v)) (b : HilbertBasis ι 𝕜 H) (μ : ι → 𝕜),
      ∀ i, HasEigenvector (T : Module.End 𝕜 H) (μ i) (b i) := by
  classical
  let E (μ : 𝕜) := eigenspace (T : Module.End 𝕜 H) μ
  have (μ : 𝕜) : CompleteSpace (E μ) :=
    (T.isClosed_eigenspace μ).completeSpace_coe
  choose s b _ using fun μ : 𝕜 ↦ exists_hilbertBasis 𝕜 (E μ)
  let e : (Σ μ, s μ) → H := fun i ↦ b i.1 i.2
  have horth : Orthonormal 𝕜 e :=
    hsymm.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun μ ↦ (b μ).orthonormal)
  have htotal :
      (⨆ μ, E μ) ≤ (Submodule.span 𝕜 (Set.range e)).topologicalClosure := by
    refine iSup_le ?_
    intro μ x hx
    have hsum := ((b μ).hasSum_repr ⟨x, hx⟩).mapL (E μ).subtypeL
    change x ∈ closure (Submodule.span 𝕜 (Set.range e) : Set H)
    refine mem_closure_of_tendsto hsum (Filter.Eventually.of_forall ?_)
    intro t
    refine Submodule.sum_mem _ ?_
    intro i _
    simpa only [map_smul, Submodule.subtypeL_apply, e] using
      (Submodule.span 𝕜 (Set.range e)).smul_mem ((b μ).repr ⟨x, hx⟩ i)
        (Submodule.subset_span (Set.mem_range.mpr ⟨⟨μ, i⟩, rfl⟩))
  have hbot : (Submodule.span 𝕜 (Set.range e))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← Submodule.orthogonal_closure]
    exact (Submodule.orthogonal_le htotal).trans_eq
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsymm)
  refine ⟨Σ μ, s μ, HilbertBasis.mkOfOrthogonalEqBot horth hbot, Sigma.fst, ?_⟩
  intro i
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact ⟨(b i.1 i.2).property, horth.ne_zero i⟩

end PDE.Analysis.Spectral
