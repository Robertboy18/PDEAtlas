/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import PDE.FDeriv.Calculus

/-!
# Scalar potentials on convex Hilbert-space domains

Mathlib's Poincaré lemma integrates a differentiable closed one-form. Here the
inner-product identification gives a scalar potential for a vector field with
symmetric derivative on any complete real inner-product space. A `Cᵏ` field
has a `Cᵏ⁺¹` potential, including smooth fields. In finite-dimensional Euclidean
space, the coordinate form identifies symmetry from the actual partial derivatives.
These calculus results are shared by classical fluid pressure reconstruction and
weak Sobolev potential construction.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Gradient

namespace EuclideanSpace

variable {n : ℕ}

/-- Equality of the off-diagonal coordinate derivatives makes the Fréchet
derivative of a Euclidean vector field symmetric with respect to the inner
product. -/
theorem inner_fderiv_apply_comm_of_partialDeriv_comm
    (g : ℝ^n → ℝ^n) (x : ℝ^n) (hg : DifferentiableAt ℝ g x)
    (hcomm : ∀ i j : Fin n,
      (∂[i] (fun y ↦ g y j)) x =
        (∂[j] (fun y ↦ g y i)) x)
    (a b : ℝ^n) :
    inner ℝ ((fderiv ℝ g x) a) b =
      inner ℝ ((fderiv ℝ g x) b) a := by
  rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv,
    PDE.fderiv_apply_eq_sum_smul_partialDeriv]
  have hsumApply (v : ℝ^n) (i : Fin n) :
      (∑ j : Fin n, v j • (∂[j] g) x) i =
        ∑ j : Fin n, v j * (∂[j] g) x i := by
    change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i)
        (∑ j : Fin n, v j • (∂[j] g) x) = _
    rw [map_sum]
    simp only [map_smul, PiLp.proj_apply, smul_eq_mul]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [hsumApply]
  calc
    (∑ i : Fin n, b i * (∑ j : Fin n,
        a j * (∂[j] g) x i)) =
        ∑ i : Fin n, ∑ j : Fin n,
          b i * (a j * (∂[j] (fun y ↦ g y i)) x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [PDE.partialDeriv_apply j i hg]
    _ = ∑ j : Fin n, ∑ i : Fin n,
          b i * (a j * (∂[j] (fun y ↦ g y i)) x) :=
      Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n,
          a j * (b i * (∂[i] (fun y ↦ g y j)) x) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hcomm j i]
      ring
    _ = ∑ j : Fin n, a j * (∑ i : Fin n,
          b i * (∂[i] g) x j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [PDE.partialDeriv_apply i j hg]

end EuclideanSpace

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A differentiable vector field with symmetric derivative on an open convex
domain in a real Hilbert space is the gradient of a scalar potential there.

The symmetry hypothesis is the coordinate-free closed-one-form condition
`<Dg(x) a, b> = <Dg(x) b, a>`. Convexity supplies the global topology needed
to integrate the field; openness upgrades the derivative within the domain to
an ordinary derivative at each of its points. -/
theorem exists_potential_of_fderiv_symmetric
    {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s)
    {g : E → E} (hg : DifferentiableOn ℝ g s)
    (hsymm : ∀ x ∈ s, ∀ a b : E,
      inner ℝ ((fderiv ℝ g x) a) b =
        inner ℝ ((fderiv ℝ g x) b) a) :
    ∃ p : E → ℝ, ∀ x ∈ s, HasGradientAt p (g x) x := by
  let omega : E → E →L[ℝ] ℝ := fun x ↦ innerSL ℝ (g x)
  have hgAt (x : E) (hx : x ∈ s) : DifferentiableAt ℝ g x :=
    (hg x hx).differentiableAt (hso.mem_nhds hx)
  have homega : DifferentiableOn ℝ omega s := by
    intro x hx
    exact ((innerSL ℝ).differentiableAt.comp x (hgAt x hx)).differentiableWithinAt
  have homegaFDeriv (x : E) (hx : x ∈ s) :
      fderiv ℝ omega x = (innerSL ℝ).comp (fderiv ℝ g x) := by
    exact ((innerSL ℝ).hasFDerivAt.comp x (hgAt x hx).hasFDerivAt).fderiv
  obtain ⟨p, hp⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric hso
    homega fun x hx a b ↦ by
      rw [homegaFDeriv x hx]
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      exact hsymm x hx a b
  exact ⟨p, fun x hx ↦ hasGradientAt_iff_hasFDerivAt.mpr (hp x hx)⟩

/-- The potential supplied by `exists_potential_of_fderiv_symmetric` has the
prescribed gradient throughout the domain. -/
theorem exists_gradient_eq_of_fderiv_symmetric
    {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s)
    {g : E → E} (hg : DifferentiableOn ℝ g s)
    (hsymm : ∀ x ∈ s, ∀ a b : E,
      inner ℝ ((fderiv ℝ g x) a) b =
        inner ℝ ((fderiv ℝ g x) b) a) :
    ∃ p : E → ℝ, ∀ x ∈ s, ∇ p x = g x := by
  obtain ⟨p, hp⟩ :=
    exists_potential_of_fderiv_symmetric hs hso hg hsymm
  exact ⟨p, fun x hx ↦ (hp x hx).gradient⟩

/-- A `Cᵏ` field with symmetric derivative on an open convex set in a real Hilbert
space has a `Cᵏ⁺¹` potential there. The order `k : ℕ∞` includes smooth fields;
`k ≠ 0` supplies the differentiability needed by the Poincaré lemma.
No regularity is asserted outside the set. -/
theorem exists_contDiffOn_potential_of_fderiv_symmetric
    {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s)
    {k : ℕ∞} (hk : k ≠ 0) {g : E → E} (hg : ContDiffOn ℝ k g s)
    (hsymm : ∀ x ∈ s, ∀ a b : E,
      inner ℝ ((fderiv ℝ g x) a) b =
        inner ℝ ((fderiv ℝ g x) b) a) :
    ∃ p : E → ℝ, ContDiffOn ℝ (k + 1) p s ∧
      ∀ x ∈ s, HasGradientAt p (g x) x := by
  obtain ⟨p, hp⟩ := exists_potential_of_fderiv_symmetric hs hso
    (hg.differentiableOn (by simpa using hk)) hsymm
  refine ⟨p, ?_, hp⟩
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hso]
  refine ⟨fun x hx ↦ (hp x hx).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply ((innerSL ℝ).contDiff.comp_contDiffOn hg).congr
  intro x hx
  exact (hp x hx).hasFDerivAt.fderiv

end InnerProductSpace

namespace EuclideanSpace

variable {n : ℕ}

/-- A differentiable vector field whose coordinate derivatives
commute on an open convex domain is a gradient field there. -/
theorem exists_potential_of_partialDeriv_comm
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {g : ℝ^n → ℝ^n} (hg : DifferentiableOn ℝ g s)
    (hcomm : ∀ x ∈ s, ∀ i j : Fin n,
      (∂[i] (fun y ↦ g y j)) x =
        (∂[j] (fun y ↦ g y i)) x) :
    ∃ p : ℝ^n → ℝ, ∀ x ∈ s, HasGradientAt p (g x) x := by
  apply InnerProductSpace.exists_potential_of_fderiv_symmetric hs hso hg
  intro x hx
  exact inner_fderiv_apply_comm_of_partialDeriv_comm g x
    ((hg x hx).differentiableAt (hso.mem_nhds hx)) (hcomm x hx)

end EuclideanSpace
