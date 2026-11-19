/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator
public import PDE.Elliptic.Regularity.Interior.ClassicalDivergence
public import PDE.Elliptic.Regularity.Interior.Eigenfunction
import PDE.Analysis.MeasureTheory.LocalRepresentative
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Interior

/-!
# Classical representatives of variable-coefficient weak eigenfunctions

The interior Sobolev bootstrap gives enough weak derivatives for Morrey reconstruction
to produce a classical representative. A finite number of bounded weak coefficient
derivatives suffices for each prescribed classical order. The bootstrap used here assumes
globally bounded coefficients with globally Lipschitz representatives and global ellipticity.
Compatible coefficient data at every order give a single smooth representative: continuity
identifies the representatives produced by the finite-order estimates.

For locally `C¹` coefficient representatives, the weak equation identifies the classical
flux equation. Expanding the flux produces the drift `bⱼ = -∑ᵢ ∂ᵢaᵢⱼ`; this term records
the variation of the coefficients. No symmetry, boundary condition, connectedness, or
sign condition on the eigenvalue is needed.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The finite-order interior bootstrap produces a `C^k` representative when
`m + 2 ≥ k + 1 + n / 2`. Coefficients need `m + 1` bounded weak derivatives, in addition
to the global Lipschitz and ellipticity hypotheses of the interior `H²` theorem.
The state is an arbitrary `H¹` weak eigenfunction; it need not have zero trace. -/
theorem IsInteriorWeakDivergenceSolution.exists_contDiffAt_eigenfunction_representative
    [Fact (0 < n)] (k m : ℕ) (hm : k + 1 + n / 2 ≤ m + 2)
    (A0 : Fin n → Fin n → DerivLp n ∞ univ)
    (a : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hA0 : ∀ i j, (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 alpha)
    (A : Fin n → Fin n → W^{m + 1,∞}(Ω))
    (hA : ∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ))
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))
      (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ k f x) ∧
      f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  apply MeasureTheory.exists_contDiffAt_ae_eq_of_locally (μ := volume)
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, W, hW⟩ :=
    BoundaryRegularity.exists_eigenfunction_interiorRegularity_open_neighborhood_of_compact
      m hu.isOpen A0 a C ha hA0 helliptic A hA lambda u hu
      {x} isCompact_singleton (by simpa using hx)
  obtain ⟨f, hreg, hrep⟩ := exists_contDiffAt_representative_of_order
    (k := k) Fact.out hV W hm
  exact ⟨V, hV, hxV (by simp), hVΩ, f,
    (fun y hy ↦ (hreg y hy).contDiffWithinAt), hrep.trans hW⟩

/-- A weak eigenfunction with sufficiently many bounded weak coefficient derivatives
has a `C²` interior representative solving the classical matrix equation. Its drift is
constructed from the first derivatives of the `C¹` coefficient representatives.
No classical representative of `u` or pointwise PDE is assumed. Symmetry and boundary
regularity are not required. -/
theorem IsInteriorWeakDivergenceSolution.exists_classical_eigenfunction_representative
    [Fact (0 < n)] (m : ℕ) (hm : 3 + n / 2 ≤ m + 2)
    (A0 : Fin n → Fin n → DerivLp n ∞ univ)
    (a : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hA0 : ∀ i j, (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j)
    (haC1 : ∀ i j x, x ∈ Ω → ContDiffAt ℝ 1 (a i j) x)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 alpha)
    (A : Fin n → Fin n → W^{m + 1,∞}(Ω))
    (hA : ∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ))
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))
      (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ,
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      ∀ x ∈ Ω, EllipticMaximum.matrixOperator (fun y i j ↦ a i j y)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
        (fun _ ↦ 0) f x = lambda * f x := by
  obtain ⟨f, hreg, hrep⟩ :=
    hu.exists_contDiffAt_eigenfunction_representative 2 m hm A0 a C ha hA0
      helliptic A hA
  have hforce : ((lambda • wkpBaseCoordinateCLM u : DerivLp n 2 Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ lambda * f x := by
    filter_upwards [Lp.coeFn_smul lambda (wkpBaseCoordinateCLM u), hrep] with x hsm hr
    rw [hsm]
    simp only [Pi.smul_apply, smul_eq_mul, hr]
  have hcoeff (i j : Fin n) :
      (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] a i j :=
    (restrictDerivLp_apply_ae (subset_univ Ω) (A0 i j)).trans
      (ae_restrict_of_ae (hA0 i j))
  have hequation := hu.neg_sum_partialDeriv_flux_eq_of_representatives
    a hcoeff haC1 hrep.symm hreg hforce
    ((show ContinuousOn f Ω from
      fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt).const_mul lambda)
  refine ⟨f, hrep.symm, hreg, ?_⟩
  intro x hx
  rw [EllipticMaximum.matrixOperator_eq_neg_sum_partialDeriv_flux
    a (fun i j ↦ haC1 i j x hx) (hreg x hx)]
  exact hequation x hx

/-- An interior weak eigenfunction has a single smooth representative when the
coefficients have compatible bounded weak derivatives at every finite order.

Each coefficient bundle represents the restriction of the fixed global `L∞` coefficient.
Global Lipschitz representatives and global uniform ellipticity are the assumptions of
the finite-order interior bootstrap. The domain need not be bounded or connected, the
coefficient matrix need not be symmetric, and the eigenvalue may have either sign.
There is no boundary regularity or zero-trace hypothesis. Smoothness is concluded only
at points of `Ω`; values of the representative outside `Ω` are unrestricted. -/
theorem IsInteriorWeakDivergenceSolution.exists_smooth_eigenfunction_representative
    [Fact (0 < n)]
    (A0 : Fin n → Fin n → DerivLp n ∞ univ)
    (a : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hA0 : ∀ i j, (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 alpha)
    (A : ∀ m : ℕ, Fin n → Fin n → W^{m + 1,∞}(Ω))
    (hA : ∀ m i j, (wkpBaseCoordinateCLM (A m i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ))
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))
      (lambda • wkpBaseCoordinateCLM u) u) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f x) ∧
      f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  have hfinite : ∀ k : ℕ, ∃ f : ℝ^n → ℝ,
      ContDiffOn ℝ k f Ω ∧
        f =ᵐ[domainMeasure n Ω] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
    intro k
    obtain ⟨f, hreg, hrep⟩ := hu.exists_contDiffAt_eigenfunction_representative
      k (k + n / 2) (by omega) A0 a C ha hA0 helliptic
      (A (k + n / 2)) (hA (k + n / 2))
    exact ⟨f, (fun x hx ↦ (hreg x hx).contDiffWithinAt), hrep⟩
  obtain ⟨f, hreg, hrep⟩ := MeasureTheory.exists_contDiffOn_ae_eq_of_forall_nat
    (𝕜 := ℝ) (μ := volume) hu.isOpen (Subset.refl Ω) subset_closure hfinite
  exact ⟨f, fun x hx ↦ hreg.contDiffAt (hu.isOpen.mem_nhds hx), hrep⟩


end SobolevSpace.GraphSpace
