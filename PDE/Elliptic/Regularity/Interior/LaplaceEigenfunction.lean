/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Eigenfunction
public import PDE.Elliptic.Variational.DistributionalPoisson

/-!
# Interior Sobolev regularity of weak Laplace eigenfunctions

The identity coefficient matrix satisfies every finite coefficient regularity requirement.
Instantiating the interior eigenfunction bootstrap therefore gives Sobolev representatives
of every finite order near each compact subset of the open domain. No boundary atlas or
boundedness of the domain is needed.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

private theorem constantHigherDerivativesMemLp
    {Ω : Set (ℝ^n)} (k : ℕ) (c : ℝ) (b : DerivIndex n k) :
    MemLp (iteratedPartialDeriv b.toList (fun _ : ℝ^n ↦ c))
      ∞ (domainMeasure n Ω) := by
  have hconstant : ∀ l : List (Fin n),
      ∃ d : ℝ, iteratedPartialDeriv l (fun _ : ℝ^n ↦ c) = fun _ ↦ d := by
    intro l
    induction l with
    | nil => exact ⟨c, rfl⟩
    | cons i l ih =>
        obtain ⟨d, hd⟩ := ih
        refine ⟨0, ?_⟩
        simp only [iteratedPartialDeriv, hd, PDE.partialDeriv_const]
  obtain ⟨d, hd⟩ := hconstant b.toList
  rw [hd]
  exact memLp_top_const d

private def constantHigherSobolev
    {Ω : Set (ℝ^n)} (k : ℕ) (c : ℝ) : W^{k,∞}(Ω) :=
  mkWkpSpaceOnOfContDiffMemLp (fun _ ↦ c) contDiff_const
    (constantHigherDerivativesMemLp k c)

private theorem constantHigherSobolev_base_ae
    {Ω : Set (ℝ^n)} (k : ℕ) (c : ℝ) :
    baseRepresentative (constantHigherSobolev (Ω := Ω) k c)
      =ᵐ[domainMeasure n Ω] fun _ ↦ c := by
  simpa [constantHigherSobolev, baseRepresentative, baseIndex_toList,
    iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (n := n) (k := k) (p := ∞)
      (Ω := Ω) (fun _ ↦ c) contDiff_const
      (constantHigherDerivativesMemLp k c) (baseIndex n k)

/-- A weak solution of `−Δu = λu` with zero trace has arbitrarily high finite
Sobolev regularity near every compact subset of its open domain. The proof constructs
the identity coefficient bundles and bootstraps the forcing `λu` from the solution. -/
theorem exists_dirichletEigenfunction_interiorRegularity_open_neighborhood_of_compact
    (m : ℕ) {Ω : Set (ℝ^n)} (lambda : ℝ) (u : H¹₀(Ω))
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω)
      (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u)
    (K : Set (ℝ^n)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ W : W^{m + 2,2}(V),
        baseRepresentative W =ᵐ[domainMeasure n V]
          (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) := by
  classical
  let a : Fin n → Fin n → ℝ^n → ℝ := fun i j _ ↦ if i = j then 1 else 0
  let A0 : Fin n → Fin n → DerivLp n ∞ univ := fun i j ↦
    wkpBaseCoordinateCLM (constantHigherSobolev (Ω := univ) 0 (if i = j then 1 else 0))
  have hA0 (i j : Fin n) : (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j := by
    simpa only [A0, a, wkpBaseCoordinateCLM_apply, baseRepresentative,
      domainMeasure, Measure.restrict_univ] using
      constantHigherSobolev_base_ae (Ω := univ) 0 (if i = j then 1 else 0)
  have hAr (i j : Fin n) :
      (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] a i j :=
    (restrictDerivLp_apply_ae (subset_univ Ω) (A0 i j)).trans
      (ae_restrict_of_ae (hA0 i j))
  have hElliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 1 := by
    refine ⟨zero_lt_one, ?_⟩
    have hall : ∀ᵐ x ∂domainMeasure n univ, ∀ i j, A0 i j x = a i j x := by
      simpa only [Filter.EventuallyEq, ae_all_iff, domainMeasure,
        Measure.restrict_univ] using hA0
    filter_upwards [hall] with x hx
    intro ξ
    simp [hx, a, ite_mul]
  let A : Fin n → Fin n → W^{m + 1,∞}(Ω) := fun i j ↦
    constantHigherSobolev (m + 1) (if i = j then 1 else 0)
  have hAbase (i j : Fin n) : (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ) :=
    (constantHigherSobolev_base_ae (m + 1) (if i = j then 1 else 0)).trans (hAr i j).symm
  have huA : IsWeakDivergenceSolution
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))
      (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u := by
    refine ⟨hu.1, fun φ ↦ ?_⟩
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
          (if i = j then (1 : ℝ) else 0) *
            ∫ x, (derivCoordCLM (n := n) (Ω := Ω) j u : ℝ^n → ℝ) x *
              (∂[i] φ.1.toFun) x ∂domainMeasure n Ω :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
          rw [← integral_const_mul]
          exact integral_congr_ae ((hAr i j).mono fun x hx ↦ by simp only [hx, a, mul_assoc])
      _ = ∑ i : Fin n,
          ∫ x, (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ) x *
            (∂[i] φ.1.toFun) x ∂domainMeasure n Ω := by
        simp [ite_mul]
      _ = _ := hu.2 φ
  exact exists_eigenfunction_interiorRegularity_open_neighborhood_of_compact
    m hu.1 A0 a (fun _ _ ↦ 0) (fun i j ↦ LipschitzWith.const (if i = j then 1 else 0))
    hA0 hElliptic A hAbase lambda (u : H¹(Ω)) huA.toInterior K hK hKΩ

end SobolevSpace.GraphSpace.BoundaryRegularity
