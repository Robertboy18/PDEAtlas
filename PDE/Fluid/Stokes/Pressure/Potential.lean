/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Regularity.Residual
public import PDE.Spaces.Sobolev.Calculus.Potential.Algebraic
import PDE.Fluid.Stokes.Pressure.Annihilator
import PDE.DistributionTheory.Distribution.Regular.Evaluation
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Weak pressure from the raw Stokes minimum

The derived locally L² residual is weakly closed. The algebraic functional from
the full constrained minimum fixes the constants of its local potentials,
giving a locally L² pressure on any open domain with distributional gradient
`Dp = Δu + f`. This fixes the sign in `-Δu = f - Dp`; neither simple
connectedness nor a global pressure estimate is assumed. On every open set `V` with compact
closure in the domain the pressure agrees almost everywhere with an element of `H¹(V)`
(`exists_pressure_local_sobolev_of_minimizes_energy`).

This is the pressure `p ∈ L²_loc(U)` of Evans (§8.4.4(a), Theorem 6), which is stated for a
bounded, simply connected open set `U` in `ℝ^3`; here the domain is any open set in `ℝ^n`,
`n > 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.4(a), Theorem 6 (Pressure as Lagrange multiplier),
  pp. 497-499.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal Distributions

namespace IncompressibleFlow.Stokes

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Opens (ℝ^n)}

variable [Fact (0 < n)]

/-- A raw divergence-free energy minimum on an arbitrary open domain
has a locally L² pressure whose distributional gradient is `Δu + f`. -/
theorem exists_pressure_distribution_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp p 2 (domainMeasure n K)) ∧
      LocallyIntegrableOn p (Ω : Set (ℝ^n)) volume ∧
      ∀ j, Distribution.lineDerivCLM (EuclideanSpace.single j (1 : ℝ))
        (Distribution.ofFun Ω p volume ⊤) = residual f u j := by
  obtain ⟨R, hRlocal, hRmem, hR⟩ :=
    exists_locally_memLp_residual_of_minimizes_energy f u hu hmin
  have hclosed (i j : Fin n) :
      Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
        (Distribution.ofFun Ω (fun x ↦ R x j) volume ⊤) =
      (Distribution.lineDerivCLM (EuclideanSpace.single j (1 : ℝ))
        (Distribution.ofFun Ω (fun x ↦ R x i) volume ⊤) : 𝓓'(Ω, ℝ)) := by
    rw [hR j, hR i]
    exact lineDeriv_residual_eq_of_minimizes_energy f u hu hmin i j
  have hweak (i j : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφ : tsupport φ ⊆ Ω) :
      (∫ x in (Ω : Set (ℝ^n)), R x j * (∂[i] (φ : ℝ^n → ℝ)) x) =
        ∫ x in (Ω : Set (ℝ^n)), R x i * (∂[j] (φ : ℝ^n → ℝ)) x := by
    let ψ : 𝓓(Ω, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    have h := congrArg (fun T : 𝓓'(Ω, ℝ) ↦ T ψ) (hclosed i j)
    simp only [Distribution.lineDerivCLM_apply,
      Distribution.ofFun_apply_eq_setIntegral_mul (hRlocal j),
      Distribution.ofFun_apply_eq_setIntegral_mul (hRlocal i)] at h
    exact neg_injective h
  obtain ⟨q, hq⟩ :=
    exists_linearMap_partialDeriv_eq_neg_residual_of_minimizes_energy f u hu hmin
  have hqR (j : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφ : tsupport φ ⊆ Ω) :
      q (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ) =
        -(∫ x in (Ω : Set (ℝ^n)), R x j * φ x) := by
    rw [hq j φ hφ, ← hR j, Distribution.ofFun_apply_eq_setIntegral_mul (hRlocal j)]
    rfl
  obtain ⟨p, hp, hpLp, hpD⟩ :=
    exists_weak_potential_of_linearMap_partialDeriv Ω.isOpen R hRmem hweak q hqR
  have i : Fin n := ⟨0, Fact.out⟩
  refine ⟨p, hp, hpLp, (hpD i).locallyIntegrable_f, fun j ↦ ?_⟩
  exact (hpD j).lineDerivCLM_ofFun.trans (hR j)

/-- The pressure of a raw Stokes minimum belongs to H¹ on every relatively
compact open subset of the domain. These local Sobolev representatives all
represent the same scalar pressure. -/
theorem exists_pressure_local_sobolev_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp p 2 (domainMeasure n K)) ∧
      (∀ j, Distribution.lineDerivCLM (EuclideanSpace.single j (1 : ℝ))
        (Distribution.ofFun Ω p volume ⊤) = residual f u j) ∧
      ∀ V : Opens (ℝ^n), IsCompact (closure (V : Set (ℝ^n))) →
        closure (V : Set (ℝ^n)) ⊆ Ω →
        ∃ P : H¹(V), baseRepresentative P =ᵐ[domainMeasure n V] p := by
  obtain ⟨p, hp, hpLp, hplocal, hpD⟩ :=
    exists_pressure_distribution_of_minimizes_energy f u hu hmin
  obtain ⟨R, hRlocal, hRmem, hR⟩ :=
    exists_locally_memLp_residual_of_minimizes_energy f u hu hmin
  have hweak (j : Fin n) : HasWeakDerivativeOn (Ω : Set (ℝ^n)) [j] p
      (fun x ↦ R x j) :=
    hasWeakDerivativeOn_of_lineDerivCLM_ofFun hplocal (hRlocal j)
      ((hpD j).trans (hR j).symm)
  refine ⟨p, hp, hpLp, hpD, fun V hV hVΩ ↦ ?_⟩
  have hpV : MemLp p 2 (domainMeasure n V) :=
    (hpLp _ hV hVΩ).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have hRV : MemLp R 2 (domainMeasure n V) :=
    memLp_piLp_iff.mpr fun j ↦
      (hRmem j _ hV hVΩ).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  obtain ⟨P, hP, _⟩ := exists_of_weakGradient hpV hRV
    (fun j ↦ (hweak j).mono V.isOpen.measurableSet (subset_closure.trans hVΩ))
  exact ⟨P, hP⟩

/-- The pressure reconstructed from the raw minimum satisfies the signed
component identity on every smooth compactly supported test. -/
theorem exists_pressure_test_identity_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp p 2 (domainMeasure n K)) ∧
      ∀ j : Fin n, ∀ φ : TestFunctionOn n (Ω : Set (ℝ^n)),
        (∑ k : Fin n, ∫ x in (Ω : Set (ℝ^n)),
          derivCoordCLM k (u j) x * (∂[k] (φ.1 : ℝ^n → ℝ)) x) =
        (∫ x in (Ω : Set (ℝ^n)), p x * (∂[j] (φ.1 : ℝ^n → ℝ)) x) +
          ∫ x in (Ω : Set (ℝ^n)), f x j * φ.1 x := by
  obtain ⟨p, hp, hpLp, hplocal, hpD⟩ :=
    exists_pressure_distribution_of_minimizes_energy f u hu hmin
  refine ⟨p, hp, hpLp, fun j φ ↦ ?_⟩
  let ψ : 𝓓(Ω, ℝ) := ⟨φ.1, φ.1.contDiff, φ.1.hasCompactSupport, φ.2⟩
  have h := congrArg (fun T : 𝓓'(Ω, ℝ) ↦ T ψ) (hpD j)
  rw [Distribution.lineDerivCLM_apply, Distribution.ofFun_apply_eq_setIntegral_mul hplocal,
    residual_apply] at h
  change -(∫ x in (Ω : Set (ℝ^n)), p x * (∂[j] (φ.1 : ℝ^n → ℝ)) x) =
    -(∑ k : Fin n, ∫ x in (Ω : Set (ℝ^n)),
      derivCoordCLM k (u j) x * (∂[k] (φ.1 : ℝ^n → ℝ)) x) +
      (∫ x in (Ω : Set (ℝ^n)), f x j * φ.1 x) at h
  linarith only [h]

end IncompressibleFlow.Stokes
