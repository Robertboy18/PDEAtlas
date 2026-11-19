/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.Variational.Principle

/-!
# Dirichlet's principle over the finite-energy boundary class

We prove Dirichlet's principle, Evans's §2.2.5(b), Theorem 17, with the energy minimized over the
competitors whose energy density is integrable.

## Main results

- `poisson_iff_isMinOn_finiteClassicalEnergy`: for forcing continuous in `Ω`,
  `-Δu = f` holds if and only if `u` has finite energy and minimizes the energy
  over the finite-energy boundary class.
- `finiteClassicalDirichletClass_eq_classicalDirichletClass_of_poisson`: for a
  classical solution, `f = -Δu` lies in `L²(Ω)`, so every member of the classical
  boundary class has finite energy.
- `exists_continuous_eqOn_of_finiteClassicalEnergy_min`: the forcing of a
  finite-energy minimizer agrees on `Ω` with a continuous function on the whole space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.5(b), Theorem 17 (Dirichlet's principle) and its proof,
  pp. 42-43.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PoissonEquation

open MeasureTheory Set SobolevSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {f g u : ℝ^n → ℝ}

/-- If `u` is `C²` up to the boundary and `-Δu = f` in `Ω`, then `f ∈ L²(Ω)`, and every
member of the classical boundary class has finite energy. -/
theorem finiteClassicalDirichletClass_eq_classicalDirichletClass_of_poisson
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 2 u Ω) (hpde : ∀ x ∈ Ω, -laplacian u x = f x) :
    finiteClassicalDirichletClass Ω f g = classicalDirichletClass Ω g := by
  have hfl := memLp_two_of_poisson hΩ hb hu hpde
  ext v
  constructor
  · exact fun hv ↦ hv.1
  · intro hv
    exact ⟨hv, integrable_classicalEnergy hΩ hb (hv.1.of_le (by omega))
      (hfl.integrable_mul (hv.1.memLp_iteratedPartialDeriv hΩ hb 2 [] (by simp)))⟩

variable [Fact (0 < n)]

/-- Dirichlet's principle over the finite-energy boundary class: for forcing continuous
in `Ω`, `u` solves `-Δu = f` if and only if it has finite energy and minimizes the
energy among all competitors with finite energy. -/
theorem poisson_iff_isMinOn_finiteClassicalEnergy
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : u ∈ classicalDirichletClass Ω g) (hf : ContinuousOn f Ω) :
    (∀ x ∈ Ω, -laplacian u x = f x) ↔
      u ∈ finiteClassicalDirichletClass Ω f g ∧
        IsMinOn (classicalEnergy Ω f) (finiteClassicalDirichletClass Ω f g) u := by
  constructor
  · intro hpde
    rw [finiteClassicalDirichletClass_eq_classicalDirichletClass_of_poisson hΩ hb hu.1 hpde]
    exact ⟨hu, fun v hv ↦ classicalEnergy_le_of_poisson hΩ hb hg hu.1 hu.2.1 hpde hv.1 hv.2.1
      (fun x hx ↦ (hv.2.2 hx).trans (hu.2.2 hx).symm)⟩
  · rintro ⟨hfinite, hmin⟩
    exact poisson_of_isMinOn_finiteClassicalEnergy hΩ hb hg hfinite hf hmin

/-- A minimizer over the finite-energy boundary class minimizes over the whole classical
boundary class, and every member of that class has finite energy. -/
theorem classicalDirichletClass_eq_and_isMinOn_of_finiteClassicalEnergy_min
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : u ∈ finiteClassicalDirichletClass Ω f g) (hf : ContinuousOn f Ω)
    (hmin : IsMinOn (classicalEnergy Ω f) (finiteClassicalDirichletClass Ω f g) u) :
    finiteClassicalDirichletClass Ω f g = classicalDirichletClass Ω g ∧
      IsMinOn (classicalEnergy Ω f) (classicalDirichletClass Ω g) u := by
  have hpde := poisson_of_isMinOn_finiteClassicalEnergy hΩ hb hg hu hf hmin
  have heq := finiteClassicalDirichletClass_eq_classicalDirichletClass_of_poisson
    hΩ hb hu.1.1 hpde (g := g)
  exact ⟨heq, heq ▸ hmin⟩

/-- For a minimizer over the finite-energy boundary class, the forcing agrees on `Ω`
with a continuous function on the whole space, namely an extension of `-Δu`. -/
theorem exists_continuous_eqOn_of_finiteClassicalEnergy_min
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : u ∈ finiteClassicalDirichletClass Ω f g) (hf : ContinuousOn f Ω)
    (hmin : IsMinOn (classicalEnergy Ω f) (finiteClassicalDirichletClass Ω f g) u) :
    ∃ F : ℝ^n → ℝ, Continuous F ∧ EqOn F f Ω := by
  have hpde := poisson_of_isMinOn_finiteClassicalEnergy hΩ hb hg hu hf hmin
  have hl : ContDiffUpToBoundary 0 (laplacian u) Ω := by
    unfold laplacian
    exact ContDiffUpToBoundary.sum Finset.univ (fun i _ ↦
        ((hu.1.1.partialDeriv_of_succ hΩ i).partialDeriv_of_succ hΩ i)) hΩ
  have hfb := (hl.neg hΩ).congr hΩ (fun x hx ↦ (hpde x hx).symm)
  exact hfb.exists_continuous_eqOn

end PoissonEquation
