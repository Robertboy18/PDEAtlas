/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Semilinear.ReactionDiffusion.Integrated

/-!
# Finite-component reaction-diffusion on bounded open sets

We solve `uₜ - Δu = f(u)` for `u : Ω → ℝ^m` in the vector zero-boundary Sobolev space `H¹₀(Ω; ℝ^m)`,
with the full matrix gradient in the weak equation. For a globally Lipschitz reaction `f`, with
`f 0` allowed to be nonzero, every finite time interval and every `L²` initial datum give a unique
weak solution, with weak time derivative in `L²(H⁻¹)` and an `L²` representative that is continuous
on the closed interval (`ReactionDiffusion.existsUnique_weakSolution`). The zero boundary condition
is the closure of compactly supported smooth tuples, so no boundary regularity of `Ω` is needed, and
`Ω` may be empty and `m` may be zero.

This is Evans's §9.2.1, Theorem 2, for the system (2) of Example 1 under his Lipschitz hypothesis
(3), with initial data in `L²` instead of `H¹₀` and no smoothness of the boundary.

## How it works

Evans obtains existence from Banach's fixed point theorem in `C([0, T]; L²)`, first on a short
interval and then by iteration, and uniqueness from Gronwall's inequality. We show instead that the
weak equation is equivalent to the integrated formulation of `ReactionDiffusion.Integrated`
(`integrated_of_weakEquation`, `exists_evolution_of_integrated`), whose unique solution comes from
the Galerkin theorem for globally Lipschitz reactions (`existsUnique_integrated`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.1, Example 1 (Reaction-diffusion equations), (2)-(7),
  p. 535, and Theorem 2 (Existence) and its proof, (8)-(14), pp. 536-537.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal InnerProductSpace

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace ReactionDiffusion

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : (ℝ^m) → (ℝ^m)} {L : ℝ≥0}

local notation "𝓥" => H¹₀(Ω; ℝ^m)
local notation "μ" => domainMeasure n Ω
local notation "ν" => volume.restrict (Ioc a b)
local notation "Pivot" => Lp (ℝ^m) 2 μ

/-- The weak derivative, initial trace, and full-gradient equation imply the integrated
formulation. No energy identity or extra regularity is assumed. -/
theorem integrated_of_weakEquation
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hab : a < b) (hf : LipschitzWith L f)
    {u : Lp 𝓥 2 ν} {d : Lp (StrongDual ℝ 𝓥) 2 ν} {w : ℝ → Pivot} {g : Pivot}
    (hd : HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d)
    (hw : ContinuousOn w (Icc a b))
    (hwae : w =ᵐ[ν] fun t ↦ toLp (u t)) (hwa : w a = g)
    (heq : ∀ᵐ t ∂ν, ∀ v : 𝓥,
      d t v + (∫ x, ∑ i : Fin m, ∑ j : Fin n,
        ∇ (u t) x (finProdFinEquiv (i, j)) *
          ∇ v x (finProdFinEquiv (i, j)) ∂μ) =
        ∫ x, inner ℝ (f (toLp (u t) x)) (toLp v x) ∂μ) :
    IsGelfandIntegratedWeakSolution (gelfandTriple hΩopen)
      (fun _ ↦ vectorDirichletForm)
      (fun t ↦ (gelfandTriple hΩopen).pivotToDual
        (reactionLp hΩbounded hf (toLp (u t)))) u g := by
  let : MeasurableSpace 𝓥 := borel _
  let : BorelSpace 𝓥 := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ 𝓥) := borel _
  let : BorelSpace (StrongDual ℝ 𝓥) := ⟨rfl⟩
  have hload := reactionForcingLp_apply_ae hΩopen hΩbounded hf u
  have hdual : ∀ᵐ t ∂ν,
      d t + vectorDirichletForm (u t) = reactionForcingLp hΩopen hΩbounded hf u t := by
    filter_upwards [heq, hload] with t ht hlt
    apply ContinuousLinearMap.ext
    intro v
    rw [add_apply, hlt, reactionLp_dual_apply,
      vectorDirichletForm_eq_integral]
    exact ht v
  have hu := hd.integrated_solution_of_ae_equation hab hw hwae
    (fun _ ↦ aestronglyMeasurable_const) 1
    (Filter.Eventually.of_forall fun _ ↦ norm_vectorDirichletForm_le) hdual
  rw [hwa] at hu
  exact hu.congr_forcing_ae hload

/-- Existence and uniqueness for finite-component reaction-diffusion in weak form, on any
bounded open set, for any globally Lipschitz reaction, finite interval, and `L²` initial datum.
The weak derivative is in `L²(H⁻¹)`, the pivot representative is continuous on `[a, b]`, and
the equation uses the full matrix gradient. Uniqueness holds among all states with these
properties. -/
theorem existsUnique_weakSolution
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hab : a < b) (hf : LipschitzWith L f) (g : Pivot) :
    ∃! u : Lp 𝓥 2 ν,
      ∃ d : Lp (StrongDual ℝ 𝓥) 2 ν, ∃ w : ℝ → Pivot,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d ∧
        ContinuousOn w (Icc a b) ∧
        w =ᵐ[ν] (fun t ↦ toLp (u t)) ∧ w a = g ∧
        ∀ᵐ t ∂ν, ∀ v : 𝓥,
          d t v + (∫ x, ∑ i : Fin m, ∑ j : Fin n,
            ∇ (u t) x (finProdFinEquiv (i, j)) *
              ∇ v x (finProdFinEquiv (i, j)) ∂μ) =
            ∫ x, inner ℝ (f (toLp (u t) x))
              (toLp v x) ∂μ := by
  obtain ⟨u, hu, hunique⟩ := existsUnique_integrated hΩopen hΩbounded hab hf g
  obtain ⟨d, E, hd, hEa, heq⟩ := exists_evolution_of_integrated hΩopen hΩbounded hf hu
  refine ⟨u, ⟨d, E.representative, hd, ?_, ?_, hEa, heq⟩, ?_⟩
  · simpa only [uIcc_of_le hab.le] using E.continuousOn
  · exact E.ae_eq_inclusion.filter_mono (ae_mono (volume.restrict_mono_set (by
      rw [uIcc_of_le hab.le]
      exact Ioc_subset_Icc_self)))
  · rintro v ⟨dv, w, hdv, hw, hwae, hwa, hv⟩
    exact hunique v (integrated_of_weakEquation hΩopen hΩbounded hab hf hdv hw hwae hwa hv)

/-- Every `H¹₀(Ω; ℝ^m)` initial datum has a continuous pivot evolution, with its weak time
derivative and the full-gradient equation on the entire finite interval. -/
theorem exists_evolution
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hab : a < b) (hf : LipschitzWith L f) (g₀ : 𝓥) :
    ∃ u : Lp 𝓥 2 ν, ∃ d : Lp (StrongDual ℝ 𝓥) 2 ν,
      ∃ E : ContinuousPivotEvolutionOn (gelfandTriple hΩopen)
          (fun t ↦ u t) (fun t ↦ d t) a b,
        HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u d ∧
        E.representative a = toLp g₀ ∧
        ∀ᵐ t ∂ν, ∀ v : 𝓥,
          d t v + (∫ x, ∑ i : Fin m, ∑ j : Fin n,
            ∇ (u t) x (finProdFinEquiv (i, j)) *
              ∇ v x (finProdFinEquiv (i, j)) ∂μ) =
            ∫ x, inner ℝ (f (toLp (u t) x))
              (toLp v x) ∂μ := by
  obtain ⟨u, hu, _⟩ := existsUnique_integrated hΩopen hΩbounded hab hf (toLp g₀)
  obtain ⟨d, E, hd, hEa, heq⟩ := exists_evolution_of_integrated hΩopen hΩbounded hf hu
  exact ⟨u, d, E, hd, hEa, heq⟩

/-- Weak solutions with the same initial data have equal state and derivative classes, and their
continuous pivot representatives agree at every time of the closed interval. -/
theorem weakSolution_unique
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (hab : a < b) (hf : LipschitzWith L f)
    {u₁ u₂ : Lp 𝓥 2 ν} {d₁ d₂ : Lp (StrongDual ℝ 𝓥) 2 ν}
    {w₁ w₂ : ℝ → Pivot} {g : Pivot}
    (hd₁ : HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u₁ d₁)
    (hd₂ : HasGelfandWeakTimeDerivativeOn (gelfandTriple hΩopen) u₂ d₂)
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hw₂ : ContinuousOn w₂ (Icc a b))
    (hwae₁ : w₁ =ᵐ[ν] fun t ↦ toLp (u₁ t))
    (hwae₂ : w₂ =ᵐ[ν] fun t ↦ toLp (u₂ t))
    (hwa₁ : w₁ a = g) (hwa₂ : w₂ a = g)
    (heq₁ : ∀ᵐ t ∂ν, ∀ v : 𝓥,
      d₁ t v + (∫ x, ∑ i : Fin m, ∑ j : Fin n,
        ∇ (u₁ t) x (finProdFinEquiv (i, j)) *
          ∇ v x (finProdFinEquiv (i, j)) ∂μ) =
        ∫ x, inner ℝ (f (toLp (u₁ t) x)) (toLp v x) ∂μ)
    (heq₂ : ∀ᵐ t ∂ν, ∀ v : 𝓥,
      d₂ t v + (∫ x, ∑ i : Fin m, ∑ j : Fin n,
        ∇ (u₂ t) x (finProdFinEquiv (i, j)) *
          ∇ v x (finProdFinEquiv (i, j)) ∂μ) =
        ∫ x, inner ℝ (f (toLp (u₂ t) x)) (toLp v x) ∂μ) :
    u₁ = u₂ ∧ d₁ = d₂ ∧ EqOn w₁ w₂ (Icc a b) := by
  have hu₁ := integrated_of_weakEquation hΩopen hΩbounded hab hf hd₁ hw₁ hwae₁ hwa₁ heq₁
  have hu₂ := integrated_of_weakEquation hΩopen hΩbounded hab hf hd₂ hw₂ hwae₂ hwa₂ heq₂
  have hu : u₁ = u₂ := (existsUnique_integrated hΩopen hΩbounded hab hf g).unique hu₁ hu₂
  subst u₂
  refine ⟨rfl, hd₁.eq hd₂, ?_⟩
  apply Measure.eqOn_Icc_of_ae_eq volume hab.ne _ hw₁ hw₂
  rw [← Measure.restrict_congr_set
    (Ioc_ae_eq_Icc : Ioc a b =ᵐ[(volume : Measure ℝ)] Icc a b)]
  exact hwae₁.trans hwae₂.symm

end ReactionDiffusion
