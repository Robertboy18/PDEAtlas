/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.Vorticity
public import PDE.Elliptic.Regularity.Interior.Divergence.LocalRepresentatives

/-!
# Local first weak derivatives of Stokes vorticity

The ordinary vorticity equation has two L² force terms. The interior
divergence estimate and native representative gluing therefore supply locally
L² first weak derivatives of every vorticity component. This is the regularity
needed for pressure; it follows from the raw energy minimum.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Sobolev ENNReal Distributions

namespace IncompressibleFlow.Stokes

open SobolevSpace SobolevSpace.GraphSpace PDE.Elliptic.Interior

variable {n : ℕ} {Ω : Opens (ℝ^n)}

/-- All components of the L² vorticity of a raw minimizer have locally
L² weak first derivatives on the original open domain. -/
theorem exists_vorticity_weak_derivatives_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w) :
    ∃ g : Fin n → Fin n → Fin n → ℝ^n → ℝ,
      (∀ i j k, AEStronglyMeasurable (g i j k) (domainMeasure n Ω)) ∧
      (∀ i j k, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp (g i j k) 2 (domainMeasure n K)) ∧
      ∀ i j k, HasWeakDerivativeOn Ω [k]
        (vorticity u i j : ℝ^n → ℝ) (g i j k) := by
  let a (i : Fin n) : DerivLp n 2 Ω :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (domainMeasure n Ω) f
  have ha (i : Fin n) :
      Distribution.ofLp Ω 2 (a i) =
        Distribution.ofFun Ω (fun x ↦ f x i) volume ⊤ :=
    Distribution.ofFun_congr_ae ((EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL f)
  have hex (i j : Fin n) :
      ∃ g : Fin n → ℝ^n → ℝ,
        (∀ k, AEStronglyMeasurable (g k) (domainMeasure n Ω)) ∧
        (∀ k, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
          MemLp (g k) 2 (domainMeasure n K)) ∧
        ∀ k, HasWeakDerivativeOn Ω [k]
          (vorticity u i j : ℝ^n → ℝ) (g k) := by
    let F : Fin 2 → DerivLp n 2 Ω := ![a i, -a j]
    let v : Fin 2 → ℝ^n :=
      ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]
    apply exists_locally_memLp_weak_derivatives_of_distributional_laplacian_eq
      (vorticity u i j) F v
    change LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'(Ω, ℝ)
      (Distribution.ofLp Ω 2 (vorticity u i j)) =
        ∑ k : Fin 2, Distribution.lineDerivCLM (v k) (Distribution.ofLp Ω 2 (F k))
    have hvorticity := laplacian_vorticity_of_minimizes_energy f u hu hmin i j
    change LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'(Ω, ℝ)
      (Distribution.ofLp Ω 2 (vorticity u i j)) =
        Distribution.lineDerivCLM (EuclideanSpace.single j (1 : ℝ))
          (Distribution.ofFun Ω (fun x ↦ f x i) volume ⊤) -
        Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
          (Distribution.ofFun Ω (fun x ↦ f x j) volume ⊤) at hvorticity
    simpa [F, v, Fin.sum_univ_two, ha, sub_eq_add_neg] using hvorticity
  choose g hg hmem hweak using hex
  exact ⟨g, hg, hmem, hweak⟩

end IncompressibleFlow.Stokes
