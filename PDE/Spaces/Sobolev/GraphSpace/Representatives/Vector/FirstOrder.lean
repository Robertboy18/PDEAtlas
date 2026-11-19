/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder

/-!
# Distributional representatives of finite Sobolev systems

The finite product and the vector distributional definition agree in
both directions. All matrix entries are weak partial derivatives of the
corresponding value coordinates, and any Lp fields satisfying these identities
give an element of the Sobolev graph product.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- Every entry of the assembled matrix is the corresponding distributional
derivative of the assembled value. -/
theorem hasWeakDerivativeOn_vectorWkpGradientCLM (u : Fin m → W^{1,p}(Ω))
    (i : Fin m) (j : Fin n) :
    HasWeakDerivativeOn Ω [j] (fun x ↦ vectorWkpValueCLM u x i)
      (fun x ↦ ∇ u x (finProdFinEquiv (i, j))) := by
  apply (hasWeakDerivativeOn_wkpGradientCLM (u i) j).congr_ae
  · exact (vectorWkpValueCLM_apply_ae u).mono fun _ hx ↦ (hx i).symm
  · exact (vectorWkpGradientCLM_apply_ae u).mono fun _ hx ↦ (hx i j).symm

/-- Vector values and a full matrix of distributional first derivatives in
`Lᵖ` determine a finite Sobolev system with precisely those fields.
No dimension, boundary, or auxiliary graph assumption is required. -/
theorem exists_vectorWkp_of_weakGradient
    (f : Lp (ℝ^m) p μ) (g : Lp (ℝ^(m * n)) p μ)
    (hweak : ∀ (i : Fin m) (j : Fin n),
      HasWeakDerivativeOn Ω [j] (fun x ↦ f x i)
        (fun x ↦ g x (finProdFinEquiv (i, j)))) :
    ∃ u : Fin m → W^{1,p}(Ω), (vectorWkpValueCLM u : ℝ^n → ℝ^m) =ᵐ[μ] f ∧
      (∇ u : ℝ^n → ℝ^(m * n)) =ᵐ[μ] g := by
  let row (i : Fin m) : ℝ^(m * n) →L[ℝ] ℝ^n :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j ↦ EuclideanSpace.proj (finProdFinEquiv (i, j)))
  have h (i : Fin m) : ∃ U : W^{1,p}(Ω),
      baseRepresentative U =ᵐ[μ] (fun x ↦ f x i) ∧
      (∇ U : ℝ^n → ℝ^n) =ᵐ[μ] (fun x ↦ row i (g x)) := by
    apply exists_of_weakGradient
    · exact (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (Lp.memLp f)
    · exact (row i).comp_memLp' (Lp.memLp g)
    · intro j
      exact hweak i j
  choose u hu using h
  have hvalues : ∀ᵐ x ∂μ, ∀ i, baseRepresentative (u i) x = f x i :=
    ae_all_iff.mpr fun i ↦ (hu i).1
  have hgradients : ∀ᵐ x ∂μ, ∀ i, ∇ (u i) x = row i (g x) :=
    ae_all_iff.mpr fun i ↦ (hu i).2
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [vectorWkpValueCLM_apply_ae u, hvalues] with x hx hy
    exact PiLp.ext fun i ↦ (hx i).trans (hy i)
  · filter_upwards [vectorWkpGradientCLM_apply_ae u, hgradients] with x hx hy
    apply PiLp.ext
    intro k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    exact (hx i j).trans (congrArg (fun v : ℝ^n ↦ v j) (hy i))

end SobolevSpace.GraphSpace
