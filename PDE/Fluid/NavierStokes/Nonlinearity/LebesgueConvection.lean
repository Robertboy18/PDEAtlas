/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.SobolevTransport
public import PDE.Spaces.Sobolev.Calculus.Product.Holder
public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFields
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Convection of fields in `W^{k,4}` into vector `H^k`

For `A : Fin n → W^{k,4}(ℝ^n)` and `V : Fin n → W^{k+1,4}(ℝ^n)`, the convection
`((A·∇)V)ⱼ = ∑ᵢ Aᵢ ∂ᵢVⱼ` lies in vector `H^k(ℝ^n)` by the `L⁴`-by-`L⁴` product `l4Product`.
It is a bounded bilinear map of norm at most `n² holderProductBound n k`, and so is its Leray
projection `-Π((A·∇)V)`, whose values are solenoidal. Fields that decay like `|x|⁻¹` at
infinity, such as self-similar profiles in three dimensions, lie in `L⁴` but not in `L²`, which
is why the products are taken in `L⁴`.

## Main results

* `lebesgueConvection`, with `lebesgueConvection_apply`, `lebesgueConvection_base_ae` and
  `norm_lebesgueConvection_le`.
* `projectedLebesgueConvection`, with `norm_projectedLebesgueConvection_le` and
  `projectedLebesgueConvection_base_mem_solenoidal`.
* `lebesgueConvection_vectorWkpOfContDiff_base_ae`: for smooth fields with derivatives in `L⁴`,
  the classical expression of the convection.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open scoped ENNReal Sobolev

namespace NavierStokes.SobolevConvection

variable {n : ℕ}

/-- Component `j` of the convection `∑ᵢ Aᵢ ∂ᵢVⱼ` of fields in `W^{k,4}(ℝ^n)` and
`W^{k+1,4}(ℝ^n)`. -/
def scalarLebesgueConvection (k : ℕ) (j : Fin n) :
    (Fin n → W^{k,4}(ℝ^n)) →L[ℝ] (Fin n → W^{k + 1,4}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n) :=
  ∑ i : Fin n, (l4Product k).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ W^{k,4}(ℝ^n)) i)
    ((partialDerivCLM i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ W^{k + 1,4}(ℝ^n)) j))

/-- The convection `(A·∇)V` of fields in `W^{k,4}(ℝ^n)` and `W^{k+1,4}(ℝ^n)`, with values in
vector `H^k(ℝ^n)`. -/
def lebesgueConvection (k : ℕ) :
    (Fin n → W^{k,4}(ℝ^n)) →L[ℝ] (Fin n → W^{k + 1,4}(ℝ^n)) →L[ℝ] VectorH n k :=
  assembleComponents (E := Fin n → W^{k,4}(ℝ^n)) (F := Fin n → W^{k + 1,4}(ℝ^n)) k
    (scalarLebesgueConvection k)

/-- The components of the convection are `∑ᵢ Aᵢ ∂ᵢVⱼ`. -/
theorem lebesgueConvection_apply (k : ℕ) (A : Fin n → W^{k,4}(ℝ^n))
    (V : Fin n → W^{k + 1,4}(ℝ^n)) (j : Fin n) :
    lebesgueConvection k A V j = ∑ i : Fin n, l4Product k (A i) (partialDerivCLM i (V j)) := by
  simp [lebesgueConvection, scalarLebesgueConvection, sum_apply]

/-- The base representative of each component is `∑ᵢ Aᵢ ∂ᵢVⱼ` almost everywhere. -/
theorem lebesgueConvection_base_ae (k : ℕ) (A : Fin n → W^{k,4}(ℝ^n))
    (V : Fin n → W^{k + 1,4}(ℝ^n)) (j : Fin n) :
    baseRepresentative (lebesgueConvection k A V j) =ᵐ[volume] fun x ↦ ∑ i : Fin n,
      baseRepresentative (A i) x * baseRepresentative (partialDerivCLM i (V j)) x := by
  rw [lebesgueConvection_apply]
  have hs := baseRepresentative_sum_ae (fun i : Fin n ↦
    l4Product k (A i) (partialDerivCLM i (V j)))
  simp only [domainMeasure, Measure.restrict_univ] at hs
  filter_upwards [hs, ae_all_iff.mpr (fun i : Fin n ↦
    l4Product_base_ae (A i) (partialDerivCLM i (V j)))] with x hsum hprod
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ ↦ hprod i

/-- The bound `‖(A·∇)V‖_{H^k} ≤ n² holderProductBound n k ‖A‖_{W^{k,4}} ‖V‖_{W^{k+1,4}}`. -/
theorem norm_lebesgueConvection_le (k : ℕ) (A : Fin n → W^{k,4}(ℝ^n))
    (V : Fin n → W^{k + 1,4}(ℝ^n)) :
    ‖lebesgueConvection k A V‖ ≤ (n : ℝ) ^ 2 * holderProductBound n k * ‖A‖ * ‖V‖ := by
  have hC := holderProductBound_nonneg n k
  apply (PiLp.norm_le_sum_norm _).trans
  calc
    _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, holderProductBound n k * ‖A‖ * ‖V‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [lebesgueConvection_apply]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_l4Product_le _ _).trans
      gcongr
      · exact norm_le_pi_norm A i
      · exact (norm_partialDeriv_le i (V j)).trans (norm_le_pi_norm V j)
    _ = _ := by simp; ring

/-- The Leray projection `-Π((A·∇)V)` of the convection, as a bounded bilinear map. -/
def projectedLebesgueConvection (k : ℕ) :
    (Fin n → W^{k,4}(ℝ^n)) →L[ℝ] (Fin n → W^{k + 1,4}(ℝ^n)) →L[ℝ] VectorH n k :=
  -((ContinuousLinearMap.compL ℝ (Fin n → W^{k + 1,4}(ℝ^n)) (VectorH n k) (VectorH n k)
    (leraySobolev n k)).comp (lebesgueConvection k))

/-- The projected convection is minus the Leray projection of the convection. -/
theorem projectedLebesgueConvection_apply (k : ℕ) (A : Fin n → W^{k,4}(ℝ^n))
    (V : Fin n → W^{k + 1,4}(ℝ^n)) :
    projectedLebesgueConvection k A V = -leraySobolev n k (lebesgueConvection k A V) :=
  rfl

/-- The projected convection has the same bound as the convection. -/
theorem norm_projectedLebesgueConvection_le (k : ℕ) (A : Fin n → W^{k,4}(ℝ^n))
    (V : Fin n → W^{k + 1,4}(ℝ^n)) :
    ‖projectedLebesgueConvection k A V‖ ≤
      (n : ℝ) ^ 2 * holderProductBound n k * ‖A‖ * ‖V‖ := by
  rw [projectedLebesgueConvection_apply, norm_neg]
  exact (norm_leraySobolev_le _).trans (norm_lebesgueConvection_le k A V)

/-- The projected convection takes values in solenoidal fields. -/
theorem projectedLebesgueConvection_base_mem_solenoidal (k : ℕ) (A : Fin n → W^{k,4}(ℝ^n))
    (V : Fin n → W^{k + 1,4}(ℝ^n)) :
    l2SobolevRow (baseIndex n k) (projectedLebesgueConvection k A V) ∈ l2Solenoidal n := by
  rw [projectedLebesgueConvection_apply, map_neg, l2SobolevRow_leraySobolev]
  exact Submodule.neg_mem _ (lerayProjection_mem n _)

/-- For smooth fields with derivatives in `L⁴`, the components of the convection are
`∑ᵢ Aᵢ (∂ᵢV)ⱼ` almost everywhere, with the classical values and partial derivatives. -/
theorem lebesgueConvection_vectorWkpOfContDiff_base_ae (k : ℕ) (A V : ℝ^n → ℝ^n)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hAmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m A) 4 volume)
    (hVmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m V) 4 volume) (j : Fin n) :
    baseRepresentative (lebesgueConvection k (vectorWkpOfContDiff A hA hAmem)
        (vectorWkpOfContDiff V hV hVmem) j) =ᵐ[volume]
      fun x ↦ ∑ i : Fin n, A x i * fderiv ℝ V x (EuclideanSpace.single i 1) j := by
  filter_upwards [lebesgueConvection_base_ae k _ _ j,
    ae_all_iff.mpr (fun i ↦ baseRepresentative_vectorWkpOfContDiff A hA hAmem i),
    ae_all_iff.mpr (fun i ↦ baseRepresentative_partialDerivCLM_vectorWkpOfContDiff V hV hVmem j i)]
    with x hx hA0 hV1
  rw [hx]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hA0 i, hV1 i]

end NavierStokes.SobolevConvection
