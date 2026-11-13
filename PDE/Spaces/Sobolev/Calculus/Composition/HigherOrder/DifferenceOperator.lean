/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.DifferenceReaction
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteOperator

/-!
# Finite differences of Sobolev composition

We write a reaction difference as its averaged derivative applied to the difference
of the inputs. The direction can be normalized independently. Both the Lipschitz
estimate and the derivative remainder use this same factorization.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Topology

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

/-- The averaged derivative as a reaction on three finite families. -/
def differenceReaction (f : (ι → ℝ) → ℝ) (y : Fin 3 × ι → ℝ) : ℝ :=
  averagedDerivative f (fun i ↦ y (0, i)) (fun i ↦ y (1, i)) (fun i ↦ y (2, i))

/-- A smooth reaction has a smooth averaged derivative reaction. -/
theorem contDiff_differenceReaction {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (differenceReaction f) :=
  (contDiff_averagedDerivative hf).comp (contDiff_pi.mpr fun j ↦
    contDiff_pi.mpr fun i ↦ contDiff_apply ℝ (fun _ ↦ ℝ) (j, i))

/-- Factor a Sobolev reaction difference through its averaged derivative,
with an arbitrary nonzero normalization. -/
theorem finiteComposition_sub_eq_smul (hk : (n : ℝ) < 2 * (k : ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (U V : ι → W^{k,2}(ℝ^n)) {c : ℝ} (hc : c ≠ 0) :
    finiteComposition hk hf hf0 U - finiteComposition hk hf hf0 V =
      c • finiteComposition hk (contDiff_differenceReaction hf)
        (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0)
        (fun ji ↦ ![U, V, c⁻¹ • (U - V)] ji.1 ji.2) := by
  let Z : Fin 3 × ι → W^{k,2}(ℝ^n) := fun ji ↦ ![U, V, c⁻¹ • (U - V)] ji.1 ji.2
  let A := finiteComposition hk hf hf0 U
  let B := finiteComposition hk hf hf0 V
  let D := finiteComposition hk (contDiff_differenceReaction hf)
    (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0) Z
  have hcoord (i : ι) : ∀ᵐ x ∂volume,
      baseRepresentative (c⁻¹ • (U i - V i)) x =
        c⁻¹ * (baseRepresentative (U i) x - baseRepresentative (V i) x) := by
    have h := (baseRepresentative_smul_ae c⁻¹ (U i - V i))
    have h' := baseRepresentative_sub_ae (U i) (V i)
    simp only [domainMeasure, Measure.restrict_univ] at h h'
    filter_upwards [h, h'] with x hx hy
    simp only [hx, hy, smul_eq_mul]
  have hZ : ∀ᵐ x ∂volume,
      (fun ji ↦ baseRepresentative (Z ji) x) =
        (fun ji ↦ ![(fun i ↦ baseRepresentative (U i) x),
          (fun i ↦ baseRepresentative (V i) x),
          c⁻¹ • ((fun i ↦ baseRepresentative (U i) x) -
            (fun i ↦ baseRepresentative (V i) x))] ji.1 ji.2) := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    funext ⟨j, i⟩
    fin_cases j
    · rfl
    · rfl
    · exact hx i
  have hsub := baseRepresentative_sub_ae A B
  have hsmul := baseRepresentative_smul_ae c D
  simp only [domainMeasure, Measure.restrict_univ] at hsub hsmul
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (A - B) =ᵐ[domainMeasure n univ] baseRepresentative (c • D)
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hsub, hsmul, finiteComposition_ae hk hf hf0 U,
    finiteComposition_ae hk hf hf0 V,
    finiteComposition_ae hk (contDiff_differenceReaction hf)
      (show differenceReaction f 0 = 0 from averagedDerivative_zero f 0 0) Z, hZ]
    with x hab hcD ha hb hD hz
  rw [hab, hcD, ha, hb, hD, hz]
  change _ = c • averagedDerivative f (fun i ↦ baseRepresentative (U i) x)
    (fun i ↦ baseRepresentative (V i) x)
    (c⁻¹ • ((fun i ↦ baseRepresentative (U i) x) -
      (fun i ↦ baseRepresentative (V i) x)))
  rw [averagedDerivative_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    averagedDerivative_sub hf]

end SobolevSpace.Composition
