/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.TensorProduct
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import PDE.Analysis.Integration.Primitive.CompactSupport
import PDE.DistributionTheory.TestFunction.Derivative.Commutation
import PDE.DistributionTheory.TestFunction.Slice

/-!
# Integrating out a coordinate of a test function

The integral of a smooth compact test in its first coordinate is a smooth
compact test in the remaining coordinates. Subtracting its tensor product
with a normalized one-dimensional test leaves a coordinate derivative of a
compact test, with support retained in the same open product.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace TestFunction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A coordinate integral of a smooth compact test is smooth. -/
theorem contDiff_integral_fst
    (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∫ t, φ (t, x)) := by
  obtain ⟨R, _, hR⟩ := φ.hasCompactSupport.isBounded.exists_pos_norm_lt
  have heq (x : E) : (∫ t, φ (t, x)) = ∫ t in -R..R, φ (t, x) := by
    symm
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro t ht
    have htnorm : |t| < R :=
      (show |t| ≤ ‖(t, x)‖ by simp [Prod.norm_def]).trans_lt
        (hR (t, x) (subset_tsupport φ ht))
    exact ⟨(abs_lt.mp htnorm).1, (abs_lt.mp htnorm).2.le⟩
  simp_rw [heq]
  exact PDE.Analysis.contDiff_intervalIntegral
    (φ.contDiff.comp (contDiff_snd.prodMk contDiff_fst)) (-R) R

/-- The support of a coordinate integral lies in the projected support. -/
theorem tsupport_integral_fst_subset
    (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) :
    tsupport (fun x ↦ ∫ t, φ (t, x)) ⊆ Prod.snd '' tsupport φ := by
  apply closure_minimal _ (φ.hasCompactSupport.image continuous_snd).isClosed
  intro x hx
  by_contra hnot
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards with t
  exact image_eq_zero_of_notMem_tsupport (fun ht ↦ hnot ⟨(t, x), ht, rfl⟩)

/-- Integrate out the first, real coordinate of a compact test. -/
def integralFst (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) :
    𝓓((⊤ : Opens E), ℝ) where
  toFun x := ∫ t, φ (t, x)
  contDiff' := contDiff_integral_fst φ
  hasCompactSupport' := (φ.hasCompactSupport.image continuous_snd).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_integral_fst_subset φ)
  tsupport_subset' := subset_univ _

/-- Evaluation of a coordinate integral. -/
@[simp]
theorem integralFst_apply (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) (x : E) :
    integralFst φ x = ∫ t, φ (t, x) :=
  rfl

/-- Integrating out a coordinate projects the support into the remaining coordinates. -/
theorem tsupport_integralFst_subset (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ)) :
    tsupport (integralFst φ) ⊆ Prod.snd '' tsupport φ :=
  tsupport_integral_fst_subset φ

/-- Subtracting a normalized tensor leaves a coordinate derivative, with support
inside the same open product as the original test. -/
theorem exists_lineDeriv_eq_sub_tensor_integralFst
    {a b : ℝ} {U : Set E} (ρ : 𝓓((⊤ : Opens ℝ), ℝ))
    (hρsupp : tsupport ρ ⊆ Ioo a b) (hρint : ∫ t, ρ t = 1)
    (φ : 𝓓((⊤ : Opens (ℝ × E)), ℝ))
    (hφsupp : tsupport φ ⊆ Ioo a b ×ˢ U) :
    ∃ ψ : 𝓓((⊤ : Opens (ℝ × E)), ℝ),
      tsupport ψ ⊆ Ioo a b ×ˢ U ∧
      lineDerivCLM ℝ (1, 0) ψ = φ - tensorProduct ρ (integralFst φ) := by
  let η := φ - tensorProduct ρ (integralFst φ)
  have hηsupp : tsupport η ⊆ Ioo a b ×ˢ U := by
    apply (tsupport_sub _ _).trans
    apply union_subset hφsupp
    apply (tsupport_tensorProduct_subset ρ (integralFst φ)).trans
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    obtain ⟨p, hp, heq⟩ := tsupport_integralFst_subset φ hx
    exact ⟨hρsupp ht, heq ▸ (hφsupp hp).2⟩
  have hzero (x : E) : ∫ t, η (t, x) = 0 := by
    change (∫ t, φ (t, x) - ρ t * integralFst φ x) = 0
    have hφint : Integrable (fun t ↦ φ (t, x)) :=
      (sliceLeft x φ).contDiff.continuous.integrable_of_hasCompactSupport
        (sliceLeft x φ).hasCompactSupport
    rw [integral_sub hφint
      ((ρ.contDiff.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport).mul_const
        (integralFst φ x)),
      integral_mul_const, hρint, one_mul, integralFst_apply, sub_self]
  obtain ⟨ψ, hψ, hcs, hsupp, hd⟩ :=
    PDE.Analysis.exists_compactSupport_partial_primitive η.contDiff
      η.hasCompactSupport hηsupp hzero
  refine ⟨⟨ψ, hψ, hcs, subset_univ _⟩, hsupp, ?_⟩
  ext p
  rw [lineDerivCLM_apply_eq_fderiv]
  exact hd p

end TestFunction
