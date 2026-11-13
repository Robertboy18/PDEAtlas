/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Composition
public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Sphere

/-!
# Admissible variations of sphere-valued Sobolev maps

For a unit-length map `U` and a bounded zero-boundary variation `V`, the field
`(U + t V) / |U + t V|` keeps both the sphere constraint and the boundary
values when `t` is small. We construct it by applying the Sobolev chain rule
to a smooth map that equals normalization on an annulus around the sphere.

The boundary argument applies for every parameter: equal traces stay equal
under smooth composition. Smallness is needed only to keep the values in the
annulus where the cutoff agrees with normalization. These are the variations (35) in the proof
of Evans, §8.4.3, Theorem 5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.3, proof of Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition
open scoped ENNReal NNReal Topology Sobolev

variable {n m : ℕ} {Ω : Set ℝ^(n + 1)}
  [H : Boundary.C1ExtensionAtlas (n + 1) Ω]

/-- A cutoff of normalization fixes a unit-length Sobolev map. Equality holds
in the Sobolev space, so it also identifies the weak derivatives. -/
theorem vectorComposition_eq_self_of_norm_values_eq_one
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    {G : ℝ^m → ℝ^m} {C : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (heq : ∀ z, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 → G z = NormedSpace.normalize z)
    (U : Fin m → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1) :
    vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound U = U := by
  apply eq_of_values_ae_eq H.isOpen
  filter_upwards [vectorCompositionOnOfExtension_values_ae H.isOpen E
    (by norm_num) hG hbound U, hunit] with x hx hu
  rw [hx, heq _ (by norm_num [hu]) (by norm_num [hu])]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one hu

/-- Composing an affine zero-boundary variation with a cutoff of normalization
preserves the original boundary values for every parameter. -/
theorem normalizedVariation_sub_mem_H10
    (P : Approximation.UpToBoundary.InwardPartition Ω)
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    {G : ℝ^m → ℝ^m} {C : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (heq : ∀ z, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 → G z = NormedSpace.normalize z)
    (U : Fin m → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1)
    (V : Fin m → H¹₀(Ω)) (t : ℝ) (j : Fin m) :
    vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound
      (fun k ↦ U k + t • (V k : H¹(Ω))) j - U j ∈
        (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule := by
  have h := Trace.C1.vectorComposition_sub_mem_H10_of_sub_mem_H10 P E hG hbound
    (fun k ↦ U k + t • (V k : H¹(Ω))) U
    (fun k ↦ by simpa using (Submodule.smul_mem
      (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule t (V k).property)) j
  rw [vectorComposition_eq_self_of_norm_values_eq_one E hG hbound heq U hunit] at h
  exact h

private theorem norm_add_smul_mem_annulus {u v : ℝ^m} {t M : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ ≤ M) (ht : |t| * M < 1 / 2) :
    1 / 2 < ‖u + t • v‖ ∧ ‖u + t • v‖ < 2 := by
  have hw : ‖t • v‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hv (abs_nonneg t)).trans_lt ht
  have hlow : 1 ≤ ‖u + t • v‖ + ‖t • v‖ := by
    simpa [hu] using norm_sub_le (u + t • v) (t • v)
  have hupp := norm_add_le u (t • v)
  constructor <;> linarith

/-- The normalized variation has unit length whenever the uniform perturbation
is smaller than half the original radius. -/
theorem normalizedVariation_norm_values_eq_one_ae
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    {G : ℝ^m → ℝ^m} {C M : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (heq : ∀ z, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 → G z = NormedSpace.normalize z)
    (U V : Fin m → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1)
    (hV : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values V x‖ ≤ M)
    {t : ℝ} (ht : |t| * M < 1 / 2) :
    ∀ᵐ x ∂domainMeasure (n + 1) Ω,
      ‖values (vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound
        (fun k ↦ U k + t • V k)) x‖ = 1 := by
  filter_upwards [vectorCompositionOnOfExtension_values_ae H.isOpen E
    (by norm_num) hG hbound (fun k ↦ U k + t • V k),
    values_add_smul_ae U V t, hunit, hV] with x hx ha hu hv
  have hb := norm_add_smul_mem_annulus hu hv ht
  rw [hx, ha, heq _ hb.1.le hb.2.le]
  exact NormedSpace.norm_normalize_eq_one_iff.mpr (norm_pos_iff.mp (by linarith [hb.1]))

end PDE.CalculusOfVariations
