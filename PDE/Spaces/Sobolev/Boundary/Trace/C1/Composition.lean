/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Order
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.AbsoluteValue
public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Vector
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Boundary values under vector composition

Two Sobolev maps with the same boundary values retain the same boundary values
after smooth composition with bounded derivative. The proof uses the mean
value estimate and trace order: the change in each output is dominated by a
sum of absolute values of zero-boundary input differences.

This argument applies to `H¹` fields and their closure-defined `H¹₀`
subspace. It needs neither continuous representatives nor smooth variations.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary Approximation.UpToBoundary
open FiniteProductComposition
open scoped ENNReal NNReal Sobolev

variable {n m l : ℕ} {Ω : Set ℝ^(n + 1)} [H : C1ExtensionAtlas (n + 1) Ω]

/-- A scalar `H¹` function bounded by the norm of a finite zero-boundary family
has zero boundary values itself. -/
theorem mem_H10_of_abs_le_norm_values (P : InwardPartition Ω) (C : ℝ≥0)
    (V : Fin m → H¹₀(Ω)) {W : H¹(Ω)}
    (hW : ∀ᵐ x ∂domainMeasure (n + 1) Ω,
      |baseRepresentative W x| ≤ C * ‖values (fun j ↦ (V j : H¹(Ω))) x‖) :
    W ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule := by
  let A : Fin m → H¹(Ω) :=
    fun j ↦ (absoluteValueH10 H.isOpen (V j) : H¹(Ω))
  have hA : (C : ℝ) • ∑ j, A j ∈
      (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule :=
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ ↦
      (absoluteValueH10 H.isOpen (V j)).property)
  apply mem_H10_of_abs_le_ae P hA
  have habs := ae_all_iff.mpr fun j ↦ absoluteValueH10_base_ae H.isOpen (V j)
  filter_upwards [hW, baseRepresentative_smul_ae (C : ℝ) (∑ j, A j),
    baseRepresentative_sum_ae A, habs] with x hx hs hsum ha
  rw [hs, hsum]
  calc
    |baseRepresentative W x|
        ≤ C * ‖values (fun j ↦ (V j : H¹(Ω))) x‖ := hx
    _ ≤ C * ∑ j, |baseRepresentative (V j : H¹(Ω)) x| := by
      apply mul_le_mul_of_nonneg_left _ C.property
      simpa [values, baseRepresentative, Real.norm_eq_abs] using
        PiLp.norm_le_sum_norm (values (fun j ↦ (V j : H¹(Ω))) x)
    _ = (C : ℝ) • ∑ j, baseRepresentative (A j) x := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (ha j).symm

/-- Smooth vector composition with bounded derivative preserves equality of
boundary values, expressed in the zero-boundary space. -/
theorem vectorComposition_sub_mem_H10_of_sub_mem_H10 (P : InwardPartition Ω)
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    {G : ℝ^m → ℝ^l} {C : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (U V : Fin m → H¹(Ω))
    (hUV : ∀ j, U j - V j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule)
    (j : Fin l) :
    vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound U j -
      vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound V j ∈
        (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule := by
  let Z : Fin m → H¹₀(Ω) := fun i ↦ ⟨U i - V i, hUV i⟩
  have hLip : LipschitzWith C G :=
    lipschitzWith_of_nnnorm_fderiv_le (hG.differentiable one_ne_zero)
      (fun z ↦ hbound z)
  apply mem_H10_of_abs_le_norm_values P C Z
  let GU := vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound U
  let GV := vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound V
  have hsub := ae_all_iff.mpr fun i ↦ baseRepresentative_sub_ae (U i) (V i)
  filter_upwards [baseRepresentative_sub_ae (GU j) (GV j),
    vectorCompositionOnOfExtension_values_ae H.isOpen E (by norm_num) hG hbound U,
    vectorCompositionOnOfExtension_values_ae H.isOpen E (by norm_num) hG hbound V,
    hsub] with x hx hu hv hz
  have hZ : values (fun i ↦ (Z i : H¹(Ω))) x =
      values U x - values V x := by
    ext i
    exact hz i
  rw [hx, hZ]
  have huj := congrArg (fun z : ℝ^l ↦ z j) hu
  have hvj := congrArg (fun z : ℝ^l ↦ z j) hv
  change baseRepresentative (GU j) x = G (values U x) j at huj
  change baseRepresentative (GV j) x = G (values V x) j at hvj
  rw [huj, hvj]
  calc
    |G (values U x) j - G (values V x) j|
        ≤ ‖G (values U x) - G (values V x)‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le (G (values U x) - G (values V x)) j
    _ ≤ C * ‖values U x - values V x‖ := hLip.norm_sub_le _ _

end SobolevSpace.Trace.C1
