/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Convexity

/-!
# Strict convexity of integral densities on linear fields

Two minimizing states with finite signed energy have the same distinguished
field if joint convexity is strict whenever that field differs. A second
linear field may enter the density without being strictly controlled.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace PDE.Analysis

variable {X U E G : Type*} [MeasurableSpace X] {μ : Measure X}
  [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ℝ≥0∞}

/-- A linear field commutes almost everywhere with affine averages
of states, despite the independent representative choices in `Lp`. -/
theorem coeFn_linearMap_smul_add (T : U →ₗ[ℝ] Lp E p μ) (a b : ℝ) (u v : U) :
    T (a • u + b • v) =ᵐ[μ] fun x ↦ a • T u x + b • T v x := by
  rw [map_add, map_smul, map_smul]
  filter_upwards [Lp.coeFn_add (a • T u) (b • T v),
    Lp.coeFn_smul a (T u), Lp.coeFn_smul b (T v)] with x ha hu hv
  simp only [ha, Pi.add_apply, hu, hv, Pi.smul_apply]

/-- Finite minimizers of a jointly convex signed integral have equal
distinguished fields when midpoint convexity is strict for unequal fields.
No integrability of derivatives of the density is assumed. -/
theorem lp_eq_of_isMinOn_lowerBoundedIntegral
    (B : U →ₗ[ℝ] Lp E p μ) (D : U →ₗ[ℝ] Lp G p μ)
    {L : X → E × G → ℝ} {b : X → ℝ} {A : Set U}
    (hA : Convex ℝ A)
    (hL : ∀ w ∈ A, AEStronglyMeasurable (fun x ↦ L x (B w x, D w x)) μ)
    (hb : Integrable b μ)
    (hlower : ∀ w ∈ A, ∀ᵐ x ∂μ, -b x ≤ L x (B w x, D w x))
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (L x))
    (hstrict : ∀ᵐ x ∂μ, ∀ z w : E × G, z.2 ≠ w.2 →
      L x ((2 : ℝ)⁻¹ • z + (2 : ℝ)⁻¹ • w) < (L x z + L x w) / 2)
    {u v : U} (hu : u ∈ A) (hv : v ∈ A)
    (hminu : IsMinOn (fun w ↦ lowerBoundedIntegral μ
      (fun x ↦ L x (B w x, D w x))) A u)
    (hminv : IsMinOn (fun w ↦ lowerBoundedIntegral μ
      (fun x ↦ L x (B w x, D w x))) A v)
    (hfinite : lowerBoundedIntegral μ (fun x ↦ L x (B u x, D u x)) ≠ ⊤) :
    D u = D v := by
  let w := (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v
  have hw : w ∈ A := hA hu hv (by norm_num) (by norm_num) (by norm_num)
  have hB := coeFn_linearMap_smul_add B (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ u v
  have hD := coeFn_linearMap_smul_add D (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ u v
  have hmid : ∀ᵐ x ∂μ,
      L x (B w x, D w x) ≤ (L x (B u x, D u x) + L x (B v x, D v x)) / 2 := by
    filter_upwards [hB, hD, hconvex] with x hxB hxD hx
    have hc := hx.2 (mem_univ (B u x, D u x)) (mem_univ (B v x, D v x))
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
    change B w x = _ at hxB
    change D w x = _ at hxD
    rw [hxB, hxD]
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,
      div_eq_mul_inv, add_mul, mul_comm (2 : ℝ)⁻¹] using hc
  have heq := ae_eq_average_of_lowerBoundedIntegral_le
    (hL u hu) (hL v hv) (hL w hw) hb (hlower u hu) (hlower v hv) (hlower w hw)
    hfinite (le_antisymm (hminu hv) (hminv hu)) (hminu hw) hmid
  apply Lp.ext
  filter_upwards [heq, hB, hD, hstrict] with x hx hxB hxD hs
  by_contra hne
  have hlt := hs (B u x, D u x) (B v x, D v x) hne
  change B w x = _ at hxB
  change D w x = _ at hxD
  rw [hxB, hxD] at hx
  exact (ne_of_lt hlt) hx

end PDE.Analysis
