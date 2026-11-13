/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IteratedFDerivSymmetry
public import PDE.LinearAlgebra.Multilinear.Conormal
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Recovering the conormal part of a jet

Differentiate a vanishing jet along an actual local parametrization. Its next
derivative vanishes in every tangent direction; symmetry moves that direction
to any slot. The remaining tensor is a multiple of the conormal tensor.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology ContDiff

namespace PDE.Analysis

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- If a jet vanishes along a parametrized hypersurface, its next derivative
is determined by the value on a transverse tuple. The tangent space is the
range of the actual derivative of the parametrization. -/
theorem iteratedFDeriv_eq_prod_smul_of_tangent_trace
    {n : ℕ} {f : E → F} (hf : ContDiff ℝ ∞ f)
    {ψ : H → E} {z : H} {ψ' : H →L[ℝ] E} (hψ : HasFDerivAt ψ ψ' z)
    (ℓ : E →ₗ[ℝ] ℝ) (hrange : LinearMap.range ψ'.toLinearMap = LinearMap.ker ℓ)
    {e : E} (he : ℓ e = 1)
    (htrace : ∀ᶠ y in 𝓝 z, iteratedFDeriv ℝ n f (ψ y) = 0)
    (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f (ψ z) v =
      (∏ i, ℓ (v i)) • iteratedFDeriv ℝ (n + 1) f (ψ z) (fun _ ↦ e) := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    (hf.iteratedFDeriv_right
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (1 + n))).differentiable
      one_ne_zero
  have hchain := ((hd (ψ z)).hasFDerivAt.comp z hψ).fderiv
  have hzero :
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ n f (ψ y)) z = 0 := by
    have htrace' : (fun y ↦ iteratedFDeriv ℝ n f (ψ y)) =ᶠ[𝓝 z] (fun _ ↦ 0) :=
      htrace
    rw [htrace'.fderiv_eq]
    simp
  have hfirst (a : E) (ha : ℓ a = 0) (r : Fin n → E) :
      iteratedFDeriv ℝ (n + 1) f (ψ z) (Fin.cons a r) = 0 := by
    have hmem : a ∈ LinearMap.range ψ'.toLinearMap := by
      rw [hrange]
      exact ha
    obtain ⟨b, hb⟩ := hmem
    change ψ' b = a at hb
    have hbzero := congrArg (fun A : H →L[ℝ] E [×n]→L[ℝ] F ↦ A b r)
      (hchain.symm.trans hzero)
    simpa only [ContinuousLinearMap.comp_apply, zero_apply, hb, iteratedFDeriv_succ_apply_left,
      Fin.cons_zero, Fin.tail_cons] using hbzero
  apply (iteratedFDeriv ℝ (n + 1) f (ψ z)).toMultilinearMap
    |>.apply_eq_prod_smul_of_vanishes_on_ker ℓ he ?_ v
  intro w i hi
  change iteratedFDeriv ℝ (n + 1) f (ψ z) w = 0
  have hw : i.insertNth (w i) (i.removeNth w) = w := Fin.insertNth_self_removeNth i w
  rw [← hw, iteratedFDeriv_insertNth_eq_cons_of_smooth n f hf]
  exact hfirst _ hi _

end PDE.Analysis
