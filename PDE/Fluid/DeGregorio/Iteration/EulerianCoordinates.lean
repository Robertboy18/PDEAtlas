/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Characteristics
import Mathlib.Analysis.ODE.ExistUnique
import CAS.ExactTactic

/-!
# Eulerian coordinates for the bounded H² iteration class

Backward characteristic construction makes every spatial flow map surjective.
Grönwall applied after time reversal gives a uniform Lipschitz bound for its
inverse. The forward flow and its inverse are jointly continuous on the same
prescribed time interval.

The input is a curve in the complete bounded weak-H² class; the flow and its
inverse are both constructed from it.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

private theorem reverse_flow_dist_le
    {b X : ℝ → ℝ → ℝ} {K : NNReal} {T : ℝ}
    (hLip : ∀ t, LipschitzWith K (fun x ↦ b x t))
    (hX : ∀ x, Continuous (X x)) (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T → HasDerivAt (X x) (b (X x t) t) t)
    (x y t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    dist x y ≤ dist (X x t) (X y t) * Real.exp ((K : ℝ) * t) := by
  have hrev (z s : ℝ) (hs : s ∈ Ico (-t) 0) :
      HasDerivAt (fun r ↦ X z (-r)) (-b (X z (-s)) (-s)) s := by
    have hs' : -s ∈ Icc (0 : ℝ) T := by
      constructor <;> linarith [hs.1, hs.2, ht.2]
    simpa only [Function.comp_def, mul_neg_one] using (hX' z (-s) hs').comp s
      (show HasDerivAt (fun r : ℝ ↦ -r) (-1) s by cas)
  have h := dist_le_of_trajectories_ODE
    (v := fun s z ↦ -b z (-s)) (fun s ↦ (hLip (-s)).neg)
    ((hX x).comp continuous_neg).continuousOn
    (fun s hs ↦ (hrev x s hs).hasDerivWithinAt)
    ((hX y).comp continuous_neg).continuousOn
    (fun s hs ↦ (hrev y s hs).hasDerivWithinAt)
    (δ := dist (X x t) (X y t))
    (by simp only [Function.comp_apply, neg_neg]; exact le_rfl)
    0 ⟨neg_nonpos.mpr ht.1, le_rfl⟩
  simpa only [Function.comp_apply, neg_zero, hX₀, zero_sub, neg_neg] using h

/-- Every bounded weak-H² input curve has forward and inverse Eulerian
coordinates on the whole prescribed interval. The inverse is jointly
continuous and has the uniform spatial Lipschitz constant `exp (2 B T)`.
Both maps are constructed from the normalized Hilbert velocity. -/
theorem exists_hkCurve_hilbert_eulerian_coordinates
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) :
    ∃ X Y : ℝ → ℝ → ℝ,
      (∀ x, X x 0 = x) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t) ∧
      Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2) ∧
      Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ Y p.1 p.2) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T → Y (X x t) t = x) ∧
      (∀ y t, t ∈ Icc (0 : ℝ) T → X (Y y t) t = y) ∧
      (∀ t, t ∈ Icc (0 : ℝ) T →
        LipschitzWith ⟨Real.exp (2 * (B : ℝ) * T), (Real.exp_pos _).le⟩
          (fun y ↦ Y y t)) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        |X x t| ≤ |x| * Real.exp (2 * (B : ℝ) * t)) := by
  obtain ⟨X, hX, hX₀, hX', _hdist, hbound, hcont, _hunique⟩ :=
    exists_hkCurve_hilbert_flow hT f
  let K : NNReal := ⟨Real.exp (2 * (B : ℝ) * T), (Real.exp_pos _).le⟩
  have hLip := lipschitzWith_hkCurveHilbertVelocity hT f
  have hanti (t : Icc (0 : ℝ) T) : AntilipschitzWith K (fun x ↦ X x t) := by
    refine .of_le_mul_dist fun x y ↦ ?_
    have h := reverse_flow_dist_le hLip hX hX₀ hX' x y t t.property
    simp only [NNReal.coe_mul, NNReal.coe_ofNat] at h
    exact h.trans <| (mul_comm _ _).trans_le <|
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by gcongr; exact t.property.2)) dist_nonneg
  have hsurj (t : Icc (0 : ℝ) T) : Function.Surjective (fun x ↦ X x t) := by
    intro y
    obtain ⟨q, hq, hqₜ, hq'⟩ := exists_backward_characteristic_Icc t.property.1
      (hkCurveHilbertVelocity hT f) (continuous_hkCurveHilbertVelocity hT f)
      (2 * B) (fun s _ ↦ hLip s) y
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right t.property.2
    have heq := ODE_solution_unique_of_mem_Icc_right
      (v := fun s x ↦ hkCurveHilbertVelocity hT f x s) (s := fun _ ↦ univ)
      (fun s _ ↦ (hLip s).lipschitzOnWith) hq.continuousOn
      (fun s hs ↦ (hq' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (hX (q 0)).continuousOn
      (fun s hs ↦ (hX' (q 0) s (hsub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (hX₀ (q 0)).symm
    exact ⟨q 0, (heq ⟨t.property.1, le_rfl⟩).symm.trans hqₜ⟩
  let e (t : Icc (0 : ℝ) T) : ℝ ≃ₜ ℝ :=
    ((hanti t).isEmbedding
      (hcont.comp (continuous_id.prodMk continuous_const))).toHomeomorphOfSurjective
        (hsurj t)
  have he (t : Icc (0 : ℝ) T) (x : ℝ) : e t x = X x t := rfl
  have hinvLip (t : Icc (0 : ℝ) T) : LipschitzWith K (e t).symm :=
    .of_dist_le_mul fun x y ↦ by
      simpa only [← he, Homeomorph.apply_symm_apply] using
        (hanti t).le_mul_dist ((e t).symm x) ((e t).symm y)
  have hinvCont : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ (e p.2).symm p.1) := by
    refine continuous_prod_of_continuous_lipschitzWith _ K (fun y ↦ continuous_iff_continuousAt.2
      fun t₀ ↦ tendsto_iff_dist_tendsto_zero.2 ?_) hinvLip
    have hmajor (t : Icc (0 : ℝ) T) :
        dist ((e t).symm y) ((e t₀).symm y) ≤ (K : ℝ) * dist y (X ((e t₀).symm y) t) := by
      simpa only [← he, Homeomorph.apply_symm_apply] using
        (hanti t).le_mul_dist ((e t).symm y) ((e t₀).symm y)
    have hlim : Tendsto
        (fun t : Icc (0 : ℝ) T ↦ (K : ℝ) * dist y (X ((e t₀).symm y) t))
        (𝓝 t₀) (𝓝 ((K : ℝ) * dist y (X ((e t₀).symm y) t₀))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.dist
        (((hX ((e t₀).symm y)).comp continuous_subtype_val).tendsto t₀))
    exact squeeze_zero (fun _ ↦ dist_nonneg) hmajor
      (by simpa only [← he, Homeomorph.apply_symm_apply, dist_self, mul_zero] using hlim)
  let Y : ℝ → ℝ → ℝ := fun y t ↦ (e (projIcc 0 T hT t)).symm y
  have hY (y : ℝ) (t : Icc (0 : ℝ) T) : Y y t = (e t).symm y := by
    simp only [Y, projIcc_val]
  refine ⟨X, Y, hX₀, hX', hcont, ?_, ?_, ?_, ?_, hbound⟩
  · simpa only [hY] using hinvCont
  · exact fun x t ht ↦ (hY (X x t) ⟨t, ht⟩).trans ((e ⟨t, ht⟩).symm_apply_apply x)
  · exact fun y t ht ↦ (congrArg (X · t) (hY y ⟨t, ht⟩)).trans ((e ⟨t, ht⟩).apply_symm_apply y)
  · exact fun t ht ↦ (funext fun y ↦ hY y ⟨t, ht⟩) ▸ hinvLip ⟨t, ht⟩

end DeGregorio.Iteration
