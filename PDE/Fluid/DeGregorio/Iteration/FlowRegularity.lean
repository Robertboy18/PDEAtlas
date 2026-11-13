/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.FlowJacobian
public import PDE.Analysis.Calculus.PartialRegularity
import PDE.Representations.Similarity.Dynamic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Joint regularity of the common Hilbert flow

The positive spatial Jacobian is jointly continuous, since it is an
exponential interval integral of a continuous coefficient along the flow.
The time derivative is the continuous velocity. Continuous partial
derivatives therefore give joint C¹ regularity on the open time cylinder.

Spatial derivatives also exist at the two time endpoints, by
`hasDerivAt_hkCurve_hilbert_flow_space`. Joint regularity is stated on the open
cylinder `ℝ × (0, T)`.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The characteristic flow is jointly C¹ on the open cylinder `ℝ × (0, T)`. -/
theorem contDiffOn_one_hkCurve_hilbert_flow
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry c))
    (hbc : ∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x)
    (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t)
    (hX : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2)) :
    ContDiffOn ℝ 1 (Function.uncurry X) (univ ×ˢ Ioo (0 : ℝ) T) := by
  let Z : ℝ → ℝ → ℝ := fun x t ↦ X x (projIcc 0 T hT t)
  have hZ : Continuous (Function.uncurry Z) :=
    hX.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
  have hZX (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Z x t = X x t := by
    simp only [Z, projIcc_of_mem hT ht]
  let k : ℝ → ℝ → ℝ := fun x t ↦ c (Z x t) t
  have hk : Continuous (Function.uncurry k) := hc.comp (hZ.prodMk continuous_snd)
  let J : ℝ → ℝ → ℝ := fun x t ↦ Real.exp (∫ s in 0..t, k x s)
  have hJ : Continuous (Function.uncurry J) :=
    (intervalIntegral.continuous_parametric_primitive_of_continuous hk).rexp
  have hJX (x t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      J x t = Real.exp (∫ s in 0..t, c (X x s) s) := by
    apply congrArg Real.exp
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change c (Z x s) s = c (X x s) s
    rw [hZX x s ⟨hs.1, hs.2.trans ht.2⟩]
  let D₁ (p : ℝ × ℝ) := ContinuousLinearMap.toSpanSingleton ℝ (J p.1 p.2)
  let D₂ (p : ℝ × ℝ) :=
    ContinuousLinearMap.toSpanSingleton ℝ (hkCurveHilbertVelocity hT f (Z p.1 p.2) p.2)
  have hD₁ : Continuous D₁ := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hJ
  have hD₂ : Continuous D₂ := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
    ((continuous_hkCurveHilbertVelocity hT f).comp (hZ.prodMk continuous_snd))
  apply contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
    hD₁.continuousOn hD₂.continuousOn
  · intro p hp
    have h := hasDerivAt_hkCurve_hilbert_flow_space hT f hbc hX₀ hX' p.1 p.2
      (Ioo_subset_Icc_self hp.2)
    rw [← hJX p.1 p.2 (Ioo_subset_Icc_self hp.2)] at h
    exact h.hasFDerivAt
  · intro p hp
    have h := hX' p.1 p.2 (Ioo_subset_Icc_self hp.2)
    rw [← hZX p.1 p.2 (Ioo_subset_Icc_self hp.2)] at h
    exact h.hasFDerivAt

private def flowCoordinateDerivative (J v : ℝ) (hJ : J ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).skewProd
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 J hJ))
      (ContinuousLinearMap.toSpanSingleton ℝ v)).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ))

/-- The Eulerian inverse is jointly C¹ on the same open time
cylinder. The inverse function theorem uses the positive flow Jacobian. -/
theorem contDiffOn_one_hkCurve_inverse
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X Y : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry c))
    (hbc : ∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x)
    (hX₀ : ∀ x, X x 0 = x)
    (hX' : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t)
    (hX : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2))
    (hY : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ Y p.1 p.2))
    (hYX : ∀ x t, t ∈ Icc (0 : ℝ) T → Y (X x t) t = x)
    (hXY : ∀ y t, t ∈ Icc (0 : ℝ) T → X (Y y t) t = y) :
    ContDiffOn ℝ 1 (Function.uncurry Y) (univ ×ˢ Ioo (0 : ℝ) T) := by
  let S : Set (ℝ × ℝ) := univ ×ˢ Ioo (0 : ℝ) T
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioo
  let F : ℝ × ℝ → ℝ × ℝ := fun p ↦ (X p.1 p.2, p.2)
  let G : ℝ × ℝ → ℝ × ℝ := fun p ↦ (Y p.1 p.2, p.2)
  have hF : ContDiffOn ℝ 1 F S :=
    (contDiffOn_one_hkCurve_hilbert_flow hT f hc hbc hX₀ hX' hX).prodMk contDiffOn_snd
  have hYclamp : Continuous (fun p : ℝ × ℝ ↦ Y p.1 (projIcc 0 T hT p.2)) :=
    hY.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT)).comp continuous_snd))
  have hG : ContinuousOn G S := by
    apply (hYclamp.prodMk continuous_snd).continuousOn.congr
    intro p hp
    simp only [G, projIcc_of_mem hT (Ioo_subset_Icc_self hp.2)]
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    { toFun := F
      invFun := G
      source := S
      target := S
      map_source' := fun p hp ↦ ⟨mem_univ _, hp.2⟩
      map_target' := fun p hp ↦ ⟨mem_univ _, hp.2⟩
      left_inv' := fun p hp ↦ Prod.ext (hYX p.1 p.2 (Ioo_subset_Icc_self hp.2)) rfl
      right_inv' := fun p hp ↦ Prod.ext (hXY p.1 p.2 (Ioo_subset_Icc_self hp.2)) rfl
      continuousOn_toFun := hF.continuousOn
      continuousOn_invFun := hG
      open_source := hS
      open_target := hS }
  intro p hp
  let q : ℝ × ℝ := G p
  have hq : q ∈ S := ⟨mem_univ _, hp.2⟩
  have hFq := hF.contDiffAt (hS.mem_nhds hq)
  let J : ℝ := Real.exp (∫ s in 0..q.2, c (X q.1 s) s)
  let v : ℝ := hkCurveHilbertVelocity hT f (X q.1 q.2) q.2
  let D := flowCoordinateDerivative J v (Real.exp_ne_zero _)
  have hspace : HasDerivAt (fun y ↦ F (y, q.2)) (J, 0) q.1 :=
    (hasDerivAt_hkCurve_hilbert_flow_space hT f hbc hX₀ hX' q.1 q.2
      (Ioo_subset_Icc_self hq.2)).prodMk (hasDerivAt_const q.1 q.2)
  have htime : HasDerivAt (fun s ↦ F (q.1, s)) (v, 1) q.2 :=
    (hX' q.1 q.2 (Ioo_subset_Icc_self hq.2)).prodMk (hasDerivAt_id q.2)
  have hD : HasFDerivAt F (D : _ →L[ℝ] _) q := by
    have heq : fderiv ℝ F q = (D : _ →L[ℝ] _) := by
      apply ContinuousLinearMap.ext
      intro z
      change fderiv ℝ (Function.uncurry (fun x t ↦ F (x, t))) (q.1, q.2)
        (z.1, z.2) = _
      rw [PDE.Representations.Similarity.fderiv_uncurry_apply_prod
        (fun x t ↦ F (x, t)) q.1 z.1 q.2 z.2 (hFq.differentiableAt (by simp)),
        fderiv_eq_smul_deriv, hspace.deriv, htime.deriv]
      change z.1 • (J, 0) + z.2 • (v, 1) = (z.1 * J + z.2 * v, z.2)
      ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_zero, zero_add, mul_one]
    rw [← heq]
    exact (hFq.differentiableAt (by simp)).hasFDerivAt
  have hinv : ContDiffAt ℝ 1 G p := e.contDiffAt_symm hp hD hFq
  exact hinv.fst.contDiffWithinAt

end DeGregorio.Iteration
