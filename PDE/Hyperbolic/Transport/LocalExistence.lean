/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.InitialData
public import PDE.Representations.Similarity.Dynamic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Construction of a local linear transport step

Jointly C¹ coefficients and C¹ initial data give a local C¹ solution of
`w_t + b w_x = c w`. The characteristic family is constructed by the ODE
existence theorem applied to the position, amplitude, and clock. Its clock
is proved equal to the independent time. Inverting position and time gives
the Eulerian solution.

This theorem constructs one transport step near an initial point, without a
common lifespan over the line.
-/

@[expose] public section

noncomputable section

open Filter Set PDE.Analysis
open scoped Topology

namespace TransportEquation

/-- Construct position and amplitude together for a prescribed drift and stretching
coefficient. The time coordinate of the autonomous ODE is identified with time. -/
theorem exists_local_transport_family (b c : ℝ → ℝ → ℝ) (hb : ContDiff ℝ 1 (Function.uncurry b))
    (hc : ContDiff ℝ 1 (Function.uncurry c)) (w₀ : ℝ → ℝ) (hw₀ : ContDiff ℝ 1 w₀) (x₀ : ℝ) :
    ∃ A : Set ℝ, IsOpen A ∧ x₀ ∈ A ∧ ∃ T : ℝ, 0 < T ∧
      ∃ F : ℝ × ℝ → ℝ × ℝ,
        ContDiffOn ℝ 1 F (A ×ˢ Ioo (-T) T) ∧
        (∀ y ∈ A, F (y, 0) = (y, w₀ y)) ∧
        ∀ y ∈ A, ∀ t ∈ Ioo (-T) T,
          HasDerivAt (fun s ↦ F (y, s))
            (b (F (y, t)).1 t, c (F (y, t)).1 t * (F (y, t)).2) t := by
  let v : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun q ↦ ((b q.1.1 q.2, c q.1.1 q.2 * q.1.2), 1)
  have hv : ContDiff ℝ 1 v := ((hb.comp (contDiff_fst.fst.prodMk contDiff_snd)).prodMk
      ((hc.comp (contDiff_fst.fst.prodMk contDiff_snd)).mul contDiff_fst.snd)).prodMk contDiff_const
  let initial : ℝ → (ℝ × ℝ) × ℝ := fun y ↦ ((y, w₀ y), 0)
  obtain ⟨A, hA, hxA, _, T, hT, curve, hcurve, hode⟩ :=
    PDE.Analysis.ODE.exists_local_contDiff_one_family_with_initialData v hv initial univ isOpen_univ
      ((contDiff_id.prodMk hw₀).prodMk contDiff_const).contDiffOn x₀ (mem_univ _)
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  have hclock (y : ℝ) (hy : y ∈ A) (t : ℝ) (ht : t ∈ Ioo (-T) T) :
      (curve (y, t)).2 = t := by
    have hd (s : ℝ) (hs : s ∈ Ioo (-T) T) :
        HasDerivAt (fun r ↦ (curve (y, r)).2 - r) 0 s := by
      have h : HasDerivAt (fun r ↦ (curve (y, r)).2) 1 s := by
        simpa [v] using ((hode y hy).2 s hs).1.hasFDerivAt.snd.hasDerivAt
      convert! h.sub (hasDerivAt_id s) using 1
      simp
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd s hs).deriv) ht hzero
    apply sub_eq_zero.mp
    simpa only [(hode y hy).1, initial, sub_self] using heq
  refine ⟨A, hA, hxA, T, hT, fun q ↦ (curve q).1, hcurve.fst, ?_, ?_⟩
  · exact fun y hy ↦ congrArg Prod.fst (hode y hy).1
  · intro y hy t ht
    simpa [v, hclock y hy t ht] using ((hode y hy).2 t ht).1.hasFDerivAt.fst.hasDerivAt

private def transportCoordinateDerivative (v : ℝ) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).skewProd (ContinuousLinearEquiv.refl ℝ ℝ)
      (ContinuousLinearMap.toSpanSingleton ℝ v)).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ))

private theorem transportCoordinateDerivative_apply (v : ℝ) (q : ℝ × ℝ) :
    transportCoordinateDerivative v q = (q.1 + q.2 * v, q.2) := rfl

/-- Prescribed jointly C¹ drift and stretching construct a C¹ Eulerian solution
near every point of the initial line. Neither a characteristic nor a solution
is supplied as a hypothesis. -/
theorem exists_local_transport_solution
    (b c : ℝ → ℝ → ℝ) (hb : ContDiff ℝ 1 (Function.uncurry b))
    (hc : ContDiff ℝ 1 (Function.uncurry c))
    (w₀ : ℝ → ℝ) (hw₀ : ContDiff ℝ 1 w₀) (x₀ : ℝ) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (x₀, 0) ∈ V ∧
      ∃ w : ℝ → ℝ → ℝ, ContDiffOn ℝ 1 (Function.uncurry w) V ∧
        (∀ x, (x, 0) ∈ V → w x 0 = w₀ x) ∧
        ∀ x t, (x, t) ∈ V →
          deriv (w x) t + b x t * deriv (fun y ↦ w y t) x = c x t * w x t := by
  obtain ⟨A, hA, hxA, T, hT, F, hF, hinit, hode⟩ :=
    exists_local_transport_family b c hb hc w₀ hw₀ x₀
  let box : Set (ℝ × ℝ) := A ×ˢ Ioo (-T) T
  let p : ℝ × ℝ := (x₀, 0)
  have hzero : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  have hp : p ∈ box := ⟨hxA, hzero⟩
  have hbox : IsOpen box := hA.prod isOpen_Ioo
  let X : ℝ × ℝ → ℝ × ℝ := fun q ↦ ((F q).1, q.2)
  have hX : ContDiffOn ℝ 1 X box := hF.fst.prodMk contDiffOn_snd
  have hXp : ContDiffAt ℝ 1 X p := hX.contDiffAt (hbox.mem_nhds hp)
  have hbase : X p = p := by simp only [X, p, hinit x₀ hxA]
  have hspace : HasDerivAt (fun y ↦ (F (y, 0)).1) 1 x₀ := by
    apply (hasDerivAt_id x₀).congr_of_eventuallyEq
    filter_upwards [hA.mem_nhds hxA] with y hy using congrArg Prod.fst (hinit y hy)
  have htime : HasDerivAt (fun s ↦ (F (x₀, s)).1) (b x₀ 0) 0 := by
    simpa [hinit x₀ hxA] using (hode x₀ hxA 0 hzero).hasFDerivAt.fst.hasDerivAt
  have hDX : HasFDerivAt X
      (transportCoordinateDerivative (b x₀ 0) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p := by
    have hs : HasDerivAt (fun y ↦ X (y, 0)) (1, 0) x₀ := hspace.prodMk (hasDerivAt_const x₀ 0)
    have ht : HasDerivAt (fun s ↦ X (x₀, s)) (b x₀ 0, 1) 0 := htime.prodMk (hasDerivAt_id 0)
    refine hXp.differentiableAt_one.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun q ↦ ?_)
    change fderiv ℝ (Function.uncurry (fun y t ↦ X (y, t))) (x₀, 0) (q.1, q.2) = _
    rw [PDE.Representations.Similarity.fderiv_uncurry_apply_prod
      (fun y t ↦ X (y, t)) x₀ q.1 0 q.2 hXp.differentiableAt_one, fderiv_eq_smul_deriv,
      hs.deriv, ht.deriv]
    ext <;> simp [transportCoordinateDerivative_apply]
  let e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    hXp.toOpenPartialHomeomorph X hDX (by simp)
  have he : (e : (ℝ × ℝ) → ℝ × ℝ) = X := rfl
  have hps : p ∈ e.source := hXp.mem_toOpenPartialHomeomorph_source hDX (by simp)
  have hpt : p ∈ e.target := by
    simpa only [hbase] using hXp.image_mem_toOpenPartialHomeomorph_target hDX (by simp)
  have hinvp : e.symm p = p := by
    nth_rw 1 [← hbase]
    exact e.left_inv hps
  have hinv : ContDiffAt ℝ 1 e.symm p := by
    have h := hXp.to_localInverse hDX (by simp)
    rwa [hbase] at h
  obtain ⟨N, hN, hreg⟩ := hinv.contDiffOn le_rfl (by simp)
  have hgood : N ∩ (e.source ∩ (box ∩ (e.target ∩ e.symm ⁻¹' box))) ∈ 𝓝 p :=
    inter_mem hN (inter_mem (e.open_source.mem_nhds hps)
      (inter_mem (hbox.mem_nhds hp) (inter_mem (e.open_target.mem_nhds hpt)
        (hinv.continuousAt (by simpa only [hinvp] using hbox.mem_nhds hp)))))
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hgood
  let w : ℝ → ℝ → ℝ := fun x t ↦ (F (e.symm (x, t))).2
  have hw : ContDiffOn ℝ 1 (Function.uncurry w) V :=
    hF.snd.comp (hreg.mono (fun q hq ↦ (hVsub hq).1)) (fun q hq ↦ (hVsub hq).2.2.2.2)
  refine ⟨V, hV, hpV, w, hw, ?_, ?_⟩
  · intro x hx
    have hxb : x ∈ A := (hVsub hx).2.2.1.1
    have heq : X (x, 0) = (x, 0) := by simp only [X, hinit x hxb]
    change (F (e.symm (x, 0))).2 = _
    rw [← heq, ← he, e.left_inv (hVsub hx).2.1, hinit x hxb]
  · intro x t hxt
    let q : ℝ × ℝ := e.symm (x, t)
    have hqbox : q ∈ box := (hVsub hxt).2.2.2.2
    have hqs : q ∈ e.source := e.map_target (hVsub hxt).2.2.2.1
    have hXq : X q = (x, t) := e.right_inv (hVsub hxt).2.2.2.1
    have hxq : (F q).1 = x := congrArg Prod.fst hXq
    have htq : q.2 = t := congrArg Prod.snd hXq
    have hfd := hode q.1 hqbox.1 q.2 hqbox.2
    simp only [Prod.mk.eta] at hfd
    have hpath : HasDerivAt (fun s ↦ X (q.1, s)) (b x t, 1) q.2 := by
      simpa [X, hxq, htq] using hfd.hasFDerivAt.fst.hasDerivAt.prodMk (hasDerivAt_id q.2)
    have hwAt := (hw.contDiffAt (hV.mem_nhds hxt)).differentiableAt_one
    have hwAt' : HasFDerivAt (Function.uncurry w)
        (fderiv ℝ (Function.uncurry w) (x, t)) (X (q.1, q.2)) := by
      simpa only [Prod.mk.eta, hXq] using hwAt.hasFDerivAt
    have hevent : (fun s ↦ (F (q.1, s)).2) =ᶠ[𝓝 q.2]
        fun s ↦ w (X (q.1, s)).1 (X (q.1, s)).2 := by
      filter_upwards [(continuous_const.prodMk continuous_id).continuousAt
        (e.open_source.mem_nhds hqs)] with s hs
      exact congrArg (fun r ↦ (F r).2) (e.left_inv hs).symm
    have hfdz : HasDerivAt (fun s ↦ (F (q.1, s)).2) (c (F q).1 q.2 * (F q).2) q.2 := by
      simpa using hfd.hasFDerivAt.snd.hasDerivAt
    have heq := ((hwAt'.comp_hasDerivAt (f := fun s ↦ X (q.1, s)) q.2 hpath).congr_of_eventuallyEq
      hevent).unique hfdz
    rw [PDE.Representations.Similarity.fderiv_uncurry_apply_prod w x (b x t) t 1 hwAt] at heq
    have hwq : (F q).2 = w x t := rfl
    simpa only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul, hxq, hwq, htq, add_comm] using heq

end TransportEquation
