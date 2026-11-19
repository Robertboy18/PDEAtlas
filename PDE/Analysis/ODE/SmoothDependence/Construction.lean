/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.FirstVariation
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import PDE.Analysis.ODE.LinearFamily
import PDE.Analysis.ODE.SmoothDependence.JointRegularity
import PDE.Analysis.ODE.SmoothDependence.UniformRemainder

/-!
# Constructing differentiable local solution families

Picard–Lindelöf supplies a family of trajectories with a uniform Lipschitz
estimate in the initial state. The variational equation constructs a candidate
for the state derivative, and Taylor-remainder estimates identify it as the
derivative. Together with the ODE's time derivative, this gives joint
`C¹` dependence on the initial state and time.

For a `C²` vector field this construction works in a real Banach space. In
finite dimensions a `C¹` vector field suffices: compactness gives uniform
continuity of `Dv` and a continuous family of solutions to the linear
variational equation. Both results construct the family and its derivative.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Construct a trajectory and its first variation on one cylinder, retaining
the uniform Lipschitz estimate in the initial state.

Both components are obtained from the same Picard–Lindelöf solution in the
product space. Thus the trajectory used in the variational equation is exactly
the trajectory whose dependence on the initial state is differentiated. -/
theorem exists_local_firstVariation_family_lipschitz
    [CompleteSpace E] (v : E → E) (hv : ContDiff ℝ 2 v) (q0 : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 < T ∧
      ∃ flow : E × ℝ → E, ∃ variation : E × ℝ → (E →L[ℝ] E),
        ContinuousOn flow (closedBall q0 r ×ˢ Icc (-T) T) ∧
        ContinuousOn variation (closedBall q0 r ×ˢ Icc (-T) T) ∧
        (∃ C : ℝ≥0, ∀ t ∈ Icc (-T) T,
          LipschitzOnWith C (fun q ↦ flow (q, t)) (closedBall q0 r)) ∧
        ∀ q ∈ closedBall q0 r,
          flow (q, 0) = q ∧
          variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-T) T,
            HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t ∧
            HasDerivAt (fun s ↦ variation (q, s))
              ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t := by
  let Q0 : E × (E →L[ℝ] E) := (q0, ContinuousLinearMap.id ℝ E)
  obtain ⟨T, hT, a, R, L, K, hR, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      ((contDiff_firstVariationVectorField_succ 1 v hv).contDiffAt (x := Q0))
  obtain ⟨α, hα, C, hC⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hαcont : ContinuousOn (Function.uncurry α) (closedBall Q0 R ×ˢ Icc (0 - T) (0 + T)) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ C
      (fun Q hQ ↦ HasDerivWithinAt.continuousOn (hα Q hQ).2) hC
  let initial : E → E × (E →L[ℝ] E) :=
    fun q ↦ (q, ContinuousLinearMap.id ℝ E)
  let flow : E × ℝ → E := fun qt ↦ (α (initial qt.1) qt.2).1
  let variation : E × ℝ → (E →L[ℝ] E) :=
    fun qt ↦ (α (initial qt.1) qt.2).2
  have hinitial (q : E) (hq : q ∈ closedBall q0 (R : ℝ)) :
      initial q ∈ closedBall Q0 R := by
    simpa [initial, Q0, Prod.dist_eq] using hq
  have hinsert : Continuous (fun qt : E × ℝ ↦ (initial qt.1, qt.2)) :=
    ((continuous_id.prodMk continuous_const).comp continuous_fst).prodMk continuous_snd
  have hmaps :
      MapsTo (fun qt : E × ℝ ↦ (initial qt.1, qt.2))
        (closedBall q0 (R : ℝ) ×ˢ Icc (-T) T)
        (closedBall Q0 R ×ˢ Icc (0 - T) (0 + T)) := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hinitial q hq, by simpa only [zero_sub, zero_add] using ht⟩
  have hc := hαcont.comp hinsert.continuousOn hmaps
  refine ⟨R, hR, T, hT, flow, variation, hc.fst, hc.snd, ?_, ?_⟩
  · refine ⟨C, fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun q hq w hw ↦ ?_⟩
    calc dist (flow (q, t)) (flow (w, t)) ≤ dist (α (initial q) t) (α (initial w) t) :=
          (le_max_left _ _).trans_eq Prod.dist_eq.symm
      _ ≤ C * dist (initial q) (initial w) :=
        (hC t (by simpa only [zero_sub, zero_add] using ht)).dist_le_mul _ (hinitial q hq) _
          (hinitial w hw)
      _ = C * dist q w := by simp [initial, Prod.dist_eq]
  · intro q hq
    have hq' := hinitial q hq
    refine ⟨congrArg Prod.fst (hα _ hq').1, congrArg Prod.snd (hα _ hq').1, fun t ht ↦ ?_⟩
    have ht' : t ∈ Ioo (0 - T) (0 + T) := by simpa only [zero_sub, zero_add] using ht
    -- the two components of the derivative of the Picard–Lindelöf solution in the product
    have hd := ((hα _ hq').2 t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
    exact ⟨by simpa [Function.comp_def, flow, firstVariationVectorField] using
      hasFDerivAt_fst.comp_hasDerivAt t hd, by simpa [Function.comp_def, flow, variation,
        firstVariationVectorField] using hasFDerivAt_snd.comp_hasDerivAt t hd⟩

/-- A `C²` autonomous vector field has a local jointly `C¹` solution family,
and its constructed first variation is the initial-state derivative.

The bounds needed by the Taylor–Grönwall argument are obtained from the
vector field and the constructed trajectories. No differentiability or
regularity of a supplied family occurs among the hypotheses. -/
theorem exists_local_contDiff_one_family
    [CompleteSpace E] (v : E → E) (hv : ContDiff ℝ 2 v) (q0 : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 < T ∧
      ∃ flow : E × ℝ → E, ∃ variation : E × ℝ → (E →L[ℝ] E),
        ContDiffOn ℝ 1 flow (ball q0 r ×ˢ Ioo (-T) T) ∧
        ContinuousOn variation (ball q0 r ×ˢ Ioo (-T) T) ∧
        ∀ q ∈ ball q0 r,
          flow (q, 0) = q ∧
          variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-T) T,
            HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t ∧
            HasDerivAt (fun s ↦ variation (q, s))
              ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t ∧
            HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
  obtain ⟨R, hR, ε, hε, flow, variation, hf, hJ, ⟨C, hC⟩, hode⟩ :=
    exists_local_firstVariation_family_lipschitz v hv q0
  have hDv : ContDiff ℝ 1 (fderiv ℝ v) :=
    hv.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, S, hS, hK⟩ := hDv.contDiffAt.exists_lipschitzOnWith (x := q0)
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp hS
  have hDvLip : LipschitzOnWith K (fderiv ℝ v) (ball q0 δ) := hK.mono hδS
  have hq0R : q0 ∈ closedBall q0 R := mem_closedBall_self hR.le
  have hf0 : flow (q0, 0) = q0 := (hode q0 hq0R).1
  have hbase : closedBall q0 R ×ˢ Icc (-ε) ε ∈ 𝓝 (q0, (0 : ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds q0 hR)
      (Icc_mem_nhds (neg_lt_zero.mpr hε) hε)
  have hinto : flow ⁻¹' ball q0 δ ∈ 𝓝 (q0, (0 : ℝ)) :=
    hf.continuousAt hbase (by simpa only [hf0] using ball_mem_nhds q0 hδ)
  obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp hinto
  let r : ℝ := min (R / 2) (d / 2)
  let T : ℝ := min (ε / 2) (d / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hd)
  have hT : 0 < T := lt_min (half_pos hε) (half_pos hd)
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hrd : r < d := (min_le_right _ _).trans_lt (half_lt_self hd)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTd : T < d := (min_le_right _ _).trans_lt (half_lt_self hd)
  have hqR {q : E} (hq : q ∈ ball q0 r) : q ∈ closedBall q0 R :=
    mem_closedBall.mpr ((mem_ball.mp hq).trans hrR).le
  have htε {t : ℝ} (ht : t ∈ Icc (-T) T) : t ∈ Ioo (-ε) ε :=
    ⟨(neg_lt_neg hTε).trans_le ht.1, ht.2.trans_lt hTε⟩
  have hsmall {q : E} (hq : q ∈ ball q0 r) {t : ℝ} (ht : t ∈ Icc (-T) T) :
      flow (q, t) ∈ ball q0 δ := by
    apply hdsub
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨(mem_ball.mp hq).trans hrd, ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact (abs_le.mpr ht).trans_lt hTd
  have hsub :
      ball q0 r ×ˢ Ioo (-T) T ⊆ closedBall q0 R ×ˢ Icc (-ε) ε := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact ⟨hqR hq, Ioo_subset_Icc_self (htε (Ioo_subset_Icc_self ht))⟩
  have hf' := hf.mono hsub
  have hJ' := hJ.mono hsub
  -- `‖Dv‖ ≤ K δ + ‖Dv q0‖` along the trajectories, which stay in `ball q0 δ`
  have hDvBound {q : E} (hq : q ∈ ball q0 r) {t : ℝ} (ht : t ∈ Icc (-T) T) :
      ‖fderiv ℝ v (flow (q, t))‖ ≤ K * δ + ‖fderiv ℝ v q0‖ := by
    have h₁ := hDvLip.dist_le_mul _ (hsmall hq ht) _ (mem_ball_self hδ)
    have h₂ := mul_le_mul_of_nonneg_left (mem_ball.mp (hsmall hq ht)).le K.coe_nonneg
    rw [dist_eq_norm] at h₁
    linarith [norm_le_norm_sub_add (fderiv ℝ v (flow (q, t))) (fderiv ℝ v q0)]
  have hspace : ∀ q ∈ ball q0 r, ∀ t ∈ Ioo (-T) T,
      HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
    intro q hq t ht
    have hlocal {w : E} (hw : w ∈ ball q (r - dist q q0)) : w ∈ ball q0 r :=
      ball_subset_ball' (sub_add_cancel _ _).le hw
    apply hasFDerivAt_flow_of_firstVariation v (fun w t ↦ flow (w, t))
      (fun w t ↦ variation (w, t)) q _ T C _ K (sub_pos.mpr (mem_ball.mp hq)) hT
    · exact fun w hw ↦ (hode w (hqR (hlocal hw))).1
    · exact (hode q (hqR hq)).2.1
    · exact fun w hw s hs ↦ ((hode w (hqR (hlocal hw))).2.2 s (htε hs)).1
    · exact fun s hs ↦ ((hode q (hqR hq)).2.2 s (htε hs)).2
    · intro w hw s hs
      simpa only [dist_eq_norm] using
        (hC s (Ioo_subset_Icc_self (htε hs))).dist_le_mul
          w (hqR (hlocal hw)) q (hqR hq)
    · exact fun s hs ↦ hDvBound hq hs
    · intro w hw s hs
      exact norm_sub_sub_fderiv_le_of_lipschitzOn_fderiv v (ball q0 δ) K
        (hv.differentiable (by norm_num)) hDvLip (convex_ball q0 δ)
        (hsmall hq hs) (hsmall (hlocal hw) hs)
    · exact K.coe_nonneg
    · exact ht
  have htime : ∀ q ∈ ball q0 r, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t :=
    fun q hq t ht ↦ ((hode q (hqR hq)).2.2 t (htε (Ioo_subset_Icc_self ht))).1
  refine ⟨r, hr, T, hT, flow, variation, ?_, hJ', ?_⟩
  · exact contDiffOn_succ_flow_of_partial_derivatives 0 v flow variation
      (ball q0 r) (Ioo (-T) T) isOpen_ball isOpen_Ioo (hv.of_le (by norm_num))
      (contDiffOn_zero.mpr hf') (contDiffOn_zero.mpr hJ') hspace htime
  · intro q hq
    refine ⟨(hode q (hqR hq)).1, (hode q (hqR hq)).2.1, ?_⟩
    intro t ht
    exact ⟨htime q hq t ht,
      ((hode q (hqR hq)).2.2 t (htε (Ioo_subset_Icc_self ht))).2,
      hspace q hq t ht⟩

/-- A finite-dimensional `C¹` vector field has a local jointly `C¹` solution
family. Its initial-state derivative is constructed by the variational equation.

Compactness is used twice: continuous matrix-valued parameter families form a
Banach space, and `Dv` is uniformly continuous on a closed ball containing the
trajectories. No second derivative of the vector field is required. -/
theorem exists_local_contDiff_one_family_of_contDiff_one
    [FiniteDimensional ℝ E] (v : E → E) (hv : ContDiff ℝ 1 v) (q0 : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 < T ∧
      ∃ flow : E × ℝ → E, ∃ variation : E × ℝ → (E →L[ℝ] E),
        ContDiffOn ℝ 1 flow (ball q0 r ×ˢ Ioo (-T) T) ∧
        ContinuousOn variation (ball q0 r ×ˢ Ioo (-T) T) ∧
        (∃ C : ℝ≥0, ∀ t ∈ Icc (-T) T,
          LipschitzOnWith C (fun q ↦ flow (q, t)) (ball q0 r)) ∧
        ∀ q ∈ ball q0 r,
          flow (q, 0) = q ∧ variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-T) T,
            HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t ∧
            HasDerivAt (fun s ↦ variation (q, s))
              ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t ∧
            HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
  classical
  obtain ⟨b, hb, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (hv.contDiffAt (x := q0))
  obtain ⟨α, hα, C, hC⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  let flow : E × ℝ → E := Function.uncurry α
  have hf : ContinuousOn flow (closedBall q0 r ×ˢ Icc (-b) b) := by
    simpa only [zero_sub, zero_add] using continuousOn_prod_of_continuousOn_lipschitzOnWith
      (Function.uncurry α) C (fun q hq ↦ HasDerivWithinAt.continuousOn (hα q hq).2) hC
  have hflow (q : E) (hq : q ∈ closedBall q0 r) :
      flow (q, 0) = q ∧ ∀ t ∈ Ioo (-b) b,
        HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t := by
    refine ⟨(hα q hq).1, fun t ht ↦ ?_⟩
    have hd : HasDerivWithinAt (α q) (v (α q t)) (Icc (-b) b) t := by
      simpa only [zero_sub, zero_add] using
        (hα q hq).2 t (by simpa only [zero_sub, zero_add] using Ioo_subset_Icc_self ht)
    exact hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hDvcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  let X := closedBall q0 (r : ℝ)
  let : CompactSpace X :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall q0 (r : ℝ))
  let A : X × ℝ → E →L[ℝ] E := fun xt ↦ fderiv ℝ v (flow (xt.1, xt.2))
  have hA : ContinuousOn A (univ ×ˢ Icc (-b) b) :=
    hDvcont.comp_continuousOn
      (hf.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
        (fun xt hxt ↦ ⟨xt.1.property, hxt.2⟩))
  obtain ⟨ε, hε, hεb, J, hJcont, hJ⟩ :=
    exists_local_continuous_linear_family A hb hA
  let T : ℝ := ε / 2
  have hT : 0 < T := half_pos hε
  have hTε : T < ε := half_lt_self hε
  have hTb : T < b := hTε.trans hεb
  have htε {t : ℝ} (ht : t ∈ Icc (-T) T) : t ∈ Ioo (-ε) ε :=
    ⟨(neg_lt_neg hTε).trans_le ht.1, ht.2.trans_lt hTε⟩
  have htb {t : ℝ} (ht : t ∈ Icc (-T) T) : t ∈ Ioo (-b) b :=
    ⟨(neg_lt_neg hTb).trans_le ht.1, ht.2.trans_lt hTb⟩
  let variation : E × ℝ → E →L[ℝ] E := fun qt ↦
    if hq : qt.1 ∈ closedBall q0 (r : ℝ) then J (⟨qt.1, hq⟩, qt.2) else 0
  have hvar_eq {q : E} (hq : q ∈ closedBall q0 (r : ℝ)) (t : ℝ) :
      variation (q, t) = J (⟨q, hq⟩, t) := dite_eq_left hq
  have hvarcont : ContinuousOn variation (ball q0 (r : ℝ) ×ˢ Ioo (-T) T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let lift : (ball q0 (r : ℝ) ×ˢ Ioo (-T) T) → X × ℝ := fun z ↦
      (⟨z.val.1, mem_closedBall.mpr (mem_ball.mp z.property.1).le⟩, z.val.2)
    have hlift : Continuous lift :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
    have hc := hJcont.comp_continuous hlift (fun z ↦
      ⟨mem_univ _, Ioo_subset_Icc_self (htε (Ioo_subset_Icc_self z.property.2))⟩)
    convert hc using 1
    funext z
    exact hvar_eq (mem_closedBall.mpr (mem_ball.mp z.property.1).le) z.val.2
  have hvarode (q : E) (hq : q ∈ closedBall q0 (r : ℝ)) :
      variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Icc (-T) T,
        HasDerivAt (fun s ↦ variation (q, s))
          ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t :=
    ⟨(hvar_eq hq 0).trans (hJ ⟨q, hq⟩).1, fun t ht ↦ by
      simpa only [variation, dite_eq_left hq, A] using (hJ ⟨q, hq⟩).2 t (htε ht)⟩
  have hcompact : IsCompact (closedBall q0 (r : ℝ) ×ˢ Icc (-b) b) :=
    (isCompact_closedBall q0 (r : ℝ)).prod isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hf
  let S : Set E := closedBall 0 B
  have hS : IsCompact S := isCompact_closedBall 0 B
  have hvalues (q : E) (hq : q ∈ closedBall q0 r) (t : ℝ)
      (ht : t ∈ Icc (-T) T) : flow (q, t) ∈ S := by
    simpa only [S, mem_closedBall, dist_zero_right] using
      hB (q, t) ⟨hq, Ioo_subset_Icc_self (htb ht)⟩
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hDvcont.continuousOn
  have hLip (t : ℝ) (ht : t ∈ Icc (-T) T) :
      LipschitzOnWith C (fun q ↦ flow (q, t)) (closedBall q0 (r : ℝ)) :=
    hC t (by simpa only [zero_sub, zero_add] using Ioo_subset_Icc_self (htb ht))
  have hspace : ∀ q ∈ ball q0 (r : ℝ), ∀ t ∈ Ioo (-T) T,
      HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
    intro q hq t ht
    have hlocal {w : E} (hw : w ∈ ball q (r - dist q q0)) : w ∈ closedBall q0 (r : ℝ) :=
      ball_subset_closedBall (ball_subset_ball' (sub_add_cancel _ _).le hw)
    have hq' : q ∈ closedBall q0 (r : ℝ) := ball_subset_closedBall hq
    apply hasFDerivAt_flow_of_uniformContinuous_fderiv v S
      (hv.differentiable (by norm_num)) (convex_closedBall 0 B)
      (hS.uniformContinuousOn_of_continuous hDvcont.continuousOn)
      (fun w s ↦ flow (w, s)) (fun s ↦ variation (q, s)) q (sub_pos.mpr (mem_ball.mp hq)) hT.le M
      C
    · exact fun w hw ↦ (hflow w (hlocal hw)).1
    · exact fun w hw s hs ↦ (hflow w (hlocal hw)).2 s (htb hs)
    · exact (hvarode q hq').1
    · exact (hvarode q hq').2
    · exact fun s hs ↦ hM _ (hvalues q hq' s hs)
    · exact fun w hw s hs ↦ hvalues w (hlocal hw) s hs
    · intro w hw s hs
      simpa only [dist_eq_norm] using (hLip s hs).dist_le_mul w (hlocal hw) q hq'
    · exact Ioo_subset_Icc_self ht
  have hsub : ball q0 (r : ℝ) ×ˢ Ioo (-T) T ⊆ closedBall q0 r ×ˢ Icc (-b) b :=
    fun qt hqt ↦
      ⟨ball_subset_closedBall hqt.1, Ioo_subset_Icc_self (htb (Ioo_subset_Icc_self hqt.2))⟩
  refine ⟨r, hr, T, hT, flow, variation, ?_, hvarcont,
    ⟨C, fun t ht ↦ (hLip t ht).mono ball_subset_closedBall⟩, ?_⟩
  · apply contDiffOn_succ_flow_of_partial_derivatives 0 v flow variation
      _ _ isOpen_ball isOpen_Ioo (hv.of_le (by norm_num))
      (contDiffOn_zero.mpr (hf.mono hsub)) (contDiffOn_zero.mpr hvarcont) hspace
    exact fun q hq t ht ↦
      (hflow q (ball_subset_closedBall hq)).2 t (htb (Ioo_subset_Icc_self ht))
  · intro q hq
    have hq' : q ∈ closedBall q0 (r : ℝ) := ball_subset_closedBall hq
    refine ⟨(hflow q hq').1, (hvarode q hq').1, fun t ht ↦
      ⟨(hflow q hq').2 t (htb (Ioo_subset_Icc_self ht)),
        (hvarode q hq').2 t (Ioo_subset_Icc_self ht), hspace q hq t ht⟩⟩

end

end PDE.Analysis.ODE
