/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.Construction
public import PDE.Analysis.ODE.SmoothDependence.JointRegularity
import PDE.Analysis.ODE.SmoothDependence.UniformRemainder
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-order joint dependence of autonomous ODE flows

A finite-dimensional vector field of class `Cⁿ⁺¹` has a local flow of the same
class, jointly in the initial state and time. We induct on `n`, applying the
previous order to the coupled equation `(q,J)' = (v(q), Dv(q) ∘ J)`.

The coupled flow constructs both the trajectory and its first variation.
Uniform Taylor remainders identify `J` with the state derivative. Together with
the ODE's time derivative, this makes the joint differential `Cⁿ` and gives the
next order of regularity. The radii may depend on the chosen finite order.
-/

@[expose] public section

namespace PDE.Analysis.ODE

noncomputable section

open Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite-dimensional `Cⁿ⁺¹` vector field constructs a jointly `Cⁿ⁺¹` local flow
and its jointly `Cⁿ` first variation, which satisfies the variational equation.

The state and time radii may depend on `n`. The initial-state Lipschitz estimate
also holds at the time endpoints; the ODE and regularity statements hold inside
that interval. -/
theorem exists_local_contDiff_succ_family (n : ℕ)
    [FiniteDimensional ℝ E] (v : E → E) (hv : ContDiff ℝ (n + 1) v) (q0 : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 < T ∧
      ∃ flow : E × ℝ → E, ∃ variation : E × ℝ → (E →L[ℝ] E),
        ContDiffOn ℝ (n + 1) flow (ball q0 r ×ˢ Ioo (-T) T) ∧
        ContDiffOn ℝ n variation (ball q0 r ×ˢ Ioo (-T) T) ∧
        (∃ C : ℝ≥0, ∀ t ∈ Icc (-T) T,
          LipschitzOnWith C (fun q ↦ flow (q, t)) (ball q0 r)) ∧
        ∀ q ∈ ball q0 r,
          flow (q, 0) = q ∧ variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
          ∀ t ∈ Ioo (-T) T,
            HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t ∧
            HasDerivAt (fun s ↦ variation (q, s))
              ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t ∧
            HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
  induction n generalizing E with
  | zero =>
    obtain ⟨r, hr, T, hT, flow, variation, hflow, hvariation, hLip, hsolve⟩ :=
      exists_local_contDiff_one_family_of_contDiff_one v (by simpa using hv) q0
    refine ⟨r, hr, T, hT, flow, variation, ?_, ?_, hLip, hsolve⟩
    · simpa using hflow
    · simpa only [Nat.cast_zero, contDiffOn_zero] using hvariation
  | succ n ih =>
    let Q0 : E × (E →L[ℝ] E) := (q0, ContinuousLinearMap.id ℝ E)
    obtain ⟨R, hR, b, hb, α, A, hα, _, ⟨C, hC⟩, hαode⟩ :=
      ih (firstVariationVectorField v)
        (contDiff_firstVariationVectorField_succ (n + 1) v (by simpa using hv)) Q0
    let initial : E → E × (E →L[ℝ] E) :=
      fun q ↦ (q, ContinuousLinearMap.id ℝ E)
    let lift : E × ℝ → (E × (E →L[ℝ] E)) × ℝ :=
      fun qt ↦ (initial qt.1, qt.2)
    let flow : E × ℝ → E := fun qt ↦ (α (lift qt)).1
    let variation : E × ℝ → E →L[ℝ] E := fun qt ↦ (α (lift qt)).2
    have hinitial (q : E) (hq : q ∈ ball q0 R) : initial q ∈ ball Q0 R := by
      simpa [initial, Q0, Prod.dist_eq] using hq
    have hlift : ContDiff ℝ (n + 1) lift :=
      ((contDiff_id.prodMk contDiff_const).comp contDiff_fst).prodMk contDiff_snd
    have hliftMaps : MapsTo lift (ball q0 R ×ˢ Ioo (-b) b)
        (ball Q0 R ×ˢ Ioo (-b) b) :=
      fun qt hqt ↦ ⟨hinitial qt.1 hqt.1, hqt.2⟩
    have hpair : ContDiffOn ℝ (n + 1) (fun qt ↦ α (lift qt))
        (ball q0 R ×ˢ Ioo (-b) b) :=
      hα.comp hlift.contDiffOn hliftMaps
    have hf : ContDiffOn ℝ (n + 1) flow (ball q0 R ×ˢ Ioo (-b) b) := hpair.fst
    have hJ : ContDiffOn ℝ (n + 1) variation (ball q0 R ×ˢ Ioo (-b) b) := hpair.snd
    have hode (q : E) (hq : q ∈ ball q0 R) :
        flow (q, 0) = q ∧ variation (q, 0) = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Ioo (-b) b,
          HasDerivAt (fun s ↦ flow (q, s)) (v (flow (q, t))) t ∧
          HasDerivAt (fun s ↦ variation (q, s))
            ((fderiv ℝ v (flow (q, t))).comp (variation (q, t))) t := by
      have hq' := hαode (initial q) (hinitial q hq)
      refine ⟨congrArg Prod.fst hq'.1, congrArg Prod.snd hq'.1, fun t ht ↦ ?_⟩
      have hd := (hq'.2.2 t ht).1
      exact ⟨(ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t hd,
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t hd⟩
    -- The closed smaller cylinder lies inside the open ODE domain. This gives
    -- compactness and keeps the endpoint derivatives needed by Grönwall valid.
    let r : ℝ := R / 2
    let T : ℝ := b / 2
    have hr : 0 < r := half_pos hR
    have hT : 0 < T := half_pos hb
    have hrR : r < R := half_lt_self hR
    have hTb : T < b := half_lt_self hb
    have hqR {q : E} (hq : q ∈ closedBall q0 r) : q ∈ ball q0 R :=
      mem_ball.mpr ((mem_closedBall.mp hq).trans_lt hrR)
    have htb {t : ℝ} (ht : t ∈ Icc (-T) T) : t ∈ Ioo (-b) b :=
      ⟨(neg_lt_neg hTb).trans_le ht.1, ht.2.trans_lt hTb⟩
    have hclosed : closedBall q0 r ×ˢ Icc (-T) T ⊆ ball q0 R ×ˢ Ioo (-b) b :=
      fun qt hqt ↦ ⟨hqR hqt.1, htb hqt.2⟩
    have hrR' : ball q0 r ⊆ ball q0 R := ball_subset_ball hrR.le
    have hopen : ball q0 r ×ˢ Ioo (-T) T ⊆ ball q0 R ×ˢ Ioo (-b) b :=
      fun qt hqt ↦ hclosed ⟨ball_subset_closedBall hqt.1, Ioo_subset_Icc_self hqt.2⟩
    have hcompact : IsCompact (closedBall q0 r ×ˢ Icc (-T) T) :=
      (isCompact_closedBall q0 r).prod isCompact_Icc
    obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn (hf.continuousOn.mono hclosed)
    let S : Set E := closedBall 0 B
    have hS : IsCompact S := isCompact_closedBall 0 B
    have hvalues (q : E) (hq : q ∈ closedBall q0 r) (t : ℝ)
        (ht : t ∈ Icc (-T) T) : flow (q, t) ∈ S := by
      simpa only [S, mem_closedBall, dist_zero_right] using hB (q, t) ⟨hq, ht⟩
    have hDvcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by simp)
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hDvcont.continuousOn
    have hLip (t : ℝ) (ht : t ∈ Icc (-T) T) :
        LipschitzOnWith C (fun q ↦ flow (q, t)) (ball q0 R) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro q hq w hw
      have h := (hC t (Ioo_subset_Icc_self (htb ht))).dist_le_mul
        (initial q) (hinitial q hq) (initial w) (hinitial w hw)
      refine (le_max_left _ _).trans (h.trans_eq ?_)
      simp [initial, Prod.dist_eq]
    have hspace : ∀ q ∈ ball q0 r, ∀ t ∈ Ioo (-T) T,
        HasFDerivAt (fun w ↦ flow (w, t)) (variation (q, t)) q := by
      intro q hq t ht
      have hρ : 0 < r - dist q q0 := sub_pos.mpr (mem_ball.mp hq)
      have hlocal {w : E} (hw : w ∈ ball q (r - dist q q0)) : w ∈ closedBall q0 r :=
        ball_subset_closedBall (ball_subset_ball' (sub_add_cancel r _).le hw)
      have hq' : q ∈ closedBall q0 r := ball_subset_closedBall hq
      apply hasFDerivAt_flow_of_uniformContinuous_fderiv v S
        (hv.differentiable (by simp)) (convex_closedBall 0 B)
        (hS.uniformContinuousOn_of_continuous hDvcont.continuousOn)
        (fun w s ↦ flow (w, s)) (fun s ↦ variation (q, s)) q hρ hT.le M C
      · exact fun w hw ↦ (hode w (hqR (hlocal hw))).1
      · exact fun w hw s hs ↦ ((hode w (hqR (hlocal hw))).2.2 s (htb hs)).1
      · exact (hode q (hqR hq')).2.1
      · exact fun s hs ↦ ((hode q (hqR hq')).2.2 s (htb hs)).2
      · exact fun s hs ↦ hM _ (hvalues q hq' s hs)
      · exact fun w hw s hs ↦ hvalues w (hlocal hw) s hs
      · intro w hw s hs
        simpa only [dist_eq_norm] using
          (hLip s hs).dist_le_mul w (hqR (hlocal hw)) q (hqR hq')
      · exact Ioo_subset_Icc_self ht
    refine ⟨r, hr, T, hT, flow, variation, ?_, hJ.mono hopen, ?_, ?_⟩
    · apply contDiffOn_succ_flow_of_partial_derivatives (n + 1) v flow variation
        _ _ isOpen_ball isOpen_Ioo (hv.of_le (by simp))
        (hf.mono hopen) (hJ.mono hopen) hspace
      exact fun q hq t ht ↦ ((hode q (hrR' hq)).2.2 t (htb (Ioo_subset_Icc_self ht))).1
    · exact ⟨C, fun t ht ↦ (hLip t ht).mono hrR'⟩
    · intro q hq
      have hq' := hode q (hrR' hq)
      exact ⟨hq'.1, hq'.2.1, fun t ht ↦ ⟨(hq'.2.2 t (htb (Ioo_subset_Icc_self ht))).1,
        (hq'.2.2 t (htb (Ioo_subset_Icc_self ht))).2, hspace q hq t ht⟩⟩

end

end PDE.Analysis.ODE
