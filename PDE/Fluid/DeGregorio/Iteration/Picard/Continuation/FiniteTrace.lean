/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Convergence
public import PDE.Fluid.DeGregorio.Model

/-!
# Terminal traces from finite-time bounds

A time-Lipschitz L² trajectory is Cauchy at a finite right endpoint. Completeness
constructs its strong limit, and weak closedness of the supported H² ball
constructs the terminal Sobolev graph with the original bound. The time estimate
also gives a quantitative rate of convergence to that graph.

The Lipschitz hypothesis can be obtained either from a bounded L² time derivative
or directly from the coupled transport equation with a common spatial L² majorant.

## Main results

* `exists_h2_terminal_of_lipschitzOnWith`: the terminal H² graph of a time-Lipschitz
  trajectory in a supported H² ball.
* `exists_h2_c1_terminal_of_lipschitzOnWith`: its C¹ representative and compact uniform
  convergence of the vorticity and its derivative.
* `IsClassicalSolutionOn.exists_h2_terminal_of_majorant`: the terminal trace of a coupled
  solution with an L² majorant for its transport production.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A time-Lipschitz trajectory in a supported H² ball has a terminal graph in
the same ball, with a linear rate of strong L² convergence. The Sobolev graph is
constructed using weak closedness after the L² limit has been obtained. -/
theorem exists_h2_terminal_of_lipschitzOnWith
    {a T : ℝ} (haT : a < T) {B C : NNReal} {K : Set (ℝ^1)}
    {F : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ K B)
    (hLip : LipschitzOnWith C F (Ioo a T)) :
    ∃ U : W^{2,2}(ℝ^1), ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ K B ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      ∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ C * (T - t) := by
  have htimes : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo a T := Ioo_mem_nhdsLT haT
  have hcauchy : Cauchy (map F (𝓝[<] T)) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hLip.uniformContinuousOn
      (le_principal_iff.mpr htimes)
  obtain ⟨g, hg⟩ := cauchy_map_iff_exists_tendsto.mp hcauchy
  have hgb : g ∈ supportedHkBaseBall 1 2 univ K B :=
    (isClosed_supportedHkBaseBall 1 2 univ K B).mem_of_tendsto hg
      (htimes.mono fun t ht ↦ hbound t ht)
  obtain ⟨U, hU, hUg⟩ := hgb.1
  refine ⟨U, hU, hUg.symm ▸ hgb, hUg.symm ▸ hg, ?_⟩
  intro t ht
  have hd : Tendsto (fun s ↦ dist (F t) (F s)) (𝓝[<] T) (𝓝 (dist (F t) g)) :=
    tendsto_const_nhds.dist hg
  have hr : Tendsto (fun s : ℝ ↦ (C : ℝ) * dist t s) (𝓝[<] T)
      (𝓝 ((C : ℝ) * dist t T)) :=
    (continuous_const.mul (continuous_const.dist continuous_id)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hle := le_of_tendsto_of_tendsto hd hr
    (htimes.mono fun s hs ↦ hLip.dist_le_mul t ht s hs)
  simpa only [hUg, dist_eq_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht.2.le),
    neg_sub] using hle

/-- A uniform L² time-derivative bound constructs the supported terminal H²
graph. -/
theorem exists_h2_terminal_of_hasDerivAt
    {a T : ℝ} (haT : a < T) {B C : NNReal} {K : Set (ℝ^1)}
    {F V : ℝ → DerivLp 1 2 univ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ K B)
    (hderiv : ∀ t ∈ Ioo a T, HasDerivAt F (V t) t)
    (hV : ∀ t ∈ Ioo a T, ‖V t‖ ≤ C) :
    ∃ U : W^{2,2}(ℝ^1), ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ K B ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      ∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ C * (T - t) := by
  apply exists_h2_terminal_of_lipschitzOnWith haT hbound
  exact (convex_Ioo a T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht ↦ (hderiv t ht).hasDerivWithinAt) (fun t ht ↦ hV t ht)

/-- The a.e. support condition defining the real-line iteration ball also
encloses the support of any continuous representative. -/
theorem tsupport_subset_of_mem_supportedHkBaseBall
    {k : ℕ} {B : ℝ} {K : Set ℝ} (hK : IsClosed K) {f : DerivLp 1 2 univ}
    (hf : f ∈ supportedHkBaseBall 1 k univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    {v : ℝ → ℝ} (hv : Continuous v)
    (hrep : (oneDimensionalPushforwardL2 f : ℝ → ℝ) =ᵐ[volume] v) :
    tsupport v ⊆ K := by
  let e := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  have hzero := ((mem_supportedHkBaseBall_iff
    (hK.measurableSet.preimage e.continuous.measurable) f).mp hf).2
  have hmp : MeasurePreserving e.symm (volume : Measure ℝ) (domainMeasure 1 univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      PDE.Analysis.Evolution.measurePreserving_equivOfUnique_symm
  have hae : ∀ᵐ x ∂volume, x ∉ K → v x = 0 := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hzero,
      oneDimensionalPushforwardL2_ae f, hrep] with x hx he hr
    intro hxK
    rw [← hr, he]
    apply hx
    simpa only [mem_preimage, e.apply_symm_apply] using hxK
  have heq : v =ᵐ[volume.restrict Kᶜ] (0 : ℝ → ℝ) :=
    (ae_restrict_iff' hK.measurableSet.compl).mpr hae
  have hvzero := Measure.eqOn_open_of_ae_eq heq hK.isOpen_compl
    hv.continuousOn continuous_const.continuousOn
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  exact hx (hvzero hxK)

/-- A time-Lipschitz half-open trajectory constructs a supported C¹ terminal
representative. Vorticity and its spatial derivative converge uniformly on
every compact set. -/
theorem exists_h2_c1_terminal_of_lipschitzOnWith
    {a T : ℝ} (haT : a < T) {B C : NNReal} {K : Set ℝ} (hK : IsClosed K)
    {F : ℝ → DerivLp 1 2 univ} {w : ℝ → ℝ → ℝ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hLip : LipschitzOnWith C F (Ioo a T))
    (hw : ∀ t ∈ Ioo a T, Continuous (fun x ↦ w x t))
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ),
      ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ K ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      (∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ C * (T - t)) ∧
      ∀ L : Set ℝ, IsCompact L →
        TendstoUniformlyOn (fun t x ↦ w x t) v (𝓝[<] T) L ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ w x t)) (deriv v) (𝓝[<] T) L := by
  obtain ⟨U, hU, hUb, hlim, hrate⟩ :=
    exists_h2_terminal_of_lipschitzOnWith haT hbound hLip
  let v := realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) U)
  have hv : Continuous v := continuous_realLineRepresentative _
  have hvr : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ)
      =ᵐ[volume] v := realLineRepresentative_lowerOrder_ae U
  refine ⟨U, v, hU, hUb, (contDiff_and_bounds_of_h2_representative U hv hvr).1,
    tsupport_subset_of_mem_supportedHkBaseBall hK hUb hv hvr, hvr, hlim, hrate, ?_⟩
  intro L hL
  let l := comap (Subtype.val : Ioo a T → ℝ) (𝓝[<] T)
  have hmap : map (Subtype.val : Ioo a T → ℝ) l = 𝓝[<] T :=
    map_comap_of_mem (by simpa only [Subtype.range_val] using Ioo_mem_nhdsLT haT)
  have hconv := tendstoUniformlyOn_representative_and_deriv_of_hkBaseBall
    (l := l) (fun t : Ioo a T ↦ (hbound t t.property).1) hUb.1
    (hlim.comp (show Tendsto (Subtype.val : Ioo a T → ℝ) l (𝓝[<] T)
      from map_comap_le))
    (fun t : Ioo a T ↦ hw t t.property) hv
    (fun t : Ioo a T ↦ hrep t t.property) hvr hL
  constructor
  · intro V hV
    rw [← hmap]
    exact hconv.1 V hV
  · intro V hV
    rw [← hmap]
    exact hconv.2 V hV

/-- A common L² majorant for the coupled transport right-hand side gives
time-Lipschitz continuity of the L² vorticity. The pointwise equation supplies
the time derivatives used by the mean value theorem. -/
theorem lipschitzOnWith_base_of_transport_majorant
    {a T : ℝ} {F : ℝ → DerivLp 1 2 univ} {w u : ℝ → ℝ → ℝ} {M : ℝ → ℝ}
    (hsol : IsClassicalSolutionOn 1 ⟨w, u⟩ (Ioo a T))
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t)
    (hM : MemLp M 2 volume)
    (hmajorant : ∀ᵐ x ∂volume, ∀ t ∈ Ioo a T,
      ‖deriv (fun y ↦ u y t) x * w x t - u x t * deriv (fun y ↦ w y t) x‖ ≤ M x) :
    LipschitzOnWith ‖hM.toLp M‖₊ F (Ioo a T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm, ← oneDimensionalPushforwardL2.norm_map,
    map_sub, Real.dist_eq]
  have hnorm :
      ‖oneDimensionalPushforwardL2 (F s) - oneDimensionalPushforwardL2 (F t)‖ ≤
        ‖s - t‖ * ‖hM.toLp M‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (oneDimensionalPushforwardL2 (F s))
      (oneDimensionalPushforwardL2 (F t)), hrep s hs, hrep t ht,
      hM.coeFn_toLp, hmajorant] with x hsub hxs hxt hxM hx
    rw [hsub, Pi.sub_apply, hxs, hxt, hxM]
    have htime (r : ℝ) (hr : r ∈ Ioo a T) :
        HasDerivAt (w x)
          (deriv (fun y ↦ u y r) x * w x r - u x r * deriv (fun y ↦ w y r) x) r := by
      have hd := (hsol.regularity.vorticity_time_differentiableAt (x := x) hr).hasDerivAt
      apply hd.congr_deriv
      have heq := hsol.transport (x := x) hr
      simpa only [one_mul] using eq_sub_of_add_eq heq
    have hdiff := (convex_Ioo a T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr ↦ (htime r hr).hasDerivWithinAt) hx ht hs
    exact hdiff.trans (by
      calc
        M x * ‖s - t‖ ≤ ‖M x‖ * ‖s - t‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ = ‖s - t‖ * ‖M x‖ := mul_comm _ _)
  simpa only [Real.norm_eq_abs, coe_nnnorm, mul_comm] using hnorm

/-- A half-open coupled solution with uniformly supported H² slices and a
common L² majorant for its transport production has a constructed supported
C¹ terminal trace, with strong L² and local uniform spatial-derivative limits. -/
theorem _root_.DeGregorio.IsClassicalSolutionOn.exists_h2_terminal_of_majorant
    {a T : ℝ} (haT : a < T) {B : NNReal} {K : Set ℝ} (hK : IsClosed K)
    {F : ℝ → DerivLp 1 2 univ} {w u : ℝ → ℝ → ℝ} {M : ℝ → ℝ}
    (hsol : IsClassicalSolutionOn 1 ⟨w, u⟩ (Ioo a T))
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t)
    (hM : MemLp M 2 volume)
    (hmajorant : ∀ᵐ x ∂volume, ∀ t ∈ Ioo a T,
      ‖deriv (fun y ↦ u y t) x * w x t - u x t * deriv (fun y ↦ w y t) x‖ ≤ M x) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ),
      ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ K ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      (∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ ‖hM.toLp M‖ * (T - t)) ∧
      ∀ L : Set ℝ, IsCompact L →
        TendstoUniformlyOn (fun t x ↦ w x t) v (𝓝[<] T) L ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ w x t)) (deriv v) (𝓝[<] T) L := by
  exact exists_h2_c1_terminal_of_lipschitzOnWith haT hK hbound
    (lipschitzOnWith_base_of_transport_majorant hsol hrep hM hmajorant)
    (fun _ ht ↦ continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt) hrep

end DeGregorio.Iteration
