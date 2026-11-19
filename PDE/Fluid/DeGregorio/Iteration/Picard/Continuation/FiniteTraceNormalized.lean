/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTraceBounds
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTraceHilbert
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.ContinuousRepresentative
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.GraphBound

/-!
# Finite terminal traces for the normalized coupled equation

For the principal-value velocity normalized at zero, H¹ control bounds the
velocity gradient globally and the velocity on every bounded interval. Thus
uniform supported H² control supplies the velocity bounds needed to construct
a terminal state from the coupled equation.

The constructed terminal vorticity also determines the Hilbert coefficient and
normalized velocity limits, which are traces of the coupled fields themselves.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- An H¹ graph bounds the principal-value coefficient and its normalized
velocity. Compact C¹ regularity identifies the pointwise principal value. -/
theorem norm_hilbertPV_and_velocity_of_h1
    (U : W^{1,2}(ℝ^1)) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 1 v) (hs : HasCompactSupport v)
    (hrep : (realLineCoordinateCLM (baseIndex 1 1) U : ℝ → ℝ) =ᵐ[volume] v)
    (x : ℝ) :
    ‖hilbertPV v x‖ ≤ 2 * ‖U‖ ∧ ‖hilbertPVVelocity v x‖ ≤ 2 * ‖U‖ * |x| := by
  have hp := (IsHilbertPair.of_contDiff_one_compactSupport hv hs).congr_ae
    (hrep.symm.trans (realLineCoordinate_ae_representative U)) EventuallyEq.rfl
  have hb := norm_hilbertPair_right_le_h1 U hp
    (continuous_hilbertPV_of_contDiff_one_compactSupport hv hs)
  refine ⟨hb x, ?_⟩
  simpa only [hilbertPVVelocity, sub_zero] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (fun y _ ↦ hb y)

/-- The classical normalized velocity is the primitive of the spectral L²
Hilbert transform. Equality of vorticity representatives is only a.e. -/
theorem hilbertPVVelocity_eq_l2Primitive_of_ae
    {f : Lp ℝ 2 (volume : Measure ℝ)} {v : ℝ → ℝ}
    (hv : ContDiff ℝ 1 v) (hs : HasCompactSupport v)
    (hrep : (f : ℝ → ℝ) =ᵐ[volume] v) :
    hilbertPVVelocity v = l2Primitive (realHilbertTransformL2 f) := by
  have hp := (IsHilbertPair.of_contDiff_one_compactSupport hv hs).congr_ae
    hrep.symm EventuallyEq.rfl
  have hae := hp.ae_eq_right (isHilbertPair_realHilbertTransformL2 f)
  funext x
  unfold hilbertPVVelocity l2Primitive
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hae] with y hy _
  exact hy

/-- A bounded H² base family with a strong L² limit has the expected compact
uniform principal-value limit. H¹ compactness of the Hilbert graphs supplies
the coefficient convergence. -/
theorem tendstoUniformlyOn_hilbertPV_of_h2_base
    {ι : Type*} {l : Filter ι} {B : NNReal}
    {f : ι → DerivLp 1 2 univ} {g : DerivLp 1 2 univ}
    (hbound : ∀ i, f i ∈ hkBaseBall 1 2 univ B)
    (hg : g ∈ hkBaseBall 1 2 univ B) (hbase : Tendsto f l (𝓝 g))
    {w : ι → ℝ → ℝ} {v : ℝ → ℝ}
    (hw : ∀ i, ContDiff ℝ 1 (w i)) (hs : ∀ i, HasCompactSupport (w i))
    (hv : ContDiff ℝ 1 v) (hvs : HasCompactSupport v)
    (hrep : ∀ i, (oneDimensionalPushforwardL2 (f i) : ℝ → ℝ) =ᵐ[volume] w i)
    (hvrep : (oneDimensionalPushforwardL2 g : ℝ → ℝ) =ᵐ[volume] v)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i ↦ hilbertPV (w i)) (hilbertPV v) l K := by
  choose u hu hubase using hbound
  obtain ⟨U, _, hUg⟩ := hg
  let A := lowerOrderCLM (n := 1) (p := 2) (Ω := univ) (by decide : 1 ≤ 2)
  have hcoord (W : W^{2,2}(ℝ^1)) :
      realLineCoordinateCLM (baseIndex 1 1) (A W) =
        oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) := by
    apply congrArg oneDimensionalPushforwardL2
    change (A W : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (W : WkpAmbientOn 1 2 2 univ) (baseIndex 1 2)
    simp only [A, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  apply tendstoUniformlyOn_hilbert_of_h1_bound
    (u := fun i ↦ A (u i)) (U := A U)
    (fun i ↦ (norm_lowerOrderCLM_apply_le _ (u i)).trans (hu i)) _
    (fun i ↦ continuous_hilbertPV_of_contDiff_one_compactSupport (hw i) (hs i))
    (continuous_hilbertPV_of_contDiff_one_compactSupport hv hvs) _ _ hK
  · simpa only [hcoord, hubase, hUg, Function.comp_def] using
      (oneDimensionalPushforwardL2.continuous.tendsto g).comp hbase
  · intro i
    rw [hcoord, hubase]
    exact (IsHilbertPair.of_contDiff_one_compactSupport (hw i) (hs i)).congr_ae
      (hrep i).symm EventuallyEq.rfl
  · rw [hcoord, hUg]
    exact (IsHilbertPair.of_contDiff_one_compactSupport hv hvs).congr_ae
      hvrep.symm EventuallyEq.rfl

/-- The coupled equation with principal-value velocity normalized at zero has a
terminal H² state under a uniform supported H² bound. The conclusion includes strong
L² convergence, compact uniform convergence of the vorticity, its derivative, the
coefficient and the velocity, and the limit of the time derivative. -/
theorem _root_.DeGregorio.IsClassicalSolutionOn.exists_h2_terminal_normalized
    {a T : ℝ} (haT : a < T) {B : NNReal} {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ} {w : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolutionOn 1
      ⟨w, fun x t ↦ hilbertPVVelocity (fun y ↦ w y t) x⟩ (Ioo a T))
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ) (L : NNReal),
      ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ K ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      (∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ L * (T - t)) ∧
      (∀ A : Set ℝ, IsCompact A →
        TendstoUniformlyOn (fun t x ↦ w x t) v (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ w x t)) (deriv v) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ hilbertPV (fun x ↦ w x t))
          (hilbertPV v) (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ hilbertPVVelocity (fun x ↦ w x t))
          (hilbertPVVelocity v) (𝓝[<] T) A) ∧
      ∀ x, Tendsto (deriv (w x)) (𝓝[<] T)
        (𝓝 (hilbertPV v x * v x - hilbertPVVelocity v x * deriv v x)) := by
  have hw (t : ℝ) (ht : t ∈ Ioo a T) : Continuous (fun x ↦ w x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  have hreg (t : ℝ) (ht : t ∈ Ioo a T) : ContDiff ℝ 1 (fun x ↦ w x t) :=
    (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1 (hw t ht) (hrep t ht)).1
  have hsupp (t : ℝ) (ht : t ∈ Ioo a T) : HasCompactSupport (fun x ↦ w x t) :=
    hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed
        (hbound t ht) (hw t ht) (hrep t ht))
  have hpoint (t : ℝ) (ht : t ∈ Ioo a T) (x : ℝ) :
      ‖hilbertPV (fun y ↦ w y t) x‖ ≤ 2 * B ∧
        ‖hilbertPVVelocity (fun y ↦ w y t) x‖ ≤ 2 * B * |x| := by
    obtain ⟨W, hW, hWbase⟩ := (hbound t ht).1
    let J := lowerOrderCLM (by decide : 1 ≤ 2) W
    have hJ : ‖J‖ ≤ B := (norm_lowerOrderCLM_apply_le _ W).trans hW
    have hr : (realLineCoordinateCLM (baseIndex 1 1) J : ℝ → ℝ)
        =ᵐ[volume] fun y ↦ w y t := by
      apply (realLineCoordinate_ae_representative J).trans
      apply (realLineRepresentative_lowerOrder_ae W).symm.trans
      simpa only [hWbase] using hrep t ht
    have hb := norm_hilbertPV_and_velocity_of_h1 J (hreg t ht) (hsupp t ht) hr x
    have hJB : 2 * ‖J‖ ≤ 2 * (B : ℝ) :=
      mul_le_mul_of_nonneg_left hJ (by norm_num)
    exact ⟨hb.1.trans hJB,
      hb.2.trans (mul_le_mul_of_nonneg_right hJB (abs_nonneg _))⟩
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  have hvelocity (t : ℝ) (ht : t ∈ Ioo a T) (x : ℝ) (hx : x ∈ K) :
      ‖hilbertPVVelocity (fun y ↦ w y t) x‖ ≤ (2 * B * R.toNNReal : NNReal) ∧
        ‖deriv (hilbertPVVelocity (fun y ↦ w y t)) x‖ ≤ (2 * B : NNReal) := by
    refine ⟨(hpoint t ht x).2.trans ?_, (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport
      (hreg t ht) (hsupp t ht) x).deriv ▸ (hpoint t ht x).1⟩
    push_cast
    gcongr
    exact (show |x| ≤ R by simpa only [Real.norm_eq_abs, id_eq] using hR x hx).trans
      (Real.le_coe_toNNReal R)
  obtain ⟨U, v, L, hU, hUb, hv, hs, hr, hlim, hrate, hspatial⟩ :=
    hsol.exists_h2_terminal_of_velocity_bounds haT hK hbound hrep hvelocity
  have hvs : HasCompactSupport v := hK.of_isClosed_subset (isClosed_tsupport _) hs
  have htimes : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo a T := Ioo_mem_nhdsLT haT
  have hc (A : Set ℝ) (hA : IsCompact A) :
      TendstoUniformlyOn (fun t ↦ hilbertPV (fun x ↦ w x t))
        (hilbertPV v) (𝓝[<] T) A := by
    let l := comap (Subtype.val : Ioo a T → ℝ) (𝓝[<] T)
    have hmap : map (Subtype.val : Ioo a T → ℝ) l = 𝓝[<] T :=
      map_comap_of_mem (by simpa only [Subtype.range_val] using Ioo_mem_nhdsLT haT)
    have hconv := tendstoUniformlyOn_hilbertPV_of_h2_base
      (l := l) (fun t : Ioo a T ↦ (hbound t t.property).1) hUb.1
      (hlim.comp (show Tendsto (Subtype.val : Ioo a T → ℝ) l (𝓝[<] T)
        from map_comap_le))
      (fun t : Ioo a T ↦ hreg t t.property) (fun t : Ioo a T ↦ hsupp t t.property)
      hv hvs (fun t : Ioo a T ↦ hrep t t.property) hr hA
    exact fun V hV ↦ by rw [← hmap]; exact hconv V hV
  have hu (A : Set ℝ) (hA : IsCompact A) :
      TendstoUniformlyOn (fun t ↦ hilbertPVVelocity (fun x ↦ w x t))
        (hilbertPVVelocity v) (𝓝[<] T) A := by
    rw [hilbertPVVelocity_eq_l2Primitive_of_ae hv hvs hr]
    exact (tendstoUniformlyOn_normalized_hilbert_velocity hlim hA).congr <| htimes.mono
      fun t ht x _ ↦ congrFun
        (hilbertPVVelocity_eq_l2Primitive_of_ae (hreg t ht) (hsupp t ht) (hrep t ht)).symm x
  refine ⟨U, v, L, hU, hUb, hv, hs, hr, hlim, hrate,
    fun A hA ↦ ⟨(hspatial A hA).1, (hspatial A hA).2, hc A hA, hu A hA⟩, ?_⟩
  intro x
  have hwx := hspatial {x} (isCompact_singleton (x := x))
  have hcx := (hc {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hux := (hu {x} isCompact_singleton).tendsto_at (mem_singleton x)
  apply ((hcx.mul (hwx.1.tendsto_at (mem_singleton x))).sub
    (hux.mul (hwx.2.tendsto_at (mem_singleton x)))).congr'
  filter_upwards [htimes] with t ht
  simpa only [one_mul, (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport
    (hreg t ht) (hsupp t ht) x).deriv] using (eq_sub_of_add_eq (hsol.transport (x := x) ht)).symm

end DeGregorio.Iteration
