/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.FluxIdentity
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Integrability
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.TestSupport
public import PDE.Elliptic.Regularity.Quasilinear.Boundary.LocalizedH2
public import PDE.Elliptic.Regularity.Boundary.Flux.CutoffIdentity
public import PDE.Elliptic.Regularity.Boundary.Flux.LoadExtension
public import PDE.Elliptic.Regularity.Boundary.H2.ReflectedPullback
import PDE.DistributionTheory.TestFunction.SupportBuffer

/-!
# Nonlinear boundary regularity in chart coordinates

A strongly monotone Lipschitz flux and an `L²` load give local `H²`
regularity after a C² boundary chart. Three nested cutoffs separate the
energy test, the solution pullback, and the globally bounded chart parameters.
The transported equation is used only where it holds.

The scalar normal recovery in the half-space theorem supplies the normal
second derivative; no second derivative of the solution is assumed here.
The dimension-one case has no tangential tests and uses the same argument.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.WeakChangeOfVariables SobolevSpace.GraphSpace.DifferenceQuotient
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- An almost-everywhere linear growth bound by the gradient controls the sum
of the scalar flux-coordinate norms by the `H¹` norm. -/
theorem sum_norm_flux_coordinates_le_of_ae_le_gradient
    (U : H¹(HalfSpace.upper n))
    (Qv : Lp (ℝ^n) 2 (domainMeasure n (HalfSpace.upper n))) (D : ℝ≥0)
    (hbound : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n),
      ‖Qv y‖ ≤ D * ‖∇ U y‖) :
    (∑ i : Fin n, ‖(EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).compLpL 2 _ Qv‖) ≤
      n * ((D * n) * ‖U‖) := by
  let Q (i : Fin n) : DerivLp n 2 (HalfSpace.upper n) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).compLpL 2 _ Qv
  have hQvnorm : ‖Qv‖ ≤ D * ‖∇ U‖ :=
    Lp.norm_le_mul_norm_of_ae_le_mul hbound
  have hQnorm (i : Fin n) : ‖Q i‖ ≤ (D * n) * ‖U‖ := by
    calc
      _ ≤ ‖Qv‖ := (Lp.norm_coordinate_le_norm_euclideanTuple Q i).trans_eq
        (congrArg norm (Lp.euclideanTuple_coordinates Qv))
      _ ≤ D * ‖∇ U‖ := hQvnorm
      _ ≤ D * (n * ‖U‖) :=
        mul_le_mul_of_nonneg_left (wkpGradientCLM_norm_le U) D.coe_nonneg
      _ = _ := by ring
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hQnorm i)

/-- A cutoff supported where the pullback cutoff is one removes that auxiliary
cutoff from the base representative, with equality for the half-space domain measure. -/
theorem baseCoord_cutoff_localizedHalfSpacePullbackCLM_ae
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (η κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηtarget : tsupport η.toFun ⊆ (hΩ.chart a).target)
    (hκtarget : tsupport κ.toFun ⊆ (hΩ.chart a).target)
    (hκη : ∀ y ∈ tsupport η.toFun, κ.toFun y = 1) (u : H¹₀(Ω)) :
    (baseCoordCLM (cutoffH10 (HalfSpace.isOpen_upper n) η
      (localizedHalfSpacePullbackCLM hΩ.isOpen.measurableSet
        (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)
        (hΩ.chart_target_bounded a) (hΩ.chart_mem_iff_upper a) κ hκtarget u)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun y ↦ η.toFun y * baseCoordCLM u ((hΩ.chart a).symm y) := by
  let U := localizedHalfSpacePullbackCLM hΩ.isOpen.measurableSet
    (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)
    (hΩ.chart_target_bounded a) (hΩ.chart_mem_iff_upper a) κ hκtarget u
  rw [baseCoordCLM_cutoffH10]
  filter_upwards [mulLpLeft_apply_ae (testFunctionLpTop (Ω := HalfSpace.upper n) η)
      (baseCoordCLM U),
    testFunctionLpTop_apply_ae (Ω := HalfSpace.upper n) η,
    localizedHalfSpacePullbackCLM_base_ae hΩ.isOpen.measurableSet
      (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)
      (hΩ.chart_target_bounded a) (hΩ.chart_mem_iff_upper a) κ hκtarget u,
    ae_restrict_mem (HalfSpace.isOpen_upper n).measurableSet] with y hm hη hu hy
  change (testFunctionLpTop (Ω := HalfSpace.upper n) η • baseCoordCLM U :
    DerivLp n 2 (HalfSpace.upper n)) y =
    testFunctionLpTop (Ω := HalfSpace.upper n) η y * baseCoordCLM U y at hm
  change baseCoordCLM U y = _ at hu
  rw [hm, hη, hu]
  by_cases hyη : η.toFun y = 0
  · simp only [hyη, zero_mul]
  · have hyηsupport := subset_tsupport η.toFun hyη
    have hyΩ : (hΩ.chart a).symm y ∈ Ω :=
      (hΩ.chart_mem_iff_upper a _ ((hΩ.chart a).map_target (hηtarget hyηsupport))).mpr
        (by simpa only [(hΩ.chart a).right_inv (hηtarget hyηsupport)] using hy)
    rw [hκη y hyηsupport, one_mul, indicator_of_mem hyΩ]

/-- The localized chart pullback of a weak solution has a
`H²` representative. The physical weak equation is the only PDE hypothesis. -/
theorem exists_H2_chartCutoff_of_monotone_weakEquation
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N)
    (hE : ContDiff ℝ 2 (fun x ↦ hΩ.chart a x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ (hΩ.chart a).symm y))
    (A : ℝ^n → ℝ^n) (hzero : A 0 = 0) {θ : ℝ} (hθ : 0 < θ)
    (hmono : ∀ z w, θ * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫)
    {C : ℝ≥0} (hLip : LipschitzWith C A)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hηtarget : tsupport η.toFun ⊆ (hΩ.chart a).target)
    (hηbound : ∀ y ∈ HalfSpace.upper n, |η.toFun y| ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : H¹₀(Ω))
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
    (∀ᵐ x ∂domainMeasure n Ω,
      A (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x)) →
    (∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
    ∃ V : W^{2,2}(HalfSpace.upper n),
      lowerOrderCLM (k := 1) (m := 2) (by omega) V ∈
        (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule ∧
      ((V.val (baseIndex n 2) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (HalfSpace.upper n)]
          fun y ↦ η.toFun y * baseCoordCLM u ((hΩ.chart a).symm y)) ∧
      ‖V‖ ≤ M * (‖u‖ + ‖f‖) := by
  obtain ⟨ρ, χ, hρ, hχtarget, hχηnhds, hbuffer, _⟩ :=
    TestFunction.exists_eq_one_on_compact_with_buffer
      (hΩ.chart a).open_target η.hasCompactSupport hηtarget
  obtain ⟨κ, hκtarget, _, hκχnhds, hκrange⟩ := TestFunction.exists_eq_one_on_compact
    (hΩ.chart a).open_target χ.hasCompactSupport hχtarget
  obtain ⟨σ, _, hσκ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    (hΩ.chart a).open_target κ.hasCompactSupport hκtarget
  obtain ⟨β, hβ, K, D, hβmono, hvariation⟩ :=
    exists_extendedChartFlux_bounds (hΩ.chart a) hE hSymm κ σ
      hκrange hκtarget hσκ A hzero hθ hmono hLip
  let B := extendedChartFlux (hΩ.chart a) A κ σ β
  obtain ⟨L, hηLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport η.hasCompactSupport
    (show ContDiff ℝ 1 η.toFun from η.contDiff.of_le (by simp)) (by norm_num)
  obtain ⟨C₀, hC₀, hload⟩ := Boundary.exists_chartLoad_extension hΩ a
  let P := localizedHalfSpacePullbackCLM hΩ.isOpen.measurableSet
    (hΩ.chart_contDiff a) (hΩ.chart_symm_contDiff a)
    (hΩ.chart_target_bounded a) (hΩ.chart_mem_iff_upper a) κ hκtarget
  let H := 1 + n * ((D : ℝ) * n)
  have hH : 0 ≤ H := by positivity
  let M := localizedH2EstimateConstant β K D L η
  have hM : 0 ≤ M := localizedH2EstimateConstant_nonneg hβ K D L η
  refine ⟨M * (C₀ + H * ‖P‖), mul_nonneg hM (add_nonneg hC₀ (mul_nonneg hH P.opNorm_nonneg)),
    fun u q f hq hweak ↦ ?_⟩
  let U := P u
  let dU := Lp.euclideanTuple (fun i ↦ derivCoordCLM i U)
  have hstate (y z w : ℝ^n) : ‖B y w - B y z‖ ≤ D * ‖w - z‖ := by
    simpa only [sub_self, norm_zero, mul_zero, zero_mul, zero_add] using
      hvariation y y z w
  have hmem := memLp_extendedChartFlux (hΩ.chart a) hE hSymm A hLip.continuous
    hzero κ σ β hstate (Lp.memLp dU)
  let Qv := hmem.toLp (fun y ↦ B y (dU y))
  let Q (i : Fin n) : DerivLp n 2 (HalfSpace.upper n) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).compLpL 2 _ Qv
  have hQv : (Qv : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (HalfSpace.upper n)]
      fun y ↦ B y (dU y) := hmem.coeFn_toLp
  have hQcoords : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n),
      ∀ i : Fin n, Q i y = Qv y i :=
    ae_all_iff.mpr fun i ↦ (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).coeFn_compLpL Qv
  have hrep : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n),
      B y (dU y) = Lp.euclideanTuple Q y := by
    rw [show Lp.euclideanTuple Q = Qv from Lp.euclideanTuple_coordinates Qv]
    exact hQv.symm
  have hcoreFlux := extendedChartFlux_localizedPullback_ae_on_core
    hΩ a A κ σ hκtarget hσκ β u q hq hκχnhds
  have hQ : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ tsupport χ.toFun →
      ∀ i : Fin n, Q i y =
        (piolaTransform (hΩ.chart a) (fun x ↦ WithLp.toLp 2 (fun j ↦ q j x)) y) i := by
    filter_upwards [hQcoords, hQv, hcoreFlux] with y hc hv hf hy i
    rw [hc i, hv]
    exact congrArg (fun z : ℝ^n ↦ z i) (hf hy)
  obtain ⟨F, hFnorm, hF⟩ := hload f
  have hequation (v : H¹₀(HalfSpace.upper n)) :
      (∑ i, ⟪Q i, derivCoordCLM i (cutoffH10 (HalfSpace.isOpen_upper n) χ v)⟫) =
        ⟪F, baseCoordCLM (cutoffH10 (HalfSpace.isOpen_upper n) χ v)⟫ :=
    Boundary.weakFlux_chartPullback_cutoff_identity hΩ a q f hweak χ hχtarget Q F hQ
      (hF.mono fun y hy hyχ ↦ hy (hχtarget hyχ)) v
  have hχη (y : ℝ^n) (hy : y ∈ tsupport η.toFun) : χ.toFun y = 1 :=
    (hχηnhds y hy).eq_of_nhds
  have htest (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
      (h : ℝ) (hh : 0 < h) (hhρ : h ≤ ρ) :
      (∑ i, ⟪Q i, derivCoordCLM i (localizedTangentialTest η k hk h U)⟫) =
        ⟪F, baseCoordCLM (localizedTangentialTest η k hk h U)⟫ := by
    have hfix := cutoffH10_localizedTangentialTest χ η k hk h hχη
      (fun y hy ↦ hbuffer y hy (coordinateStep k h) (by
        simpa only [norm_coordinateStep, abs_of_pos hh] using hhρ)) U
    simpa only [hfix] using hequation (localizedTangentialTest η k hk h U)
  have hdiv (φ : TestFunctionOn n (HalfSpace.upper n)) :
      (∑ i, ⟪Q i, derivCoordCLM i
        (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))⟫) =
      ⟪F, baseCoordCLM
        (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))⟫ := by
    simpa only [cutoffH10_cutoffH10_of_eq_one (HalfSpace.isOpen_upper n) χ η hχη] using
      hequation (cutoffH10 (HalfSpace.isOpen_upper n) η (testFunctionToH10 φ))
  obtain ⟨V, hV, hVnorm⟩ := exists_localized_H2_of_monotone_weakEquation B K D hβ
    (fun y _ z w ↦ hβmono y z w) (fun x _ y _ z w ↦ hvariation x y z w)
    η hηLip hηbound U Q F hrep hρ htest hdiv
  have hsum : ∑ i, ‖Q i‖ ≤ n * ((D * n) * ‖U‖) :=
    sum_norm_flux_coordinates_le_of_ae_le_gradient
      (U : H¹(HalfSpace.upper n)) Qv D (by
        filter_upwards [hQv] with y hy
        rw [hy]
        change ‖B y (dU y)‖ ≤ D * ‖dU y‖
        simpa only [B, extendedChartFlux_zero (hΩ.chart a) A hzero κ σ β y, sub_zero]
          using hstate y 0 (dU y))
  have hinput : ‖F‖ + ‖U‖ + ∑ i, ‖Q i‖ ≤ (C₀ + H * ‖P‖) * (‖u‖ + ‖f‖) := by
    have hHU : ‖U‖ + n * ((D * n) * ‖U‖) = H * ‖U‖ := by dsimp only [H]; ring
    linarith [mul_le_mul_of_nonneg_left (P.le_opNorm u) hH, mul_nonneg hC₀ (norm_nonneg u),
      mul_nonneg (mul_nonneg hH P.opNorm_nonneg) (norm_nonneg f)]
  have hnorm : ‖V‖ ≤ (M * (C₀ + H * ‖P‖)) * (‖u‖ + ‖f‖) :=
    hVnorm.trans ((mul_le_mul_of_nonneg_left hinput hM).trans_eq (mul_assoc _ _ _).symm)
  refine ⟨V, lowerOrderCLM_mem_H10_of_base_ae V (cutoffH10 (HalfSpace.isOpen_upper n) η U)
    (by rw [hV]; exact .rfl), ?_, hnorm⟩
  rw [hV]
  exact baseCoord_cutoff_localizedHalfSpacePullbackCLM_ae hΩ a η κ hηtarget hκtarget
    (fun y hy ↦ (hκχnhds y (subset_tsupport χ.toFun
      (show χ.toFun y ≠ 0 by rw [hχη y hy]; norm_num))).eq_of_nhds) u

end PDE.Elliptic.Regularity.Quasilinear
