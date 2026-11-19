/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.NormalizedEvolution
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative.Trace
import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import CAS.ExactTactic

/-!
# From classical H² energy to the closed Sobolev graph ball

Compact C² vorticity constructs compatible H¹ graphs for the function and its
first derivative. Their assembly gives an H² graph with a quantitative bound.
Consequently the classical energy estimate supplies membership in the L²-closed
H² ball used by finite terminal traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- An H¹ graph bound controls the two classical L² norms used in the coupled
energy coefficient. Continuity suffices to identify the representative. -/
theorem lpNorm_add_deriv_le_two_norm_h1 (U : W^{1,2}(ℝ^1)) {w : ℝ → ℝ}
    (hw : Continuous w)
    (hrep : (realLineCoordinateCLM (baseIndex 1 1) U : ℝ → ℝ) =ᵐ[volume] w) :
    lpNorm w 2 volume + lpNorm (deriv w) 2 volume ≤ 2 * ‖U‖ := by
  have heq : realLineRepresentative U = w :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative U) hw).mp
      ((realLineCoordinate_ae_representative U).symm.trans hrep)
  have hderiv := ae_deriv_realLineRepresentative U
  rw [heq] at hderiv
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, eLpNorm_congr_ae hrep.symm,
    eLpNorm_congr_ae hderiv, ← Lp.norm_def, ← Lp.norm_def]
  exact (add_le_add (norm_realLineCoordinateCLM_le _ U)
    (norm_realLineCoordinateCLM_le _ U)).trans_eq (two_mul ‖U‖).symm

/-- Compact C² data construct an H² graph with a bound from the three classical
L² derivative norms. -/
theorem exists_h2_graph_of_contDiff_two {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hc : HasCompactSupport w) :
    ∃ W : W^{2,2}(ℝ^1),
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume] w ∧
      ‖W‖ ≤ succOrderAssemblyNormBound 1 1 *
        ((lpNorm w 2 volume + lpNorm (deriv w) 2 volume) +
          (lpNorm (deriv w) 2 volume + lpNorm (deriv (deriv w)) 2 volume)) := by
  have hq : ContDiff ℝ 1 (deriv w) := hw.deriv'
  have hr : Continuous (deriv (deriv w)) := hq.continuous_deriv le_rfl
  have hwLp : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hc
  have hqLp : MemLp (deriv w) 2 volume := hq.continuous.memLp_of_hasCompactSupport hc.deriv
  have hrLp : MemLp (deriv (deriv w)) 2 volume := hr.memLp_of_hasCompactSupport hc.deriv.deriv
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc
    (hw.of_le (by norm_num)) one_ne_zero
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc.deriv hq one_ne_zero
  have hweak := Calculus.hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport hK hc
  have hweakq := Calculus.hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport hD hc.deriv
  let U := mkW12OfWeakDerivative hwLp hqLp hweak
  let V := mkW12OfWeakDerivative hqLp hrLp hweakq
  have hVU : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U := by
    simp only [U, V, realLineCoordinateCLM_mkW12_base, realLineCoordinateCLM_mkW12_single]
  obtain ⟨W, hbase, hnorm⟩ := exists_h2_of_realLine_h1_derivative U V hVU
  refine ⟨W, ?_, hnorm.trans ?_⟩
  · rw [hbase, realLineCoordinateCLM_mkW12_base]
    exact hwLp.coeFn_toLp
  · have hU : ‖U‖ ≤ lpNorm w 2 volume + lpNorm (deriv w) 2 volume := by
      change ‖realLineH1Jet (hwLp.toLp w) (hqLp.toLp (deriv w))‖ ≤ _
      simpa only [Lp.norm_toLp, toReal_eLpNorm] using
        norm_realLineH1Jet_le (hwLp.toLp w) (hqLp.toLp (deriv w))
    have hV : ‖V‖ ≤ lpNorm (deriv w) 2 volume + lpNorm (deriv (deriv w)) 2 volume := by
      change ‖realLineH1Jet (hqLp.toLp (deriv w)) (hrLp.toLp (deriv (deriv w)))‖ ≤ _
      simpa only [Lp.norm_toLp, toReal_eLpNorm] using
        norm_realLineH1Jet_le (hqLp.toLp (deriv w)) (hrLp.toLp (deriv (deriv w)))
    exact mul_le_mul_of_nonneg_left (add_le_add hU hV) succOrderAssemblyNormBound_nonneg

/-- A classical H² energy bound puts the represented L² slice in the closed
H² graph ball. The constant comes from `succOrderAssemblyNormBound`. -/
theorem mem_hkBaseBall_of_sobolevEnergyTwo_le
    {w : ℝ → ℝ → ℝ} {L t E : ℝ} {F : DerivLp 1 2 univ}
    (hw : ContDiff ℝ 2 (fun x ↦ w x t))
    (hsupp : tsupport (fun x ↦ w x t) ⊆ Icc (-L) L)
    (hrep : (oneDimensionalPushforwardL2 F : ℝ → ℝ) =ᵐ[volume] (fun x ↦ w x t))
    (henergy : sobolevEnergyTwo w L t ≤ E) :
    F ∈ hkBaseBall 1 2 univ (4 * succOrderAssemblyNormBound 1 1 * Real.sqrt E) := by
  let v := fun x ↦ w x t
  have hc : HasCompactSupport v :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hq : ContDiff ℝ 1 (deriv v) := hw.deriv'
  have hwLp : MemLp v 2 volume := hw.continuous.memLp_of_hasCompactSupport hc
  have hqLp : MemLp (deriv v) 2 volume := hq.continuous.memLp_of_hasCompactSupport hc.deriv
  have hrLp : MemLp (deriv (deriv v)) 2 volume :=
    (hq.continuous_deriv le_rfl).memLp_of_hasCompactSupport hc.deriv.deriv
  have hout (x : ℝ) (hx : x ∉ Icc (-L) L) :
      v x = 0 ∧ deriv v x = 0 ∧ deriv (deriv v) x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupp h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupp (tsupport_deriv_subset h))),
      image_eq_zero_of_notMem_tsupport
        (fun h ↦ hx (hsupp (tsupport_deriv_subset (tsupport_deriv_subset h))))⟩
  have hglobal₀ : (∫ x in Icc (-L) L, v x ^ 2) = ∫ x, v x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp only [(hout x hx).1, zero_pow (by decide : 2 ≠ 0)]
  have hglobal₁ : (∫ x in Icc (-L) L, deriv v x ^ 2) = ∫ x, deriv v x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp only [(hout x hx).2.1, zero_pow (by decide : 2 ≠ 0)]
  have hglobal₂ : (∫ x in Icc (-L) L, deriv (deriv v) x ^ 2) = ∫ x, deriv (deriv v) x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp only [(hout x hx).2.2, zero_pow (by decide : 2 ≠ 0)]
  have hsq : lpNorm v 2 volume ^ 2 + lpNorm (deriv v) 2 volume ^ 2 +
      lpNorm (deriv (deriv v)) 2 volume ^ 2 ≤ E := by
    change ((∫ x in Icc (-L) L, v x ^ 2) + (∫ x in Icc (-L) L, deriv v x ^ 2) +
      ∫ x in Icc (-L) L, deriv (deriv v) x ^ 2) ≤ E at henergy
    rw [hglobal₀, hglobal₁, hglobal₂] at henergy
    simpa only [integral_sq_eq_eLpNorm_toReal_sq hwLp, integral_sq_eq_eLpNorm_toReal_sq hqLp,
      integral_sq_eq_eLpNorm_toReal_sq hrLp, toReal_eLpNorm] using henergy
  have hE : 0 ≤ E := (sobolevEnergyTwo_nonneg w L t).trans henergy
  have hroot {b c d : ℝ} (hb : 0 ≤ b) (h : b ^ 2 + c ^ 2 + d ^ 2 ≤ E) : b ≤ √E := by
    apply (Real.le_sqrt hb hE).mpr
    exact (le_add_of_nonneg_right (sq_nonneg c) |>.trans
      (le_add_of_nonneg_right (sq_nonneg d))).trans h
  have hb₀ : lpNorm v 2 volume ≤ √E := hroot lpNorm_nonneg hsq
  have hb₁ : lpNorm (deriv v) 2 volume ≤ √E :=
    hroot (c := lpNorm v 2 volume) (d := lpNorm (deriv (deriv v)) 2 volume) lpNorm_nonneg
      (by simpa only [add_comm, add_left_comm, add_assoc] using hsq)
  have hb₂ : lpNorm (deriv (deriv v)) 2 volume ≤ √E :=
    hroot (c := lpNorm v 2 volume) (d := lpNorm (deriv v) 2 volume) lpNorm_nonneg
      (by simpa only [add_comm, add_left_comm, add_assoc] using hsq)
  obtain ⟨W, hWrep, hW⟩ := exists_h2_graph_of_contDiff_two hw hc
  refine ⟨W, hW.trans ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hb₀ hb₁) (add_le_add hb₁ hb₂))
      (succOrderAssemblyNormBound_nonneg (n := 1) (m := 1))
    convert h using 1
    cas
  · apply oneDimensionalPushforwardL2.injective
    exact Lp.ext (hWrep.trans hrep.symm)

/-- The same energy bound supplies the fixed support condition needed by
the finite trace theorem, using the support of the classical slice. -/
theorem mem_supportedHkBaseBall_of_sobolevEnergyTwo_le
    {w : ℝ → ℝ → ℝ} {L t E : ℝ} {F : DerivLp 1 2 univ}
    (hw : ContDiff ℝ 2 (fun x ↦ w x t))
    (hsupp : tsupport (fun x ↦ w x t) ⊆ Icc (-L) L)
    (hrep : (oneDimensionalPushforwardL2 F : ℝ → ℝ) =ᵐ[volume] (fun x ↦ w x t))
    (henergy : sobolevEnergyTwo w L t ≤ E) :
    F ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-L) L)
      (4 * succOrderAssemblyNormBound 1 1 * Real.sqrt E) := by
  let e := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  have hK : MeasurableSet (e ⁻¹' Icc (-L) L) :=
    measurableSet_Icc.preimage e.continuous.measurable
  apply (mem_supportedHkBaseBall_iff hK F).mpr
  refine ⟨mem_hkBaseBall_of_sobolevEnergyTwo_le hw hsupp hrep henergy, ?_⟩
  have hc : HasCompactSupport (fun x ↦ w x t) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hLp : MemLp (fun x ↦ w x t) 2 volume :=
    hw.continuous.memLp_of_hasCompactSupport hc
  have hF : F = oneDimensionalPullbackL2 (hLp.toLp (fun x ↦ w x t)) := by
    apply oneDimensionalPushforwardL2.injective
    rw [oneDimensionalPushforwardL2_pullback]
    exact Lp.ext (hrep.trans hLp.coeFn_toLp.symm)
  rw [hF]
  filter_upwards [oneDimensionalPullbackL2_toLp_ae hLp] with x hx
  intro hxK
  rw [hx]
  change w (e x) t = 0
  exact image_eq_zero_of_notMem_tsupport (f := fun y ↦ w y t)
    (fun hv ↦ hxK (hsupp hv))

end DeGregorio.Iteration

namespace DeGregorio

/-- The smooth normalized rescaled equation produces a single supported H²
ball for all times before the terminal time from an H¹ bound. This is the
uniform graph bound needed for the finite terminal trace. -/
theorem IsClassicalRescaledSolutionOn.mem_supportedHkBaseBall_of_h1On
    {fields : Fields} {ρ : ℝ → ℝ} {F : ℝ → DerivLp 1 2 univ} {L R B a t₀ T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (hw : ContDiffOn ℝ 3 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T) (hL : 0 ≤ L) (hR : 0 < R)
    (hsupp : ∀ t ∈ Ioo a T, tsupport (fun x ↦ fields.vorticity x t) ⊆ Ioo (-L) L)
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hinput : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t)) :
    ∀ t ∈ Ico t₀ T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-L) L)
      (4 * succOrderAssemblyNormBound 1 1 *
        Real.sqrt (sobolevEnergyTwo fields.vorticity L t₀ *
          Real.exp (11 * B * (T - t₀)))) := by
  intro t ht
  have htI : t ∈ Ioo a T := ⟨ht₀.1.trans_le ht.1, ht.2⟩
  apply Iteration.mem_supportedHkBaseBall_of_sobolevEnergyTwo_le
    (w := fields.vorticity)
  · exact (hw.of_le (by norm_num)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun x ↦ ⟨mem_univ x, htI⟩)
  · exact (hsupp t htI).trans Ioo_subset_Icc_self
  · exact hrep t htI
  · exact hsol.sobolevEnergyTwo_uniform_bound_of_h1On hw ht₀ hL hR hsupp hzero
      hnormalized hinput t ht

end DeGregorio
