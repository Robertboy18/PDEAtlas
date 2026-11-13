/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakGronwall
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Finite-time H² bounds from locally bounded H² and uniform H¹

The weak transport calculation requires an H² bound only on compact interior
time intervals. Its Grönwall coefficient depends on H¹ alone. Comparing the
weak derivative at one fixed interior time therefore gives a single H² bound
all the way to a finite terminal time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace DeGregorio.Iteration

local notation "L₂" => Lp ℝ 2 (volume : Measure ℝ)

/-- Two compatible weak derivative rows assemble a quantitatively bounded
H² graph. -/
theorem exists_h2_graph_of_weak_jet
    {w q : ℝ → ℝ} {r : L₂}
    (hw : MemLp w 2 volume) (hq : MemLp q 2 volume)
    (hwq : HasWeakTimeDerivativeOn univ w q)
    (hqr : HasWeakTimeDerivativeOn univ q r) :
    ∃ W : W^{2,2}(ℝ^1),
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume] w ∧
      ‖W‖ ≤ succOrderAssemblyNormBound 1 1 *
        ((lpNorm w 2 volume + lpNorm q 2 volume) + (lpNorm q 2 volume + ‖r‖)) := by
  let U := mkW12OfWeakDerivative hw hq hwq
  let V := mkW12OfWeakDerivative hq (Lp.memLp r) hqr
  have hVU : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U := by
    simp only [U, V, realLineCoordinateCLM_mkW12_base, realLineCoordinateCLM_mkW12_single]
  obtain ⟨W, hbase, hnorm⟩ := exists_h2_of_realLine_h1_derivative U V hVU
  refine ⟨W, ?_, hnorm.trans ?_⟩
  · rw [hbase, realLineCoordinateCLM_mkW12_base]
    exact hw.coeFn_toLp
  · have hU : ‖U‖ ≤ lpNorm w 2 volume + lpNorm q 2 volume := by
      change ‖realLineH1Jet (hw.toLp w) (hq.toLp q)‖ ≤ _
      simpa only [Lp.norm_toLp, toReal_eLpNorm] using
        norm_realLineH1Jet_le (hw.toLp w) (hq.toLp q)
    have hV : ‖V‖ ≤ lpNorm q 2 volume + ‖r‖ := by
      change ‖realLineH1Jet (hq.toLp q) ((Lp.memLp r).toLp r)‖ ≤ _
      simpa only [Lp.toLp_coeFn, Lp.norm_toLp, toReal_eLpNorm] using
        norm_realLineH1Jet_le (hq.toLp q) r
    exact mul_le_mul_of_nonneg_left (add_le_add hU hV) succOrderAssemblyNormBound_nonneg

/-- The weak derivative of a continuous function is unique as an L² class. -/
theorem weak_derivative_l2_unique {q : ℝ → ℝ} {r s : L₂} (hq : Continuous q)
    (hr : HasWeakTimeDerivativeOn univ q r)
    (hs : HasWeakTimeDerivativeOn univ q s) : r = s := by
  apply Lp.ext
  filter_upwards [hr.ae_hasDerivAt_of_continuous hq, hs.ae_hasDerivAt_of_continuous hq]
    with x hx hy
  exact hx.unique hy

end DeGregorio.Iteration

namespace DeGregorio

local notation "e" => PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
local notation "L₂" => Lp ℝ 2 (volume : Measure ℝ)

/-- A rescaled solution on `I` is a rescaled solution on every `J ⊆ I`. -/
theorem IsClassicalRescaledSolutionOn.mono
    {fields : Fields} {a : ℝ} {cl cw : ℝ → ℝ} {I J : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw I) (hJI : J ⊆ I) :
    IsClassicalRescaledSolutionOn a fields cl cw J :=
  { regularity :=
      { vorticity_differentiableAt := fun {_ _} ht ↦
          hsol.regularity.vorticity_differentiableAt (hJI ht)
        velocity_differentiableAt := fun {_ _} ht ↦
          hsol.regularity.velocity_differentiableAt (hJI ht) }
    transport := fun {_ _} ht ↦ hsol.transport (hJI ht)
    biotSavart := fun {_} ht ↦ hsol.biotSavart (hJI ht) }

/-- Local H² boundedness and a uniform H¹ bound give a uniform supported
H² bound from any interior time to the finite endpoint. The initial weak
second derivative is constructed from the local graph. -/
theorem IsClassicalRescaledSolutionOn.exists_uniform_h2_of_local_h2_h1
    {fields : Fields} {ρ : ℝ → ℝ} {a t₀ T R M : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T) (hR : 0 < R) {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ}
    (hlocal : ∀ c d : ℝ, Icc c d ⊆ Ioo a T →
      ∃ B : NNReal, ∀ t ∈ Icc c d,
        F t ∈ supportedHkBaseBall 1 2 univ ((e) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ fields.vorticity x t))
    (hzero : ∀ t ∈ Ioo a T, fields.velocity 0 t = 0)
    (hnormalized : ∀ t ∈ Ioo a T, ρ t = -fields.velocity R t / R)
    (hH1 : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ fields.vorticity x t) 2 volume +
        lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ M) :
    ∃ r₀ : L₂,
      HasWeakTimeDerivativeOn univ (deriv (fun x ↦ fields.vorticity x t₀)) r₀ ∧
      ∀ t ∈ Ico t₀ T,
        F t ∈ supportedHkBaseBall 1 2 univ ((e) ⁻¹' K)
          (succOrderAssemblyNormBound 1 1 *
            (2 * M + Real.sqrt ((M ^ 2 + ‖r₀‖ ^ 2) * Real.exp (11 * M * (T - t₀))))) := by
  have hw (t : ℝ) (ht : t ∈ Ioo a T) :
      Continuous (fun x ↦ fields.vorticity x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  obtain ⟨B₀, hB₀⟩ := hlocal t₀ t₀ (by simpa only [Icc_self, singleton_subset_iff] using ht₀)
  obtain ⟨W₀, _, hW₀⟩ := (hB₀ t₀ ⟨le_rfl, le_rfl⟩).1
  obtain ⟨r₀, hreg₀, _, _, hr₀⟩ :=
    Iteration.exists_weak_secondDerivative_of_h2 W₀ (hw t₀ ht₀) (hW₀ ▸ hrep t₀ ht₀)
  refine ⟨r₀, hr₀, ?_⟩
  have hM : 0 ≤ M := (add_nonneg lpNorm_nonneg lpNorm_nonneg).trans (hH1 t₀ ht₀)
  intro t ht
  have htI : t ∈ Ioo a T := ⟨ht₀.1.trans_le ht.1, ht.2⟩
  obtain ⟨c, hac, hct₀⟩ := exists_between ht₀.1
  obtain ⟨d, htd, hdT⟩ := exists_between ht.2
  have hcd : Icc c d ⊆ Ioo a T := fun _ hs ↦
    ⟨hac.trans_le hs.1, hs.2.trans_lt hdT⟩
  have hsub : Ioo c d ⊆ Ioo a T := Ioo_subset_Icc_self.trans hcd
  obtain ⟨B, hB⟩ := hlocal c d hcd
  obtain ⟨r, hr, hg⟩ := (hsol.mono hsub).exists_secondDerivative_gronwall hR hK
    (fun s hs ↦ hB s (Ioo_subset_Icc_self hs))
    (fun s hs ↦ hrep s (hsub hs)) (fun s hs ↦ hzero s (hsub hs))
    (fun s hs ↦ hnormalized s (hsub hs)) (fun s hs ↦ hH1 s (hsub hs))
  have ht₀d : t₀ < d := ht.1.trans_lt htd
  have ht₀cd : t₀ ∈ Ioo c d := ⟨hct₀, ht₀d⟩
  have htcd : t ∈ Ioo c d := ⟨hct₀.trans_le ht.1, htd⟩
  have hrbase : r t₀ = r₀ := Iteration.weak_derivative_l2_unique
    (hreg₀.continuous_deriv le_rfl) (hr t₀ ht₀cd).2 hr₀
  obtain ⟨s, hts, hsd⟩ := exists_between htd
  have ht₀s : t₀ < s := ht.1.trans_lt hts
  have he := hg t₀ s ht₀s
    (fun _ hu ↦ ⟨hct₀.trans_le hu.1, hu.2.trans_lt hsd⟩) t ⟨ht.1, hts.le⟩
  rw [hrbase] at he
  let E := (M ^ 2 + ‖r₀‖ ^ 2) * Real.exp (11 * M * (T - t₀))
  have hE : 0 ≤ E :=
    mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.exp_pos _).le
  have hrnorm : ‖r t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    apply (le_add_of_nonneg_left (sq_nonneg M)).trans (he.trans ?_)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (sub_le_sub_right ht.2.le t₀) (mul_nonneg (by norm_num) hM)))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨W, _, hWbase⟩ := (hB t (Ioo_subset_Icc_self htcd)).1
  obtain ⟨_, _, hq, _, _⟩ :=
    Iteration.exists_weak_secondDerivative_of_h2 W (hw t htI) (hWbase ▸ hrep t htI)
  have hwLp : MemLp (fun x ↦ fields.vorticity x t) 2 volume :=
    (memLp_congr_ae (hrep t htI)).mp (Lp.memLp (oneDimensionalPushforwardL2 (F t)))
  obtain ⟨V, hVrep, hVnorm⟩ :=
    Iteration.exists_h2_graph_of_weak_jet hwLp hq (hr t htcd).1 (hr t htcd).2
  refine ⟨⟨V, hVnorm.trans ?_, ?_⟩, (hB t (Ioo_subset_Icc_self htcd)).2⟩
  · apply mul_le_mul_of_nonneg_left _ succOrderAssemblyNormBound_nonneg
    have hqnorm : lpNorm (deriv (fun x ↦ fields.vorticity x t)) 2 volume ≤ M :=
      (le_add_of_nonneg_left lpNorm_nonneg).trans (hH1 t htI)
    have hsum := add_le_add (hH1 t htI) (add_le_add hqnorm hrnorm)
    convert hsum using 1
    ring
  · apply oneDimensionalPushforwardL2.injective
    exact Lp.ext (hVrep.trans (hrep t htI).symm)

end DeGregorio
