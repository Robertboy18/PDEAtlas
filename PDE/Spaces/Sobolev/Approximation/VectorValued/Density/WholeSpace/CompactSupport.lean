/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.WholeSpace
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.CutoffConvergence
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.SmoothMultiplier
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff

/-!
# Compact smooth density in Banach-valued first-order Sobolev spaces

Expanding scalar cutoffs converge in the graph norm: their principal terms converge
in `Lp`, and their first derivatives vanish uniformly. Applying these cutoffs to
whole-space smooth approximants gives compact smooth representatives at every finite
exponent, including one, for arbitrary Banach codomains.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem tendsto_eLpNorm_cutoff_smul_sub (hp : p ≠ ∞)
    {f : ℝ^n → F} (hf : MemLp f p volume)
    {R : ℕ → ℝ} (hRpos : ∀ m, 0 < R m) (hR : Tendsto R atTop atTop) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ cutoff (R m) x • f x - f x) p volume)
      atTop (𝓝 0) := by
  have ht := tendsto_eLpNorm_cutoff_mul_sub hp hf.norm
    (fun _ ↦ hf.aestronglyMeasurable.norm)
    (by simp) hRpos hR
  apply ht.congr'
  filter_upwards [] with m
  apply eLpNorm_congr_norm_ae
    (((cutoff_contDiff (R m)).continuous.aestronglyMeasurable.mul
      hf.aestronglyMeasurable.norm).sub hf.aestronglyMeasurable.norm)
    (((cutoff_contDiff (R m)).continuous.aestronglyMeasurable.smul
      hf.aestronglyMeasurable).sub hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x ↦ by
    change ‖cutoff (R m) x * ‖f x‖ - ‖f x‖‖ = ‖cutoff (R m) x • f x - f x‖
    have he : cutoff (R m) x • f x - f x = (cutoff (R m) x - 1) • f x := by
      rw [sub_smul, one_smul]
    rw [he, ← sub_one_mul, norm_mul, norm_smul, norm_norm]

omit [CompleteSpace F] [Fact (1 ≤ p)] in
private theorem tendsto_eLpNorm_partial_cutoff_smul (i : Fin n)
    {f : ℝ^n → F} (hf : MemLp f p volume)
    {R : ℕ → ℝ} (hRpos : ∀ m, 0 < R m) (hR : Tendsto R atTop atTop) :
    Tendsto (fun m ↦ eLpNorm
      (fun x ↦ (∂[i] (cutoff (R m))) x • f x) p volume) atTop (𝓝 0) := by
  have ht := tendsto_eLpNorm_iteratedPartialDeriv_cutoff_mul [i] (by simp)
    hRpos hR (fun _ ↦ hf.aestronglyMeasurable.norm)
    hf.norm.eLpNorm_ne_top (fun _ ↦ le_rfl)
  apply ht.congr'
  filter_upwards [] with m
  have hd : AEStronglyMeasurable (iteratedPartialDeriv [i] (cutoff (R m))) volume :=
    (PDE.contDiff_top_iteratedPartialDeriv
      (cutoff_contDiff (R m)) [i]).continuous.aestronglyMeasurable
  apply eLpNorm_congr_norm_ae (hd.mul hf.aestronglyMeasurable.norm)
    (hd.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x ↦ by
    change ‖iteratedPartialDeriv [i] (cutoff (R m)) x * ‖f x‖‖ =
      ‖iteratedPartialDeriv [i] (cutoff (R m)) x • f x‖
    rw [norm_mul, norm_smul, norm_norm]

/-- Expanding compact smooth cutoffs converge to the identity in the first-order Banach
Sobolev graph at every finite exponent, including one. -/
theorem tendsto_compactSmoothMultiplierCLM_cutoff (hp : p ≠ ∞)
    (U : W^{1,p}(ℝ^n; F)) {R : ℕ → ℝ}
    (hRpos : ∀ m, 0 < R m) (hR : Tendsto R atTop atTop) :
    Tendsto (fun m ↦ compactSmoothMultiplierCLM (cutoff (R m))
      (cutoff_contDiff (R m)) (cutoff_hasCompactSupport (hRpos m).ne') U)
      atTop (𝓝 U) := by
  apply tendsto_subtype_rng.mpr
  apply ((PiLp.homeomorph p (fun _ : DerivIndex n 1 ↦
    Lp F p (domainMeasure n (⊤ : Opens ℝ^n)))).symm.continuous.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro a
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (U.val a)).mpr
  have hmem (b : DerivIndex n 1) : MemLp (U.val b : ℝ^n → F) p volume := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using Lp.memLp (U.val b)
  have hmain := tendsto_eLpNorm_cutoff_smul_sub hp (hmem a) hRpos hR
  have hrow (m : ℕ) :
      ((compactSmoothMultiplierCLM (cutoff (R m)) (cutoff_contDiff (R m))
        (cutoff_hasCompactSupport (hRpos m).ne') U).val a : ℝ^n → F)
        =ᵐ[volume] smoothLeibnizRepresentative (cutoff (R m)) U a.toList := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      compactSmoothMultiplierCLM_coordinate_ae (cutoff (R m)) (cutoff_contDiff (R m))
        (cutoff_hasCompactSupport (hRpos m).ne') U a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · apply hmain.congr'
    filter_upwards [] with m
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
    apply eLpNorm_congr_ae
    filter_upwards [hrow m] with x hx
    change cutoff (R m) x • U.val (baseIndex n 1) x - U.val (baseIndex n 1) x =
      (compactSmoothMultiplierCLM (cutoff (R m)) (cutoff_contDiff (R m))
        (cutoff_hasCompactSupport (hRpos m).ne') U).val (baseIndex n 1) x -
          U.val (baseIndex n 1) x
    simpa only [baseIndex_toList, smoothLeibnizRepresentative_nil] using
      congrArg (· - U.val (baseIndex n 1) x) hx.symm
  · have herr := tendsto_eLpNorm_partial_cutoff_smul i (hmem (baseIndex n 1)) hRpos hR
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hmain.add herr) (fun _ ↦ bot_le) fun m ↦ ?_
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
    calc
      _ = eLpNorm ((fun x ↦ cutoff (R m) x • U.val (singleDerivIndex n i) x -
          U.val (singleDerivIndex n i) x) +
          fun x ↦ (∂[i] (cutoff (R m))) x • U.val (baseIndex n 1) x) p volume := by
        apply eLpNorm_congr_ae
        filter_upwards [hrow m] with x hx
        change (compactSmoothMultiplierCLM (cutoff (R m)) (cutoff_contDiff (R m))
          (cutoff_hasCompactSupport (hRpos m).ne') U).val (singleDerivIndex n i) x -
            U.val (singleDerivIndex n i) x = _
        rw [hx]
        rw [singleDerivIndex_toList]
        simp only [smoothLeibnizRepresentative,
          List.reverse_cons, List.reverse_nil, List.nil_append, derivativeSplits,
          List.map_cons, List.map_nil, List.cons_append, List.sum_cons, List.sum_nil,
          iteratedPartialDeriv, wordRepresentative, List.length_singleton, le_refl,
          ↓reduceDIte, List.length_nil, Nat.zero_le, derivIndexOfList_nil,
          add_zero, Pi.add_apply]
        simp only [singleDerivIndex]
        abel
      _ ≤ _ := eLpNorm_add_le (Fact.out : 1 ≤ p)

/-- Compactly supported ambient smooth representatives are dense in whole-space
first-order Sobolev spaces with any Banach codomain and finite exponent. -/
theorem dense_compact_smooth_univ (hp : p ≠ ∞) :
    Dense {U : W^{1,p}(ℝ^n; F) | ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨V, f, hf, hbase, hVU⟩ :=
    exists_smooth_approximation_univ (standardMollifier n) hp U (half_pos hδ)
  let R (m : ℕ) : ℝ := m + 1
  have hRpos (m : ℕ) : 0 < R m := by dsimp [R]; positivity
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht := tendsto_compactSmoothMultiplierCLM_cutoff hp V hRpos hR
  obtain ⟨m, hm⟩ := (((ht.sub tendsto_const_nhds).norm).eventually
    (gt_mem_nhds (show ‖V - V‖ < δ / 2 by simpa using half_pos hδ))).exists
  let A := compactSmoothMultiplierCLM (cutoff (R m)) (cutoff_contDiff (R m))
    (cutoff_hasCompactSupport (hRpos m).ne') V
  refine ⟨A, ⟨fun x ↦ cutoff (R m) x • f x, (cutoff_contDiff (R m)).smul hf,
    (cutoff_hasCompactSupport (hRpos m).ne').smul_right, ?_⟩, ?_⟩
  · have ha := compactSmoothMultiplierCLM_base_ae (cutoff (R m))
      (cutoff_contDiff (R m)) (cutoff_hasCompactSupport (hRpos m).ne') V
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at ha
    filter_upwards [ha, hbase] with x hx hv
    exact hx.trans (congrArg (cutoff (R m) x • ·) hv)
  · rw [dist_eq_norm, norm_sub_rev]
    exact (norm_sub_le_norm_sub_add_norm_sub A V U).trans_lt
      ((add_lt_add hm hVU).trans_eq (add_halves δ))

end SobolevSpace.VectorValued
