/-
Copyright (c) 2021 Yury Kudryashov, 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, LeanPDE Team
-/

module

public import Mathlib.Analysis.BoxIntegral.Box.SubboxInduction
public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Induction under coordinatewise contracting subdivision

Mathlib's subbox induction uses central bisection in every coordinate. Here each
coordinate may have its own fixed division factor. The nested-box proof is adapted
from `BoxIntegral.Box.subbox_induction_on'`; boxes and prepartitions are Mathlib's.
-/

@[expose] public noncomputable section

open Set Function Filter
open scoped Topology

namespace BoxIntegral.Box

variable {ι : Type*}

/-- Subbox induction for a subdivision with a fixed, strictly contracting factor in
each coordinate. The neighborhood condition only concerns boxes with the resulting
coordinate side lengths. The factors need not be equal or have bounded ratios. -/
@[elab_as_elim]
theorem subbox_induction_on_division {p : Box ι → Prop} (I : Box ι)
    (division : ι → ℝ) (hdivision : ∀ i, 1 < division i)
    (split : ∀ J : Box ι, Prepartition J)
    (hside : ∀ J K, K ∈ split J → ∀ i,
      K.upper i - K.lower i = (J.upper i - J.lower i) / division i)
    (H_ind : ∀ J ≤ I, (∀ K ∈ split J, p K) → p J)
    (H_nhds : ∀ z ∈ I.Icc, ∃ U ∈ 𝓝[I.Icc] z, ∀ J ≤ I, ∀ m : ℕ,
      z ∈ J.Icc → J.Icc ⊆ U →
      (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / division i ^ m) → p J) :
    p I := by
  classical
  let : Inhabited (Box ι) := ⟨I⟩
  by_contra hpI
  have H_bad : ∀ J ≤ I, ¬p J → ∃ K ∈ split J, ¬p K := by
    intro J hJI hpJ
    by_contra h
    push Not at h
    exact hpJ (H_ind J hJI h)
  choose! K hKmem hKp using H_bad
  let J : ℕ → Box ι := fun m ↦ K^[m] I
  have J_succ : ∀ m, J (m + 1) = K (J m) :=
    fun m ↦ iterate_succ_apply' _ _ _
  have hJ : ∀ m, J m ≤ I ∧ ¬p (J m) := by
    intro m
    induction m with
    | zero => exact ⟨le_rfl, hpI⟩
    | succ m hm =>
      rw [J_succ]
      exact ⟨((split (J m)).le_of_mem (hKmem (J m) hm.1 hm.2)).trans hm.1,
        hKp (J m) hm.1 hm.2⟩
  have hJmono : Antitone J :=
    antitone_nat_of_succ_le fun m ↦ by
      rw [J_succ]
      exact (split (J m)).le_of_mem (hKmem (J m) (hJ m).1 (hJ m).2)
  have hJsub (m : ℕ) (i : ι) :
      (J m).upper i - (J m).lower i =
        (I.upper i - I.lower i) / division i ^ m := by
    induction m with
    | zero => simp [J]
    | succ m hm =>
      rw [J_succ, hside _ _ (hKmem (J m) (hJ m).1 (hJ m).2), hm, div_div, pow_succ]
  let z : ι → ℝ := ⨆ m, (J m).lower
  have hzJ : ∀ m, z ∈ (J m).Icc :=
    mem_iInter.1 (ciSup_mem_iInter_Icc_of_antitone_Icc
      ((@Box.Icc ι).monotone.comp_antitone hJmono) fun m ↦ (J m).lower_le_upper)
  have hJl_mem : ∀ m, (J m).lower ∈ I.Icc :=
    fun m ↦ le_iff_Icc.1 (hJ m).1 (J m).lower_mem_Icc
  have hJu_mem : ∀ m, (J m).upper ∈ I.Icc :=
    fun m ↦ le_iff_Icc.1 (hJ m).1 (J m).upper_mem_Icc
  have hJlz : Tendsto (fun m ↦ (J m).lower) atTop (𝓝 z) :=
    tendsto_atTop_ciSup (antitone_lower.comp hJmono)
      ⟨I.upper, fun x ⟨m, hm⟩ ↦ hm ▸ (hJl_mem m).2⟩
  have hJuz : Tendsto (fun m ↦ (J m).upper) atTop (𝓝 z) := by
    suffices Tendsto (fun m ↦ (J m).upper - (J m).lower) atTop (𝓝 0) by
      simpa using hJlz.add this
    refine tendsto_pi_nhds.2 fun i ↦ ?_
    simpa [hJsub] using
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (hdivision i))
  replace hJlz : Tendsto (fun m ↦ (J m).lower) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJlz
      (Eventually.of_forall hJl_mem)
  replace hJuz : Tendsto (fun m ↦ (J m).upper) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJuz
      (Eventually.of_forall hJu_mem)
  obtain ⟨U, hUz, hU⟩ := H_nhds z (hzJ 0)
  obtain ⟨m, hUm⟩ := (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists
  exact (hJ m).2 (hU (J m) (hJ m).1 m (hzJ m) hUm (hJsub m))

end BoxIntegral.Box
