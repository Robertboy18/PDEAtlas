/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Uniqueness.Classical
public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Bootstrap
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.PhysicalRecognition
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.SupportedContinuity
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.SupportedRepresentative

/-!
# Persistence of smoothness for classical De Gregorio solutions

A classical solution of the De Gregorio equation on `[0, T)` (`IsClassicalSolutionFrom`) whose
vorticity slices are bounded in H² on every `[0, T']` with `T' < T` stays `C^∞` in space if its
datum is `C^∞` with compact support: every slice `ω (·, t)`, `t ∈ [0, T)`, is `C^∞`.

On `[0, T']` the slices form an `L²`-continuous curve whose values have uniformly bounded H²
graphs with a common support, so the solution is a coupled H² output
(`exists_isHkFrozenOutput_of_classical`), and the derivative towers of
`IsHkFrozenOutput.contDiff_vorticity` apply on the whole of `[0, T']`. The H² bound is the
regularity in which the local theory is set; it is an additional hypothesis, not derived from
the classical class.

## Main results

* `IsClassicalSolutionFrom.contDiff_vorticity`: persistence of `C^∞` spatial regularity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped ContDiff Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio

namespace IsClassicalSolutionFrom

variable {w₀ : ℝ → ℝ} {T : ℝ} {fields : Fields}

/-- A classical solution from a smooth compactly supported datum, whose vorticity slices are
bounded in H² on every `[0, T']` with `T' < T`, has `C^∞` vorticity slices at every time of
`[0, T)`. -/
theorem contDiff_vorticity (h : IsClassicalSolutionFrom w₀ T fields)
    (hw₀ : ContDiff ℝ ∞ w₀) (hc₀ : HasCompactSupport w₀)
    (hH2 : ∀ T' < T, ∃ B : ℝ, ∀ t ∈ Icc 0 T', ∃ V : W^{2,2}(ℝ^1), ‖V‖ ≤ B ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM V) : ℝ → ℝ) =ᵐ[volume]
        fun x ↦ fields.vorticity x t)
    {t : ℝ} (ht : t ∈ Ico 0 T) : ContDiff ℝ ∞ (fun x ↦ fields.vorticity x t) := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    simpa only [h.initial] using hw₀
  obtain ⟨B, hB⟩ := hH2 t ht.2
  obtain ⟨L, C, hL, -, hsupp, -⟩ := h.exists_bounds ht.2
  choose V hVb hVrep using fun s : Icc (0 : ℝ) t ↦ hB s s.property
  let B' : NNReal := ⟨max B 0, le_max_right _ _⟩
  have hsub : (univ : Set ℝ) ×ˢ Icc 0 t ⊆ univ ×ˢ Ico 0 T :=
    fun p hp ↦ ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt ht.2⟩
  have hw : Continuous (fun p : ℝ × Icc (0 : ℝ) t ↦ fields.vorticity p.1 p.2) :=
    (h.vorticity_contDiffOn.continuousOn.mono hsub).comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ ⟨mem_univ _, p.2.property⟩)
  have hs (s : Icc (0 : ℝ) t) : Function.support (fun x ↦ fields.vorticity x s) ⊆ Icc (-L) L := by
    intro x hx
    by_contra hnot
    apply hx
    apply hsupp s s.property x
    rw [mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with hlt | hlt
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact hlt.le
  have hbase := Iteration.continuous_base_of_common_compact_support
    (f := fun s : Icc (0 : ℝ) t ↦ wkpBaseCoordinateCLM (V s))
    (w := fun s x ↦ fields.vorticity x s) isCompact_Icc hw hs hVrep
  let F : C(Icc (0 : ℝ) t, supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-L) L) B') :=
    ⟨fun s ↦ ⟨wkpBaseCoordinateCLM (V s),
      Iteration.mem_supportedHkBaseBall_of_real_representative measurableSet_Icc
        ⟨V s, (hVb s).trans (le_max_left _ _), rfl⟩ (hVrep s) (hs s)⟩,
      hbase.subtype_mk _⟩
  have hsol : IsClassicalSolutionOn 1 fields (Ioo 0 t) :=
    h.isClassicalSolutionOn fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  obtain ⟨W₀, c, hout⟩ := Iteration.exists_isHkFrozenOutput_of_classical hpos.le F hsol hw
    (fun s ↦ hVrep s)
    (fun s _ ↦ closure_minimal (hs ⟨s, by assumption⟩) isClosed_Icc)
    (fun s hs ↦ h.velocity_zero s ⟨hs.1.le, hs.2.trans ht.2⟩)
  have hinit : (fun x ↦ fields.vorticity x 0) = w₀ := funext h.initial
  rw [hinit] at hout
  exact hout.contDiff_vorticity hw₀ hc₀ ⟨hpos.le, le_rfl⟩

end IsClassicalSolutionFrom

end DeGregorio
