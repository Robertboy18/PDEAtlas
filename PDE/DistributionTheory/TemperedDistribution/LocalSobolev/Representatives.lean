/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Sobolev

/-!
# Representatives of compact Sobolev localizations

A smooth compact cutoff converts local L² data to global L² data. If the cutoff
distribution has a Sobolev order, the L∞-L² product has that same order and
agrees with the original representative wherever the cutoff equals one.

Both the first-order estimate for divergence data and the second-order estimate
for Poisson data use these facts.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A compact Schwartz cutoff turns locally L² data into a global L² function. -/
theorem memLp_cutoff_of_locally_memLp {Ω : Set E} {u : E → F}
    (hu : ∀ K : Set E, IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K))
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) :
    MemLp (fun x ↦ a x • u x) 2 volume := by
  have hi : MemLp ((tsupport a).indicator u) 2 volume :=
    (memLp_indicator_iff_restrict
      (isClosed_tsupport (a : E → ℂ)).measurableSet.nullMeasurableSet).mpr
      (hu _ ha haΩ)
  have hmul : MemLp ((a : E → ℂ) • (tsupport a).indicator u) 2 volume :=
    (a.memLp_top volume).smul hi
  have heq : (a : E → ℂ) • (tsupport a).indicator u = fun x ↦ a x • u x := by
    funext x
    by_cases hx : x ∈ tsupport a
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport hx]
  rwa [heq] at hmul

variable [CompleteSpace F]

/-- An L² cutoff has the original integral pairing wherever the cutoff is one. -/
theorem cutoff_pairing (a : 𝓢(E, ℂ)) (u : E → F)
    (hu : MemLp (fun x ↦ a x • u x) 2 volume) (φ : 𝓢(E, ℂ))
    (hflat : ∀ x ∈ tsupport φ, a x = 1) :
    ((hu.toLp (fun x ↦ a x • u x) : Lp F 2 volume) : 𝓢'(E, F)) φ =
      ∫ x, φ x • u x := by
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx]
  by_cases hφ : φ x = 0
  · simp [hφ]
  · rw [hflat x (subset_tsupport φ hφ), one_smul]

/-- A Sobolev cutoff distribution has an L² representative of the same order,
equal to the original data on the set where the cutoff is one. -/
theorem exists_memSobolev_ae_eq_of_cutoff
    (χ : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E))
    {V : Set E} (hV : MeasurableSet V) (hχone : ∀ x ∈ V, χ x = 1)
    {s : ℝ} (hs : MemSobolev s 2 (smulLeftCLM F χ (u : 𝓢'(E, F)))) :
    ∃ U : Lp F 2 (volume : Measure E),
      MemSobolev s 2 (U : 𝓢'(E, F)) ∧ (U : E → F) =ᵐ[volume.restrict V] u := by
  let U : Lp F 2 volume := (χ.memLp_top volume).toLp χ • u
  have hUdist : (U : 𝓢'(E, F)) = smulLeftCLM F χ (u : 𝓢'(E, F)) :=
    Lp.toTemperedDistribution_smul_eq (p := ⊤) (q := 2) (r := 2)
      χ.hasTemperateGrowth (χ.memLp_top volume) u
  refine ⟨U, ?_, ?_⟩
  · rw [hUdist]
    exact hs
  · filter_upwards [ae_restrict_mem hV,
      ae_restrict_of_ae (Lp.coeFn_lpSMul (r := 2) ((χ.memLp_top volume).toLp χ) u),
      ae_restrict_of_ae (χ.memLp_top volume).coeFn_toLp] with x hx hUx hχx
    calc
      U x = ((χ.memLp_top volume).toLp χ) x • u x := hUx
      _ = u x := by rw [hχx, hχone x hx, one_smul]

end TemperedDistribution
