/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.H2Persistence
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Compact truncations of local Sobolev Cauchy data

The local Sobolev predicate admits arbitrary data on every relatively
compact open set. Smooth cutoff extension produces whole-space data agreeing
with them on any prescribed compact set, at the same Sobolev order. Applying
the first-jet wave construction gives global truncated solutions.

This is the data extension step in the localization argument. Agreement of different truncated
solutions in interior cones requires finite propagation.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

variable {n k : ℕ} {g : ℝ^n → ℝ}

/-- Arbitrary local Sobolev data admit a whole-space truncation at the same
order, agreeing almost everywhere on any prescribed compact set. -/
theorem exists_sobolev_truncation_on_compact
    (hg : IsLocallyWkpOn k 2 univ g) {K : Set (ℝ^n)} (hK : IsCompact K) :
    ∃ G : W^{k,2}(ℝ^n), baseRepresentative G =ᵐ[volume.restrict K] g := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  obtain ⟨U, hU⟩ := hg V hV hVc hVU
  obtain ⟨κ, hκV, hκone, _, _⟩ := TestFunction.exists_eq_one_on_compact hV hK hKV
  let G := extendByCutoff hV (subset_univ V) κ hκV U
  have hG := extendByCutoff_base_ae hV (subset_univ V) κ hκV U
  simp only [domainMeasure, Measure.restrict_univ] at hG
  have hUK : baseRepresentative U =ᵐ[volume.restrict K] g :=
    ae_restrict_of_ae_restrict_of_subset hKV hU
  refine ⟨G, ?_⟩
  filter_upwards [hG.filter_mono (ae_mono Measure.restrict_le_self), hUK,
    ae_restrict_mem hK.measurableSet] with y hy hUy hyK
  rw [hy, hκone y hyK, one_mul, hUy]

/-- Local H¹ displacement and local L² velocity give whole-space energy
solutions whose initial values agree with both data on a chosen compact set.
Local L² is expressed as the order-zero local Sobolev predicate. -/
theorem exists_energySolution_truncation {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ} (hg : IsLocallyWkpOn 1 2 univ g)
    (hv : IsLocallyWkpOn 0 2 univ v) {K : Set (ℝ^n)} (hK : IsCompact K) :
    ∃ x : H¹(ℝ^n) × DerivLp n 2 univ, baseRepresentative x.1 =ᵐ[volume.restrict K] g ∧
      (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict K] v ∧ ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      IsEnergySolution hf hf0 x u := by
  obtain ⟨G, hG⟩ := exists_sobolev_truncation_on_compact hg hK
  obtain ⟨V, hV⟩ := exists_sobolev_truncation_on_compact hv hK
  exact ⟨(G, wkpBaseCoordinateCLM V), hG, hV,
    exists_energySolution hf hf0 (G, wkpBaseCoordinateCLM V)⟩

/-- Local H² × H¹ data admit truncated solutions with the exact H² persistence
regularity. The truncation imposes no stronger local hypothesis on either datum. -/
theorem exists_h2_energySolution_truncation
    {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    {g v : ℝ^n → ℝ} (hg : IsLocallyWkpOn 2 2 univ g)
    (hv : IsLocallyWkpOn 1 2 univ v) {K : Set (ℝ^n)} (hK : IsCompact K) :
    ∃ (G : W^{2,2}(ℝ^n)) (V : H¹(ℝ^n)),
      baseRepresentative G =ᵐ[volume.restrict K] g ∧
      baseRepresentative V =ᵐ[volume.restrict K] v ∧
      ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
        IsEnergySolution hf hf0
          (lowerOrderCLM (by decide : 1 ≤ 2) G, (energyTriple n).inclusion V) u ∧
        ∀ T : ℝ, ∃ (U : ℝ → W^{2,2}(ℝ^n)) (W : ℝ → H¹(ℝ^n))
          (A : ℝ → DerivLp n 2 univ),
          MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
          MemLp W ∞ (volume.restrict (Icc 0 T)) ∧
          MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
          ∀ t ∈ Icc (0 : ℝ) T,
            lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
            (energyTriple n).inclusion (W t) = (u t).2 ∧
            (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t) ∧
            A t = wkpLaplacianCLM (U t) - reaction hf hf0 (u t) := by
  obtain ⟨G, hG⟩ := exists_sobolev_truncation_on_compact hg hK
  obtain ⟨V, hV⟩ := exists_sobolev_truncation_on_compact hv hK
  exact ⟨G, V, hG, hV, exists_energySolution_h2 hf hf0 G V⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
