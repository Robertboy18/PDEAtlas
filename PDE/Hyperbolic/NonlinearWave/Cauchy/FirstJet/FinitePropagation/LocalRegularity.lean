/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalPatching
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalReaction
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# Local Sobolev regularity of the patched first-jet wave

The patched field has strongly continuous local H¹ × L² representatives.
For arbitrary local H² × H¹ data these representatives have bounded H²
displacement, H¹ velocity and L² acceleration on every finite cylinder.
The acceleration is the time derivative and equals the weak Laplacian
minus the full first-jet reaction. Only global Lipschitz continuity of the
reaction is used, as in Evans, §12.2.1, whose hypothesis (2) for Theorem 1(ii) is that `f` is
Lipschitz continuous.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, equation (2) and Theorem 1(ii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- A field represented on each bounded finite cylinder by a
whole-space weak energy wave. This property is obtained by finite propagation. -/
def HasLocalEnergyModels (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (w : ℝ → ℝ^n → ℝ × ℝ) : Prop :=
  ∀ {V : Set (ℝ^n)}, Bornology.IsBounded V → ∀ T : ℝ,
    ∃ (x : H¹(ℝ^n) × DerivLp n 2 univ)
      (u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)), IsEnergySolution hf hf0 x u ∧
      ∀ t ∈ Icc (0 : ℝ) T, w t =ᵐ[volume.restrict V] stateRepresentative (u t)

/-- Restricting the natural state gives the same pair of scalar fields locally. -/
theorem restrictStateCLM_representative_ae {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    (fun y ↦ (baseRepresentative (restrictStateCLM hΩ z).1 y, (restrictStateCLM hΩ z).2 y))
      =ᵐ[domainMeasure n Ω] stateRepresentative z := by
  filter_upwards [restrictCLM_apply_ae hΩ (subset_univ Ω) z.1 (baseIndex n 1),
    restrictDerivLp_apply_ae (subset_univ Ω) z.2] with y hq hv
  exact Prod.ext hq hv

/-- On each finite cylinder, the patched functions have one strongly
continuous local energy representative. -/
theorem HasLocalEnergyModels.exists_continuous_local_curve {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {w : ℝ → ℝ^n → ℝ × ℝ} (hw : HasLocalEnergyModels hf hf0 w) {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hb : Bornology.IsBounded Ω) (T : ℝ) :
    ∃ q : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω), ∀ t ∈ Icc (0 : ℝ) T, w t =ᵐ[domainMeasure n Ω] fun y ↦
      (baseRepresentative (q t).1 y, (q t).2 y) := by
  obtain ⟨x, u, _, hu⟩ := hw hb T
  refine ⟨⟨fun t ↦ restrictStateCLM hΩ (u t),
    (restrictStateCLM hΩ).continuous.comp u.continuous⟩, ?_⟩
  intro t ht
  exact (hu t ht).trans (restrictStateCLM_representative_ae hΩ (u t)).symm

/-- The patched displacement and velocity have the asserted local Sobolev
orders at every nonnegative time. -/
theorem HasLocalEnergyModels.local_sobolev {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {w : ℝ → ℝ^n → ℝ × ℝ} (hw : HasLocalEnergyModels hf hf0 w) {t : ℝ} (ht : 0 ≤ t) :
    IsLocallyWkpOn 1 2 univ (fun y ↦ (w t y).1) ∧ IsLocallyWkpOn 0 2 univ (fun y ↦ (w t y).2) := by
  constructor
  · intro Ω hΩ hc _
    obtain ⟨q, hq⟩ := hw.exists_continuous_local_curve hΩ.measurableSet
      (hc.isBounded.subset subset_closure) t
    exact ⟨(q t).1, (hq t ⟨ht, le_rfl⟩).symm.mono fun _ h ↦ congrArg Prod.fst h⟩
  · intro Ω hΩ hc _
    obtain ⟨q, hq⟩ := hw.exists_continuous_local_curve hΩ.measurableSet
      (hc.isBounded.subset subset_closure) t
    exact ⟨lpToZeroOrder (q t).2, (hq t ⟨ht, le_rfl⟩).symm.mono fun _ h ↦ congrArg Prod.snd h⟩

/-- The whole-space H² persistence property retained during spatial patching. -/
def HasH2Lifts (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) : Prop :=
  ∀ T : ℝ, ∃ (U : ℝ → W^{2,2}(ℝ^n)) (V : ℝ → H¹(ℝ^n))
    (A : ℝ → DerivLp n 2 univ),
    MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
    MemLp V ∞ (volume.restrict (Icc 0 T)) ∧
    MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
    ∀ t ∈ Icc (0 : ℝ) T,
      lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
      (energyTriple n).inclusion (V t) = (u t).2 ∧
      (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t) ∧
      A t = wkpLaplacianCLM (U t) - reaction hf hf0 (u t)

/-- Whole-space H² persistence restricts to the exact local H²/H¹/L²
bounds, the time derivative, and the full first-jet PDE in local L². -/
theorem IsEnergySolution.local_h2_persistence
    {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : IsEnergySolution hf hf0 x u) (hl : HasH2Lifts hf hf0 u)
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∃ (U : ℝ → W^{2,2}(Ω)) (V : ℝ → W^{1,2}(Ω)) (A : ℝ → DerivLp n 2 Ω),
      MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
      MemLp V ∞ (volume.restrict (Icc 0 T)) ∧
      MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (restrictStateCLM hΩ (u t)).1 ∧
        wkpBaseCoordinateCLM (V t) = (restrictStateCLM hΩ (u t)).2 ∧
        A t = wkpLaplacianCLM (U t) - localReaction hf hf0 (restrictStateCLM hΩ (u t))) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T),
        HasDerivAt (fun s ↦ restrictStateCLM hΩ (u s)) (V t, A t) t := by
  obtain ⟨U, V, A, hU, hV, hA, hr⟩ := hl T
  let R₂ : W^{2,2}(ℝ^n) →L[ℝ] W^{2,2}(Ω) := restrictCLM hΩ (subset_univ Ω)
  let R₁ : H¹(ℝ^n) →L[ℝ] W^{1,2}(Ω) := restrictCLM hΩ (subset_univ Ω)
  let R₀ : DerivLp n 2 univ →L[ℝ] DerivLp n 2 Ω := restrictDerivLp (subset_univ Ω)
  refine ⟨fun t ↦ R₂ (U t), fun t ↦ R₁ (V t), fun t ↦ R₀ (A t),
    R₂.comp_memLp' hU, R₁.comp_memLp' hV, R₀.comp_memLp' hA, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · exact (restrictCLM_lowerOrderCLM_apply hΩ (subset_univ Ω) (by decide : 1 ≤ 2)
        (U t)).symm.trans (congrArg R₁ (hr t ht).1)
    · exact congrArg R₀ (hr t ht).2.1
    · change restrictDerivLp (subset_univ Ω) (A t) = _
      rw [(hr t ht).2.2.2, map_sub, ← laplacian_restrict hΩ, ← localReaction_restrict hf hf0 hΩ]
  · have hd := (hu.absolutelyContinuous_of_lifts hT hV hA
      (fun t ht ↦ (hr t ht).2.1) (fun t ht ↦ (hr t ht).2.2.1)).2
    filter_upwards [hd] with t ht
    have h := (restrictStateCLM (n := n) (Ω := Ω) hΩ).hasFDerivAt (x := u t) |>.comp_hasDerivAt t ht
    exact h

/-- Local H²/H¹/L² persistence, with the weak PDE and the energy-state
time derivative on every finite bounded cylinder. -/
def HasLocalH2Regularity (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (w : ℝ → ℝ^n → ℝ × ℝ) : Prop :=
  ∀ {Ω : Set (ℝ^n)}, MeasurableSet Ω → Bornology.IsBounded Ω →
    ∀ T : ℝ, 0 ≤ T →
    ∃ (q : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω))
      (U : ℝ → W^{2,2}(Ω)) (V : ℝ → W^{1,2}(Ω)) (A : ℝ → DerivLp n 2 Ω),
      MemLp U ∞ (volume.restrict (Icc 0 T)) ∧
      MemLp V ∞ (volume.restrict (Icc 0 T)) ∧
      MemLp A ∞ (volume.restrict (Icc 0 T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        (w t =ᵐ[domainMeasure n Ω] fun y ↦ (baseRepresentative (q t).1 y, (q t).2 y)) ∧
        lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (q t).1 ∧
        wkpBaseCoordinateCLM (V t) = (q t).2 ∧
        A t = wkpLaplacianCLM (U t) - localReaction hf hf0 (q t)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 T), HasDerivAt q (V t, A t) t

/-- Arbitrary local H² displacement and local H¹ velocity admit a global
forward patched wave with bounded local H²/H¹/L² derivatives on every finite
cylinder. The lower local energy curve is strongly continuous and satisfies
the full first-jet equation in local L². -/
theorem exists_patched_local_h2_fields (hf : LipschitzWith L f) (hf0 : f 0 = 0) {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 2 2 univ g) (hv : IsLocallyWkpOn 1 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ, (∀ i : ℕ, w 0 =ᵐ[volume.restrict (ball 0 ((i : ℝ) + 1))] fun y ↦
      (g y, v y)) ∧ HasLocalEnergyModels hf hf0 w ∧ HasLocalH2Regularity hf hf0 w := by
  have hext (K : Set (ℝ^n)) (hK : IsCompact K) : ∃ x : H¹(ℝ^n) × DerivLp n 2 univ,
        baseRepresentative x.1 =ᵐ[volume.restrict K] g ∧ (x.2 : ℝ^n → ℝ) =ᵐ[volume.restrict K] v ∧
        ∃ u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
          IsEnergySolution hf hf0 x u ∧ HasH2Lifts hf hf0 u := by
    obtain ⟨G, V, hG, hV, u, hu, hl⟩ := exists_h2_energySolution_truncation hf hf0 hg hv hK
    exact ⟨(lowerOrderCLM (by decide : 1 ≤ 2) G, (energyTriple n).inclusion V), hG, hV, u, hu, hl⟩
  obtain ⟨w, hw0, hw⟩ := exists_patched_local_energy_fields_of_extensions hf hf0 hext
  refine ⟨w, hw0, ?_, ?_⟩
  · intro Ω hb T
    obtain ⟨x, u, hu, _, heq⟩ := hw hb T
    exact ⟨x, u, hu, heq⟩
  · intro Ω hΩ hb T hT
    obtain ⟨x, u, hu, hl, heq⟩ := hw hb T
    obtain ⟨U, V, A, hU, hV, hA, hr, hd⟩ := hu.local_h2_persistence hl hΩ hT
    let q : C(ℝ, W^{1,2}(Ω) × DerivLp n 2 Ω) :=
      ⟨fun t ↦ restrictStateCLM hΩ (u t), (restrictStateCLM hΩ).continuous.comp u.continuous⟩
    refine ⟨q, U, V, A, hU, hV, hA, ?_, hd⟩
    intro t ht
    exact ⟨(heq t ht).trans (restrictStateCLM_representative_ae hΩ (u t)).symm, hr t ht⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
