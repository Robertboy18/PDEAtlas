/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.LocalConvergence
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Local reaction limits of truncated energy waves

Joint representatives can be constructed after choosing the displacement subsequence. Strong
convergence of compact spatial observations then gives local spacetime L² convergence and identifies
the arbitrary-growth reaction in local L¹. Its integrability follows from the truncated PDE and
common energy bound, without a growth restriction on the original reaction. This is the convergence
(9) of step 5 of the proof of Theorem 1 of Evans, §12.3.1, for the subsequence chosen in step 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.1, steps 2 and 5 of the proof of Theorem 1,
  equation (9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev SobolevSpace.WholeSpaceHilbert Distributions

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Construct joint representatives for a locally convergent sequence of
energy waves and its displacement limit. On every compact spatial set the
representatives converge in spacetime L² and their reactions converge in L¹.
Only L² continuity of the limiting displacement is required; its H¹ curve may
be merely weakly continuous. -/
theorem exists_jointRepresentatives_with_local_reaction_limit {n : ℕ} {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {K : ℕ → NNReal} (hf : Continuous f) (hg : ∀ i, LipschitzWith (K i) (g i))
    (hsign : ∀ i z, 0 ≤ z * g i z) (hdom : ∀ i z, |g i z| ≤ |f z|) {r : ℕ → ℝ}
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r atTop atTop)
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (reaction_zero (hg i).continuous (hsign i)) x (u i))
    {T E : ℝ} (hT : 0 ≤ T) (he : ∀ i t, 0 ≤ t → physicalEnergy (g i) (u i t) ≤ E) {p : ℝ → H¹(ℝ^n)}
    (hp : ContinuousOn (fun t ↦ (energyTriple n).inclusion (p t)) (Icc 0 T))
    (hconv : ∀ χ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ),
      TendstoUniformlyOn (fun i t ↦ (energyTriple n).inclusion (cutoffCLM χ (u i t).1))
      (fun t ↦ (energyTriple n).inclusion (cutoffCLM χ (p t))) atTop (Icc 0 T)) :
    ∃ U : ℕ → ℝ × (ℝ^n) → ℝ, ∃ V : ℝ × (ℝ^n) → ℝ,
      (∀ i, StronglyMeasurable (U i)) ∧ StronglyMeasurable V ∧
      (∀ i, MemLp (U i) 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ))) ∧
      MemLp V 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 T),
        (fun y ↦ U i (t, y)) =ᵐ[domainMeasure n univ]
          (energyTriple n).inclusion (u i t).1) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T),
        (fun y ↦ V (t, y)) =ᵐ[domainMeasure n univ] (energyTriple n).inclusion (p t)) ∧
      ∀ s : Set (ℝ^n), IsCompact s →
        Tendsto (fun i ↦ eLpNorm (U i - V) 2
          ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)))
          atTop (𝓝 0) ∧
        Integrable (fun z ↦ f (V z))
          ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)) ∧
        Tendsto (fun i ↦ eLpNorm (fun z ↦ g i (U i z) - f (V z)) 1
          ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)))
          atTop (𝓝 0) := by
  choose U hU hUp hUsec using fun i ↦ exists_displacement_jointRepresentative T (u i)
  have hpm : MemLp (fun t ↦ (energyTriple n).inclusion (p t)) 2 (volume.restrict (Ioc 0 T)) :=
    hp.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  obtain ⟨V, hV, hVp, hVsec⟩ := hpm.exists_jointRepresentative
  refine ⟨U, V, hU, hV, hUp, hVp, hUsec, hVsec, ?_⟩
  intro s hs
  have : IsFiniteMeasure ((domainMeasure n univ).restrict s) :=
    isFiniteMeasure_restrict.mpr hs.measure_ne_top
  obtain ⟨χ, _, hχ, _, _⟩ := TestFunction.exists_eq_one_on_compact isOpen_univ hs (subset_univ s)
  have hL2 := tendsto_L2_restrict_of_cutoff_convergence
    (fun i ↦ (u i).continuous.fst.continuousOn) χ s hs.measurableSet hχ
    (fun i ↦ (hU i).aestronglyMeasurable) hV.aestronglyMeasurable hUsec hVsec (hconv χ)
  exact ⟨hL2, integrable_reaction_and_tendsto_L1_of_energy_waves hf hg hsign hdom
    hagree hr hu hT he s hUp hUsec hL2⟩

/-- A sequence of sign-preserving energy waves with a common energy bound has
one displacement subsequence and locally integrable limiting reaction on every
finite cylinder. The compactness and nonlinear-integrability hypotheses of the
preceding lemmas are derived here from the PDE. Fixed-time
strong cutoff convergence is retained for the potential-energy passage. -/
theorem exists_energy_displacement_reaction_limit {n : ℕ} {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {K : ℕ → NNReal} (hf : Continuous f) (hg : ∀ i, LipschitzWith (K i) (g i))
    (hsign : ∀ i z, 0 ≤ z * g i z) (hdom : ∀ i z, |g i z| ≤ |f z|) {r : ℕ → ℝ}
    (hagree : ∀ i, EqOn (g i) f (Metric.closedBall 0 (r i))) (hr : Tendsto r atTop atTop)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ))
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (reaction_zero (hg i).continuous (hsign i)) x (u i))
    {E : ℝ} (he : ∀ i t, 0 ≤ t → physicalEnergy (g i) (u i t) ≤ E) :
    ∃ q : Ici (0 : ℝ) → H¹(ℝ^n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      q ⟨0, le_rfl⟩ = x.1 ∧
      Continuous (fun t ↦ toWeakSpace ℝ H¹(ℝ^n) (q t)) ∧
      LipschitzWith ⟨Real.sqrt (2 * E), Real.sqrt_nonneg _⟩
        (fun t ↦ (energyTriple n).inclusion (q t)) ∧
      (∀ t, ‖q t‖ ≤ ‖(energyTriple n).inclusion x.1‖ +
        (t.val + 1) * Real.sqrt (2 * E)) ∧
      (∀ t, gradientForm n (q t) (q t) ≤ 2 * E) ∧
      (∀ k : ℕ, ∀ v : H¹(ℝ^n), TendstoUniformly
        (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ v (u (φ i) t).1)
        (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ v (q ⟨t.val, t.property.1⟩)) atTop) ∧
      (∀ k : ℕ, ∀ χ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ),
        let A := (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := univ)).comp
          (cutoffCLM (n := n) (p := 2) (Ω := univ) χ)
        TendstoUniformly (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ A (u (φ i) t).1)
          (fun t : Icc (0 : ℝ) (k : ℝ) ↦ A (q ⟨t.val, t.property.1⟩)) atTop) ∧
      ∀ T : ℝ, 0 ≤ T →
        ∃ U : ℕ → ℝ × (ℝ^n) → ℝ, ∃ V : ℝ × (ℝ^n) → ℝ,
          (∀ i, StronglyMeasurable (U i)) ∧ StronglyMeasurable V ∧
          (∀ i, MemLp (U i) 2
            ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ))) ∧
          MemLp V 2 ((volume.restrict (Ioc 0 T)).prod (domainMeasure n univ)) ∧
          (∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 T),
            (fun y ↦ U i (t, y)) =ᵐ[domainMeasure n univ]
              (energyTriple n).inclusion (u (φ i) t).1) ∧
          (∀ᵐ t ∂volume.restrict (Ioc 0 T),
            (fun y ↦ V (t, y)) =ᵐ[domainMeasure n univ]
              (energyTriple n).inclusion (IciExtend q t)) ∧
          ∀ s : Set (ℝ^n), IsCompact s →
            Tendsto (fun i ↦ eLpNorm (U i - V) 2
              ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)))
              atTop (𝓝 0) ∧
            Integrable (fun z ↦ f (V z))
              ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)) ∧
            Tendsto (fun i ↦ eLpNorm (fun z ↦ g (φ i) (U i z) - f (V z)) 1
              ((volume.restrict (Ioc 0 T)).prod ((domainMeasure n univ).restrict s)))
              atTop (𝓝 0) := by
  obtain ⟨q, φ, hφ, hq0, hqc, hqlip, hqbound, hqgrad, hweak, hcut⟩ :=
    exists_energy_displacement_limit hg
      (fun i ↦ reaction_zero (hg i).continuous (hsign i)) hsign x u hu he
  refine ⟨q, φ, hφ, hq0, hqc, hqlip, hqbound, hqgrad, hweak, hcut, ?_⟩
  intro T hT
  have hproj : Continuous (projIci (0 : ℝ)) := by
    apply Continuous.subtype_mk
    exact continuous_const.max continuous_id
  have hc : ContinuousOn (fun t ↦ (energyTriple n).inclusion (IciExtend q t))
      (Icc 0 T) := (hqlip.continuous.comp hproj).continuousOn
  apply exists_jointRepresentatives_with_local_reaction_limit hf
    (fun i ↦ hg (φ i)) (fun i ↦ hsign (φ i)) (fun i ↦ hdom (φ i))
    (fun i ↦ hagree (φ i)) (hr.comp hφ.tendsto_atTop) (fun i ↦ hu (φ i)) hT (fun i ↦ he (φ i)) hc
  intro χ
  obtain ⟨k, hk⟩ := exists_nat_ge T
  have hcutk : TendstoUniformlyOn (fun i t ↦ (energyTriple n).inclusion (cutoffCLM χ (u (φ i) t).1))
      (fun t ↦ (energyTriple n).inclusion (cutoffCLM χ (IciExtend q t)))
      atTop (Icc 0 (k : ℝ)) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have hlim (t : Icc (0 : ℝ) (k : ℝ)) :
        IciExtend q t = q ⟨t.val, t.property.1⟩ := IciExtend_of_mem q t.property.1
    simpa only [energyTriple, ContinuousLinearMap.comp_apply, Function.comp_def, hlim]
      using hcut k χ
  exact hcutk.mono (Icc_subset_Icc le_rfl hk)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
