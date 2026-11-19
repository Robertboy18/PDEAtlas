/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.VelocityPairing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.ReactionPairing
import PDE.Analysis.Evolution.Compactness.HalfLine
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# A weakly continuous velocity from the truncated waves

Uniform limits of the scalar velocity pairings give equicontinuity on each
bounded time interval. Density of compactly supported smooth tests and the
common kinetic-energy bound then give one weakly continuous L² velocity on
the whole forward half-line, with its original initial value.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A uniformly convergent sequence of continuous maps is equicontinuous.
A common neighborhood handles its tail; finitely many earlier maps are
handled by their individual continuity. -/
theorem equicontinuous_of_tendstoUniformly {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {F : ℕ → X → Y} {G : X → Y} (hF : ∀ i, Continuous (F i)) (hconv : TendstoUniformly F G atTop) :
    Equicontinuous F := by
  have hG : Continuous G := hconv.continuous (Eventually.of_forall hF).frequently
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp hconv) _ hε3)
  have hearly : ∀ᶠ y in 𝓝 x, ∀ i ∈ Finset.range N, dist (F i x) (F i y) < ε := by
    apply (Finset.range N).eventually_all.mpr
    intro i _
    filter_upwards [(Metric.tendsto_nhds.mp (hF i).continuousAt) ε hε] with y hy
    simpa only [dist_comm] using hy
  filter_upwards [hearly, (Metric.tendsto_nhds.mp hG.continuousAt) _ hε3] with y hy hGy
  intro i
  by_cases hi : i < N
  · exact hy i (Finset.mem_range.mpr hi)
  · have hx := hN i (Nat.le_of_not_gt hi) x
    have hy' := hN i (Nat.le_of_not_gt hi) y
    have htri := dist_triangle4 (F i x) (G x) (G y) (F i y)
    have hx' : dist (F i x) (G x) < ε / 3 := by simpa only [dist_comm] using hx
    have hGy' : dist (G x) (G y) < ε / 3 := by simpa only [dist_comm] using hGy
    linarith

/-- Uniform convergence of a dense family of observations produces a weakly
continuous half-line limit with the common Hilbert bound and initial value. -/
theorem exists_weak_trajectory_limit_of_uniform_pairings {H R : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (test : R → H)
    (htest : DenseRange test) (u : ℕ → Ici (0 : ℝ) → H) (hu : ∀ i, Continuous (u i)) (x : H)
    (hzero : ∀ i, u i ⟨0, le_rfl⟩ = x) (M : ℝ) (hbound : ∀ i t, ‖u i t‖ ≤ M)
    (hpair : ∀ k : ℕ, ∀ r, ∃ G : Icc (0 : ℝ) (k : ℝ) → ℝ, TendstoUniformly
      (fun i t ↦ inner ℝ (test r) (u i ⟨t.val, t.property.1⟩)) G atTop) :
    ∃ v : Ici (0 : ℝ) → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      v ⟨0, le_rfl⟩ = x ∧ (∀ t, ‖v t‖ ≤ M) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H (v t)) ∧
      ∀ k : ℕ, ∀ w : H, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ w (u (φ i) ⟨t.val, t.property.1⟩))
        (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ w (v ⟨t.val, t.property.1⟩)) atTop := by
  have hequi (k : ℕ) (r : R) : Equicontinuous
      (fun i (t : Icc (0 : ℝ) (0 + (k : ℝ))) ↦ inner ℝ (test r) (u i ⟨t.val, t.property.1⟩)) := by
    obtain ⟨G, hG⟩ := hpair k r
    let incl : Icc (0 : ℝ) (0 + (k : ℝ)) → Icc (0 : ℝ) (k : ℝ) :=
      fun t ↦ ⟨t.val, t.property.1, by simpa only [zero_add] using t.property.2⟩
    exact equicontinuous_of_tendstoUniformly (fun i ↦ by fun_prop) (hG.comp incl)
  obtain ⟨v, φ, hφ, hvb, hvc, hv⟩ :=
    exists_weak_trajectory_limit_Ici 0 test htest u hu M hbound (fun k r ↦ by
      refine ⟨0, ?_⟩
      exact (hequi k r).comp (fun i : Ici (0 : ℕ) ↦ i.val))
  have hv' : ∀ k : ℕ, ∀ w : H, TendstoUniformly
      (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ w (u (φ i) ⟨t.val, t.property.1⟩))
      (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ w (v ⟨t.val, t.property.1⟩)) atTop := by
    intro k w
    exact (hv k w).comp (fun t : Icc (0 : ℝ) (k : ℝ) ↦
      ⟨t.val, t.property.1, by simpa only [zero_add] using t.property.2⟩)
  refine ⟨v, φ, hφ, ?_, hvb, hvc, hv'⟩
  apply ext_inner_left ℝ
  intro w
  have h := (hv' 0 w).tendsto_at ⟨0, le_rfl, by simp⟩
  have h0 : Tendsto (fun _ : ℕ ↦ inner ℝ w x) atTop
      (𝓝 (inner ℝ w (v ⟨0, le_rfl⟩))) := by
    simpa only [hzero] using h
  exact tendsto_nhds_unique h0 tendsto_const_nhds

/-- The kinetic bound and local reaction convergence of energy waves
produce a global weakly continuous velocity. -/
theorem exists_weak_velocity_limit_of_local_reaction_convergence {n : ℕ} {g : ℕ → ℝ → ℝ}
    {K : ℕ → NNReal} {hg : ∀ i, LipschitzWith (K i) (g i)} {hg0 : ∀ i, g i 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {q : ℝ → H¹(ℝ^n)}
    (hweak : ∀ k : ℕ, ∀ ell : StrongDual ℝ H¹(ℝ^n), TendstoUniformlyOn (fun i t ↦ ell (u i t).1)
      (fun t ↦ ell (q t)) atTop (Icc 0 k))
    {M : ℝ} (hbound : ∀ i t, 0 ≤ t → ‖(u i t).2‖ ≤ M)
    (hlocal : ∀ k : ℕ, ∃ U : ℕ → ℝ × (ℝ^n) → ℝ, ∃ G : ℝ × (ℝ^n) → ℝ,
      (∀ i, MemLp (U i) 2 ((volume.restrict (Ioc 0 (k : ℝ))).prod (domainMeasure n univ))) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 (k : ℝ)), (fun y ↦ U i (t, y)) =ᵐ[domainMeasure n univ]
      (energyTriple n).inclusion (u i t).1) ∧ ∀ s : Set (ℝ^n), IsCompact s →
      Integrable G ((volume.restrict (Ioc 0 (k : ℝ))).prod ((domainMeasure n univ).restrict s)) ∧
      Tendsto (fun i ↦ eLpNorm (fun z ↦ g i (U i z) - G z) 1
      ((volume.restrict (Ioc 0 (k : ℝ))).prod ((domainMeasure n univ).restrict s))) atTop (𝓝 0)) :
    ∃ v : Ici (0 : ℝ) → DerivLp n 2 univ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      v ⟨0, le_rfl⟩ = x.2 ∧ (∀ t, ‖v t‖ ≤ M) ∧
      Continuous (fun t ↦ toWeakSpace ℝ (DerivLp n 2 univ) (v t)) ∧
      ∀ k : ℕ, ∀ w : DerivLp n 2 univ, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ w (u (φ i) t).2)
        (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ w (v ⟨t.val, t.property.1⟩)) atTop := by
  have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 univ) := Lp.SecondCountableTopology
  let test : TestFunctionOn n univ → DerivLp n 2 univ := fun φ ↦ baseCoordCLM (testFunctionToH10 φ)
  have hd : DenseRange test :=
    (baseCoordCLM_denseRange isOpen_univ).comp denseRange_testFunctionToH10Linear
      (baseCoordCLM (n := n) (Ω := univ)).continuous
  apply exists_weak_trajectory_limit_of_uniform_pairings test hd
    (fun i t ↦ (u i t).2) (fun i ↦ (u i).continuous.snd.comp continuous_subtype_val)
    x.2 (fun i ↦ congrArg Prod.snd (hu i).initial) M (fun i t ↦ hbound i t t.property)
  intro k φ
  obtain ⟨U, G, hU, hUsec, hG⟩ := hlocal k
  have hs : IsCompact (tsupport φ.1.toFun) := φ.1.hasCompactSupport
  have : IsFiniteMeasure ((domainMeasure n univ).restrict (tsupport φ.1.toFun)) :=
    isFiniteMeasure_restrict.mpr hs.measure_ne_top
  obtain ⟨C, hC⟩ := φ.1.hasCompactSupport.exists_bound_of_continuous φ.1.contDiff.continuous
  have hb (y : ℝ^n) : ‖φ.1.toFun y‖ ≤ (⟨max C 0, le_max_right _ _⟩ : NNReal) :=
    (hC y).trans (le_max_left _ _)
  obtain ⟨hR, hconv⟩ := tendsto_L1_reaction_pairing_of_joint_convergence hg hg0 hU hUsec
    (hG _ hs).1 (hG _ hs).2 (test φ) φ.1.contDiff.continuous.stronglyMeasurable hb
    (fun y hy ↦ image_eq_zero_of_notMem_tsupport hy) (baseCoordCLM_testFunction_apply_ae φ)
  have hpair := tendstoUniformlyOn_velocity_pairing hu (hweak k) (testFunctionToH1 φ) hR hconv
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hpair
  refine ⟨_, (tendstoUniformly_congr ?_).mp hpair⟩
  exact Eventually.of_forall fun i ↦ funext fun t ↦ (real_inner_comm (u i t).2 (test φ)).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
