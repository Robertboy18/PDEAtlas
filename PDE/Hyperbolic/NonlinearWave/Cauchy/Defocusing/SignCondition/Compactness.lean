/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.UniformEstimates
public import PDE.Analysis.Evolution.Compactness.FixedTests
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Cutoff
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Local compactness of finite-energy displacement trajectories

A bounded velocity gives a time modulus in L². Testing through the adjoint of
the injective H¹ inclusion gives a dense family of H¹ pairings with the same
modulus. The fixed-test extraction theorem supplies one subsequence on
all finite time windows. Their weak limits agree on overlaps, and every compact
spatial cutoff of that same subsequence converges strongly and uniformly in time.
The H¹ bounds are allowed to grow with the time window.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
  BoundedContinuousFunction Distributions ENNReal

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

open PDE.Analysis.Evolution

/-- An injective Hilbert-space inclusion has dense adjoint range. This converts
pairings in the weaker norm into a dense family of energy-space tests. -/
theorem denseRange_adjoint_of_injective
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (J : H →L[ℝ] E) (hJ : Function.Injective J) : DenseRange J.adjoint := by
  change Dense (J.adjoint.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← J.orthogonal_ker]
  have hk : J.ker = ⊥ := LinearMap.ker_eq_bot.mpr hJ
  rw [hk, Submodule.bot_orthogonal_eq_top]

/-- Lipschitz control after an injective Hilbert inclusion and energy bounds on
finite windows give one weakly continuous limit on the forward half-line. The bound may depend on
the window. -/
theorem exists_local_weak_limit_of_lipschitz_inclusion {H E : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (J : H →L[ℝ] E)
    (hJ : Function.Injective J) (q : ℕ → C(ℝ, H)) (M : ℕ → ℝ) (C : NNReal)
    (hbound : ∀ (i k : ℕ), ∀ t ∈ Icc (0 : ℝ) (k : ℝ), ‖q i t‖ ≤ M k)
    (hlip : ∀ i, LipschitzOnWith C (fun t ↦ J (q i t)) (Ici 0)) :
    ∃ qLimit : Ici (0 : ℝ) → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ (k : ℕ) (t : Icc (0 : ℝ) (k : ℝ)), ‖qLimit ⟨t.val, t.property.1⟩‖ ≤ M k) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H (qLimit t)) ∧
      ∀ k : ℕ, ∀ v : H, TendstoUniformly
        (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ v (q (φ i) t))
        (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ v (qLimit ⟨t.val, t.property.1⟩))
        atTop := by
  let X (k : ℕ) : Type := Icc (0 : ℝ) (k : ℝ)
  let incl (k : ℕ) (t : X k) : Ici (0 : ℝ) := ⟨t.val, t.property.1⟩
  let w (i k : ℕ) : X k →ᵇ H := BoundedContinuousFunction.mkOfCompact
    ⟨fun t ↦ q i t, (q i).continuous.comp continuous_subtype_val⟩
  have hpair (k : ℕ) (e : E) : ∃ N : ℕ, Equicontinuous
      (fun i : Ici N ↦ fun t : X k ↦ inner ℝ (J.adjoint e) (w i.val k t)) := by
    refine ⟨0, ?_⟩
    apply Metric.equicontinuous_of_continuity_modulus (fun r ↦ ‖e‖ * (C : ℝ) * r)
    · have hb : Continuous (fun r : ℝ ↦ ‖e‖ * (C : ℝ) * r) := by fun_prop
      simpa only [mul_zero] using hb.tendsto (0 : ℝ)
    · intro s t i
      change dist (inner ℝ (J.adjoint e) (q i.val s))
        (inner ℝ (J.adjoint e) (q i.val t)) ≤ ‖e‖ * (C : ℝ) * dist s t
      rw [J.adjoint_inner_left, J.adjoint_inner_left, Real.dist_eq, ← inner_sub_right]
      have hb := (hlip i.val).dist_le_mul s.val s.property.1 t.val t.property.1
      rw [dist_eq_norm] at hb
      exact (abs_real_inner_le_norm _ _).trans (by
        change ‖e‖ * ‖J (q i.val s) - J (q i.val t)‖ ≤ ‖e‖ * (C : ℝ) * dist (s : ℝ) (t : ℝ)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hb (norm_nonneg e))
  obtain ⟨p, φ, hφ, hM, hc, hp⟩ := exists_subsequence_tendstoUniformly_pairings_family
    X J.adjoint (denseRange_adjoint_of_injective J hJ) w M
    (fun i k t ↦ hbound i k t t.property) hpair
  let index (t : Ici (0 : ℝ)) : ℕ := Classical.choose (exists_nat_gt t.val)
  have hindex (t : Ici (0 : ℝ)) : t.val < (index t : ℝ) :=
    Classical.choose_spec (exists_nat_gt t.val)
  let inWindow (t : Ici (0 : ℝ)) : X (index t) := ⟨t.val, t.property, (hindex t).le⟩
  let qLimit (t : Ici (0 : ℝ)) : H := p (index t) (inWindow t)
  have hagree (k : ℕ) (t : X k) : qLimit (incl k t) = p k t :=
    ext_inner_left ℝ fun v ↦ tendsto_nhds_unique
      ((hp (index (incl k t)) v).tendsto_at (inWindow (incl k t))) ((hp k v).tendsto_at t)
  refine ⟨qLimit, φ, hφ, ?_, ?_, ?_⟩
  · intro k t
    change ‖qLimit (incl k t)‖ ≤ M k
    rw [hagree]
    exact hM k t
  · rw [continuous_iff_continuousAt]
    intro t
    let k := index t
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcont : Continuous (fun s : Ici (0 : ℝ) ↦
        toWeakSpace ℝ H (p k (projIcc 0 (k : ℝ) hk s.val))) :=
      (hc k).comp (continuous_projIcc.comp continuous_subtype_val)
    apply hcont.continuousAt.congr_of_eventuallyEq
    have hnear : ∀ᶠ s : Ici (0 : ℝ) in 𝓝 t, s.val < (k : ℝ) :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds (hindex t)
    filter_upwards [hnear] with s hs
    rw [projIcc_of_mem hk ⟨s.property, hs.le⟩]
    exact congrArg (toWeakSpace ℝ H) (hagree k ⟨s.val, s.property, hs.le⟩)
  · intro k v
    change TendstoUniformly (fun i (t : X k) ↦ inner ℝ v (w (φ i) k t))
      (fun t ↦ inner ℝ v (qLimit (incl k t))) atTop
    simpa only [hagree] using hp k v

/-- Whole-space displacement compactness on every finite time window. All smooth
compact spatial cutoffs converge along the same subsequence and to cutoffs of
one weakly continuous H¹ path. -/
theorem exists_displacement_subsequence {n : ℕ} (q : ℕ → C(ℝ, H¹(ℝ^n))) (M : ℕ → ℝ) (C : NNReal)
    (hbound : ∀ (i k : ℕ), ∀ t ∈ Icc (0 : ℝ) (k : ℝ), ‖q i t‖ ≤ M k)
    (hlip : ∀ i, LipschitzOnWith C (fun t ↦ (energyTriple n).inclusion (q i t)) (Ici 0)) :
    ∃ qLimit : Ici (0 : ℝ) → H¹(ℝ^n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ (k : ℕ) (t : Icc (0 : ℝ) (k : ℝ)), ‖qLimit ⟨t.val, t.property.1⟩‖ ≤ M k) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H¹(ℝ^n) (qLimit t)) ∧
      (∀ k : ℕ, ∀ v : H¹(ℝ^n), TendstoUniformly
        (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ v (q (φ i) t))
        (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ v (qLimit ⟨t.val, t.property.1⟩))
        atTop) ∧
      ∀ k : ℕ, ∀ χ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ),
        let A := (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := univ)).comp
          (cutoffCLM (n := n) (p := 2) (Ω := univ) χ)
        TendstoUniformly (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ A (q (φ i) t))
          (fun t : Icc (0 : ℝ) (k : ℝ) ↦ A (qLimit ⟨t.val, t.property.1⟩)) atTop := by
  have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 univ) := Lp.SecondCountableTopology
  have : SecondCountableTopology H¹(ℝ^n) := inferInstance
  obtain ⟨qLimit, φ, hφ, hM, hc, hp⟩ := exists_local_weak_limit_of_lipschitz_inclusion
    (energyTriple n).inclusion (energyTriple n).injective q M C hbound hlip
  refine ⟨qLimit, φ, hφ, hM, hc, hp, fun k χ ↦ ?_⟩
  dsimp only
  apply tendstoUniformly_compactOperator_of_dense_pairings _
    (RellichKondrachov.cutoffBaseCoordinate_isCompactOperator (by norm_num) χ)
    id denseRange_id (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ q (φ i) t)
    (fun t : Icc (0 : ℝ) (k : ℝ) ↦ qLimit ⟨t.val, t.property.1⟩) (M k)
    (fun i t ↦ hbound (φ i) k t t.property) (hM k) (hp k)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
