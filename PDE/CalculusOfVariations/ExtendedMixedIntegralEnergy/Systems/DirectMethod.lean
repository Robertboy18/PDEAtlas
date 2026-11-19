/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedDirectMethod
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Functional
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Coercivity
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Reflexivity
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The direct method in affine classes of Sobolev systems

Gradient coercivity bounds the finite energy sublevels after translation by any
Sobolev boundary lift. The zero-trace space is reflexive and separable, and its
inclusion and translation preserve weak convergence. Thus sequential weak lower
semicontinuity gives a minimizer, including when all admissible energies are
infinite. The convex and polyconvex modules verify this last hypothesis.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Sobolev

namespace PDE.CalculusOfVariations

/-- A weakly lower semicontinuous, gradient-coercive extended energy attains a
minimum in each nonempty, weakly sequentially closed constraint within an affine
zero-trace class. Coercivity and reflexivity supply the
bounded sublevels and weak subsequence; the boundary lift need not have finite
energy. No boundary regularity is needed. -/
theorem exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_weak_lsc
    {m n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} (hbounded : Bornology.IsBounded Ω)
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 < p)
    {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ} {b : ℝ^n → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (z : ℝ^(m * n)),
      c * ‖z‖ ^ (p : ℝ) - b x ≤ F x (s, z))
    (hlsc : ∀ {u : ℕ → Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
      {U : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)},
      Tendsto (fun j ↦ toWeakSpace ℝ
        (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) (u j)) atTop
        (𝓝 (toWeakSpace ℝ (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) U)) →
      vectorWkpLIntegral F b U ≤ liminf (fun j ↦ vectorWkpLIntegral F b (u j)) atTop)
    {A : Set (Fin m → W^{1,(p : ℝ≥0∞)}(Ω))}
    (hA : IsSeqClosed (toWeakSpace ℝ (Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) '' A))
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) (hg : g ∈ A) :
    ∃ u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
      u ∈ A ∧ (∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) ∧
      ∀ v ∈ A,
        (∀ i, v i - g i ∈ wkp0SubmoduleOn
          (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
        vectorWkpLIntegral F b u ≤ vectorWkpLIntegral F b v := by
  let W₀ := W^{1,(p : ℝ≥0∞)}(Ω)
  let V₀ := W₀^{1,(p : ℝ≥0∞)}(Ω)
  let _ : NormedAddCommGroup W₀ :=
    Submodule.normedAddCommGroup (wkpSubmoduleOn n 1 (p : ℝ≥0∞) Ω)
  let _ : NormedSpace ℝ W₀ := Submodule.normedSpace (wkpSubmoduleOn n 1 (p : ℝ≥0∞) Ω)
  let _ : NormedAddCommGroup V₀ := Submodule.normedAddCommGroup
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  let _ : NormedSpace ℝ V₀ := Submodule.normedSpace
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule
  let W := Fin m → W₀
  let V := Fin m → V₀
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have : Fact (1 ≤ p) := ⟨hp.le⟩
  have : Fact ((p : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.coe_ne_top⟩
  have : SecondCountableTopology V₀ := inferInstance
  have : SecondCountableTopology V := inferInstance
  let incl₀ : V₀ →L[ℝ] W₀ :=
    (wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)).toSubmodule.subtypeL
  let incl : V →L[ℝ] W :=
    ContinuousLinearMap.pi fun i ↦ incl₀.comp (ContinuousLinearMap.proj i)
  let C : Set V := {w | g + incl w ∈ A}
  let J (w : V) := vectorWkpLIntegral F b (g + incl w)
  have hseq (u : ℕ → V) (uLimit : V) (_hu : ∀ j, u j ∈ C)
      (_hbound : Bornology.IsBounded (range u))
      (hu : Tendsto (fun j ↦ toWeakSpace ℝ V (u j)) atTop
        (𝓝 (toWeakSpace ℝ V uLimit))) : J uLimit ≤ liminf (fun j ↦ J (u j)) atTop := by
    have hweak : Tendsto (fun j ↦ toWeakSpace ℝ W (incl (u j))) atTop
        (𝓝 (toWeakSpace ℝ W (incl uLimit))) :=
      (WeakSpace.map incl).continuous.continuousAt.tendsto.comp hu
    apply hlsc
    simpa only [map_add] using
      (tendsto_const_nhds.add hweak : Tendsto
        (fun j ↦ toWeakSpace ℝ W g + toWeakSpace ℝ W (incl (u j))) atTop
        (𝓝 (toWeakSpace ℝ W g + toWeakSpace ℝ W (incl uLimit))))
  have hpE : 1 < (p : ℝ≥0∞) := by exact_mod_cast hp
  have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ V) :=
    NormedSpace.surjective_inclusionInDoubleDual_pi (fun _ : Fin m ↦ V₀)
      (fun _ ↦ Wkp0SpaceOn.surjective_inclusionInDoubleDual hpE ENNReal.coe_ne_top)
  have hclosed : IsSeqClosed ((toWeakSpace ℝ V) '' C) := by
    have hpre := hA.preimage
      ((continuous_const (y := toWeakSpace ℝ W g)).add
        (WeakSpace.map incl).continuous).seqContinuous
    convert hpre using 1
    ext w
    simp only [mem_image, mem_preimage, C, mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g + incl v, hv, map_add _ _ _⟩
    · rintro ⟨v, hv, he⟩
      refine ⟨(toWeakSpace ℝ V).symm w, ?_, (toWeakSpace ℝ V).apply_symm_apply w⟩
      have hm : WeakSpace.map incl w =
          toWeakSpace ℝ W (incl ((toWeakSpace ℝ V).symm w)) := by
        obtain ⟨z, rfl⟩ := (toWeakSpace ℝ V).surjective w
        rfl
      have he' : g + incl ((toWeakSpace ℝ V).symm w) = v := by
        apply (toWeakSpace ℝ W).injective
        simpa only [Pi.add_apply, hm, map_add] using he.symm
      exact he' ▸ hv
  have hsublevel (K : ℝ≥0∞) (hK : K ≠ ∞) :
      Bornology.IsBounded {w : V | w ∈ C ∧ J w ≤ K} :=
    (isBounded_sublevel_vectorWkpLIntegral_prescribed_boundary
      (show 0 < n from Fact.out) hbounded hp.le hc hlower g hK).subset
        (fun _ hw ↦ hw.2)
  obtain ⟨w, hwC, hw⟩ :=
    exists_isMinOn_of_weak_seq_lowerSemicontinuity_of_bounded_finite_sublevels
      hreflexive J hclosed hseq ⟨0, by simpa only [C, mem_ofPred_eq, map_zero, add_zero]⟩
        hsublevel
  refine ⟨g + incl w, hwC, ?_, ?_⟩
  · intro i
    change g i + (w i : W₀) - g i ∈ _
    rw [add_sub_cancel_left]
    exact (w i).property
  · intro v hvA hv
    let z : V := fun i ↦ ⟨v i - g i, hv i⟩
    have hz : g + incl z = v := by
      funext i
      change g i + (v i - g i) = v i
      abel
    have hmin : J w ≤ J z := hw (show z ∈ C from by simpa only [C, mem_ofPred_eq, hz] using hvA)
    simpa only [J, hz] using hmin

end PDE.CalculusOfVariations
