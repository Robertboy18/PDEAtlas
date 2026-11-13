/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Continuation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothData

/-!
# Classical continuation of bounded higher Sobolev waves

The extended higher mild trajectory projects to the original energy solution
on its full interval. Its integrated PDE equations give the time derivatives,
and Sobolev embedding gives a jointly C² representative. The representative
agrees pointwise with the earlier displacement and velocity.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

/-- A higher mild wave with bounded Sobolev state norm at a finite endpoint
has a classical extension agreeing with both earlier fields.
The target composition estimates and all classical derivatives are derived. -/
theorem exists_classical_extension_of_bounded_higherSmooth (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)} {b : ℝ} {u : ℝ → W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (hu : (higherLinearSemigroup n (k + 1)).IsMildSolutionBefore (higherSmoothMap hv hs hf0) x b u)
    (hb : 0 < b) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ t ∈ Ico 0 b, ‖u t‖ ≤ R) :
    ∃ ρ : ℝ, b < ρ ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 ρ ×ˢ univ) ∧
      (∀ y, q (0, y) = classicalRepresentativeCLM hq x.1 y ∧
        HasDerivWithinAt (fun t ↦ q (t, y)) (classicalRepresentativeCLM hv x.2 y)
          (Icc 0 ρ) 0) ∧
      (∀ t ∈ Ico 0 b, ∀ y,
        q (t, y) = classicalRepresentativeCLM hq (u t).1 y ∧
        HasDerivWithinAt (fun s ↦ q (s, y)) (classicalRepresentativeCLM hv (u t).2 y)
          (Icc 0 ρ) t) ∧
      ∀ t ∈ Ioo 0 ρ, ∀ y,
        deriv (fun s ↦ deriv (fun r ↦ q (r, y)) s) t -
          Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  obtain ⟨ρ, hρ, V, hV, hext⟩ := exists_higherSmooth_extension_of_bounded hv hs hf0 hu hb hR hbound
  let U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :=
    ⟨IccExtend ρ.property V, V.continuous.Icc_extend'⟩
  have hU₀ : U 0 = x := (IccExtend_of_mem ρ.property V ⟨le_rfl, ρ.property⟩).trans hV.initial_value
  obtain ⟨e, he⟩ := exists_energySolution hf hf0
    (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2)
  have hproj := he.eq_higherSmooth_mild_projection hv hs hf hf0 x V hV
  obtain ⟨q, v, a, hq₂, hzero, hfield⟩ :=
    he.exists_pointwise_higherLift_smoothReaction hk hs hf hf0 hq hv x U hU₀ hproj
  have hfields (t : ℝ) (ht : t ∈ Icc 0 (ρ : ℝ)) :
      (fun y ↦ q (t, y)) = (classicalRepresentativeCLM hq (U t).1 : ℝ^n → ℝ) ∧
      (fun y ↦ v (t, y)) = (classicalRepresentativeCLM hv (U t).2 : ℝ^n → ℝ) := by
    have hqt := (hfield t ht).1
    have hvt := (hfield t ht).2.1
    rw [← hproj t ht] at hqt hvt
    exact ⟨eq_classicalRepresentativeCLM_of_ae_eq hq (U t).1
      (q.continuous.comp (continuous_const.prodMk continuous_id)) hqt,
      eq_classicalRepresentativeCLM_of_ae_eq hv (U t).2
        (v.continuous.comp (continuous_const.prodMk continuous_id)) hvt⟩
  refine ⟨ρ, hρ, q, hq₂, ?_, ?_, ?_⟩
  · intro y
    refine ⟨(hzero y).1, ?_⟩
    rw [← (hzero y).2]
    exact ((hfield 0 ⟨le_rfl, ρ.property⟩).2.2.2 y).1
  · intro t ht y
    have htρ : t ∈ Icc 0 (ρ : ℝ) := ⟨ht.1, ht.2.le.trans hρ.le⟩
    have hUeq : U t = u t := hext ht
    have hqeq := congrFun (hfields t htρ).1 y
    have hveq := congrFun (hfields t htρ).2 y
    rw [hUeq] at hqeq hveq
    refine ⟨hqeq, ?_⟩
    rw [← hveq]
    exact ((hfield t htρ).2.2.2 y).1
  · intro t ht y
    have hdd := deriv_deriv_eq_of_wave_derivatives
      (fun s hst ↦ ⟨((hfield s hst).2.2.2 y).1, ((hfield s hst).2.2.2 y).2.1⟩) ht
    rw [hdd]
    exact ((hfield t ⟨ht.1.le, ht.2.le⟩).2.2.2 y).2.2

end PDE.Hyperbolic.NonlinearWave.Cauchy
