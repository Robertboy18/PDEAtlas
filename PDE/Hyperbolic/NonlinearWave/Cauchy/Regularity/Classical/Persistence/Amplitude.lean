/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Composition
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Growth
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.ClassicalContinuation

/-!
# Continuation from bounded amplitude

The tame composition estimate gives affine source growth on trajectories
whose displacement is uniformly bounded. Grönwall then supplies the higher
Sobolev norm bound required for continuation. No derivative bound for the
unknown solution is a hypothesis.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- The wave source has affine state growth on each amplitude range. -/
theorem exists_affine_higherSmoothMap_bound (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n), (∀ y, ‖classicalRepresentativeCLM hq z.1 y‖ ≤ B) →
        ‖higherSmoothMap hk hs hf0 z‖ ≤ C * (1 + ‖z‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_tame_higherComposition_bound hk hs hf0 hB
  refine ⟨1 + C, by positivity, fun z hz ↦ ?_⟩
  have hlow : ‖lowerOrderCLM (Nat.le_succ k) z.1‖ ≤ ‖z‖ :=
    (norm_lowerOrderCLM_apply_le (Nat.le_succ k) z.1).trans (norm_fst_le z)
  have hcomp := hbound (lowerOrderCLM (Nat.le_succ k) z.1) (by
    simpa only [classicalRepresentativeCLM_lowerOrderCLM hk hq] using hz)
  change ‖(0, lowerOrderCLM (Nat.le_succ k) z.1 -
    higherComposition hk hs hf0 (lowerOrderCLM (Nat.le_succ k) z.1))‖ ≤ _
  rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
  exact (norm_sub_le _ _).trans (by nlinarith)

/-- Uniform amplitude on a finite higher mild trajectory implies a uniform
bound for its entire Sobolev state, by the proved tame estimate and Grönwall. -/
theorem exists_higherSmooth_norm_bound_of_amplitude (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {b : ℝ} {u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)}
    (hu : (higherLinearSemigroup n k).IsMildSolutionBefore (higherSmoothMap hk hs hf0) x b u)
    (hb : 0 < b) {B : ℝ}
    (hamp : ∀ t ∈ Ico 0 b, ∀ y, ‖classicalRepresentativeCLM hq (u t).1 y‖ ≤ B) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ico 0 b, ‖u t‖ ≤ R := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hamp 0 ⟨le_rfl, hb⟩ 0)
  obtain ⟨C, hC, hsource⟩ := exists_affine_higherSmoothMap_bound hk hq hs hf0 hB
  exact exists_norm_mildSolutionBefore_bound_of_affine_source hu hb hC
    (fun t ht ↦ hsource (u t) (hamp t ht))

/-- Bounded amplitude extends a finite higher Sobolev solution. -/
theorem exists_higherSmooth_extension_of_amplitude (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {b : ℝ} {u : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)}
    (hu : (higherLinearSemigroup n k).IsMildSolutionBefore (higherSmoothMap hk hs hf0) x b u)
    (hb : 0 < b) {B : ℝ}
    (hamp : ∀ t ∈ Ico 0 b, ∀ y, ‖classicalRepresentativeCLM hq (u t).1 y‖ ≤ B) :
    ∃ ρ : ℝ≥0, b < (ρ : ℝ) ∧ ∃ v : C(Icc (0 : ℝ) (ρ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hs hf0) x ρ v ∧
      EqOn (IccExtend ρ.coe_nonneg v) u (Ico 0 b) := by
  obtain ⟨R, hR, hbound⟩ := exists_higherSmooth_norm_bound_of_amplitude hk hq hs hf0 hu hb hamp
  exact exists_higherSmooth_extension_of_bounded hk hs hf0 hu hb hR hbound

/-- Bounded amplitude gives a C² continuation with the pointwise PDE,
initial values, and agreement with both earlier displacement and velocity. -/
theorem exists_classical_extension_of_amplitude (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) {K : ℝ≥0} (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)} {b : ℝ} {u : ℝ → W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (hu : (higherLinearSemigroup n (k + 1)).IsMildSolutionBefore (higherSmoothMap hv hs hf0) x b u)
    (hb : 0 < b) {B : ℝ}
    (hamp : ∀ t ∈ Ico 0 b, ∀ y, ‖classicalRepresentativeCLM hq (u t).1 y‖ ≤ B) :
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
  obtain ⟨R, hR, hbound⟩ := exists_higherSmooth_norm_bound_of_amplitude hv hq hs hf0 hu hb hamp
  exact exists_classical_extension_of_bounded_higherSmooth hk hs hf hf0 hq hv hu hb hR hbound

end PDE.Hyperbolic.NonlinearWave.Cauchy
