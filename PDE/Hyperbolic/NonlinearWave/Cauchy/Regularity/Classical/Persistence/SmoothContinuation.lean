/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothTrajectory

/-!
# Smooth continuation from a uniform amplitude bound

The higher Sobolev continuation criterion constructs a longer mild trajectory.
Smooth compact data retain every order along that trajectory, including both
time endpoints. The canonical representative therefore extends the original
wave with its pointwise equation and displacement and velocity traces.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- Uniform displacement amplitude gives an all-orders smooth extension
from smooth compact Cauchy data. Only smoothness of the original reaction is assumed. -/
theorem exists_smooth_extension_of_amplitude (hn : n < 4) (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {b : ℝ}
    {u : ℝ → W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (hu : (higherLinearSemigroup n (k + 1)).IsMildSolutionBefore (higherSmoothMap hv hs hf0)
      (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) b u)
    (hb : 0 < b) {B : ℝ}
    (hamp : ∀ t ∈ Ico 0 b, ∀ y, ‖classicalRepresentativeCLM hq (u t).1 y‖ ≤ B) :
    ∃ ρ : ℝ, b < ρ ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) q (Icc 0 ρ ×ˢ univ) ∧
      (∀ y, q (0, y) = g y ∧
        HasDerivWithinAt (fun t ↦ q (t, y)) (h y) (Icc 0 ρ) 0) ∧
      (∀ t ∈ Ico 0 b, ∀ y,
        q (t, y) = classicalRepresentativeCLM hq (u t).1 y ∧
        HasDerivWithinAt (fun s ↦ q (s, y)) (classicalRepresentativeCLM hv (u t).2 y)
          (Icc 0 ρ) t) ∧
      ∀ t ∈ Ioo 0 ρ, ∀ y,
        deriv (fun s ↦ deriv (fun r ↦ q (r, y)) s) t -
          Δ (fun z ↦ q (t, z)) y + f (q (t, y)) = 0 := by
  obtain ⟨ρ, hρ, V, hV, hext⟩ :=
    exists_higherSmooth_extension_of_amplitude hv hq hs hf0 hu hb hamp
  let U := IccExtend ρ.property V
  let q : C(ℝ × ℝ^n, ℝ) := ⟨fun p ↦ classicalRepresentativeCLM hq (U p.1).1 p.2,
      continuous_eval.comp ((((classicalRepresentativeCLM hq).continuous.comp
        V.continuous.Icc_extend'.fst).comp continuous_fst).prodMk continuous_snd)⟩
  have hzero : U 0 = (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) :=
    (IccExtend_of_mem ρ.property V ⟨le_rfl, ρ.property⟩).trans hV.initial_value
  have hqsmooth : ContDiffOn ℝ (⊤ : ℕ∞) q (Icc 0 (ρ : ℝ) ×ˢ univ) :=
    contDiffOn_infty_higherSmooth_trajectory_of_smoothCompact hn hv hq hs hf0 g h hg hh hgc hhc V hV
  have hd (t : ℝ) (ht : t ∈ Icc 0 (ρ : ℝ)) (y : ℝ^n) :=
    (hasDerivWithinAt_classical_higherSmooth_trajectory hk hv hq hs hf0 V hV ht y).1
  refine ⟨ρ, hρ, q, hqsmooth, ?_, ?_, ?_⟩
  · intro y
    constructor
    · change classicalRepresentativeCLM hq (U 0).1 y = g y
      rw [hzero]
      exact congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) y
    · have h := hd 0 ⟨le_rfl, ρ.property⟩ y
      change HasDerivWithinAt (fun t ↦ q (t, y))
        (classicalRepresentativeCLM hv (U 0).2 y) (Icc 0 (ρ : ℝ)) 0 at h
      simpa only [hzero, classicalRepresentative_mkWkpSpaceOnOfContDiff] using h
  · intro t ht y
    have htρ : t ∈ Icc 0 (ρ : ℝ) := ⟨ht.1, ht.2.le.trans hρ.le⟩
    constructor
    · change classicalRepresentativeCLM hq (U t).1 y = _
      rw [show U t = u t from hext ht]
    · have h := hd t htρ y
      change HasDerivWithinAt (fun s ↦ q (s, y))
        (classicalRepresentativeCLM hv (U t).2 y) (Icc 0 (ρ : ℝ)) t at h
      rwa [show U t = u t from hext ht] at h
  · exact fun t ht y ↦ higherSmooth_trajectory_wave_equation hk hv hq hs hf0 V hV ht y

end PDE.Hyperbolic.NonlinearWave.Cauchy
