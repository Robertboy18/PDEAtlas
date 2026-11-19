/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Existence
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.SmoothData

/-!
# Smooth compact data and general smooth globally Lipschitz reactions

In every positive dimension, arbitrary smooth compactly supported initial
displacement and velocity yield a jointly C² whole-space wave on a
positive time strip. The scalar reaction is smooth, globally Lipschitz, and
vanishes at zero. All Sobolev composition and embedding hypotheses are proved.
The statement is local in time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [NeZero n]
variable {f : ℝ → ℝ} {K : ℝ≥0}

/-- In every positive dimension, smooth compact data yield a local
classical whole-space wave for the general smooth globally Lipschitz reaction.
No bound, composition hypothesis, embedding hypothesis, or regularity of the
unknown solution is an input. -/
theorem exists_classical_smoothReaction_of_smoothCompact (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : LipschitzWith K f) (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 b ×ˢ univ) ∧
      (∀ x, q (0, x) = g x ∧
        HasDerivWithinAt (fun t ↦ q (t, x)) (h x) (Icc 0 b) 0) ∧
      ∀ t ∈ Ioo 0 b, ∀ x,
        deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t -
          Δ (fun y ↦ q (t, y)) x + f (q (t, x)) = 0 := by
  let k := n + 2
  have hk : (n : ℝ) < 2 * ((k : ℝ) - 1) := by
    dsimp [k]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  let G := mkWkpSpaceOnOfContDiff (k := k + 2) (p := 2) (Ω := univ) g hg hgc
  let H := mkWkpSpaceOnOfContDiff (k := k + 1) (p := 2) (Ω := univ) h hh hhc
  obtain ⟨u, hu⟩ := exists_energySolution hf hf0
    (lowerOrderCLM (by omega : 1 ≤ k + 2) G, wkpBaseCoordinateCLM H)
  obtain ⟨b, hb, q, v, a, hq₂, hzero, hfield⟩ :=
    hu.exists_local_pointwise_smoothReaction (k := k) hk hs hf hf0 hq hv (G, H)
  refine ⟨b, hb, q, hq₂, ?_, ?_⟩
  · intro x
    have hq₀ := (hzero x).1
    have hv₀ := (hzero x).2
    have hg' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) x
    have hh' := congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hv hh hhc) x
    refine ⟨hq₀.trans hg', ?_⟩
    rw [← hv₀.trans hh']
    exact ((hfield 0 ⟨le_rfl, hb.le⟩).2.2.2 x).1
  · intro t ht x
    have hdd := deriv_deriv_eq_of_wave_derivatives
      (fun s hs ↦ ⟨((hfield s hs).2.2.2 x).1, ((hfield s hs).2.2.2 x).2.1⟩) ht
    rw [hdd]
    exact ((hfield t ⟨ht.1.le, ht.2.le⟩).2.2.2 x).2.2

end PDE.Hyperbolic.NonlinearWave.Cauchy
