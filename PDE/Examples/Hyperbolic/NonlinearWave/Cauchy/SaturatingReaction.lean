/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothData
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Reaction

/-!
# A classical wave for the saturating reaction `s / (1 + s²)`

The reaction `f(s) = s / (1 + s²)` is smooth, globally 1-Lipschitz and vanishes at zero
(`contDiff_saturatingReaction`, `lipschitzWith_saturatingReaction`, `saturatingReaction_zero`).
So the local existence theorem for smooth globally Lipschitz reactions,
`exists_classical_smoothReaction_of_smoothCompact`, applies to it: in every positive dimension,
smooth compactly supported data give a solution of `u_tt - Δu + u / (1 + u²) = 0` that is
jointly `C²` on a time strip `0 < t < b` and attains both data.
-/

@[expose] public noncomputable section

open Set
open scoped Laplacian

namespace PDE.Examples.Cauchy

open PDE.Hyperbolic.NonlinearWave.Cauchy

/-- In every positive dimension, smooth compactly supported data give a local classical solution
of `u_tt - Δu + u / (1 + u²) = 0`. -/
example {n : ℕ} [NeZero n] (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧ ∃ q : C(ℝ × ℝ^n, ℝ),
      ContDiffOn ℝ 2 q (Ioo 0 b ×ˢ univ) ∧
      (∀ x, q (0, x) = g x ∧
        HasDerivWithinAt (fun t ↦ q (t, x)) (h x) (Icc 0 b) 0) ∧
      ∀ t ∈ Ioo 0 b, ∀ x,
        deriv (fun s ↦ deriv (fun r ↦ q (r, x)) s) t -
          Δ (fun y ↦ q (t, y)) x + q (t, x) / (1 + q (t, x) ^ 2) = 0 :=
  exists_classical_smoothReaction_of_smoothCompact contDiff_saturatingReaction
    lipschitzWith_saturatingReaction saturatingReaction_zero g h hg hh hgc hhc

end PDE.Examples.Cauchy
