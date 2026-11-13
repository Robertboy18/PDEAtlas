/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.NonlinearWave.Cauchy.FirstJet
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalWeak
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.HigherBochnerWeak

/-!
# Local energy data and higher regularity for first-jet reactions

For the Lipschitz reaction `‖Du‖ + |u_t| + u`, data that are locally in `H¹ × L²` give
a local weak solution (`FirstJet.exists_localWeakSolution`), and data locally in
`H² × H¹` give one with local `H²` regularity (`FirstJet.exists_localWeakSolution_h2`).
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Examples.Cauchy.FirstJet

open PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Locally `H¹ × L²` data give a local weak solution. -/
example {n : ℕ} {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 1 2 univ g) (hv : IsLocallyWkpOn 0 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ,
      FirstJet.IsLocalWeakSolution (normReaction_lipschitz n)
        (by simp [normReaction]) g v w := by
  obtain ⟨w, hw, _⟩ := FirstJet.exists_localWeakSolution
    (normReaction_lipschitz n) (by simp [normReaction]) hg hv
  exact ⟨w, hw⟩

/-- Locally `H² × H¹` data give a local weak solution with local `H²` regularity. -/
example {n : ℕ} {g v : ℝ^n → ℝ}
    (hg : IsLocallyWkpOn 2 2 univ g) (hv : IsLocallyWkpOn 1 2 univ v) :
    ∃ w : ℝ → ℝ^n → ℝ × ℝ,
      FirstJet.IsLocalWeakSolution (normReaction_lipschitz n)
        (by simp [normReaction]) g v w ∧
      FirstJet.HasLocalH2Regularity (normReaction_lipschitz n)
        (by simp [normReaction]) w :=
  FirstJet.exists_localWeakSolution_h2 (normReaction_lipschitz n)
    (by simp [normReaction]) hg hv

end PDE.Examples.Cauchy.FirstJet
