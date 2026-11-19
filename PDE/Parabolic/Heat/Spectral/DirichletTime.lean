/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.DirichletHolder

/-!
# Time smoothness in classical derivative norms

The derivative identity for every weighted heat vector gives arbitrary time
smoothness in each Hölder derivative graph. Evaluation then gives joint continuity
of every spatial derivative field on positive time times the domain closure.
-/

@[expose] public section

noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace HolderSpace Set
open scoped ContDiff

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- Every weighted heat vector is continuous in each classical derivative norm. -/
theorem continuousOn_holderPower (j m : ℕ) (f : DerivLp n 2 Ω) :
    ContinuousOn (S.holderPower hopen hbounded hgraph hγ j m f) (Ioi 0) :=
  fun _ ht ↦
    (S.hasDerivAt_holderPower hopen hbounded hgraph hγ j m f ht).continuousAt.continuousWithinAt

/-- The heat trajectory is smooth in time with values in every classical derivative graph. -/
theorem contDiffOn_holderPower (j m : ℕ) (f : DerivLp n 2 Ω) :
    ContDiffOn ℝ ∞ (S.holderPower hopen hbounded hgraph hγ j m f) (Ioi 0) := by
  apply contDiffOn_infty.mpr
  intro r
  induction r generalizing m with
  | zero =>
    exact contDiffOn_zero.mpr
      (S.continuousOn_holderPower hopen hbounded hgraph hγ j m f)
  | succ r ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨?_, by simp, ?_⟩
    · intro t ht
      exact (S.hasDerivAt_holderPower hopen hbounded hgraph hγ j m f ht)
        |>.differentiableAt.differentiableWithinAt
    · apply (ih (m + 1)).neg.congr
      intro t ht
      exact (S.hasDerivAt_holderPower hopen hbounded hgraph hγ j m f ht).deriv

/-- The derivative fields are jointly continuous in positive time and space, including
the domain boundary. -/
theorem continuous_holderPower_derivative (j m : ℕ) (a : MultiIndex n j)
    (f : DerivLp n 2 Ω) :
    Continuous (fun p : Ioi (0 : ℝ) × closure Ω ↦
      (S.holderPower hopen hbounded hgraph hγ j m f p.1).derivative a p.2) := by
  have h := (S.continuousOn_holderPower hopen hbounded hgraph hγ j m f).domRestrict
  exact continuous_eval.comp
    (((CKGammaOn.derivativeCLM a).continuous.comp (h.comp continuous_fst)).prodMk
      continuous_snd)

end HeatEquation.DirichletHeatSpectrum
