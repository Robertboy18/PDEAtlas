/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.Convergence
public import PDE.Fluid.HalfPlaneSystem.FixedPoint
public import PDE.Fluid.HalfPlaneSystem.Solution

/-!
# Local existence for half-plane systems with a velocity law

This module proves local existence of classical solutions of a half-plane system for Hölder data, on
a time interval that depends only on the size of the data (`exists_isSolutionOn_Ioo`). Let `U` be a
velocity law with constants `C` up to the radius `R₀` (`IsVelocityLaw U R₀ C`), `κ` a forcing
coefficient with bounds `Bκ` (`IsForcingCoefficient κ Bκ`), `0 < α < 1`, and `ω₀ ∈ C^{1,α}`,
`θ₀ ∈ C^{2,α}` data within the closed half-plane vanishing there outside the disc of radius
`R < R₀`, with norms at most `N`. Then the system `θ_t + u · ∇θ = 0`, `ω_t + u · ∇ω = κ ∂₀θ`,
`u(t) = U (ω t)` has a solution in the class `IsSolutionOn U κ R₀` on an interval `(-T, T)` whose
length depends only on `α`, `R`, `N`, `R₀`, `C` and `Bκ`, so one `T` serves all data of the class
`IsHolderData … α R N`. At every time of `(-T, T)` the fields are again data of the class, with
support radius `(R + R₀) / 2` and the bound `iterationOutputBound C α N T`. The time `T` comes from
`exists_iterationTime` and is not computed.

The solution is the assembly (`isSolutionOn_of_fixedPoint`) of the fixed point of the iteration map
`carriedHistory U κ ω₀ θ₀ (-T) T`, which exists because the map preserves the class
`IsIterationClass T α ((R + R₀) / 2) N` for these times (`exists_iterationTime`,
`isIterationClass_carriedHistory`) and satisfies the difference estimate of Osgood type
`abs_carriedHistory_sub_le` there (`IsOsgoodIteration.exists_fixedPoint`). Negative times are
included so that the time derivatives at `t = 0` are two-sided. The library also proves the theorem
for the half-plane Biot-Savart law and `κ = 1` directly
(`Boussinesq.HalfPlane.exists_isSolutionOn_Ioo`).

## Main results

* `exists_isSolutionOn_Ioo`: local existence at regularity `C^{1,α} × C^{2,α}`.
* `isOsgoodIteration_carriedHistory`: the iteration map is of Osgood type on the class of the
  iteration, for a time `T` with the four inequalities of `exists_iterationTime`.
* `iterationCarriedConst`: the constant of the difference estimate on the class.

Uniqueness is in `Uniqueness.lean`. `Maximal.lean` restarts the local theorem to build the maximal
solution, and `IterationHigher.lean` shows that the same solution keeps the regularity of data of
order `k`.
-/

@[expose] public section

noncomputable section

open Set
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane

namespace HalfPlaneSystem

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

/-- The constant of the difference estimate of the iteration map on the class
`IsIterationClass T α R' N`. -/
def iterationCarriedConst (C : ℕ → ℝ → ℝ) (Bκ : ℕ → ℝ) (α N T : ℝ) : ℝ :=
  pairCarriedConst T
    (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 *
      (C 0 α * (1 + (2 * N + 1) * Real.log (2 + 2 * (2 * N + 1)) + (2 * N + 1)))))
    (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
      (C 1 α * max (2 * N + 1) (max (2 * N + 1) (2 * N + 1)))))
    (C 0 α * (1 + (2 * N + 1) * Real.log (2 + 2 * (2 * N + 1)) + (2 * N + 1))) (C 0 0)
    (2 * C 0 α) N (iterationAmplitudeLipschitz C Bκ α N T) Bκ

/-- **The iteration map is of Osgood type** on the class of the iteration, for a time `T` as in
`exists_iterationTime` with the margin `R' - R`. With the fixed point theorem for such maps this
gives a fixed point of the iteration. Proof: the class is invariant by
`isIterationClass_carriedHistory` and contains the constant history of the extended datum; the
difference estimate is `abs_carriedHistory_sub_le`, with the Lipschitz bound of the amplitude
in the label for histories of the class. -/
theorem isOsgoodIteration_carriedHistory (hU : IsVelocityLaw U R₀ C)
    (hκ : IsForcingCoefficient κ Bκ) {ω₀ θ₀ : ℝ^2 → ℝ} {α R R' N T : ℝ}
    (hd : IsHolderData ω₀ θ₀ α R N) (hα : 0 < α) (hα1 : α < 1) (hRR' : R ≤ R')
    (hR' : R' ≤ R₀) (hT : 0 < T)
    (h₁ : N + T * weightedForcingBound Bκ N (iterationVariationBound C α N T) ≤ 2 * N + 1)
    (h₂ : iterationGradientBound C Bκ α N T ≤ 2 * N + 1)
    (h₃ : iterationHolderBound C Bκ α N T ≤ 2 * N + 1)
    (h₄ : iterationVelocityBound C N * T ≤ R' - R) :
    IsOsgoodIteration (carriedHistory U κ ω₀ θ₀ (-T) T) (fun _ ↦ dataVorticity ω₀) T α R'
      (2 * N + 1) (2 * (2 * N + 1)) (2 * N + 1) (2 * N + 1) (iterationCarriedConst C Bκ α N T)
      (pairModulusBound (2 * (2 * N + 1) + 1) (2 * (2 * N + 1))) := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hd.abs_vorticity_le 0 (by simp))
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hstart : IsIterationClass T α R' N (fun _ ↦ dataVorticity ω₀) :=
    isIterationClass_dataVorticity hd hRR' hα.le hα1.le
  have hb := hstart.isBoundedFlowOn hU hR' hα hα1 hT.le
  have hL0 : 0 ≤ iterationAmplitudeLipschitz C Bκ α N T :=
    add_nonneg hN (mul_nonneg hT.le (weightedForcingDerivBound_nonneg hκ hN (hb.zero_le_L h0)
      (hb.zero_le_σ h0)))
  have hC00 := hU.const_nonneg 0 0
  have hC0α := hU.const_nonneg 0 α
  have hB0 := hκ.bound_nonneg 0
  have hB1 := hκ.bound_nonneg 1
  have hT0 := hT.le
  exact
    { nonneg := hT.le
      pos := hα
      const_nonneg := by
        unfold iterationCarriedConst pairCarriedConst pairVariationConst pairFlowConst
        positivity
      modulus_pos := IsHistoryPair.modulus_pos
      le_modulus := (le_max_left _ 1).trans (le_max_right _ _)
      start := hstart
      invariant := fun ω hω ↦ isIterationClass_carriedHistory hU hκ hd hα hα1 hR' hT h₁ h₂ h₃ h₄ hω
      abs_map_sub_le := fun ω₁ ω₂ hω₁ hω₂ Dm hmono hDm0 hDmA hsub t ht x hx ↦
        abs_carriedHistory_sub_le hU hκ hω₁ hω₂ hR' hα hα1 hT.le (by positivity) hmono hDm0 hDmA
          hsub hd.temperature_contDiffOn hd.norm_fderivWithin_temperature_le hL0
          (fun t ht a' a'' ha' ha'' ↦ IsIterationClass.abs_amplitude_sub_le hω₁ hU hR' hκ hd hα
            hα1 hT.le ht ha' ha'') ht hx }

/-- **Local existence at regularity `C^{1,α} × C^{2,α}`.** For a velocity law `U` up to the
radius `R₀`, a forcing coefficient `κ`, `0 < α < 1`, `R < R₀` and `N ≥ 0` there is a time
`T > 0`, depending only on `α`, `R`, `N`, `R₀`, `C` and `Bκ`, such that all data of the class
`IsHolderData ω₀ θ₀ α R N` have a solution on `(-T, T)` in the class `IsSolutionOn U κ R₀` with
these data at time zero, whose time slices are data of the class with support radius
`(R + R₀) / 2` and bound `iterationOutputBound C α N T`. The uniform time and the uniform bound
of the slices are what the construction of the maximal solution needs. Proof: for the time of
`exists_iterationTime` the iteration map is of Osgood type, so it has a fixed point in the class
of the iteration, and a fixed point is a solution by `isSolutionOn_of_fixedPoint`. -/
theorem exists_isSolutionOn_Ioo (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
    {α R N : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : R < R₀) (hN : 0 ≤ N) :
    ∃ T > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N →
      ∃ sol : Fields, IsSolutionOn U κ R₀ sol (Ioo (-T) T) ∧ HasDataAt sol 0 ω₀ θ₀ ∧
        ∀ t ∈ Ioo (-T) T, IsHolderData (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α ((R + R₀) / 2) (iterationOutputBound C α N T) := by
  set R' := (R + R₀) / 2
  have hRR' : R < R' := by simp only [R']; linarith
  have hR'R₀ : R' < R₀ := by simp only [R']; linarith
  obtain ⟨T, hT, h₁, h₂, h₃, h₄⟩ := exists_iterationTime (d := R' - R) C Bκ hα hN (by linarith)
  refine ⟨T, hT, fun ω₀ θ₀ hd ↦ ?_⟩
  have hP := isOsgoodIteration_carriedHistory (U := U) (κ := κ) hU hκ hd hα hα1 hRR'.le
    hR'R₀.le hT h₁ h₂ h₃ h₄
  obtain ⟨ω, hω, hfix⟩ := hP.exists_fixedPoint
  have hV : iterationVelocityBound C N * T ≤ R' - R := h₄
  have hsupp : R + C 0 0 * (2 * N + 1) * max (-(-T)) T < R₀ := by
    rw [neg_neg, max_self]
    unfold iterationVelocityBound at hV
    linarith
  obtain ⟨hsol, hdat⟩ := isSolutionOn_of_fixedPoint hU hκ hα hα1 hd (by linarith) hT hω
    hR'R₀.le hsupp hfix
  exact ⟨assembled U κ ω₀ θ₀ ω (-T) T, hsol, hdat, fun t ht ↦
    isHolderData_carried hU hd hα hα1 hR'R₀.le hT h₄ hω
      (isIterationClass_carriedHistory hU hκ hd hα hα1 hR'R₀.le hT h₁ h₂ h₃ h₄ hω)
      (Ioo_subset_Icc_self ht)⟩

end HalfPlaneSystem
