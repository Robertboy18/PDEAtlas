/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Fixed

/-!
# The physical terminal jet of a fixed signed gate

A supplied family has the same terminal ratio as the weight moment on
one open parameter neighborhood. The coefficients range over an arbitrary set.
Localization, the candidate equation, and agreement with the family
establish this identity before the derivative transfer.

For each fixed coefficient vector, the fixed-gate moment theorem gives
the value and both parameter derivatives. Restricting the identity to the two
continuous parameter axes transfers this jet to the same supplied family and
terminal event. The bumps and the base lower-weight normalizer remain fixed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- A terminal identity on a common open parameter neighborhood transfers the
fixed-gate moment jet to the supplied physical family. The moments are the integrals of the fixed
bumps with the given coefficients. The displacement factor is the derivative of the same event
gap. -/
theorem prescribed_clock_physical_jet_of_terminal_identity (L Bhit : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)}
    {V : Set (Fin 3 → ℝ)} (hU : IsOpen U) (h0 : (0, 0) ∈ U) (hL : ContDiffOn ℝ ∞ L U)
    (hBhit : ContDiffOn ℝ ∞ Bhit U) (β : Fin 3 → ℝ → ℝ) (q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3)
    (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j)) (hβcompact : ∀ j, HasCompactSupport (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint : let D0 := parameterizedClockPassageData L Bhit (0, 0); ∀ j i : Fin 3,
      Integrable (fun y ↦ β j y * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i)) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : (Fin 3 → ℝ) → ℝ → ℝ := fun c ↦
      (Ioo (205 : ℝ) (2051 / 10)).indicator
        (fun y ↦ (∑ j, c j * β j y) / D0.wMinus y)
    (∀ p ∈ U, ∀ c ∈ V,
      (q p c (L p)) 0 / (q p c (L p)) 2 =
        prescribedClockWeightMoment (b c) L Bhit p) →
    ∀ c ∈ V,
      let m : Fin 3 → ℝ := fun i ↦ ∫ y, (∑ j, c j * β j y) *
        (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i
      (q (0, 0) c (L (0, 0))) 0 / (q (0, 0) c (L (0, 0))) 2 = m 0 + m 1 ∧
      HasDerivAt
        (fun μ ↦ (q (μ, 0) c (L (μ, 0))) 0 / (q (μ, 0) c (L (μ, 0))) 2)
        (m 2) 0 ∧
      HasDerivAt
        (fun a ↦ (q (0, a) c (L (0, a))) 0 / (q (0, a) c (L (0, a))) 2)
        (-4 * deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0 * m 1) 0 := by
  classical
  dsimp only
  intro hterminal c hc
  let D0 := parameterizedClockPassageData L Bhit (0, 0)
  let m : Fin 3 → ℝ := fun i ↦ ∫ y, (∑ j, c j * β j y) * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i
  obtain ⟨_, _, _, _, _, _, hbase, hspeed, hdisplacement⟩ :=
    prescribed_clock_fixed_gate_of_selected_moments L Bhit hU h0 hL hBhit
      β c m hβsmooth hβcompact hβsupport hβint rfl
  have hspeedAxis : Continuous (fun μ : ℝ ↦ (μ, (0 : ℝ))) := continuous_id.prodMk continuous_const
  have hdisplacementAxis : Continuous (fun a : ℝ ↦ ((0 : ℝ), a)) :=
    continuous_const.prodMk continuous_id
  have hspeedMem : ∀ᶠ μ : ℝ in 𝓝 0, (μ, (0 : ℝ)) ∈ U :=
    hspeedAxis.continuousAt.eventually_mem (hU.mem_nhds h0)
  have hdisplacementMem : ∀ᶠ a : ℝ in 𝓝 0, ((0 : ℝ), a) ∈ U :=
    hdisplacementAxis.continuousAt.eventually_mem (hU.mem_nhds h0)
  refine ⟨(hterminal (0, 0) h0 c hc).trans hbase, ?_, ?_⟩
  · apply hspeed.congr_of_eventuallyEq
    exact hspeedMem.mono (fun μ hμ ↦ hterminal (μ, 0) hμ c hc)
  · apply hdisplacement.congr_of_eventuallyEq
    exact hdisplacementMem.mono (fun a ha ↦ hterminal (0, a) ha c hc)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
