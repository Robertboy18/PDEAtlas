/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Interpolation.Strip.Rank
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

/-!
# Retained rank data for the selected clock construction

The bundle records the branches on their intervals of definition, their common extension,
and the
strip frame on a compact gate interval. It keeps the transition function outside
the choice of that interval.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open PDE.Analysis.ODE

/-- The retained phase construction together with a compact gate interval on
which the blended strip satisfies the compact chart's frame hypothesis.

All witnesses, including the rank interval, precede the transition function.
The phase interval still contains the event `e`; the smaller rank interval lies
in the outgoing interval of definition and maps into `Ω`. The original families
and their moving events remain explicit parameters, so the initial-section and
jet equalities do not merely compare newly chosen unrelated flows. -/
def RetainedSelectedRankStrip
    (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
    (σ : ℝ × (Fin 3 → ℝ)) (f : ℝ^3 → ℝ^3) (q : ℝ → ℝ^3)
    (Fout Fincoming : ℝ → ℝ → ℝ^3) (τout τin : ℝ → ℝ)
    (I₀ Jgate : Set ℝ) (Ω : Set (ℝ^3)) (H e tStar : ℝ)
    (rStar : Module.Basis (Fin 3) ℝ (ℝ^3)) (i : Fin 3) : Prop :=
  let lo := min 0 (e + e - H)
  let hi := max H (e + e)
  let W := prescribedClockFullVariation Ψ σ (1, 0)
  let ν := rStar i
  ∃ (Gout Gin U V : ℝ → ℝ → ℝ^3) (C : ℝ × ℝ → ℝ^3)
    (a b r : ℝ) (J O : Set ℝ) (l u : ℝ),
    ContDiff ℝ ∞ Gout.uncurry ∧ ContDiff ℝ ∞ Gin.uncurry ∧
    (∀ μ, Gout 0 μ = Fout 0 μ ∧ Gin (e + e) μ = Fincoming (e + e) μ) ∧
    EqOn (fun t ↦ Gout t 0) q (Icc lo hi) ∧
    EqOn (fun t ↦ Gin t 0) q (Icc lo hi) ∧
    (∀ t ∈ Icc (0 : ℝ) H, Gout t =ᶠ[𝓝 (0 : ℝ)] Fout t) ∧
    (∀ t ∈ Icc (e + e - H) (e + e), Gin t =ᶠ[𝓝 (0 : ℝ)] Fincoming t) ∧
    e ∈ Ioo a b ∧ tStar ∈ Ioo a b ∧ Icc a b ⊆ Ioo lo hi ∧
    IsOpen J ∧ (0 : ℝ) ∈ J ∧ J ⊆ I₀ ∧ 0 < r ∧ Icc (-r) r ⊆ J ∧
    (∀ μ ∈ J,
      EqOn (fun t ↦ Gout t μ) (fun t ↦ Fout t μ) (Icc (0 : ℝ) H) ∧
      EqOn (fun t ↦ Gin t μ) (fun t ↦ Fincoming t μ)
        (Icc (e + e - H) (e + e))) ∧
    (∀ μ ∈ J,
      Gout (τout μ) μ = Fout (τout μ) μ ∧
      Gin (τin μ) μ = Fincoming (τin μ) μ) ∧
    (∀ μ ∈ J,
      (∀ t ∈ Icc lo hi,
        HasDerivAt (fun s ↦ Gout s μ) (f (Gout t μ) - μ • Gout t μ) t) ∧
      (∀ t ∈ Icc lo hi,
        HasDerivAt (fun s ↦ Gin s μ) (f (Gin t μ) - μ • Gin t μ) t)) ∧
    ContDiff ℝ ∞ U.uncurry ∧ ContDiff ℝ ∞ V.uncurry ∧ ContDiff ℝ ∞ C ∧
    (∀ μ ∈ J, ∀ t,
      U t μ = Gout (t + τout μ - e) μ ∧ V t μ = Gin (t + τin μ - e) μ) ∧
    (∀ t ∈ Icc a b, ∀ μ ∈ J,
      HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t ∧
      HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t) ∧
    EqOn (fun t ↦ U t 0) q (Icc a b) ∧
    EqOn (fun t ↦ V t 0) q (Icc a b) ∧
    (∀ t ∈ Icc a b, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • C (t, μ)) ∧
    ((fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ) =ᶠ[𝓝 (0 : ℝ)]
      (fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ)) ∧
    (Gout (τout 0) 0 - Gin (τin 0) 0 = 0) ∧
    HasDerivAt (fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ) 0 0 ∧
    HasDerivAt (deriv (fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ)) 0 0 ∧
    IsOpen O ∧ tStar ∈ Ioo l u ∧ Icc l u ⊆ O ∧
    O ⊆ (Ioo a b ∩ Ioo (0 : ℝ) H) ∩ q ⁻¹' Ω ∧ O ⊆ Jgate ∧
    (∀ t ∈ O, Matrix.det ![⇑(f (q t)), ⇑ν, ⇑(W t)] ≠ 0) ∧
    ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ →
      ContDiff ℝ ∞ (StripRank.blendedStrip U V θ) ∧
      EqOn (fun t ↦ StripRank.blendedStrip U V θ (t, 0)) q O ∧
      InjOn (fun t ↦ StripRank.blendedStrip U V θ (t, 0)) O ∧
      MapsTo (fun t ↦ StripRank.blendedStrip U V θ (t, 0)) O Ω ∧
      ∀ t ∈ O,
        HasFDerivAt
          (fun z : (ℝ × ℝ) × ℝ ↦ StripRank.blendedStrip U V θ z.1 + z.2 • ν)
          (StripRank.stripDifferential (f (q t))
            (W t + deriv τout 0 • f (q t)) ν) ((t, 0), 0) ∧
        Matrix.det ![⇑(f (q t)), ⇑(W t + deriv τout 0 • f (q t)), ⇑ν] =
          -Matrix.det ![⇑(f (q t)), ⇑ν, ⇑(W t)] ∧
        ∃ D : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^3,
          HasFDerivAt
            (fun z : (ℝ × ℝ) × ℝ ↦ StripRank.blendedStrip U V θ z.1 + z.2 • ν)
            (D : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^3) ((t, 0), 0)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
