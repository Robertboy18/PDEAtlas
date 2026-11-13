/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PrincipalForms
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoffWeak

/-!
# Local negative-Sobolev acceleration

The local spatial wave form is a bounded functional on H¹₀. Its value along
an L²-time energy curve is an L²-time H⁻¹-valued function. The endpoint weak
velocity equation identifies this function as the distributional acceleration,
including the prescribed initial velocity, on the original spatial domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.ZeroTrace
open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- The weak gradient form on an arbitrary spatial domain, valued in H⁻¹. -/
def localGradientDualCLM : H¹(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
  ∑ i : Fin n, (innerSL ℝ).bilinearComp (wkpCoordinateCLM (singleDerivIndex n i))
    (derivCoordCLM i)

/-- The distributional acceleration Δu − f(Du,v,u), as an H⁻¹ functional. -/
def localAcceleration (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(Ω) × DerivLp n 2 Ω) : StrongDual ℝ H¹₀(Ω) :=
  -localGradientDualCLM z.1 - loadFunctionalCLM (localReaction hf hf0 z)

/-- Evaluation of the H⁻¹ acceleration is the negative spatial weak form. -/
theorem localAcceleration_apply (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(Ω) × DerivLp n 2 Ω) (ψ : H¹₀(Ω)) :
    localAcceleration hf hf0 z ψ = -localSpatialPairing hf hf0 z ψ := by
  simp only [localAcceleration, localGradientDualCLM, sub_apply, neg_apply, sum_apply]
  change -(∑ i : Fin n, ⟪z.1.val (singleDerivIndex n i),
      (ψ : H¹(Ω)).val (singleDerivIndex n i)⟫_ℝ) -
    ⟪localReaction hf hf0 z, wkpBaseCoordinateCLM (ψ : H¹(Ω))⟫_ℝ =
      -((∑ i : Fin n, ⟪z.1.val (singleDerivIndex n i), (ψ : H¹(Ω)).val (singleDerivIndex n i)⟫_ℝ) +
          ⟪localReaction hf hf0 z, wkpBaseCoordinateCLM (ψ : H¹(Ω))⟫_ℝ)
  simp only [sub_eq_add_neg, neg_add]

/-- An L²-time local energy curve has an L²-time H⁻¹ acceleration. -/
theorem memLp_localAcceleration (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    {μ : Measure ℝ} {u : ℝ → H¹(Ω) × DerivLp n 2 Ω} (hu : MemLp u 2 μ) :
    MemLp (fun t ↦ localAcceleration hf hf0 (u t)) 2 μ := by
  let G : (H¹(Ω) × DerivLp n 2 Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) :=
    localGradientDualCLM.comp (.fst ℝ _ _)
  let P : DerivLp n 2 Ω →L[ℝ] StrongDual ℝ H¹₀(Ω) := loadFunctionalCLM
  have hG : MemLp (fun t ↦ G (u t)) 2 μ := G.comp_memLp' hu
  have hR : MemLp (fun t ↦ localReaction hf hf0 (u t)) 2 μ := memLp_localReaction hf hf0 hu
  have hP : MemLp (fun t ↦ P (localReaction hf hf0 (u t))) 2 μ := P.comp_memLp' hR
  exact hG.neg.sub hP

/-- A local weak solution has a Bochner L²(H⁻¹) distributional second
time derivative, with its initial velocity encoded by the same endpoint tests. -/
theorem IsLocalBochnerWeakCurveOn.exists_acceleration {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(Ω) × DerivLp n 2 Ω} {T : ℝ} {u : ℝ → H¹(Ω) × DerivLp n 2 Ω}
    (hu : IsLocalBochnerWeakCurveOn hf hf0 x T u) :
    ∃ A : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 T)),
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ ψ : H¹₀(Ω),
        A t ψ = -localSpatialPairing hf hf0 (u t) ψ) ∧
      ∀ (ψ : H¹₀(Ω)) (τ : TimeTest 0 T),
        -(∫ t in (0 : ℝ)..T,
          ⟪wkpBaseCoordinateCLM (ψ : H¹(Ω)), (u t).2⟫_ℝ * τ.derivFun t) =
          (∫ t in (0 : ℝ)..T, A t ψ * τ.toFun t) +
            ⟪wkpBaseCoordinateCLM (ψ : H¹(Ω)), x.2⟫_ℝ * τ.toFun 0 := by
  have hA := memLp_localAcceleration hf hf0 hu.integrable
  refine ⟨hA.toLp _, ?_, ?_⟩
  · filter_upwards [hA.coeFn_toLp] with t ht
    intro ψ
    rw [ht, localAcceleration_apply]
  · intro ψ τ
    rw [hu.velocity]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hu.interval_nonempty.le]
    filter_upwards [hA.coeFn_toLp] with t ht
    rw [ht, localAcceleration_apply]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
