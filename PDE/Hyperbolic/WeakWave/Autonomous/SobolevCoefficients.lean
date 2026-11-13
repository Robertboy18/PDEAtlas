/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Coefficients.LInfinity
public import PDE.Hyperbolic.WeakWave.Coefficients.IntegrationByParts
public import PDE.Hyperbolic.WeakWave.Autonomous.Uniqueness

/-!
# Autonomous waves with Sobolev coefficients

A symmetric elliptic principal matrix, a `W¹,∞` drift and a bounded potential give
uniqueness and a uniform energy bound for every weak wave. Spatial integration by
parts supplies the reverse lower-order estimate used by backward-test uniqueness.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Autonomous weak waves agree for a Sobolev drift, with no sign assumption on
lower-order coefficients. All form bounds follow from the coefficient norms. -/
theorem weakWave_eq_of_autonomous_sobolev_coefficients (hn : 0 < n) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (A : Fin n → Fin n → DerivLp n ∞ Ω) (B : Fin n → W^{1,∞}(Ω))
    (C : DerivLp n ∞ Ω) (hsymm : AESymmetricCoefficient A) {alpha : ℝ}
    (helliptic : AEUniformlyElliptic A alpha)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))} {q₀ : H¹₀(Ω)}
    {p₀ : DerivLp n 2 Ω} {u₁ u₂ : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v₁ v₂ : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {w₁ w₂ : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (h₁ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
      (fun i ↦ mulLpLeft (wkpBaseCoordinateCLM (B i))) (mulLpLeft C)) ell u₁ v₁ w₁ q₀ p₀)
    (h₂ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
      (fun i ↦ mulLpLeft (wkpBaseCoordinateCLM (B i))) (mulLpLeft C)) ell u₂ v₂ w₂ q₀ p₀) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ w₁ = w₂ := by
  let F := variableCoeffForm (multiplicationCoefficientOperator A)
  let R := lowerOrderForm (fun i ↦ mulLpLeft (wkpBaseCoordinateCLM (B i))) (mulLpLeft C)
  let LR := (∑ i, (‖(B i : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)‖ +
    ‖(B i : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n i)‖)) + ‖C‖
  obtain ⟨κ, hκ, hcoerc⟩ := exists_uniform_coercivity_coefficient_forms
    hn hbounded h₁.interval_nonempty (fun _ ↦ A) (fun _ _ ↦ helliptic)
  exact h₁.eq_of_autonomous (A := F) (R := R)
    (variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae A hsymm))
    hκ (by dsimp [LR]; positivity) (hcoerc a ⟨le_rfl, h₁.interval_nonempty.le⟩)
    (abs_lowerOrderForm_le_base_left hΩ B C) h₂

/-- One constant controls every weak wave with these autonomous coefficients.
The existence and uniqueness assertions use arbitrary `H¹₀ × L²` initial data. -/
theorem exists_uniform_energy_bound_of_autonomous_sobolev_coefficients (hn : 0 < n) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hab : a < b) (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → W^{1,∞}(Ω)) (C : DerivLp n ∞ Ω) (hsymm : AESymmetricCoefficient A) {alpha : ℝ}
    (helliptic : AEUniformlyElliptic A alpha) :
    let T := h10L2GelfandTriple hΩ
    let F := fullDivergenceForm (multiplicationCoefficientOperator A)
      (fun i ↦ mulLpLeft (wkpBaseCoordinateCLM (B i))) (mulLpLeft C)
    ∃ M : ℝ, 0 < M ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (q₀ : H¹₀(Ω)) (p₀ : DerivLp n 2 Ω),
      (∃ u v w, Hyperbolic.Variational.IsGelfandWeakWaveSolution T (fun _ ↦ F)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u v w q₀ p₀) ∧
      ∀ u v w, Hyperbolic.Variational.IsGelfandWeakWaveSolution T (fun _ ↦ F)
        (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u v w q₀ p₀ →
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧
        ∀ᵐ t ∂volume.restrict (Ioc a b),
          ‖u t‖ + ‖v t‖ ≤ M * (‖f‖ + ‖q₀‖ + ‖p₀‖) := by
  let z := ((fun i ↦ wkpBaseCoordinateCLM (B i)), C)
  obtain ⟨M, hM, hex⟩ := exists_uniform_energy_bound_of_linf_coefficients
    hn hΩ hbounded hab (fun _ ↦ A) (fun _ ↦ 0) (fun _ ↦ z)
    (LipschitzWith.const A).lipschitzOnWith.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall fun _ ↦ hasDerivAt_const _ A)
    0 ‖z‖₊ (by simp) aestronglyMeasurable_const
    (fun _ _ ↦ le_rfl) (fun _ _ ↦ hsymm) (fun _ _ ↦ helliptic)
  refine ⟨M, hM, fun f q₀ p₀ ↦ ?_⟩
  obtain ⟨u₀, v₀, w₀, h₀, hu₀, hv₀, hbound⟩ := hex f q₀ p₀
  refine ⟨⟨u₀, v₀, w₀, h₀⟩, fun u v w h ↦ ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := weakWave_eq_of_autonomous_sobolev_coefficients
    hn hΩ hbounded A B C hsymm helliptic h h₀
  exact ⟨hu₀, hv₀, hbound⟩

end SobolevSpace.GraphSpace
