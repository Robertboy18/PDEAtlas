/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Coefficients.CompactRegularity
public import PDE.Hyperbolic.WeakWave.Coefficients.Continuous
public import PDE.Hyperbolic.WeakWave.EvansCoefficientIntegrability

/-!
# Evans's weak-wave uniqueness from classical coefficients

On a bounded open domain, a symmetric uniformly elliptic principal matrix with continuous
time derivative and a drift with continuous spatial derivatives determine a unique weak
Dirichlet wave. Potential and drift values are jointly continuous on the closed cylinder.
These hypotheses follow from Evans's `C¹` coefficient assumptions.

The proof derives norm regularity from compactness, coercivity from Poincaré's inequality,
and the `L² × H¹₀` lower-order estimate from spatial integration by parts. The
backward-test uniqueness theorem then identifies displacement, velocity, and acceleration.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.1, assumptions (5)-(7), and §7.2.2, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Convert coefficient norm regularity to the hypotheses of backward-test uniqueness. -/
private theorem weakWave_eq_of_coefficient_regularity (hn : 0 < n) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
    (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hcoeffDotCont : ContinuousOn coeffDot (Icc a b)) (N : ℝ≥0)
    (hcoeffDotBound : ∀ t ∈ Icc a b, ‖coeffDot t‖ ≤ N)
    (hcoeffAC : AbsolutelyContinuousOnInterval coeff a b)
    (hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt coeff (coeffDot t) t)
    (hzcont : ContinuousOn z (Icc a b)) (LR : ℝ) (hLR : 0 ≤ LR)
    (hRbound : ∀ t ∈ Icc a b, ∀ u v : H¹₀(Ω), |lowerOrderForm (fun i ↦ mulLpLeft ((z t).1 i))
      (mulLpLeft (z t).2) u v| ≤ LR * ‖baseCoordCLM u‖ * ‖v‖)
    (hsymmAE : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t)) {alpha : ℝ}
    (hellipticAE : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))} {q₀ : H¹₀(Ω)}
    {p₀ : DerivLp n 2 Ω} {u₁ u₂ : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v₁ v₂ : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {w₁ w₂ : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (h₁ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
      (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)) ell u₁ v₁ w₁ q₀ p₀)
    (h₂ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
      (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)) ell u₂ v₂ w₂ q₀ p₀) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ w₁ = w₂ := by
  classical
  let : MeasurableSpace (H¹₀(Ω)) := borel (H¹₀(Ω))
  have : BorelSpace (H¹₀(Ω)) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (H¹₀(Ω))) := borel (StrongDual ℝ (H¹₀(Ω)))
  have : BorelSpace (StrongDual ℝ (H¹₀(Ω))) := ⟨rfl⟩
  have hab := h₁.interval_nonempty
  let F := multiplicationCoeffFormCLMOf (H¹₀(Ω)) (H¹₀(Ω))
    (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le
  let G := multiplicationLowerOrderFormCLMOf (H¹₀(Ω))
    (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le baseCoordCLM baseCoordCLM_norm_le
  obtain ⟨κ, hκ, hcoercive⟩ :=
    exists_uniform_coercivity_coefficient_forms hn hΩbounded hab coeff hellipticAE
  have hmeas {X : Type} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
      {f : ℝ → X} (hf : ContinuousOn f (Icc a b)) :
      AEStronglyMeasurable f (volume.restrict (Ioc a b)) :=
    (hf.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc).mono_set
      Ioc_subset_Icc_self
  refine h₁.eq_of_evans_coefficients_of_operator_measurable h₂
    (A := fun t ↦ F (coeff t)) (Adot := fun t ↦ F (coeffDot t)) (R := fun t ↦ G (z t))
    (fun _ _ _ _ ↦ rfl) ((lipschitzWith_multiplicationCoeffFormCLMOf (H¹₀(Ω)) (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le (fun i ↦ derivCoordCLM i)
      derivCoordCLM_norm_le).comp_absolutelyContinuousOnInterval hcoeffAC)
    (hcoeffDeriv.mono fun t ht ↦ hasDerivAt_multiplicationCoeffFormOf (H¹₀(Ω)) (H¹₀(Ω))
      (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le (fun i ↦ derivCoordCLM i)
      derivCoordCLM_norm_le ht) (F.continuous.comp_aestronglyMeasurable (hmeas hcoeffDotCont))
    (G.continuous.comp_aestronglyMeasurable (hmeas hzcont)) (fun t ht x y ↦ variableCoeffForm_symm
        (symmetricCoefficientOperator_multiplication_of_ae (coeff t) (hsymmAE t ht)) x y)
    κ ((n : ℝ) ^ 2 * N) LR hκ (by positivity) hLR hcoercive (fun t ht x ↦ ?_) hRbound
  have hnorm : ‖F (coeffDot t)‖ ≤ (n : ℝ) ^ 2 * N :=
    (norm_multiplicationCoeffFormOf_le (H¹₀(Ω)) (H¹₀(Ω)) (fun i ↦ derivCoordCLM i)
      derivCoordCLM_norm_le (fun i ↦ derivCoordCLM i) derivCoordCLM_norm_le (coeffDot t)).trans
      (mul_le_mul_of_nonneg_left (hcoeffDotBound t ht) (sq_nonneg _))
  calc
    _ = ‖F (coeffDot t) x x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖F (coeffDot t)‖ * ‖x‖ * ‖x‖ := (F (coeffDot t)).le_opNorm₂ x x
    _ ≤ (n : ℝ) ^ 2 * N * ‖x‖ * ‖x‖ := by gcongr
    _ = _ := by ring

/-- Weak Dirichlet waves with the same data agree under classical Evans coefficient
hypotheses. All operator bounds and time integrability conditions are derived from the
coefficient fields. The coefficient classes may be any representatives of those fields. -/
theorem weakWave_eq_of_continuousOn_compact_coefficients (hn : 0 < n) (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (A Adot : ℝ → Fin n → Fin n → ℝ^n → ℝ)
    (B : ℝ → Fin n → ℝ^n → ℝ) (DB : ℝ → Fin n → Fin n → ℝ^n → ℝ) (C : ℝ → ℝ^n → ℝ)
    (hA : ∀ i j, ContinuousOn (fun p ↦ A p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAdot : ∀ i j, ContinuousOn (fun p ↦ Adot p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAderiv : ∀ i j, ∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ A s i j x) (Adot t i j x) (Icc a b) t)
    (hB : ∀ i, ContinuousOn (fun p ↦ B p.1 i p.2) (Icc a b ×ˢ closure Ω))
    (hDB : ∀ i j, ContinuousOn (fun p ↦ DB p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hC : ContinuousOn (Function.uncurry C) (Icc a b ×ˢ closure Ω))
    (hBdiff : ∀ t ∈ Icc a b, ∀ i, ∀ x ∈ Ω, ContDiffAt ℝ 1 (B t i) x)
    (hDBderiv : ∀ t ∈ Icc a b, ∀ i j, ∀ x ∈ Ω, DB t i j x = (∂[j] (B t i)) x)
    (hsymm : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ i j, A t i j x = A t j i x) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i : Fin n, ξ i * ξ i ≤ ∑ i :
      Fin n, ∑ j : Fin n, A t i j x * ξ j * ξ i)
    (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω) (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω)
    (hArep : ∀ t ∈ Icc a b, ∀ i j, (coeff t i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A t i j)
    (hBrep : ∀ t ∈ Icc a b, ∀ i, ((z t).1 i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] B t i)
    (hCrep : ∀ t ∈ Icc a b, ((z t).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] C t)
    {ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))} {q₀ : H¹₀(Ω)}
    {p₀ : DerivLp n 2 Ω} {u₁ u₂ : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v₁ v₂ : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {w₁ w₂ : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (h₁ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
      (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)) ell u₁ v₁ w₁ q₀ p₀)
    (h₂ : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hΩ)
      (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
      (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2)) ell u₂ v₂ w₂ q₀ p₀) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ w₁ = w₂ := by
  classical
  have hab := h₁.interval_nonempty
  have hμΩ : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hΩ.measurableSet
  obtain ⟨coeffDot, N, hcoeffDotCont, hcoeffDotBound, hcoeffAC, hcoeffDeriv⟩ :=
    exists_principal_derivative_of_continuousOn_compact hΩ hΩbounded hab
      A Adot coeff hA hAdot hAderiv hArep
  obtain ⟨hzcont, LR, hLR, hRbound⟩ :=
    exists_lowerOrder_bound_base_left_of_continuousOn_compact hΩ hΩbounded
      B DB C z hB hDB hC hBdiff hDBderiv hBrep hCrep
  refine weakWave_eq_of_coefficient_regularity hn hΩ hΩbounded coeff coeffDot z
    hcoeffDotCont N hcoeffDotBound hcoeffAC hcoeffDeriv hzcont LR hLR hRbound
    (fun t ht i j ↦ ?_) (fun t ht ↦ ⟨halpha, ?_⟩) h₁ h₂
  · filter_upwards [hμΩ, hArep t ht i j, hArep t ht j i] with x hx hij hji
    exact hij.trans ((hsymm t ht x hx i j).trans hji.symm)
  · filter_upwards [hμΩ, ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hArep t ht i j]
      with x hx hxeq ξ
    simpa only [hxeq] using helliptic t ht x hx ξ

end SobolevSpace.GraphSpace
