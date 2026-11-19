/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Basic
public import PDE.Hyperbolic.WeakWave.Galerkin.BochnerRealization
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Energy
import PDE.Hyperbolic.WeakWave.Galerkin.EnergyBounds

/-!
# Uniform bounds for finite differentiated Galerkin families

The projected Evans compatibility data give one initial-energy bound for
every time-derivative level.  Combining this finite sum with the common
forcing budget yields the dimension-independent bounds used in the weak
compactness argument.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, compatibility conditions (62) and estimate
  (64).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
The finite sum of the ambient compatibility energies bounds the projected
initial energy at every derivative level.

The kinetic estimate is the pivot contractivity of `P.projection`; the
potential estimate uses the operator norm of `A` and the uniform
energy-space stability constant `K`.
-/
theorem projectedInitialData_gelfandWaveEnergy_le_sum (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) {K : NNReal} (P : StableTrialProjection T S K) (A : V →L[ℝ] StrongDual ℝ V)
    {m : ℕ} (q : Fin (m + 1) → V) (p : Fin (m + 1) → H) (q0 p0 : Fin (m + 1) → S)
    (hinitial : ∀ r : Fin (m + 1), q0 r = P.energyProjection (q r) ∧ p0 r = P.projection (p r)) :
    ∀ r : Fin (m + 1), (1 / 2 : ℝ) * ‖T.inclusion (p0 r : V)‖ ^ 2 + (1 / 2 : ℝ) *
      A (q0 r : V) (q0 r : V) ≤ ∑ j : Fin (m + 1),
      ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * ((K : ℝ) * ‖q j‖) ^ 2) := by
  intro r
  obtain ⟨hq, hp⟩ := hinitial r
  have hkinetic : ‖T.inclusion (p0 r : V)‖ ^ 2 ≤ ‖p r‖ ^ 2 := by
    rw [hp]
    gcongr
    exact P.norm_inclusion_projection_le (p r)
  have hpotential : A (q0 r : V) (q0 r : V) ≤ ‖A‖ * ((K : ℝ) * ‖q r‖) ^ 2 := by
    refine (Real.le_norm_self _).trans ((A.le_opNorm₂ _ _).trans ?_)
    rw [mul_assoc, ← sq, hq]
    gcongr
    exact P.norm_le (q r)
  refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦
    (1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * ((K : ℝ) * ‖q j‖) ^ 2)
    (fun j _ ↦ by positivity) (Finset.mem_univ r))
  linarith

/--
Evans's uniform estimates for every level of a finite differentiated
Galerkin family.

One explicit constant controls all derivative indices:

`(sum_j (‖p_j‖²/2 + ‖A‖ (K‖q_j‖)²/2) + G)
  exp ((2 + LR²/c)(b-a))`.

It depends on the ambient compatibility data and the common structural and
forcing constants, but not on the selected derivative index or the
dimension of the trial space.  The theorem also returns the corresponding
essential `L∞` and Bochner `L²` estimates used in Evans's compactness step.
-/
theorem finiteTimeDerivativeFamily_uniformBounds (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] [CompleteSpace S] {K : NNReal}
    (P : StableTrialProjection T S K) (A R : V →L[ℝ] StrongDual ℝ V) {m : ℕ}
    (dualForcing : Fin (m + 1) → ℝ → StrongDual ℝ V) (forcing : Fin (m + 1) → ℝ → H) {a b : ℝ}
    (q : Fin (m + 1) → V) (p : Fin (m + 1) → H) (q0 p0 : Fin (m + 1) → S)
    (U : (r : Fin (m + 1)) → SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T S (A + R))
      (gelfandGalerkinForcing T S (dualForcing r)) a b (q0 r) (p0 r))
    (hinitial : ∀ r : Fin (m + 1), q0 r = P.energyProjection (q r) ∧ p0 r = P.projection (p r))
    (hab : a ≤ b)
    (hdualForcing : ∀ r : Fin (m + 1), ∀ᵐ s ∂volume.restrict (Set.Ioc a b), dualForcing r s =
      T.pivotToDual (forcing r s))
    (hforcingSqIntegrable : ∀ r : Fin (m + 1),
      IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2) volume a b)
    (G c LR : ℝ)
    (hforcingBudget : ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      (∫ s in a..t, (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2) ≤ G)
    (hc : 0 < c) (hA_symmetric : ∀ x y : V, A x y = A y x)
    (hcoercive : ∀ v : V, c * ‖v‖ ^ 2 ≤ A v v)
    (hRbound : ∀ v w : V, |R v w| ≤ LR * ‖v‖ * ‖T.inclusion w‖) :
    (∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      gelfandWaveEnergy T S (fun _ ↦ A) (U r).displacement (U r).velocity t ≤
        ((∑ j : Fin (m + 1), ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
          Real.exp ((2 + LR ^ 2 / c) * (b - a))) ∧
    (∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖(U r).displacementLp hab t‖ ≤ Real.sqrt ((2 / c) *
        (((∑ j : Fin (m + 1),
          ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
          Real.exp ((2 + LR ^ 2 / c) * (b - a))))) ∧
    (∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      ‖(U r).velocityLp hab t‖ ≤ Real.sqrt (2 *
        (((∑ j : Fin (m + 1),
          ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
          Real.exp ((2 + LR ^ 2 / c) * (b - a))))) ∧
    (∀ r : Fin (m + 1),
      ‖(U r).displacementLp hab‖ ^ 2 ≤ ((2 / c) *
        (((∑ j : Fin (m + 1),
          ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
          Real.exp ((2 + LR ^ 2 / c) * (b - a)))) * (b - a)) ∧
    (∀ r : Fin (m + 1),
      ‖(U r).velocityLp hab‖ ^ 2 ≤ (2 *
        (((∑ j : Fin (m + 1),
          ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
          Real.exp ((2 + LR ^ 2 / c) * (b - a)))) * (b - a)) := by
  have hG : 0 ≤ G := by simpa using hforcingBudget (Fin.last m) a ⟨le_rfl, hab⟩
  have henergy (r : Fin (m + 1)) (t : ℝ) (ht : t ∈ Icc a b) :
      gelfandWaveEnergy T S (fun _ ↦ A) (U r).displacement (U r).velocity t ≤
        ((∑ j : Fin (m + 1), ((1 / 2 : ℝ) * ‖p j‖ ^ 2 + (1 / 2 : ℝ) * ‖A‖ * (K * ‖q j‖) ^ 2)) + G) *
          Real.exp ((2 + LR ^ 2 / c) * (b - a)) := by
    refine (finiteTimeDerivativeFamily_gelfandWaveEnergy_le_exp T S A R dualForcing forcing q0
      p0 U hab hdualForcing hforcingSqIntegrable G c LR hforcingBudget hc hA_symmetric hcoercive
      hRbound r t ht).trans ?_
    gcongr (?_ + _) * Real.exp (_ * (?_ - _))
    · rw [gelfandWaveEnergy, (U r).initialDisplacement, (U r).initialVelocity]
      exact projectedInitialData_gelfandWaveEnergy_le_sum T S P A q p q0 p0 hinitial r
    · exact ht.2
  have hco (r : Fin (m + 1)) : ∀ t ∈ Icc a b, c * ‖((U r).displacement t : V)‖ ^ 2 ≤
      A ((U r).displacement t : V) ((U r).displacement t : V) := fun t _ ↦ hcoercive _
  exact ⟨henergy, fun r ↦ (U r).ae_norm_displacementLp_le_of_gelfandWaveEnergy_le
      (A := fun _ ↦ A) (R := fun _ ↦ R) hab hc (hco r) (henergy r),
    fun r ↦ (U r).ae_norm_velocityLp_le_of_gelfandWaveEnergy_le (A := fun _ ↦ A)
      (R := fun _ ↦ R) hab hc (hco r) (henergy r),
    fun r ↦ (U r).norm_displacementLp_sq_le_of_gelfandWaveEnergy_le (A := fun _ ↦ A)
      (R := fun _ ↦ R) hab hc (hco r) (henergy r),
    fun r ↦ (U r).norm_velocityLp_sq_le_of_gelfandWaveEnergy_le (A := fun _ ↦ A)
      (R := fun _ ↦ R) hab hc (hco r) (henergy r)⟩

end Hyperbolic.Variational.GelfandGalerkin
