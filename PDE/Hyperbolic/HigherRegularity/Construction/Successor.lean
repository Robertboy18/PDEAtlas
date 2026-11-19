/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Temporal.CompatibleStep
public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.IntegratedStep
public import PDE.Hyperbolic.HigherRegularity.Data.WaveJet

/-!
# The successor in the all-order wave construction

A regular differentiated wave gives the next wave by integration and
shifted elliptic recovery. The differentiated data budget is estimated by
the original one, so the resulting constant can be fixed before the data.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The structural constant for one descent in the wave construction. -/
def waveSuccessorConstant (a b mu loadNorm inverseNorm K : ℝ) : ℝ :=
  let R := ((b - a)⁻¹ + 1) * max 1 (b - a)
  let P := K * (1 + R + loadNorm)
  1 + P + inverseNorm * (R + P + |mu| * (1 + (b - a) * P))

/-- Positive input constants give a positive successor constant. -/
theorem waveSuccessorConstant_pos (hab : a < b) (mu : ℝ)
    {loadNorm inverseNorm K : ℝ} (hL : 0 ≤ loadNorm) (hS : 0 ≤ inverseNorm) (hK : 0 < K) :
    0 < waveSuccessorConstant a b mu loadNorm inverseNorm K := by
  unfold waveSuccessorConstant
  positivity

/-- Integrate and upgrade one differentiated wave, retaining its
velocity and acceleration and converting its estimate to the original data. -/
theorem exists_regular_wave_successor
    (hopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (hL : ∀ (G : W^{(m + 2),2}(Ω)) (g : H¹₀(Ω)),
      wkpBaseCoordinateCLM G = baseCoordCLM g →
      fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C) g =
          loadFunctional (wkpBaseCoordinateCLM (L m G)))
    (mu : ℝ) (S : W^{m,2}(Ω) →L[ℝ] W^{(m + 2),2}(Ω))
    (hS : ∀ (F : W^{m,2}(Ω)) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution A B C mu (wkpBaseCoordinateCLM F) 0 u →
      wkpBaseCoordinateCLM (S F) = baseCoordCLM u)
    (K : ℝ) (hK : 0 < K)
    (D : WaveProblemData n (m + 1) Ω a b) (hD : D.HasCompatibleBoundaryTraces L)
    (du : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (dv : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (dw : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
    (dU : SobolevTimeJet n (m + 1) Ω a b)
    (hdweak : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
      (dirichletLoadTimeLp hopen D.forcing.timeDerivative.head) du dv dw
      (WaveProblemData.initialPosition hD.2)
      (wkpBaseCoordinateCLM (D.forcingTraces.head - L m D.displacement)))
    (hdU : ∀ᵐ t ∂volume.restrict (Ioc a b),
      lowerOrderCLM (by omega : 1 ≤ m + 1) (dU.head t) = h10SubtypeL (du t))
    (hdv : baseCoordinateTimeLp dU.timeDerivative.head = dv)
    (hdTop : dU.IsEssentiallyBounded)
    (hdBound : ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum dU t ≤
      K * evansHigherRegularityDataBudget
        (D.timeDerivative (D.forcingTraces.head - L m D.displacement))) :
    ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
      (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
      (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
      (U : SobolevTimeJet n (m + 2) Ω a b),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
          (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
        (dirichletLoadTimeLp hopen D.forcing.head) u v w
        (WaveProblemData.initialPosition hD) (wkpBaseCoordinateCLM D.velocity) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (by omega : 1 ≤ m + 2) (U.head t) = h10SubtypeL (u t)) ∧
      baseCoordinateTimeLp U.timeDerivative.head = v ∧
      U.RepresentsAcceleration hopen w ∧
      U.IsEssentiallyBounded ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum U t ≤
        waveSuccessorConstant a b mu ‖L m‖ ‖S‖ K * evansHigherRegularityDataBudget D := by
  let T := h10L2GelfandTriple hopen
  let F := fullDivergenceForm (multiplicationCoefficientOperator A)
    (fun i ↦ mulLpLeft (B i)) (mulLpLeft C)
  let R := ((b - a)⁻¹ + 1) * max 1 (b - a)
  let E := 1 + R + ‖L m‖
  let P := K * E
  have hab := D.time_lt
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hP : 0 < P := mul_pos hK hE
  obtain ⟨u, hweak, hprimitive⟩ := D.exists_integrated_compatible_wave hopen F L hL hD hdweak
  let Z := P * evansHigherRegularityDataBudget D
  have hZ : 0 ≤ Z := mul_nonneg hP.le (evansHigherRegularityDataBudget_nonneg D)
  have hdBound' : ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum dU t ≤ Z := by
    have hstep := mul_le_mul_of_nonneg_left (D.differentiated_budget_le (L m)) hK.le
    filter_upwards [hdBound] with t ht
    exact ht.trans (by simpa only [Z, P, E, R, mul_assoc] using hstep)
  obtain ⟨U, hU, htail, hvU, hTop, hBound⟩ :=
    exists_jet_of_integrated_full_wave D hopen A B C mu S hS
      (WaveProblemData.initialPosition hD) rfl hweak hprimitive dU hdU hdv hdTop hZ hdBound'
  refine ⟨u, T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) du,
    T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) dv, U, hweak, hU, hvU, ?_, hTop, ?_⟩
  · change dirichletLoadTimeLp hopen U.timeDerivative.timeDerivative.head = _
    rw [htail]
    simp only [dirichletLoadTimeLp, liftPivotToDualTimeLp, hdv]
    rfl
  · have hbudget := evansHigherRegularityDataBudget_nonneg D
    have hf : forcingSobolevLpNormSum D.forcing ≤ evansHigherRegularityDataBudget D := by
      unfold evansHigherRegularityDataBudget
      linarith only [norm_nonneg D.displacement, norm_nonneg D.velocity]
    have hg : ‖D.displacement‖ ≤ evansHigherRegularityDataBudget D := by
      unfold evansHigherRegularityDataBudget
      linarith only [forcingSobolevLpNormSum_nonneg D.forcing, norm_nonneg D.velocity]
    have hforce := mul_le_mul_of_nonneg_left hf hR
    have hshift := mul_le_mul_of_nonneg_left (add_le_add hg (le_refl ((b - a) * Z))) (abs_nonneg mu)
    have hspatial := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hforce (le_refl Z)) hshift) (norm_nonneg S)
    filter_upwards [hBound] with t ht
    change solutionSobolevNormSum U t ≤ Z + ‖S‖ * (R * forcingSobolevLpNormSum D.forcing + Z +
        |mu| * (‖D.displacement‖ + (b - a) * Z)) at ht
    apply ht.trans
    calc
      _ ≤ Z + ‖S‖ * (R * evansHigherRegularityDataBudget D + Z +
          |mu| * (evansHigherRegularityDataBudget D + (b - a) * Z)) := add_le_add le_rfl hspatial
      _ ≤ waveSuccessorConstant a b mu ‖L m‖ ‖S‖ K * evansHigherRegularityDataBudget D := by
        change _ ≤ (1 + P + ‖S‖ * (R + P + |mu| * (1 + (b - a) * P))) * _
        dsimp only [Z]
        nlinarith only [hbudget]

end Hyperbolic.HigherRegularity
