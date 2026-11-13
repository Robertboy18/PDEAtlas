/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Compatibility.Conditions
public import PDE.Hyperbolic.HigherRegularity.Data.TraceEstimate
public import PDE.Hyperbolic.HigherRegularity.Estimate.Symmetric

/-!
# Compatible initial jets and their data bounds

The equation determines each new initial velocity as `f_j(a) - L q_j`.
The forcing trace is constructed from the time derivative; the bounded
spatial operator supplies its Sobolev regularity. Only the initial positions
of the differentiated waves require zero boundary trace.

The estimates here are uniform in the original data. In particular, passing
to a differentiated problem costs a constant depending on the interval and
the spatial operator, not an additional trace norm on the right-hand side.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Splitting the forcing norm sum separates the undifferentiated forcing
from the complete differentiated budget. -/
theorem forcingSobolevLpNormSum_succ (F : SobolevTimeJet n (m + 1) Ω a b) :
    forcingSobolevLpNormSum F = forcingSobolevLpNormSum F.timeDerivative + ‖F.head‖ := by
  unfold forcingSobolevLpNormSum
  rw [Fin.sum_univ_castSucc]
  simp only [SobolevTimeJet.iteratedTimeDerivative_castSucc,
    SobolevTimeJet.iteratedTimeDerivative_last]

/-- Each forcing derivative's Bochner norm is part of the original sum. -/
theorem norm_forcing_head_le (F : SobolevTimeJet n m Ω a b) :
    ‖F.head‖ ≤ forcingSobolevLpNormSum F := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun r : Fin (m + 1) ↦ ‖(F.iteratedTimeDerivative r).head‖)
    (fun r _ ↦ norm_nonneg (F.iteratedTimeDerivative r).head) (Finset.mem_univ (Fin.last m))
  simpa only [SobolevTimeJet.iteratedTimeDerivative_last, forcingSobolevLpNormSum] using h

/-- The two norms needed for the forcing trace already occur in the data budget. -/
theorem forcing_head_pair_le (F : SobolevTimeJet n (m + 1) Ω a b) :
    ‖F.head‖ + ‖F.timeDerivative.head‖ ≤ forcingSobolevLpNormSum F := by
  rw [forcingSobolevLpNormSum_succ]
  linarith only [norm_forcing_head_le F.timeDerivative]

/-- Quantitative construction of the next initial velocity. This vector has
the required Sobolev order, with no boundary condition imposed on it. -/
theorem WaveProblemData.norm_initialAcceleration_le (D : WaveProblemData n (m + 1) Ω a b)
    (L : W^{(m + 2),2}(Ω) →L[ℝ] W^{m,2}(Ω)) :
    ‖D.forcingTraces.head - L D.displacement‖ ≤ (((b - a)⁻¹ + 1) * max 1 (b - a)) *
      forcingSobolevLpNormSum D.forcing + ‖L‖ * ‖D.displacement‖ := by
  have hK : 0 ≤ ((b - a)⁻¹ + 1) * max 1 (b - a) := by
    have hab := D.time_lt
    positivity
  exact (norm_sub_le _ _).trans (add_le_add ((D.forcingTraces.norm_head_le D.time_lt).trans
      (mul_le_mul_of_nonneg_left (forcing_head_pair_le D.forcing) hK)) (L.le_opNorm D.displacement))

/-- Differentiating a compatible problem preserves a data-only budget. The
constant is explicit and depends on no initial or forcing value. -/
theorem WaveProblemData.differentiated_budget_le (D : WaveProblemData n (m + 1) Ω a b)
    (L : W^{(m + 2),2}(Ω) →L[ℝ] W^{m,2}(Ω)) :
    evansHigherRegularityDataBudget (D.timeDerivative (D.forcingTraces.head - L D.displacement)) ≤
      (1 + (((b - a)⁻¹ + 1) * max 1 (b - a)) + ‖L‖) * evansHigherRegularityDataBudget D := by
  let K := ((b - a)⁻¹ + 1) * max 1 (b - a)
  have hK : 0 ≤ K := by
    have hab := D.time_lt
    dsimp [K]
    positivity
  have hforce : forcingSobolevLpNormSum D.forcing.timeDerivative ≤
      forcingSobolevLpNormSum D.forcing := by
    rw [forcingSobolevLpNormSum_succ]
    exact le_add_of_nonneg_right (norm_nonneg D.forcing.head)
  have hF : forcingSobolevLpNormSum D.forcing ≤ evansHigherRegularityDataBudget D := by
    unfold evansHigherRegularityDataBudget
    linarith only [norm_nonneg D.displacement, norm_nonneg D.velocity]
  have hg : ‖D.displacement‖ ≤ evansHigherRegularityDataBudget D := by
    unfold evansHigherRegularityDataBudget
    linarith only [forcingSobolevLpNormSum_nonneg D.forcing, norm_nonneg D.velocity]
  have hrest : forcingSobolevLpNormSum D.forcing.timeDerivative + ‖D.velocity‖ ≤
      evansHigherRegularityDataBudget D := by
    unfold evansHigherRegularityDataBudget
    linarith only [hforce, norm_nonneg D.displacement]
  have hacc := D.norm_initialAcceleration_le L
  have hKF := mul_le_mul_of_nonneg_left hF hK
  have hLg := mul_le_mul_of_nonneg_left hg (norm_nonneg L)
  change forcingSobolevLpNormSum D.forcing.timeDerivative + ‖D.velocity‖ +
    ‖D.forcingTraces.head - L D.displacement‖ ≤ _
  dsimp only [K] at hKF
  nlinarith only [hrest, hacc, hKF, hLg]

namespace WaveProblemData

/-- All differentiated initial problems, computed from the equation and
canonical forcing traces. The last velocity uses `f_{m-1}(a)`, never `f_m(a)`. -/
def compatibilityData
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)) :
    {m : ℕ} → WaveProblemData n m Ω a b →
      (r : Fin (m + 1)) → WaveProblemData n r.1 Ω a b
  | 0, D, r => Fin.lastCases D (fun s ↦ Fin.elim0 s) r
  | m + 1, D, r => Fin.lastCases D
      (fun s ↦ compatibilityData L
        (D.timeDerivative (D.forcingTraces.head - L m D.displacement)) s) r

/-- Reverse index `Fin.last` is the original problem. -/
@[simp]
theorem compatibilityData_last (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (D : WaveProblemData n m Ω a b) :
    compatibilityData L D (Fin.last m) = D := by
  cases m <;> exact Fin.lastCases_last

/-- Dropping the original equation computes the next acceleration from its trace. -/
@[simp]
theorem compatibilityData_castSucc (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (D : WaveProblemData n (m + 1) Ω a b) (r : Fin (m + 1)) :
    compatibilityData L D r.castSucc =
      compatibilityData L (D.timeDerivative (D.forcingTraces.head - L m D.displacement)) r := by
  simp only [compatibilityData, Fin.lastCases_castSucc]

/-- Compatibility supplies boundary traces for every computed position.
The terminal velocity remains an unrestricted `L²` value. -/
theorem IsCompatible.compatibilityData {D : WaveProblemData n m Ω a b}
    {A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω))} {L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    (hD : D.IsCompatible A L) (r : Fin (m + 1)) :
    (compatibilityData L D r).IsCompatible A L := by
  induction m with
  | zero =>
      refine Fin.lastCases ?_ (fun s ↦ Fin.elim0 s) r
      simpa only [compatibilityData_last] using hD
  | succ m ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simpa only [compatibilityData_last] using hD
      · rw [compatibilityData_castSucc]
        exact ih (hD.timeDerivative _ rfl) s

/-- A single structural constant controls every computed initial problem. -/
theorem exists_compatibilityData_budget_bound (hab : a < b)
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D : WaveProblemData n m Ω a b) (r : Fin (m + 1)),
      evansHigherRegularityDataBudget (compatibilityData L D r) ≤
        K * evansHigherRegularityDataBudget D := by
  induction m with
  | zero =>
      refine ⟨1, zero_lt_one, fun D r ↦ ?_⟩
      refine Fin.lastCases ?_ (fun s ↦ Fin.elim0 s) r
      simp only [compatibilityData_last, one_mul, le_refl]
  | succ m ih =>
      obtain ⟨K, hK, hbound⟩ := ih
      let E := 1 + (((b - a)⁻¹ + 1) * max 1 (b - a)) + ‖L m‖
      have hE : 0 < E := by dsimp [E]; positivity
      refine ⟨1 + K * E, by positivity, fun D r ↦ ?_⟩
      have hD := evansHigherRegularityDataBudget_nonneg D
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · rw [compatibilityData_last]
        nlinarith [mul_nonneg hK.le hE.le]
      · rw [compatibilityData_castSucc]
        apply (hbound _ s).trans
        have hstep := mul_le_mul_of_nonneg_left (D.differentiated_budget_le (L m)) hK.le
        change _ ≤ K * (E * evansHigherRegularityDataBudget D) at hstep
        nlinarith only [hstep, hD]

end WaveProblemData

end Hyperbolic.HigherRegularity
