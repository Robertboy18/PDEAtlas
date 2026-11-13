/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Construction.AllOrder
public import PDE.Hyperbolic.HigherRegularity.AllOrder.FiniteCoefficients

/-!
# All-order regularity of the original classical-coefficient wave

At every finite order, compatible initial data and a forcing time jet give
spatial Sobolev regularity of the wave and its time derivatives, following
the proof of Theorem 6 in Evans, §7.2.3.
The principal coefficient matrix is symmetric and uniformly
elliptic; drift and potential have arbitrary sign. Finite regularity of the
boundary and coefficients supplies exactly the elliptic lifts used by the
construction. Smooth data specialize this result at every order.

The result concerns any solution in the original energy weak class. Uniqueness
identifies its displacement, velocity and acceleration with the constructed
wave. All members of the resulting Sobolev time jet are weak derivatives,
and their norm sum satisfies the unshifted estimate on the closed interval.
The constant is fixed before the initial data, forcing and solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6 and estimate (64).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity
open PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Finite classical regularity gives the full Sobolev time jet of any original
weak wave. The principal and drift coefficients need only `C^{max 1 m}` regularity,
the potential `C^m`, and the graph boundary `C^{m+1}`. Only elliptic lifts of
orders `r < m` enter the construction, including the empty family when `m = 0`.

Reverse index `r` denotes derivative order `m + 1 - r`, in spatial `H^r`.
Compatibility computes its forcing traces and imposes zero boundary trace only
through `q_m`. The estimate bounds the essential supremum of
`∑_{k=0}^{m+1} ‖∂ₜ^k u‖_{H^{m+1-k}}`, with the constant fixed before the data
and the solution. -/
theorem exists_allOrderSobolevTimeJet_of_finite_classical_wave
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (m : ℕ) (hgraph : Boundary.HasContDiffGraphBoundary (m + 1) Ω) (hab : a < b)
    {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
    (hA : ∀ i j, ContDiffUpToBoundary (max 1 m) (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary (max 1 m) (B i) Ω) (hC : ContDiffUpToBoundary m C Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (A x) alpha) :
    let L := classicalWaveLoadUpTo hopen hbounded (fun i j ↦ (hA i j).of_le (le_max_right 1 m))
      (fun i ↦ (hB i).of_le (le_max_right 1 m)) hC
    let F := classicalAutonomousWaveForm hopen hbounded (fun i j ↦ (hA i j).of_le (le_max_left 1 m))
      (fun i ↦ (hB i).of_le (le_max_left 1 m)) (hC.of_le (Nat.zero_le m))
    ∃ K : ℝ, 0 < K ∧ ∀ (D : WaveProblemData n m Ω a b) (hD : D.HasCompatibleBoundaryTraces L)
      (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
      (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
      (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ F) (dirichletLoadTimeLp hopen D.forcing.head) u v w
        (WaveProblemData.initialPosition hD) (wkpBaseCoordinateCLM D.velocity) →
      ∃ U : SobolevTimeJet n (m + 1) Ω a b,
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          lowerOrderCLM (by omega : 1 ≤ m + 1) (U.head t) = h10SubtypeL (u t)) ∧
        baseCoordinateTimeLp U.timeDerivative.head = v ∧
        U.RepresentsAcceleration hopen w ∧
        U.IsEssentiallyBounded ∧
        (∀ r : Fin (m + 2),
          MemLp (fun t ↦ (U.iteratedTimeDerivative r).head t) ∞
            (volume.restrict (Icc a b))) ∧
        (∀ r : Fin (m + 1), HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ lowerOrderCLM (Nat.le_succ r.1)
            ((U.iteratedTimeDerivative r.succ).head t))
          (U.iteratedTimeDerivative r.castSucc).head) ∧
        eLpNormEssSup (solutionSobolevNormSum U) (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (K * evansHigherRegularityDataBudget D) := by
  classical
  let : Fact (0 < n) := ⟨hn⟩
  let hA₁ := fun i j ↦ (hA i j).of_le (le_max_left 1 m)
  let hB₁ := fun i ↦ (hB i).of_le (le_max_left 1 m)
  let hC₀ := hC.of_le (Nat.zero_le m)
  let hAₘ := fun i j ↦ (hA i j).of_le (le_max_right 1 m)
  let hBₘ := fun i ↦ (hB i).of_le (le_max_right 1 m)
  let L := classicalWaveLoadUpTo hopen hbounded hAₘ hBₘ hC
  let F := classicalAutonomousWaveForm hopen hbounded hA₁ hB₁ hC₀
  let ALp := fun i j ↦ (hA₁ i j).toLp hopen hbounded ∞
  let BLp := fun i ↦ (hB₁ i).toLp hopen hbounded ∞
  let CLp := hC₀.toLp hopen hbounded ∞
  have he : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i := fun x hx ξ ↦ by
    simpa only [principalEnergy, dotProduct, mul_right_comm] using hell x hx ξ
  obtain ⟨M, hM, henergy⟩ := exists_uniform_energy_bound_of_classical_autonomous_coefficients
      hn hopen hbounded hab hA₁ hB₁ hC₀ hsymm halpha he
  obtain ⟨mu, Sfin, hSfin⟩ := exists_classical_full_higher_lifts_family
    (fun r : Fin m ↦ r.1) hopen hbounded
    (fun r ↦ hgraph.of_le (by exact_mod_cast (show r.1 + 2 ≤ m + 1 by omega))) A B C hA₁ hB₁ hC₀
    (fun r i j ↦ (hA i j).of_le (by omega))
    (fun r i ↦ (hB i).of_le (by omega)) (fun r ↦ hC.of_le (by omega)) halpha hell
  let S (r : ℕ) : W^{r,2}(Ω) →L[ℝ] W^{(r + 2),2}(Ω) := if hr : r < m then Sfin ⟨r, hr⟩ else 0
  have hS (r : ℕ) (hr : r < m) (G : W^{r,2}(Ω)) (g : H¹₀(Ω))
      (hg : IsWeakShiftedFullDivergenceSolution ALp BLp CLp mu (wkpBaseCoordinateCLM G) 0 g) :
      wkpBaseCoordinateCLM (S r G) = baseCoordCLM g := by
    simpa only [S, dite_eq_left hr] using hSfin ⟨r, hr⟩ G g hg
  obtain ⟨K, hK, hregular⟩ := exists_allOrder_wave_of_energy_and_shifted_inverses
    hopen hab ALp BLp CLp L mu S M hM (fun f q p ↦ by
      obtain ⟨⟨u, v, w, hweak⟩, hbound⟩ := henergy f q p
      exact ⟨u, v, w, hweak, hbound u v w hweak⟩) m
    (fun r hr ↦ classicalWaveForm_eq_loadUpTo hopen hbounded hAₘ hBₘ hC (by omega) r hr) hS
  refine ⟨K, hK, fun D hD u v w hweak ↦ ?_⟩
  obtain ⟨u₀, v₀, w₀, U, hweak₀, hU, hv, hw, htop, hbound⟩ := hregular D hD
  obtain ⟨rfl, rfl, rfl⟩ := weakWave_eq_of_classical_autonomous_coefficients hn hopen hbounded
    hA₁ hB₁ hC₀ hsymm halpha he hweak₀ hweak
  exact ⟨U, hU, hv, hw, htop, htop.memLp_iterated_Icc,
    U.hasWeakTimeDerivative_iterated, eLpNormEssSup_solutionSobolevNormSum_Icc_le U hbound⟩

/-- Smooth coefficients and boundary give every finite-order Sobolev time jet
of the original weak wave. This is the smooth specialization of the finite-order
theorem, with the same compatibility recurrence and unshifted norm-sum estimate. -/
theorem exists_allOrderSobolevTimeJet_of_classical_wave
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hab : a < b)
    {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
    (hA : ∀ k : ℕ, ∀ i j, ContDiffUpToBoundary k (fun x ↦ A x i j) Ω)
    (hB : ∀ k : ℕ, ∀ i, ContDiffUpToBoundary k (B i) Ω) (hC : ∀ k : ℕ, ContDiffUpToBoundary k C Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (A x) alpha) (m : ℕ) :
    let L := classicalWaveLoad hopen hbounded hA hB hC
    let F := classicalAutonomousWaveForm hopen hbounded (hA 1) (hB 1) (hC 0)
    ∃ K : ℝ, 0 < K ∧ ∀ (D : WaveProblemData n m Ω a b) (hD : D.HasCompatibleBoundaryTraces L)
      (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
      (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
      (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ F) (dirichletLoadTimeLp hopen D.forcing.head) u v w
        (WaveProblemData.initialPosition hD) (wkpBaseCoordinateCLM D.velocity) →
      ∃ U : SobolevTimeJet n (m + 1) Ω a b,
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          lowerOrderCLM (by omega : 1 ≤ m + 1) (U.head t) = h10SubtypeL (u t)) ∧
        baseCoordinateTimeLp U.timeDerivative.head = v ∧
        U.RepresentsAcceleration hopen w ∧
        U.IsEssentiallyBounded ∧
        (∀ r : Fin (m + 2),
          MemLp (fun t ↦ (U.iteratedTimeDerivative r).head t) ∞
            (volume.restrict (Icc a b))) ∧
        (∀ r : Fin (m + 1), HasWeakTimeDerivativeOn (Ioo a b)
          (fun t ↦ lowerOrderCLM (Nat.le_succ r.1)
            ((U.iteratedTimeDerivative r.succ).head t))
          (U.iteratedTimeDerivative r.castSucc).head) ∧
        eLpNormEssSup (solutionSobolevNormSum U) (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (K * evansHigherRegularityDataBudget D) := by
  obtain ⟨K, hK, hregular⟩ := exists_allOrderSobolevTimeJet_of_finite_classical_wave
    hn hopen hbounded m (hgraph (m + 1)) hab (hA (max 1 m)) (hB (max 1 m)) (hC m) hsymm halpha hell
  exact ⟨K, hK, fun D hD ↦ hregular D ((WaveProblemData.hasCompatibleBoundaryTraces_congr
    (L := classicalWaveLoadUpTo hopen hbounded (hA m) (hB m) (hC m))
    (L' := classicalWaveLoad hopen hbounded hA hB hC)
    (fun r hr ↦ classicalWaveLoadUpTo_eq_classicalWaveLoad hopen hbounded hA hB hC r hr) D).mpr hD)⟩

end Hyperbolic.HigherRegularity
