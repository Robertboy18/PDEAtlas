/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Construction.Successor

/-!
# Constructing all orders of wave regularity

The induction starts with a single energy solution of the highest
differentiated problem. Each descent integrates one weak wave with the
computed compatible initial data and recovers the higher spatial head.
The constants are chosen before any data. Forcing traces are controlled by
adjacent data norms, and the shifted elliptic term is controlled by a time
primitive of the already constructed derivative.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Compatibility through order `m` depends only on spatial loads of orders less than `m`.
In particular, extending a finite load family to unused orders does not change the data. -/
theorem WaveProblemData.hasCompatibleBoundaryTraces_congr
    {L L' : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω)}
    {m : ℕ} (hL : ∀ r, r < m → L r = L' r) (D : WaveProblemData n m Ω a b) :
    D.HasCompatibleBoundaryTraces L ↔ D.HasCompatibleBoundaryTraces L' := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [WaveProblemData.HasCompatibleBoundaryTraces]
      rw [hL m (Nat.lt_succ_self m)]
      exact and_congr_right fun _ ↦ ih (fun r hr ↦ hL r (Nat.lt_succ_of_lt hr)) _

/-- Energy existence and the shifted spatial inverses through order `m - 1`
construct the entire order-`m + 1` regularity jet with a data-only estimate. -/
theorem exists_allOrder_wave_of_energy_and_shifted_inverses (hopen : IsOpen Ω) (hab : a < b)
    (A : Fin n → Fin n → DerivLp n ∞ Ω) (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (mu : ℝ) (S : ∀ r, W^{r,2}(Ω) →L[ℝ] W^{(r + 2),2}(Ω)) (M : ℝ) (hM : 0 < M)
    (henergy : ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
      (q : H¹₀(Ω)) (p : DerivLp n 2 Ω),
      ∃ u v w, Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
          (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
        u v w q p ∧
      MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
      MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), ‖u t‖ + ‖v t‖ ≤ M * (‖f‖ + ‖q‖ + ‖p‖))
    (m : ℕ)
    (hL : ∀ (r : ℕ), r < m → ∀ (G : W^{(r + 2),2}(Ω)) (g : H¹₀(Ω)),
      wkpBaseCoordinateCLM G = baseCoordCLM g →
      fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C) g = loadFunctional (wkpBaseCoordinateCLM (L r G)))
    (hS : ∀ (r : ℕ), r < m → ∀ (F : W^{r,2}(Ω)) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution A B C mu (wkpBaseCoordinateCLM F) 0 u →
      wkpBaseCoordinateCLM (S r F) = baseCoordCLM u) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D : WaveProblemData n m Ω a b) (hD : D.HasCompatibleBoundaryTraces L),
      ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
        (U : SobolevTimeJet n (m + 1) Ω a b),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
          (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
        (dirichletLoadTimeLp hopen D.forcing.head) u v w
        (WaveProblemData.initialPosition hD) (wkpBaseCoordinateCLM D.velocity) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (by omega : 1 ≤ m + 1) (U.head t) = h10SubtypeL (u t)) ∧
      baseCoordinateTimeLp U.timeDerivative.head = v ∧
      U.RepresentsAcceleration hopen w ∧
      U.IsEssentiallyBounded ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b),
        solutionSobolevNormSum U t ≤ K * evansHigherRegularityDataBudget D := by
  induction m with
  | zero =>
      let N := 1 + ‖orderZeroSobolevCLM (n := n) (p := 2) (Omega := Ω)‖
      have hN : 0 < N := by dsimp [N]; positivity
      refine ⟨N * M, mul_pos hN hM, fun D hD ↦ ?_⟩
      obtain ⟨u, v, w, hweak, hu, hv, hbound⟩ :=
        henergy (baseCoordinateTimeLp D.forcing.head) (WaveProblemData.initialPosition hD)
          (wkpBaseCoordinateCLM D.velocity)
      have hbudget : ‖baseCoordinateTimeLp D.forcing.head‖ +
          ‖WaveProblemData.initialPosition hD‖ + ‖wkpBaseCoordinateCLM D.velocity‖ ≤
          evansHigherRegularityDataBudget D :=
        add_le_add (add_le_add ((norm_baseCoordinateTimeLp_le D.forcing.head).trans
          (norm_forcing_head_le D.forcing)) (WaveProblemData.norm_initialPosition_le hD))
          (wkpBaseCoordinateCLM_norm_le D.velocity)
      obtain ⟨U, hU, hdU, htop, hsum⟩ := exists_orderOneSobolevTimeJet_norm_le hopen _
        (dirichletLoadTimeLp hopen D.forcing.head) u v w (WaveProblemData.initialPosition hD)
        (wkpBaseCoordinateCLM D.velocity) hweak hu hv
        (hbound.mono fun _ ht ↦ ht.trans (mul_le_mul_of_nonneg_left hbudget hM.le))
      refine ⟨u, v, w, U, hweak, ?_, hdU, trivial, htop, ?_⟩
      · simpa only [lowerOrderCLM_refl_apply] using hU
      · simpa only [N, mul_assoc] using hsum
  | succ m ih =>
      obtain ⟨K, hK, hInd⟩ := ih (fun r hr ↦ hL r (Nat.lt_succ_of_lt hr))
        (fun r hr ↦ hS r (Nat.lt_succ_of_lt hr))
      refine ⟨waveSuccessorConstant a b mu ‖L m‖ ‖S m‖ K,
        waveSuccessorConstant_pos hab mu (norm_nonneg (L m)) (norm_nonneg (S m)) hK, fun D hD ↦ ?_⟩
      obtain ⟨du, dv, dw, dU, hdweak, hdU, hdv, _, hdTop, hdBound⟩ :=
        hInd (D.timeDerivative (D.forcingTraces.head - L m D.displacement)) hD.2
      exact exists_regular_wave_successor hopen A B C L (hL m (Nat.lt_succ_self m)) mu (S m)
        (hS m (Nat.lt_succ_self m)) K hK D hD du dv dw dU hdweak hdU hdv hdTop hdBound

end Hyperbolic.HigherRegularity
