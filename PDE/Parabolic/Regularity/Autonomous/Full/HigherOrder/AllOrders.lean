/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Induction.Base
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Induction.Derivative
public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Induction.Assemble

/-!
# All-order parabolic regularity from compatible data

For each natural `m`, the data are `g ∈ H^{2m+1}` and the forcing
derivatives `fₖ ∈ L²(H^{2m-2k})`, for `0 ≤ k ≤ m`. The initial derivatives are
computed recursively from the forcing traces and the full autonomous spatial
operator. Compatibility requires only that these computed fields have zero
boundary trace through order `m`.

Every original weak solution then has all derivatives
`uₖ ∈ L²(H^{2m+2-2k})`, for `0 ≤ k ≤ m+1`, with their full sum bounded by the
data. The constant is fixed before the forcing, initial data, compatibility
proofs and weak solution. This is Evans's §7.1.3, Theorem 6 (Higher regularity), with the
estimate (55), for symmetric smooth principal coefficients and smooth drift and potential
on a domain with `C^r` graph boundary for every `r` (`exists_all_order_regularity`).

## How it works

We follow Evans's induction on `m`. The base case is Theorem 5(i) for the full operator
(`exists_improved_regularity_of_contDiffUpToBoundary`, used in `exists_base_solution_jet`).
In the induction step the time derivative of the solution is the weak solution with
forcing `fₜ` and initial value `g₁ = f(a) - Lg` (`exists_derivative_solution`), as in Evans's
(57), and these data satisfy the compatibility conditions of one order lower. The induction
hypothesis bounds its derivatives, and the higher elliptic estimate applied to
`Lu = f - uₜ` at almost every time gives the next spatial order of `u`
(`exists_assembled_solution_jet`), as in step 2 of Evans's proof, (60).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity), p. 340;
  §7.1.3, Theorem 5 (Improved regularity), p. 382, and Theorem 6 (Higher regularity), (55), and the
  remark after it, p. 386, and its proof, (56)-(60), pp. 387-388.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}

/-- All-order regularity for every original weak solution of the full
smooth autonomous parabolic problem. All solution derivatives and their
estimate are constructed from the compatible initial and forcing data. -/
theorem exists_all_order_regularity (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ r : ℕ, Boundary.HasContDiffGraphBoundary r Ω) (hab : a < b)
    (hsymm : ∀ x ∈ Ω, ∀ i j, P.principal x i j = P.principal x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : ForcingJet n Ω a b m) (hF : F.HasWeakDerivatives)
        (g : W^{(2 * m + 1),2}(Ω)),
      Compatible (P.load hopen hbounded) hopen hbounded (hgraph 2) hab F hF g →
      ∀ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ P.form hopen hbounded)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) F.headBase) u (wkpBaseCoordinateCLM g) →
      ∃ U : ForcingJet n Ω a b (m + 1), U.HasWeakDerivatives ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b),
          wkpBaseCoordinateCLM (U.head t) = baseCoordCLM (u t)) ∧
        U.normSum ≤ C * (‖g‖ + F.normSum) := by
  induction m with
  | zero =>
    obtain ⟨C, hC, hbase⟩ :=
      exists_base_solution_jet P hopen hbounded (hgraph 2) hab hsymm halpha hell
    refine ⟨C, hC, ?_⟩
    intro F hF g hcompat u hu
    obtain ⟨g₀, hg⟩ := hcompat.zeroBoundary
    exact hbase F g g₀ u hg hu
  | succ m ih =>
    obtain ⟨C, hC, hIH⟩ := ih
    obtain ⟨Q, hQ, hstate⟩ := exists_raw_initial_state_bound P hopen hbounded hab halpha hell
    obtain ⟨E, hE, hassemble⟩ := exists_assembled_solution_jet P m hopen hbounded
      (hgraph (2 * (m + 1) + 2)) halpha hell
    let D := ForcingJet.traceConstant m hopen hbounded (hgraph 2) hab +
      ‖P.load hopen hbounded (2 * m + 1)‖ + 1
    have hD : 0 < D := by
      have htrace := ForcingJet.traceConstant_nonneg m hopen hbounded (hgraph 2) hab
      have hload := (P.load hopen hbounded (2 * m + 1)).opNorm_nonneg
      dsimp only [D]
      linarith only [htrace, hload]
    have hCD : 0 < C * D := mul_pos hC hD
    refine ⟨E * (1 + C * D + Q) + C * D, by positivity, ?_⟩
    intro F hF g hcompat u hu
    let g₁ := initialDerivative (P.load hopen hbounded) hopen hbounded (hgraph 2) hab F hF g
    have hcompat₁ : Compatible (P.load hopen hbounded) hopen hbounded (hgraph 2) hab
        F.2 hF.2 g₁ := hcompat.2
    obtain ⟨g₀, hg⟩ := hcompat.1
    obtain ⟨g₁₀, hg₁⟩ := hcompat₁.zeroBoundary
    obtain ⟨v, huv, hveq⟩ := exists_derivative_solution P hopen hbounded (hgraph 2) hab
      halpha hell F hF g g₀ g₁₀ hg hg₁ u hu
    obtain ⟨V, hV, hVbase, hVnorm⟩ := hIH F.2 hF.2 g₁ hcompat₁ v hveq
    obtain ⟨W, hW, hWbase, hWnorm⟩ :=
      hassemble F V u v (wkpBaseCoordinateCLM g) hu huv hV hVbase
    refine ⟨W, hW, hWbase, ?_⟩
    let dataNorm := ‖g‖ + F.normSum
    have hdata : ‖g₁‖ + F.2.normSum ≤ D * dataNorm :=
      initialDerivative_norm_add_tail_le (P.load hopen hbounded)
        hopen hbounded (hgraph 2) hab F hF g
    have hVbound : V.normSum ≤ C * D * dataNorm := by
      exact hVnorm.trans ((mul_le_mul_of_nonneg_left hdata hC.le).trans_eq
        (mul_assoc C D dataNorm).symm)
    have hVhead : ‖V.head‖ ≤ C * D * dataNorm :=
      V.norm_head_le_normSum.trans hVbound
    have hFhead : ‖F.head‖ ≤ dataNorm :=
      F.norm_head_le_normSum.trans (le_add_of_nonneg_left (norm_nonneg g))
    have huBound : ‖u‖ ≤ Q * dataNorm := by
      have h := hstate (2 * (m + 1) + 1) (by omega) g g₀ F.headBase u hg hu
      exact h.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (F.norm_headBase_le.trans F.norm_head_le_normSum)) hQ.le)
    calc
      W.normSum ≤ E * (‖F.head‖ + ‖V.head‖ + ‖u‖) + V.normSum := hWnorm
      _ ≤ E * ((1 + C * D + Q) * dataNorm) + C * D * dataNorm :=
        add_le_add (mul_le_mul_of_nonneg_left
          (by nlinarith only [hFhead, hVhead, huBound]) hE.le) hVbound
      _ = (E * (1 + C * D + Q) + C * D) * (‖g‖ + F.normSum) := by
        dsimp only [dataNorm]
        ring

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder
