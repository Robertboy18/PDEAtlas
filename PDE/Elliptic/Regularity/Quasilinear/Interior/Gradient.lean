/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.LocalizedEnergy
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized.InteriorCutoffs
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalConverse
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Interior weak derivatives of a monotone equation's gradient

Nested cutoffs supply admissible tests uniformly in the step. The
localized coercive estimate and the difference-quotient converse
construct first-order Sobolev representatives of every gradient
coordinate on any compactly contained open subset. The estimate constant
is chosen before the flux, solution and source.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.DifferenceQuotient SobolevSpace.Extension.Lp
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- Interior first weak derivatives of each original gradient
coordinate, with one constant fixed before all equation data.
No boundary condition on `u` is assumed. -/
theorem exists_interior_gradient_of_monotone_weakEquation
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {m C : ℝ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℝ^n → ℝ^n),
      (∀ z w, m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫) →
      (∀ z w, ‖A z - A w‖ ≤ C * ‖z - w‖) →
      ∀ (u : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
      (∀ᵐ x ∂domainMeasure n Ω,
        A (Lp.euclideanTuple (fun i ↦ u.val (singleDerivIndex n i)) x) =
          Lp.euclideanTuple q x) →
      (∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
      ∃ W : Fin n → H¹(V),
        (∀ i, (W i).val (baseIndex n 1) =
          restrictDerivLp (subset_closure.trans hVΩ) (u.val (singleDerivIndex n i))) ∧
        ∀ i, ‖∇ (W i)‖ ≤ K * (‖f‖ + ‖∇ u‖) := by
  rcases lt_or_ge C 0 with hC | hC
  · refine ⟨1, one_pos, fun A _ hLip u q f _ _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
    · have h := (norm_nonneg _).trans (hLip (EuclideanSpace.single ⟨0, hn⟩ 1) 0)
      simp only [sub_zero, PiLp.norm_single, norm_one, mul_one] at h
      linarith
  obtain ⟨η, hηΩ, hone, _, _⟩ := TestFunction.exists_eq_one_on_compact hΩ hVc hVΩ
  obtain ⟨χ, S, ρ, hS, hSΩ, hχ, hχone, hηS, hρ, hρΩ, hsteps⟩ :=
    exists_interior_cutoff_collar hΩ η hηΩ
  let B := interiorQuotientEstimateConstant m C η
  have hB : 0 < B := interiorQuotientEstimateConstant_pos hm hC η
  refine ⟨1 + n * B, by positivity, ?_⟩
  intro A hmono hLip u q f hrep hweak
  have honeV (x : ℝ^n) (hx : x ∈ V) : η.toFun x = 1 := hone x (subset_closure hx)
  have hVη : V ⊆ tsupport η.toFun := by
    intro x hx
    apply subset_tsupport η.toFun
    simpa only [Function.mem_support, honeV x hx] using (one_ne_zero : (1 : ℝ) ≠ 0)
  let T := ‖f‖ + ‖∇ u‖
  have hT : 0 ≤ T := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbounds (i k : Fin n) (h : ℝ) (hh : h ≠ 0) (hhρ : |h| < ρ) :
      ‖restrictDerivLp (subset_univ V) (differenceQuotientLp 2 k h
        (zeroExtendLp hΩ.measurableSet (u.val (singleDerivIndex n i))))‖ ≤ B * T := by
    let P (j : Fin n) := differenceQuotientLp 2 k h
      (zeroExtendLp hΩ.measurableSet (u.val (singleDerivIndex n j)))
    have hcoord : ‖testFunctionLpTop (Ω := univ) η • P i‖ ≤
        ‖testFunctionLpTop (Ω := univ) η • Lp.euclideanTuple P‖ := by
      simpa only [Lp.euclideanTuple_lpSMul] using
        Lp.norm_coordinate_le_norm_euclideanTuple
          (fun j ↦ testFunctionLpTop (Ω := univ) η • P j) i
    exact (norm_restrict_le_testFunction_smul hV.measurableSet η honeV (P i)).trans
      (hcoord.trans (norm_weighted_interior_gradient_le hΩ hS hSΩ A hm hC hmono hLip
        χ hχ hχone η hηS hρ hρΩ k hh hhρ (hsteps k h hhρ).1 u q f hrep hweak))
  have hfields (i : Fin n) : ∃ W : H¹(V),
      W.val (baseIndex n 1) =
        restrictDerivLp (subset_closure.trans hVΩ) (u.val (singleDerivIndex n i)) ∧
      ‖∇ W‖ ≤ n * (B * T) := by
    apply exists_sobolev_of_restricted_differenceQuotient_bounds
      (by norm_num : 1 < (2 : ℝ≥0∞)) (by norm_num) hΩ.measurableSet hV
      (subset_closure.trans hVΩ) hρ (mul_nonneg hB.le hT)
      (fun k h hh x hx ↦ hSΩ ((hsteps k h hh).1 (hVη hx)))
      (u.val (singleDerivIndex n i))
    exact hbounds i
  choose W hbase hnorm using hfields
  refine ⟨W, hbase, fun i ↦ (hnorm i).trans ?_⟩
  change n * (B * T) ≤ (1 + n * B) * T
  nlinarith

end PDE.Elliptic.Regularity.Quasilinear
