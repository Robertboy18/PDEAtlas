/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.Uniqueness
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Factorial convergence of semilinear Picard iteration

For a globally Lipschitz nonlinearity, the Duhamel Picard map has a contracting
iterate on every finite time interval. Successive integrations give the factor
`(M * L * t)^n / n!`, where `M` bounds the semigroup and `L` is the Lipschitz
constant. This constructs a unique mild solution without a small-time condition,
and every continuous starting curve converges uniformly to that solution.

Only strong continuity of the semigroup is required.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Repeated Duhamel integration gives a factorial estimate at each time. -/
theorem dist_iterate_picardMap_apply_le (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} (hF : LipschitzWith L F)
    (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M) (x₀ : E)
    (u v : C(Icc (0 : ℝ) (τ : ℝ), E)) (n : ℕ)
    (t : Icc (0 : ℝ) (τ : ℝ)) :
    dist (((T.picardMap F x₀ τ)^[n]) u t) (((T.picardMap F x₀ τ)^[n]) v t) ≤
      ((M * L * (t : ℝ)) ^ n / n.factorial) * dist u v := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := u) (g := v) t
  | succ n hn =>
      let P := T.picardMap F x₀ τ
      let D : ℝ → ℝ := fun s ↦
        (L : ℝ) * (((M * L * s) ^ n / n.factorial) * dist u v)
      have hD : Continuous D := by fun_prop
      have hfg : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
          ‖F (IccExtend τ.property ((P^[n]) u) s) -
            F (IccExtend τ.property ((P^[n]) v) s)‖ ≤ D s := by
        intro s hs
        have hsτ : s ∈ Icc (0 : ℝ) (τ : ℝ) := ⟨hs.1, hs.2.trans t.property.2⟩
        have hdist := (hF.dist_le_mul (((P^[n]) u) ⟨s, hsτ⟩)
          (((P^[n]) v) ⟨s, hsτ⟩)).trans
            (mul_le_mul_of_nonneg_left (hn ⟨s, hsτ⟩) L.property)
        have hu : IccExtend τ.property ((P^[n]) u) s = ((P^[n]) u) ⟨s, hsτ⟩ :=
          IccExtend_of_mem τ.property ((P^[n]) u) hsτ
        have hv : IccExtend τ.property ((P^[n]) v) s = ((P^[n]) v) ⟨s, hsτ⟩ :=
          IccExtend_of_mem τ.property ((P^[n]) v) hsτ
        simpa only [hu, hv, D, dist_eq_norm] using hdist
      have hnorm := T.norm_duhamel_sub_le_integral
        (F.continuous.comp ((P^[n]) u).continuous.Icc_extend')
        (F.continuous.comp ((P^[n]) v).continuous.Icc_extend')
        hbound t.property hD hfg
      rw [iterate_succ_apply', iterate_succ_apply']
      change dist
        (T (t : ℝ).toNNReal x₀ +
          T.duhamel (fun s ↦ F (IccExtend τ.property ((P^[n]) u) s)) t)
        (T (t : ℝ).toNNReal x₀ +
          T.duhamel (fun s ↦ F (IccExtend τ.property ((P^[n]) v) s)) t) ≤ _
      rw [dist_add_left, dist_eq_norm]
      refine hnorm.trans_eq ?_
      dsimp only [D]
      simp_rw [mul_pow]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
        integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, div_eq_mul_inv, mul_inv_rev]
      ring

/-- The factorial estimate also holds in the uniform metric on continuous curves. -/
theorem dist_iterate_picardMap_le (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} (hF : LipschitzWith L F)
    (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M) (x₀ : E)
    (u v : C(Icc (0 : ℝ) (τ : ℝ), E)) (n : ℕ) :
    dist (((T.picardMap F x₀ τ)^[n]) u) (((T.picardMap F x₀ τ)^[n]) v) ≤
      (((M : ℝ) * L * τ) ^ n / n.factorial) * dist u v := by
  apply (ContinuousMap.dist_le (by positivity)).2
  intro t
  apply (T.dist_iterate_picardMap_apply_le hF hbound x₀ u v n t).trans
  have ht : 0 ≤ (t : ℝ) := t.property.1
  gcongr
  exact t.property.2

/-- Some iterate of the Duhamel Picard map contracts on every finite interval. -/
theorem exists_contractingWith_iterate_picardMap (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L M τ : NNReal} (hF : LipschitzWith L F)
    (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M) (x₀ : E) :
    ∃ (n : ℕ) (q : NNReal), ContractingWith q ((T.picardMap F x₀ τ)^[n]) := by
  obtain ⟨n, hn⟩ :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop ((M : ℝ) * L * τ)).eventually
      (gt_mem_nhds zero_lt_one) |>.exists
  let q : NNReal := ⟨((M : ℝ) * L * τ) ^ n / n.factorial, by positivity⟩
  refine ⟨n, q, hn, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  exact T.dist_iterate_picardMap_le hF hbound x₀ u v n

/-- A globally Lipschitz nonlinearity has exactly one continuous mild solution on
any prescribed finite interval. Strong continuity supplies the semigroup bound. -/
theorem existsUnique_mildSolutionOn_of_lipschitzWith (T : StronglyContinuousSemigroup E)
    {F : C(E, E)} {L : NNReal} (hF : LipschitzWith L F) (x₀ : E) (τ : NNReal) :
    ∃! u : C(Icc (0 : ℝ) (τ : ℝ), E), T.IsMildSolutionOn F x₀ τ u := by
  obtain ⟨M, hM, hbound⟩ := T.exists_norm_le_on_Icc τ
  obtain ⟨n, q, hPn⟩ :=
    T.exists_contractingWith_iterate_picardMap hF (M := ⟨M, hM⟩) hbound x₀
  let u := hPn.fixedPoint ((T.picardMap F x₀ τ)^[n])
  have hu : IsFixedPt (T.picardMap F x₀ τ) u := hPn.isFixedPt_fixedPoint_iterate
  refine ⟨u, ?_, ?_⟩
  · intro t
    exact (congrArg (fun w : C(Icc (0 : ℝ) (τ : ℝ), E) ↦ w t) hu).symm
  · intro v hv
    have hvfix : IsFixedPt (T.picardMap F x₀ τ) v :=
      ContinuousMap.ext fun t ↦ (hv t).symm
    exact hPn.fixedPoint_unique (hvfix.iterate n)

/-- The distance from a Picard iterate to the mild solution decays factorially.
The starting curve need not satisfy the initial condition. -/
theorem IsMildSolutionOn.dist_picard_iterate_le {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {L M τ : NNReal} {x₀ : E}
    {w : C(Icc (0 : ℝ) (τ : ℝ), E)} (hw : T.IsMildSolutionOn F x₀ τ w)
    (hF : LipschitzWith L F) (hbound : ∀ r ∈ Icc (0 : NNReal) τ, ‖T r‖ ≤ M)
    (u : C(Icc (0 : ℝ) (τ : ℝ), E)) (n : ℕ) :
    dist (((T.picardMap F x₀ τ)^[n]) u) w ≤
      (((M : ℝ) * L * τ) ^ n / n.factorial) * dist u w := by
  have hwfix : IsFixedPt (T.picardMap F x₀ τ) w :=
    ContinuousMap.ext fun t ↦ (hw t).symm
  simpa only [(hwfix.iterate n).eq] using T.dist_iterate_picardMap_le hF hbound x₀ u w n

/-- Every continuous starting curve converges uniformly under Picard iteration
to the mild solution, without requiring a one-step contraction. -/
theorem IsMildSolutionOn.tendsto_picard_iterates {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {L τ : NNReal} {x₀ : E}
    {w : C(Icc (0 : ℝ) (τ : ℝ), E)} (hw : T.IsMildSolutionOn F x₀ τ w)
    (hF : LipschitzWith L F) (u : C(Icc (0 : ℝ) (τ : ℝ), E)) :
    Tendsto (fun n ↦ ((T.picardMap F x₀ τ)^[n]) u) atTop (𝓝 w) := by
  obtain ⟨M, hM, hbound⟩ := T.exists_norm_le_on_Icc τ
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg)
    (hw.dist_picard_iterate_le hF (M := ⟨M, hM⟩) hbound u)
  change Tendsto (fun n : ℕ ↦ (M * (L : ℝ) * τ) ^ n / n.factorial * dist u w)
    atTop (𝓝 (0 : ℝ))
  simpa only [zero_mul] using
    (FloorSemiring.tendsto_pow_div_factorial_atTop (M * L * τ)).mul_const (dist u w)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
