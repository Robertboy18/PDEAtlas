/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.Forcing
public import PDE.Hyperbolic.HigherRegularity.Data.WaveProblem
public import PDE.Analysis.Evolution.LionsMagenes.TimeSobolev

/-!
# Evans's higher wave regularity estimate from levelwise bounds

For the homogeneous Dirichlet problem

`u_tt + L u = f`,

Evans proves, under the regularity and order-`m` compatibility hypotheses
of Theorem 6 in §7.2.3,

`ess sup_(0 <= t <= T) sum_(k=0)^(m+1)
    ‖partial_t^k u(t)‖_(H^(m+1-k)(U))`

`  <= C * (sum_(k=0)^m
    ‖partial_t^k f‖_(L²(0,T;H^(m-k)(U)))
    + ‖g‖_(H^(m+1)(U)) + ‖h‖_(H^m(U)))`.

The constant depends on the domain, the operator coefficients, the
ellipticity constants, `m`, and `T`, but not on the Galerkin dimension.

## Main results

`SobolevTimeJet.iteratedTimeDerivative` stores the decreasing Sobolev
scales in this formula. We define the finite sum on the left and the data
budget on the right. The main theorem shows that levelwise estimates, each
with an explicit constant, combine into Evans's single estimate (64). The
uniform-level corollary is the form used by a finite differentiated Galerkin
argument.

The levelwise estimates are hypotheses. For the nonsymmetric operator,
`Estimate.Nonsymmetric` propagates constants through the two-step spatial
recurrence associated with Evans's estimate (59), starting from the two top
energy bounds, and
`eLpNormEssSup_solutionSobolevNormSum_le_of_nonsymmetricSpatialRecurrence`
proves the resulting essential-supremum estimate; there too the energy bounds
and recurrence are hypotheses on the jet.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, estimate (64), p. 412.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
The left-hand side of Evans (64) before taking the essential supremum.

The index runs in reverse:
`Fin.last (m + 1)` is `u`, and moving toward zero takes successive time
derivatives. Since the sum is finite, this is exactly

`sum_(k=0)^(m+1) ‖partial_t^k u(t)‖_(H^(m+1-k)(Omega))`.
-/
noncomputable def solutionSobolevNormSum
    (u : SobolevTimeJet n (m + 1) Omega t0 t1) (t : ℝ) : ℝ :=
  ∑ r : Fin (m + 2), ‖(u.iteratedTimeDerivative r).head t‖

/-- The pointwise Sobolev norm sum is nonnegative. -/
theorem solutionSobolevNormSum_nonneg (u : SobolevTimeJet n (m + 1) Omega t0 t1) (t : ℝ) :
    0 ≤ solutionSobolevNormSum u t := by
  unfold solutionSobolevNormSum
  positivity

/--
The forcing contribution on the right-hand side of Evans (64).

Each norm is the Bochner `L²` norm of the corresponding weak time
derivative in its exact spatial Sobolev space.
-/
noncomputable def forcingSobolevLpNormSum
    (f : SobolevTimeJet n m Omega t0 t1) : ℝ :=
  ∑ r : Fin (m + 1), ‖(f.iteratedTimeDerivative r).head‖

/--
The explicit common quadratic forcing budget used by the differentiated
wave-energy estimates.

At every reverse derivative index this stores one half of the full
`L²_t L²_x` norm squared of the base-coordinate forcing. Summing over the
finite chain gives a single constant that controls every time prefix and
every differentiated equation.
-/
noncomputable def forcingQuadraticBudget
    (f : SobolevTimeJet n m Omega t0 t1) : ℝ :=
  ∑ r : Fin (m + 1),
    (1 / 2 : ℝ) *
      ‖baseCoordinateTimeLp (f.iteratedTimeDerivative r).head‖ ^ 2

/--
The full data budget on the right-hand side of Evans (64).
-/
noncomputable def evansHigherRegularityDataBudget
    (D : WaveProblemData n m Omega t0 t1) : ℝ :=
  forcingSobolevLpNormSum D.forcing +
    ‖D.displacement‖ + ‖D.velocity‖

/-- The forcing part of the Evans data budget is nonnegative. -/
theorem forcingSobolevLpNormSum_nonneg (f : SobolevTimeJet n m Omega t0 t1) :
    0 ≤ forcingSobolevLpNormSum f := by
  unfold forcingSobolevLpNormSum
  positivity

/-- The common quadratic forcing budget is nonnegative. -/
theorem forcingQuadraticBudget_nonneg (f : SobolevTimeJet n m Omega t0 t1) :
    0 ≤ forcingQuadraticBudget f := by
  unfold forcingQuadraticBudget
  positivity

/--
Every quadratic forcing prefix is bounded by the explicit common budget.

The common budget is computed from the squared norms and time integrals
of the Sobolev forcing jet.
-/
theorem SobolevTimeJet.forcing_prefix_le_quadraticBudget (f : SobolevTimeJet n m Omega t0 t1)
    (ht : t0 < t1) (r : Fin (m + 1)) (t : ℝ) (htt : t ∈ Set.Icc t0 t1) :
    (∫ s in t0..t, (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (f.iteratedTimeDerivative r).head s‖ ^ 2) ≤
      forcingQuadraticBudget f := by
  let g := baseCoordinateTimeLp (f.iteratedTimeDerivative r).head
  have hgIntegrable : IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) * ‖g s‖ ^ 2) volume t0 t1 :=
    (f.intervalIntegrable_norm_sq_baseCoordinateTimeLp ht.le r)
  have hprefix : (∫ s in t0..t, (1 / 2 : ℝ) * ‖g s‖ ^ 2) ≤ ∫ s in t0..t1, (1 / 2 : ℝ) * ‖g s‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl htt.1 htt.2
      (Filter.Eventually.of_forall fun s ↦ by positivity) hgIntegrable
  have hfull : (∫ s in t0..t1, (1 / 2 : ℝ) * ‖g s‖ ^ 2) =
        (1 / 2 : ℝ) * ‖g‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le ht.le,
      ← MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  rw [hfull] at hprefix
  refine hprefix.trans ?_
  unfold forcingQuadraticBudget
  change (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (f.iteratedTimeDerivative r).head‖ ^ 2 ≤
      ∑ i : Fin (m + 1), (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (f.iteratedTimeDerivative i).head‖ ^ 2
  have hnonneg : ∀ i : Fin (m + 1), 0 ≤ (1 / 2 : ℝ) * ‖baseCoordinateTimeLp
          (f.iteratedTimeDerivative i).head‖ ^ 2 :=
    fun i ↦ mul_nonneg (by norm_num) (sq_nonneg _)
  exact Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin (m + 1) ↦ (1 / 2 : ℝ) *
        ‖baseCoordinateTimeLp (f.iteratedTimeDerivative i).head‖ ^ 2)
    (fun i _ ↦ hnonneg i) (Finset.mem_univ r)

/-- The full Evans data budget is nonnegative. -/
theorem evansHigherRegularityDataBudget_nonneg (D : WaveProblemData n m Omega t0 t1) :
    0 ≤ evansHigherRegularityDataBudget D :=
  add_nonneg (add_nonneg (forcingSobolevLpNormSum_nonneg D.forcing) (norm_nonneg D.displacement))
    (norm_nonneg D.velocity)

/--
Every adjacent pair in an Evans forcing jet has the explicit
one-dimensional Sobolev bound needed by the elliptic induction.

For an order-`m+1` jet this controls the head after lowering one spatial
order:

`‖f(t)‖_{H^m} ≤ sqrt (‖f‖²_{L²(H^m)} /(t1-t0)
  + 2 ‖f‖_{L²(H^m)} ‖f_t‖_{L²(H^m)})`.

Unlike `SobolevTimeJet.exists_lowerOrder_head_bound`, the constant here is
not chosen existentially. It is computed from the two Bochner norms stored
by the jet and can therefore be propagated into a final data-only estimate.
-/
theorem SobolevTimeJet.ae_lowerOrder_head_norm_le_timeSobolevBound
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) (ht : t0 < t1) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), ‖lowerOrderCLM (n := n) (p := 2) (Ω := Omega)
      (Nat.le_succ m) (F.head t)‖ ≤ PDE.Analysis.Evolution.timeSobolevBound
      (lowerOrderTimeLp F.head) F.timeDerivative.head := by
  let X := W^{m,2}(Omega)
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ X) := borel (StrongDual ℝ X)
  let : BorelSpace (StrongDual ℝ X) := ⟨rfl⟩
  cases F with
  | mk head derivatives =>
      cases derivatives with
      | succ _ df hderiv _ =>
          change ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
              ‖lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (head t)‖ ≤
                PDE.Analysis.Evolution.timeSobolevBound (lowerOrderTimeLp head) df
          have hbound := hderiv.ae_norm_le_timeSobolevBound_of_identity ht
          filter_upwards [hbound, lowerOrderTimeLp_apply_ae head] with
            t hbound hhead
          rwa [hhead] at hbound

/--
Finite levelwise bounds assemble into one bound for the Sobolev norm sum.

This is the measure-theoretic bookkeeping behind the essential supremum in
Evans (64): because there are only `m + 2` derivative levels, the
almost-everywhere exceptional sets can be intersected.
-/
theorem solutionSobolevNormSum_le_sum_of_levelBounds (u : SobolevTimeJet n (m + 1) Omega t0 t1)
    (levelBound : Fin (m + 2) → ℝ)
    (hlevel : ∀ r : Fin (m + 2), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative r).head t‖ ≤ levelBound r) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), solutionSobolevNormSum u t ≤ ∑ r, levelBound r := by
  filter_upwards [Filter.eventually_all.2 hlevel] with t ht using Finset.sum_le_sum fun r _ ↦ ht r

/--
Quantitative assembly of Evans, §7.2.3, estimate (64).

Assume that at every derivative level `r`

`‖partial_t^k u(t)‖ <= levelConstant r * dataBudget`

almost everywhere, where reverse index `r` represents derivative order
`k = m + 1 - r`. If the sum of the level constants is at most `C`, then the
complete Sobolev norm sum satisfies Evans's estimate (64) with constant `C`.

The hypotheses are strictly levelwise: none assumes the summed estimate or
an essential-supremum bound for the complete solution jet.
-/
theorem solutionSobolevNormSum_le_mul_dataBudget_of_levelBounds
    (D : WaveProblemData n m Omega t0 t1) (u : SobolevTimeJet n (m + 1) Omega t0 t1)
    (levelConstant : Fin (m + 2) → ℝ) (C : ℝ)
    (hlevel : ∀ r : Fin (m + 2), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative r).head t‖ ≤ levelConstant r * evansHigherRegularityDataBudget D)
    (hconstant : ∑ r, levelConstant r ≤ C) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), solutionSobolevNormSum u t ≤
      C * evansHigherRegularityDataBudget D := by
  have hsum := solutionSobolevNormSum_le_sum_of_levelBounds u
      (fun r ↦ levelConstant r * evansHigherRegularityDataBudget D) hlevel
  filter_upwards [hsum] with t ht
  calc
    solutionSobolevNormSum u t ≤ ∑ r, levelConstant r * evansHigherRegularityDataBudget D := ht
    _ = (∑ r, levelConstant r) *
        evansHigherRegularityDataBudget D := by
      rw [Finset.sum_mul]
    _ ≤ C * evansHigherRegularityDataBudget D := mul_le_mul_of_nonneg_right hconstant
        (evansHigherRegularityDataBudget_nonneg D)

/--
The essential-supremum form of
`solutionSobolevNormSum_le_mul_dataBudget_of_levelBounds`.

`eLpNormEssSup` is extended-real-valued, so the real Evans bound appears
through `ENNReal.ofReal`.
-/
theorem eLpNormEssSup_solutionSobolevNormSum_le_of_levelBounds (D : WaveProblemData n m Omega t0 t1)
    (u : SobolevTimeJet n (m + 1) Omega t0 t1) (levelConstant : Fin (m + 2) → ℝ) (C : ℝ)
    (hlevel : ∀ r : Fin (m + 2), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative r).head t‖ ≤ levelConstant r * evansHigherRegularityDataBudget D)
    (hconstant : ∑ r, levelConstant r ≤ C) :
    eLpNormEssSup (solutionSobolevNormSum u) (volume.restrict (Set.Ioc t0 t1)) ≤
      ENNReal.ofReal (C * evansHigherRegularityDataBudget D) := by
  apply eLpNormEssSup_le_of_ae_bound
  have hbound := solutionSobolevNormSum_le_mul_dataBudget_of_levelBounds
      D u levelConstant C hlevel hconstant
  filter_upwards [hbound] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (solutionSobolevNormSum_nonneg u t)]
  exact ht

/--
Uniform version of the quantitative assembly theorem.

If one constant `C_level` controls every differentiated energy and
elliptic level, then `(m + 2) * C_level` is a valid constant in Evans (64).
Dependence on `m` is permitted in Theorem 6.
-/
theorem solutionSobolevNormSum_le_of_uniformLevelBound (D : WaveProblemData n m Omega t0 t1)
    (u : SobolevTimeJet n (m + 1) Omega t0 t1) (Clevel : ℝ)
    (hlevel : ∀ r : Fin (m + 2), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
      ‖(u.iteratedTimeDerivative r).head t‖ ≤ Clevel * evansHigherRegularityDataBudget D) :
    ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1), solutionSobolevNormSum u t ≤
      ((m + 2 : ℕ) : ℝ) * Clevel * evansHigherRegularityDataBudget D := by
  have h := solutionSobolevNormSum_le_mul_dataBudget_of_levelBounds
    D u (fun _ ↦ Clevel) (((m + 2 : ℕ) : ℝ) * Clevel) hlevel
    (by simp)
  simpa only [mul_assoc] using h

end Hyperbolic.HigherRegularity
