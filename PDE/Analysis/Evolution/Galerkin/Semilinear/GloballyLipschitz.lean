/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Galerkin.Semilinear.Pivot
import PDE.Analysis.Evolution.Integrated.TimeChange.Exponential
import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition

/-!
# Globally Lipschitz reactions in a Gelfand triple

A Gårding form and a globally Lipschitz reaction admit a unique weak solution
on every finite time interval. The linear response is constructed by the
Galerkin theorem. Multiplying the unknown by an exponential adds enough pivot
coercivity to make the nonlinear response contractive.

The rescaled reaction retains its original Lipschitz constant: the exponential
factors cancel in its difference estimate. Its value at zero need not vanish;
the constant offset is square integrable on a finite interval. The solution
satisfies the integrated weak equation with its original initial datum.

Evans solves the reaction–diffusion system `u_t - Δu = f(u)` with Lipschitz `f`
(§9.2.1, Example 1 and Theorem 2). He shows that the solution map is a strict contraction
on `C([0, T]; L²)` when `T` is small and then extends the solution interval by interval.
The exponential weight lets us apply Banach's theorem once, on the whole interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.1, Example 1 and Theorem 2 (existence for the
  reaction-diffusion system with Lipschitz nonlinearity). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis.Evolution

private theorem lipschitzWith_exponential_superposition
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a b : ℝ} {R : H → H} {L : ℝ≥0} (hR : LipschitzWith L R)
    (hmem : ∀ v : Lp H 2 (volume.restrict (Ioc a b)),
      MemLp (fun t ↦ R (v t)) 2 (volume.restrict (Ioc a b)))
    (eta : ℝ) :
    LipschitzWith L (fun v ↦ exponentialMulLp (-eta)
      (Lp.superposition (fun _ ↦ R) hmem (exponentialMulLp eta v))) := by
  let N := Lp.superposition (fun _ ↦ R) hmem
  refine LipschitzWith.of_dist_le_mul fun v w ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards
    [Lp.coeFn_sub (exponentialMulLp (-eta) (N (exponentialMulLp eta v)))
      (exponentialMulLp (-eta) (N (exponentialMulLp eta w))),
    exponentialMulLp_apply_ae (-eta) (N (exponentialMulLp eta v)),
    exponentialMulLp_apply_ae (-eta) (N (exponentialMulLp eta w)),
    Lp.coeFn_superposition (fun _ ↦ R) hmem (exponentialMulLp eta v),
    Lp.coeFn_superposition (fun _ ↦ R) hmem (exponentialMulLp eta w),
    exponentialMulLp_apply_ae eta v, exponentialMulLp_apply_ae eta w,
    Lp.coeFn_sub v w] with t hsub hv hw hNv hNw hev hew hvw
  change N (exponentialMulLp eta v) t = _ at hNv
  change N (exponentialMulLp eta w) t = _ at hNw
  have hcancel : Real.exp (-eta * (t - a)) * Real.exp (eta * (t - a)) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  rw [hsub, Pi.sub_apply, hv, hw, hNv, hNw, hev, hew, hvw, Pi.sub_apply, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  calc _ ≤ Real.exp (-eta * (t - a)) *
        ((L : ℝ) * ‖Real.exp (eta * (t - a)) • v t - Real.exp (eta * (t - a)) • w t‖) :=
        mul_le_mul_of_nonneg_left (hR.norm_sub_le _ _) (Real.exp_pos _).le
    _ = (L : ℝ) * ‖v t - w t‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      linear_combination ((L : ℝ) * ‖v t - w t‖) * hcancel

/-- Let `t ↦ B(t) v` be measurable, with `‖B(t)‖ ≤ MB` and the Gårding inequality
`θ ‖v‖² ≤ B(t)(v, v) + γ ‖ι v‖²` almost everywhere, and let `R : H → H` be Lipschitz. Then
`u' + B(t) u = R(ι u)` has exactly one integrated weak solution on `[a, b]` with initial value
`uInit`. The interval length and the Lipschitz constant are arbitrary. -/
theorem IsGelfandIntegratedWeakSolution.existsUnique_of_lipschitz_reaction
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : StableTrialSystem T)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b theta gamma : ℝ}
    (hab : a < b) (htheta : 0 < theta)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Ioc a b)))
    (MB : ℝ≥0)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      theta * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2)
    (R : H → H) {L : ℝ≥0} (hR : LipschitzWith L R) (uInit : H) :
    ∃! u : Lp V 2 (volume.restrict (Ioc a b)),
      IsGelfandIntegratedWeakSolution T B
        (fun t ↦ T.pivotToDual (R (T.inclusion (u t)))) u uInit := by
  classical
  let ν := volume.restrict (Ioc a b)
  let J := T.inclusion.compLpL 2 ν
  let Q := T.pivotToDual.compLpL 2 ν
  have hmem (v : Lp H 2 ν) : MemLp (fun t ↦ R (v t)) 2 ν :=
    hR.comp_memLp_of_memLp_const (memLp_const (R 0)) (Lp.memLp v)
  let N := Lp.superposition (fun _ ↦ R) hmem
  let eta : ℝ := gamma + (L : ℝ) + 1
  let F (v : Lp H 2 ν) := exponentialMulLp (-eta) (N (exponentialMulLp eta v))
  have hF : LipschitzWith L F := lipschitzWith_exponential_superposition hR hmem eta
  have hshiftBound : ∀ᵐ t ∂ν,
      ‖gardingShiftForm T B eta t‖ ≤ (MB : ℝ) + ‖eta‖ * ‖T.energyToDual‖ :=
    hbound.mono fun t ht ↦ (norm_gardingShiftForm_le T B eta t).trans (add_le_add ht le_rfl)
  have hshiftGarding : ∀ᵐ t ∂ν, ∀ v : V,
      theta * ‖v‖ ^ 2 ≤ gardingShiftForm T B eta t v v + 0 * ‖T.inclusion v‖ ^ 2 := by
    filter_upwards [hGarding] with t ht v
    rw [gardingShiftForm_apply, real_inner_self_eq_norm_sq, zero_mul, add_zero]
    have hnonneg := mul_nonneg (show 0 ≤ (L : ℝ) + 1 by positivity)
      (sq_nonneg ‖T.inclusion v‖)
    dsimp only [eta]
    linarith [ht v]
  have hcoercive : ∀ᵐ t ∂ν, ∀ v : V,
      ((L + 1 : ℝ≥0) : ℝ) * ‖T.inclusion v‖ ^ 2 ≤
        gardingShiftForm T B eta t v v := by
    filter_upwards [hGarding] with t ht v
    rw [gardingShiftForm_apply, real_inner_self_eq_norm_sq]
    have hnonneg := mul_nonneg htheta.le (sq_nonneg ‖v‖)
    simp only [NNReal.coe_add, NNReal.coe_one]
    dsimp only [eta]
    linarith [ht v]
  obtain ⟨w, hw, hunique⟩ :=
    IsGelfandIntegratedWeakSolution.existsUnique_of_lipschitz_pivot T S
      (gardingShiftForm T B eta) hab htheta (le_refl 0)
      (aestronglyMeasurable_gardingShiftForm T hB)
      (MB + ‖eta‖₊ * ‖T.energyToDual‖₊) hshiftBound hshiftGarding
      hcoercive F hF (by simp) uInit
  -- The two embeddings commute with the time weight, so the nonlinear
  -- forcing transforms by the same rule as a prescribed linear forcing.
  have hload (v : Lp V 2 ν) :
      Q (F (J v)) =
        exponentialMulLp (-eta) (Q (N (J (exponentialMulLp eta v)))) := by
    dsimp [F, J, Q]
    rw [ContinuousLinearMap.compLpL_exponentialMulLp,
      ContinuousLinearMap.compLpL_exponentialMulLp]
  have hloadAE (v : Lp V 2 ν) :
      (Q (N (J v)) : ℝ → StrongDual ℝ V) =ᵐ[ν]
        fun t ↦ T.pivotToDual (R (T.inclusion (v t))) := by
    filter_upwards [T.pivotToDual.coeFn_compLpL (N (J v)),
      Lp.coeFn_superposition (fun _ ↦ R) hmem (J v),
      T.inclusion.coeFn_compLpL v] with t hQ hN hJ
    change Q (N (J v)) t = _ at hQ
    change N (J v) t = _ at hN
    change J v t = _ at hJ
    rw [hQ, hN, hJ]
  refine ⟨exponentialMulLp eta w, ?_, ?_⟩
  · change IsGelfandIntegratedWeakSolution T (gardingShiftForm T B eta)
      (Q (F (J w))) w uInit at hw
    rw [hload] at hw
    exact (hw.of_exponential_gardingShift hB MB hbound).congr_forcing_ae
      (hloadAE (exponentialMulLp eta w))
  · intro v hv
    have hcancel : exponentialMulLp eta (exponentialMulLp (-eta) v) = v := by
      simpa only [neg_neg] using exponentialMulLp_neg_cancel (-eta) v
    have hvfixed : IsGelfandIntegratedWeakSolution T (gardingShiftForm T B eta)
        (Q (F (J (exponentialMulLp (-eta) v)))) (exponentialMulLp (-eta) v) uInit := by
      rw [hload, hcancel]
      exact (hv.congr_forcing_ae (hloadAE v).symm).exponential_gardingShift (gamma := eta) hB MB
        hbound
    exact hcancel.symm.trans (congrArg (exponentialMulLp eta) (hunique _ hvfixed))

end PDE.Analysis.Evolution
