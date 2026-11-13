/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.ClassicalHigherFull
public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.WeakTimeDerivative

/-!
# Quantitative higher spatial recovery for the full wave operator

The shifted elliptic solver acts on `f - u_tt + mu * P`, where `P` is a lower
spatial representative of the same displacement. Bounded linear composition
constructs the higher Bochner curve. The original weak equation then identifies
its whole first-order Sobolev graph.

The bound on `P` is a hypothesis. In the wave induction it comes
from the initial displacement and the time integral of the next derivative.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n r : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Recover two spatial orders by applying the shifted inverse to a genuine
Sobolev-valued residual of the original unshifted wave. -/
theorem exists_higher_trajectory_of_full_weakWave
    (hopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (mu : ℝ) (S : W^{r,2}(Ω) →L[ℝ] W^{(r + 2),2}(Ω))
    (hS : ∀ (F : W^{r,2}(Ω)) (u : H¹₀(Ω)),
      IsWeakShiftedFullDivergenceSolution A B C mu (wkpBaseCoordinateCLM F) 0 u →
      wkpBaseCoordinateCLM (S F) = baseCoordCLM u)
    {f w P : Lp (W^{r,2}(Ω)) 2 (volume.restrict (Ioc a b))}
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {g : H¹₀(Ω)} {h : DerivLp n 2 Ω}
    (hweak : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ fullDivergenceForm (multiplicationCoefficientOperator A)
        (fun i ↦ mulLpLeft (B i)) (mulLpLeft C))
      (dirichletLoadTimeLp hopen f) u v (dirichletLoadTimeLp hopen w) g h)
    (hP : ∀ᵐ t ∂volume.restrict (Ioc a b), wkpBaseCoordinateCLM (P t) = baseCoordCLM (u t))
    {Cf Cw Cp : ℝ}
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖f t‖ ≤ Cf)
    (hw : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖w t‖ ≤ Cw)
    (hp : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖P t‖ ≤ Cp) :
    ∃ U : Lp (W^{(r + 2),2}(Ω)) 2 (volume.restrict (Ioc a b)),
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        lowerOrderCLM (by omega : 1 ≤ r + 2) (U t) = h10SubtypeL (u t)) ∧
      MemLp (fun t ↦ U t) ∞ (volume.restrict (Ioc a b)) ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), ‖U t‖ ≤ ‖S‖ * (Cf + Cw + |mu| * Cp) := by
  let μ := volume.restrict (Ioc a b)
  let residual := f - w + mu • P
  let U := S.compLpL 2 μ residual
  have hr : (residual : ℝ → W^{r,2}(Ω)) =ᵐ[μ]
      fun t ↦ f t - w t + mu • P t := by
    filter_upwards [Lp.coeFn_add (f - w) (mu • P), Lp.coeFn_sub f w,
      Lp.coeFn_smul mu P] with t hadd hsub hsmul
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hadd hsub hsmul
    rw [hadd, hsub, hsmul]
  have hrbound : ∀ᵐ t ∂μ, ‖residual t‖ ≤ Cf + Cw + |mu| * Cp := by
    filter_upwards [hr, hf, hw, hp] with t ht hft hwt hpt
    rw [ht]
    calc
      _ ≤ ‖f t‖ + ‖w t‖ + |mu| * ‖P t‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using (norm_add_le (f t - w t) (mu • P t)).trans
            (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hft hwt) (mul_le_mul_of_nonneg_left hpt (abs_nonneg mu))
  have hU := S.coeFn_compLpL residual
  have hUbound : ∀ᵐ t ∂μ, ‖U t‖ ≤ ‖S‖ * (Cf + Cw + |mu| * Cp) := by
    filter_upwards [hU, hrbound] with t ht hb
    rw [show U t = S (residual t) from ht]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg S))
  refine ⟨U, ?_, memLp_top_of_bound (Lp.aestronglyMeasurable U) _ hUbound, hUbound⟩
  filter_upwards [hU, hr, hP, hweak.equationAE,
    dirichletLoadTimeLp_apply_ae hopen f, dirichletLoadTimeLp_apply_ae hopen w]
    with t hUt hrt hPt hEq hft hwt
  have hspatial : IsWeakShiftedFullDivergenceSolution A B C 0
      (wkpBaseCoordinateCLM (f t) - wkpBaseCoordinateCLM (w t)) 0 (u t) := by
    apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen A B C 0 _ 0 _).mp
    intro x
    have hx := congrArg (fun ell ↦ ell x) hEq
    rw [hft, hwt] at hx
    simp only [shiftedDivergenceForm_apply, zero_mul, add_zero,
      generalizedLoad_apply, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, inner_sub_left]
    exact eq_sub_of_add_eq' hx
  have hshift : IsWeakShiftedFullDivergenceSolution A B C mu
      (wkpBaseCoordinateCLM (f t - w t + mu • P t)) 0 (u t) := by
    have hs := (isWeakShiftedFullDivergenceSolution_change_shift A B C 0 mu
      (wkpBaseCoordinateCLM (f t) - wkpBaseCoordinateCLM (w t)) (u t)).mp hspatial
    simpa only [sub_zero, map_add, map_sub, map_smul, hPt] using hs
  apply wkpBaseCoordinateCLM_injective hopen
  change wkpBaseCoordinateCLM (U t) = baseCoordCLM (u t)
  rw [show U t = S (residual t) from hUt, hrt]
  exact hS _ _ hshift

end Hyperbolic.HigherRegularity
