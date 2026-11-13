/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.Speed
public import PDE.Examples.Hyperbolic.ConservationLaw.System.OneComponent
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Symbolic.PDEDerivatives

/-!
# The nonzero quadratic speed defect of a cubic flux

For `F(u) = u³/3`, the shock speed based at one differs from the
mean of the endpoint characteristic speeds by `-(u - 1)²/6`. Along the smooth shock
curve through `1` from `exists_local_shock_curves_with_quadratic_speed`, the speed
therefore differs from the mean characteristic speed by exactly this quadratic term
(`exists_smooth_shock_with_nonzero_quadratic_defect`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.ShockCurve.Cubic

open PDE.Common PDE.Hyperbolic.ConservationLaw.System
open Filter Set
open scoped ContDiff Topology

/-- Cubic flux on a one-component Euclidean state space. -/
def flux (q : ℝ^1) : ℝ^1 := WithLp.toLp 2 ![q 0 ^ 3 / 3]

/-- The polynomial flux is smooth. -/
theorem contDiff_flux : ContDiff ℝ ∞ flux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  change ContDiff ℝ ∞ (fun q : ℝ^1 ↦ q 0 ^ 3 / 3)
  cas

/-- The Jacobian acts by multiplication by the square of the state. -/
theorem fderiv_flux (q v : ℝ^1) : fderiv ℝ flux q v = q 0 ^ 2 • v := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  ext i
  fin_cases i
  simp only [Fin.sum_univ_one, PiLp.smul_apply, smul_eq_mul]
  have hd : (∂[0] flux) q 0 = q 0 ^ 2 := by
    rw [partialDeriv_apply 0 0 (contDiff_flux.differentiable (by simp) q)]
    change (∂[0] ((fun y : ℝ^1 ↦ y 0 ^ 3 / 3) : ℝ^1 → ℝ)) q = q 0 ^ 2
    cas
  change v 0 * (∂[0] flux) q 0 = q 0 ^ 2 * v 0
  rw [hd, mul_comm]

/-- The cubic flux is strictly hyperbolic at every state. -/
theorem isStrictlyHyperbolicAt_flux (q : ℝ^1) : IsStrictlyHyperbolicAt flux q :=
  OneComponent.isStrictlyHyperbolicAt_of_fderiv_eq_smul
    (contDiff_flux.differentiable (by simp) q) (fderiv_flux q)

/-- The ordered speed is the square of the scalar state. -/
theorem characteristicSpeed_flux (q : ℝ^1) (k : Fin 1) :
    characteristicSpeed flux k q = q 0 ^ 2 :=
  OneComponent.characteristicSpeed_eq_of_fderiv_eq_smul (fderiv_flux q) k

/-- Rankine–Hugoniot determines the explicit speed for a nonzero jump. -/
theorem speed_eq_of_rankineHugoniot {q : ℝ^1} {a : ℝ}
    (hq : q ≠ WithLp.toLp 2 ![(1 : ℝ)])
    (hRH : RankineHugoniot flux (WithLp.toLp 2 ![1]) q a) :
    a = (q 0 ^ 2 + q 0 + 1) / 3 := by
  have hne : q 0 - 1 ≠ 0 := by
    intro h
    apply hq
    ext i
    fin_cases i
    exact sub_eq_zero.mp h
  have heq := congrArg (fun v : ℝ^1 ↦ v 0) hRH
  change q 0 ^ 3 / 3 - 1 ^ 3 / 3 = a * (q 0 - 1) at heq
  apply mul_right_cancel₀ hne
  calc
    a * (q 0 - 1) = q 0 ^ 3 / 3 - 1 ^ 3 / 3 := heq.symm
    _ = ((q 0 ^ 2 + q 0 + 1) / 3) * (q 0 - 1) := by cas

/-- `(u² + u + 1)/3 - (u² + 1)/2 = -(u - 1)²/6`. -/
theorem midpoint_defect (u : ℝ) :
    (u ^ 2 + u + 1) / 3 - (u ^ 2 + 1) / 2 = -(u - 1) ^ 2 / 6 := by
  cas

/-- The shock curve through `1` is smooth, its speed is `(u² + u + 1)/3`, and the speed
minus the mean characteristic speed is `-(u - 1)²/6`, negative at every nonzero
strength. -/
theorem exists_smooth_shock_with_nonzero_quadratic_defect :
    ∃ S : ℝ → ℝ^1, ∃ speed : ℝ → ℝ, ∃ I : Set ℝ, ∃ C : ℝ,
      IsOpen I ∧ 0 ∈ I ∧ 0 ≤ C ∧ S 0 = WithLp.toLp 2 ![1] ∧ speed 0 = 1 ∧
      ContDiffOn ℝ ∞ S I ∧ ContDiffOn ℝ ∞ speed I ∧
      ∀ s ∈ I, RankineHugoniot flux (WithLp.toLp 2 ![1]) (S s) (speed s) ∧
        speed s = ((S s 0) ^ 2 + S s 0 + 1) / 3 ∧
        speed s - ((S s 0) ^ 2 + 1) / 2 = -(S s 0 - 1) ^ 2 / 6 ∧
        |speed s - ((S s 0) ^ 2 + 1) / 2| ≤ C * ‖S s - WithLp.toLp 2 ![1]‖ ^ 2 ∧
        (s ≠ 0 → speed s - ((S s 0) ^ 2 + 1) / 2 < 0) := by
  obtain ⟨b, S, speed, I, _V, C, hC, _heigen, hI, hzero, _hV, _huV, _hVU,
      hcurves, _hclass⟩ :=
    exists_local_shock_curves_with_quadratic_speed (n := ⊤) (by simp)
      isOpen_univ (mem_univ (WithLp.toLp 2 ![(1 : ℝ)]))
      (by simpa using contDiff_flux.contDiffOn)
      (isStrictlyHyperbolicAt_flux _)
  have hbase : speed 0 0 = 1 := by
    simpa only [characteristicSpeed_flux, PiLp.toLp_apply, Matrix.cons_val_zero, one_pow]
      using (hcurves 0).2.1
  refine ⟨S 0, speed 0, I, C, hI, hzero, hC, (hcurves 0).1, hbase,
    (hcurves 0).2.2.1, (hcurves 0).2.2.2.1, ?_⟩
  intro s hs
  obtain ⟨_hsU, hsRH, hscoord, hsbound⟩ := (hcurves 0).2.2.2.2.2.2 s hs
  have hstate (h : S 0 s = WithLp.toLp 2 ![(1 : ℝ)]) : s = 0 := by
    simpa only [h, sub_self, map_zero, Pi.zero_apply] using hscoord.symm
  have hformula : speed 0 s = ((S 0 s 0) ^ 2 + S 0 s 0 + 1) / 3 := by
    by_cases h : S 0 s = WithLp.toLp 2 ![(1 : ℝ)]
    · rw [hstate h, (hcurves 0).1, hbase]
      norm_num
    · exact speed_eq_of_rankineHugoniot h hsRH
  have hdefect : speed 0 s - ((S 0 s 0) ^ 2 + 1) / 2 = -(S 0 s 0 - 1) ^ 2 / 6 := by
    rw [hformula]
    exact midpoint_defect _
  refine ⟨hsRH, hformula, hdefect, ?_, ?_⟩
  · simpa only [characteristicSpeed_flux, PiLp.toLp_apply, Matrix.cons_val_zero, one_pow]
      using hsbound
  · intro hsne
    have hne : S 0 s 0 - 1 ≠ 0 := by
      intro h
      apply hsne
      apply hstate
      ext i
      fin_cases i
      exact sub_eq_zero.mp h
    rw [hdefect]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero hne)) (by norm_num)

end PDE.Examples.Hyperbolic.ConservationLaw.System.ShockCurve.Cubic
