/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient.CoerciveComparison
public import PDE.FDeriv.Operators
import CAS.ExactTactic

/-!
# Properness of eikonal functions under quadratic matrix growth

An upper quadratic-form bound of order `1 + ‖x - c‖²` gives a logarithmic lower
bound for a positive eikonal function vanishing at `c`. The comparison is obtained
from derivatives, and compactness follows from an explicit closed-ball
inclusion. Lower ellipticity and symmetry are not needed for this geometric result.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis.Eikonal

open Filter Set
open scoped Topology

section Radius

variable {E : Type*} [NormedAddCommGroup E]

/-- The logarithmic comparison radius for a matrix bound of order `C²(1 + ‖x - c‖²)`. -/
def logarithmicRadius (C : ℝ) (c x : E) : ℝ :=
  Real.log (1 + ‖x - c‖ ^ 2) / (2 * C)

/-- The comparison radius is continuous, including at its center. -/
theorem continuous_logarithmicRadius (C : ℝ) (c : E) :
    Continuous (logarithmicRadius C c) := by
  exact ((continuous_const.add ((continuous_id.sub continuous_const).norm.pow 2)).log
    (fun x ↦ by
      change 1 + ‖x - c‖ ^ 2 ≠ 0
      positivity)).div_const (2 * C)

/-- The comparison radius vanishes at its center. -/
@[simp] theorem logarithmicRadius_self (C : ℝ) (c : E) :
    logarithmicRadius C c c = 0 := by
  simp [logarithmicRadius]

/-- On a proper normed space, the logarithmic radius tends to infinity off compact sets. -/
theorem tendsto_logarithmicRadius_cocompact [ProperSpace E] {C : ℝ} (hC : 0 < C)
    (c : E) : Tendsto (logarithmicRadius C c) (cocompact E) atTop := by
  have hn : Tendsto (fun x : E ↦ ‖x - c‖) (cocompact E) atTop := by
    simpa only [dist_eq_norm] using tendsto_dist_right_cocompact_atTop c
  have hsq := (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hn
  have hsum : Tendsto (fun x : E ↦ 1 + ‖x - c‖ ^ 2) (cocompact E) atTop :=
    tendsto_atTop_mono (fun _ ↦ le_add_of_nonneg_left zero_le_one) hsq
  exact (Real.tendsto_log_atTop.comp hsum).atTop_div_const (mul_pos zero_lt_two hC)

variable [InnerProductSpace ℝ E]

/-- The Fréchet derivative of the logarithmic comparison radius. -/
theorem hasFDerivAt_logarithmicRadius {C : ℝ} (hC : 0 < C) (c x : E) :
    HasFDerivAt (logarithmicRadius C c)
      ((C * (1 + ‖x - c‖ ^ 2))⁻¹ • innerSL ℝ (x - c)) x := by
  have hp : 0 < 1 + ‖x - c‖ ^ 2 := by positivity
  have hd := (((hasFDerivAt_id x).sub_const c).norm_sq.const_add 1).log hp.ne'
  unfold logarithmicRadius
  simp only [div_eq_mul_inv]
  convert hd.mul_const ((2 * C)⁻¹) using 1
  · rfl
  · ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      id_eq, smul_eq_mul, innerSL_apply_apply]
    cas

/-- Its derivative norm is the exact radial quotient. -/
theorem norm_fderiv_logarithmicRadius {C : ℝ} (hC : 0 < C) (c x : E) :
    ‖fderiv ℝ (logarithmicRadius C c) x‖ =
      ‖x - c‖ / (C * (1 + ‖x - c‖ ^ 2)) := by
  rw [(hasFDerivAt_logarithmicRadius hC c x).fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (mul_pos hC (by positivity))), innerSL_apply_norm]
  exact (div_eq_inv_mul _ _).symm

end Radius

variable {n : ℕ}

/-- Raw quadratic matrix growth and the eikonal identity give a logarithmic lower bound.
The function need only be differentiable away from its unique zero. -/
theorem logarithmicRadius_le_of_matrix_eikonal
    {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {C : ℝ} (hC : 0 < C) {c : ℝ^n}
    (hupper : ∀ x (v : ℝ^n),
      (∑ i, ∑ j, a x i j * v i * v j) ≤ C ^ 2 * (1 + ‖x - c‖ ^ 2) * ‖v‖ ^ 2)
    {q : ℝ^n → ℝ} (hq : Continuous q) (hqc : q c = 0)
    (hqpos : ∀ x, x ≠ c → 0 < q x)
    (hqd : ∀ x, x ≠ c → DifferentiableAt ℝ q x)
    (heik : ∀ x, x ≠ c →
      ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1)
    (x : ℝ^n) : logarithmicRadius C c x ≤ q x := by
  have henergy (y : ℝ^n) (hy : y ≠ c) :
      1 ≤ C ^ 2 * (1 + ‖y - c‖ ^ 2) * ‖fderiv ℝ q y‖ ^ 2 := by
    have hn : ‖∇ q y‖ = ‖fderiv ℝ q y‖ :=
      (InnerProductSpace.toDual ℝ (ℝ^n)).symm.norm_map _
    rw [← hn]
    simpa only [gradient_apply_eq_partialDeriv, heik y hy] using hupper y (∇ q y)
  apply coercive_le_of_fderiv_norm_le hq (continuous_logarithmicRadius C c)
      (fun y ↦ ?_) hqc (logarithmicRadius_self C c)
      (tendsto_logarithmicRadius_cocompact hC c) hqd
      (fun y _ ↦ (hasFDerivAt_logarithmicRadius hC c y).differentiableAt)
      (fun y hy ↦ ?_) (fun y hy ↦ ?_) x
  · by_cases hy : y = c
    · simp [hy, hqc]
    · exact (hqpos y hy).le
  · intro hz
    have hh := henergy y hy
    norm_num [hz] at hh
  · rw [norm_fderiv_logarithmicRadius hC]
    have hp : 0 < 1 + ‖y - c‖ ^ 2 := by positivity
    apply (div_le_iff₀ (mul_pos hC hp)).mpr
    have hh := mul_le_mul_of_nonneg_left (henergy y hy) hp.le
    have hnonneg : 0 ≤ ‖fderiv ℝ q y‖ * (C * (1 + ‖y - c‖ ^ 2)) := by positivity
    nlinarith [norm_nonneg (y - c)]

/-- The logarithmic lower bound puts every sublevel in an explicit closed ball. -/
theorem sublevel_subset_closedBall_of_logarithmicRadius_le
    {C : ℝ} (hC : 0 < C) {c : ℝ^n} {q : ℝ^n → ℝ}
    (hlower : ∀ x, logarithmicRadius C c x ≤ q x) (r : ℝ) :
    {x | q x ≤ r} ⊆ Metric.closedBall c (√(Real.exp (2 * C * r) - 1)) := by
  intro x hx
  have hlog : Real.log (1 + ‖x - c‖ ^ 2) ≤ 2 * C * r := by
    have hh := (hlower x).trans hx
    exact ((div_le_iff₀ (mul_pos zero_lt_two hC)).mp hh).trans_eq (mul_comm r _)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : 0 < 1 + ‖x - c‖ ^ 2)] at hexp
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- All eikonal sublevels are compact under raw at-most-quadratic matrix growth.
Compactness is derived, not assumed. The statement includes dimension zero. -/
theorem isCompact_sublevel_of_matrix_eikonal
    {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {C : ℝ} (hC : 0 < C) {c : ℝ^n}
    (hupper : ∀ x (v : ℝ^n),
      (∑ i, ∑ j, a x i j * v i * v j) ≤ C ^ 2 * (1 + ‖x - c‖ ^ 2) * ‖v‖ ^ 2)
    {q : ℝ^n → ℝ} (hq : Continuous q) (hqc : q c = 0)
    (hqpos : ∀ x, x ≠ c → 0 < q x)
    (hqd : ∀ x, x ≠ c → DifferentiableAt ℝ q x)
    (heik : ∀ x, x ≠ c →
      ∑ i, ∑ j, a x i j * (∂[i] q) x * (∂[j] q) x = 1)
    (r : ℝ) : IsCompact {x | q x ≤ r} := by
  exact (isCompact_closedBall c (√(Real.exp (2 * C * r) - 1))).of_isClosed_subset
    (isClosed_le hq continuous_const)
    (sublevel_subset_closedBall_of_logarithmicRadius_le hC
      (logarithmicRadius_le_of_matrix_eikonal hC hupper hq hqc hqpos hqd heik) r)

end PDE.Analysis.Eikonal
