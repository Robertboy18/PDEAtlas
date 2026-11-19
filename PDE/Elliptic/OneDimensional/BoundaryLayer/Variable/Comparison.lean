/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.Weak
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CAS.ExactTactic

/-!
# Comparison for a positive-drift convection-diffusion equation

The scalar equation `εu″ + a u′ = f` is normalized to the sign convention of
the weak maximum principle. An affine barrier controls zero-trace residuals,
and an exponential barrier localizes the homogeneous left boundary correction.
-/

@[expose] public section

noncomputable section

namespace PDE.Elliptic.BoundaryLayer.Variable

open Set

/-- Unit-direction curvature is the ordinary second derivative, even for totalized derivatives. -/
theorem secondDirectionalDerivative_one (u : ℝ → ℝ) (x : ℝ) :
    PDE.Analysis.secondDirectionalDerivative u x 1 = deriv (deriv u) x := by
  simp only [PDE.Analysis.secondDirectionalDerivative, smul_eq_mul, mul_one]
  change deriv (fun t ↦ deriv (fun s ↦ u (x + s)) t) 0 = _
  simp_rw [deriv_comp_const_add]
  simp

/-- The normalized scalar drift operator has the sign required by the weak maximum principle. -/
theorem scalar_operator (a u : ℝ → ℝ) (ε x : ℝ) :
    EllipticMaximum.factoredOperator (fun (_ : ℝ) (_ : Unit) ↦ (1 : ℝ))
      (fun y ↦ -(a y / ε)) (fun _ ↦ 0) u x =
      -deriv (deriv u) x - (a x / ε) * deriv u x := by
  simp only [EllipticMaximum.factoredOperator, Fintype.sum_unique, secondDirectionalDerivative_one,
    fderiv_eq_smul_deriv, smul_eq_mul, zero_mul, add_zero]
  ring

/-- Nonnegative drift gives comparison for the singularly perturbed scalar equation. -/
theorem scalar_comparison {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (a : ℝ → ℝ) (ha : ∀ x ∈ Ioo 0 L, 0 ≤ a x)
    {u v : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hu₂ : ∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 u x)
    (hv₂ : ∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 v x)
    (hop : ∀ x ∈ Ioo 0 L,
      ε * deriv (deriv v) x + a x * deriv v x ≤
        ε * deriv (deriv u) x + a x * deriv u x)
    (hzero : u 0 ≤ v 0) (hend : u L ≤ v L) :
    ∀ x ∈ Icc 0 L, u x ≤ v x := by
  have hclosure : closure (Ioo 0 L) = Icc 0 L := closure_Ioo hL.ne
  rw [← hclosure]
  refine EllipticMaximum.le_of_operator_le_of_boundary_le
    (Ω := Ioo 0 L) isOpen_Ioo (by rw [hclosure]; exact isCompact_Icc)
    (fun (_ : ℝ) (_ : Unit) ↦ (1 : ℝ)) (fun x ↦ -(a x / ε)) (fun _ ↦ 0)
    (ContinuousLinearMap.id ℝ ℝ) (α := 1) (B := 0) (by norm_num)
    (by intros; simp) (by intro x hx; simpa using neg_nonpos.mpr (div_nonneg (ha x hx) hε.le))
    (by intros; exact le_rfl) (by rwa [hclosure]) (by rwa [hclosure]) hu₂ hv₂
    (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [scalar_operator, scalar_operator]
    have h := hop x hx
    have heq (z : ℝ → ℝ) :
        -deriv (deriv z) x - (a x / ε) * deriv z x =
          -(ε * deriv (deriv z) x + a x * deriv z x) / ε := by
      have hid (b d e : ℝ) : -e - (b / ε) * d = -(ε * e + b * d) / ε := by
        cas using hε.ne'
      exact hid _ _ _
    rw [heq, heq]
    exact div_le_div_of_nonneg_right (neg_le_neg h) hε.le
  · rw [frontier_Ioo hL] at hx
    rcases hx with rfl | hx
    · exact hzero
    · have hxL : x = L := Set.mem_singleton_iff.mp hx
      simpa [hxL] using hend

/-- Equal residuals and endpoint values determine a classical solution on the interval. -/
theorem scalar_uniqueness {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (a : ℝ → ℝ) (ha : ∀ x ∈ Ioo 0 L, 0 ≤ a x)
    {u v : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 L)) (hv : ContinuousOn v (Icc 0 L))
    (hu₂ : ∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 u x)
    (hv₂ : ∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 v x)
    (hop : ∀ x ∈ Ioo 0 L,
      ε * deriv (deriv u) x + a x * deriv u x =
        ε * deriv (deriv v) x + a x * deriv v x)
    (hzero : u 0 = v 0) (hend : u L = v L) : EqOn u v (Icc 0 L) := by
  intro x hx
  exact le_antisymm
    (scalar_comparison hL hε a ha hu hv hu₂ hv₂
      (fun y hy ↦ (hop y hy).ge) hzero.le hend.le x hx)
    (scalar_comparison hL hε a ha hv hu hv₂ hu₂
      (fun y hy ↦ (hop y hy).le) hzero.ge hend.ge x hx)

/-- A bounded residual with zero endpoint traces gives a uniform error bound of order ε. -/
theorem residual_bound {L ε α M : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hα : 0 < α) (hM : 0 ≤ M) (a : ℝ → ℝ)
    (ha : ∀ x ∈ Ioo 0 L, α ≤ a x)
    {r : ℝ → ℝ} (hr : ContinuousOn r (Icc 0 L))
    (hr₂ : ∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 r x)
    (hres : ∀ x ∈ Ioo 0 L, |ε * deriv (deriv r) x + a x * deriv r x| ≤ ε * M)
    (hzero : r 0 = 0) (hend : r L = 0) :
    ∀ x ∈ Icc 0 L, |r x| ≤ ε * M * (L - x) / α := by
  let φ : ℝ → ℝ := fun x ↦ ε * M * (L - x) / α
  have hφ : ContDiff ℝ 2 φ := by dsimp [φ]; fun_prop
  have hφpos (x : ℝ) (hx : x ∈ Icc 0 L) : 0 ≤ φ x :=
    div_nonneg (mul_nonneg (mul_nonneg hε.le hM) (sub_nonneg.mpr hx.2)) hα.le
  have hφderiv (x : ℝ) : HasDerivAt φ (-ε * M / α) x := by
    dsimp [φ]
    cas using hα.ne'
  have hφderiv_eq : deriv φ = fun _ ↦ -ε * M / α :=
    funext fun x ↦ (hφderiv x).deriv
  have hφsecond (x : ℝ) : deriv (deriv φ) x = 0 := by
    rw [hφderiv_eq]
    simp
  have hφop (x : ℝ) (hx : x ∈ Ioo 0 L) :
      ε * deriv (deriv φ) x + a x * deriv φ x ≤ -ε * M := by
    rw [hφsecond, (hφderiv x).deriv, mul_zero, zero_add]
    have hm : 0 ≤ ε * M / α := div_nonneg (mul_nonneg hε.le hM) hα.le
    have hbound := mul_le_mul_of_nonneg_right (ha x hx) hm
    have hcancel : α * (ε * M / α) = ε * M := mul_div_cancel₀ _ hα.ne'
    rw [hcancel] at hbound
    calc
      a x * (-ε * M / α) = -(a x * (ε * M / α)) := by ring
      _ ≤ -(ε * M) := neg_le_neg hbound
      _ = -ε * M := by ring
  have ha₀ (x : ℝ) (hx : x ∈ Ioo 0 L) : 0 ≤ a x := hα.le.trans (ha x hx)
  have hupper := scalar_comparison hL hε a ha₀ hr hφ.continuous.continuousOn hr₂
    (fun _ _ ↦ hφ.contDiffAt)
    (fun x hx ↦ (hφop x hx).trans (by simpa only [neg_mul] using (abs_le.mp (hres x hx)).1))
    (by rw [hzero]; exact hφpos 0 ⟨le_rfl, hL.le⟩)
    (by simp [hend, φ])
  have hnegop (x : ℝ) :
      ε * deriv (deriv (fun y ↦ -φ y)) x + a x * deriv (fun y ↦ -φ y) x =
        -(ε * deriv (deriv φ) x + a x * deriv φ x) := by
    have hd : deriv (fun y ↦ -φ y) = fun y ↦ -deriv φ y :=
      funext fun _ ↦ deriv.neg
    rw [hd]
    have hdd : deriv (fun y ↦ -deriv φ y) x = -deriv (deriv φ) x := deriv.neg
    rw [hdd]
    ring
  have hlower := scalar_comparison hL hε a ha₀ hφ.neg.continuous.continuousOn hr
    (fun _ _ ↦ hφ.neg.contDiffAt) hr₂
    (fun x hx ↦ by
      rw [hnegop]
      exact (abs_le.mp (hres x hx)).2.trans (by linarith [hφop x hx]))
    (by rw [hzero]; exact neg_nonpos.mpr (hφpos 0 ⟨le_rfl, hL.le⟩))
    (by simp [hend, φ])
  exact fun x hx ↦ abs_le.mpr ⟨hlower x hx, hupper x hx⟩

/-- The homogeneous left boundary correction decays exponentially into the interval. -/
theorem homogeneous_bound {L ε α : ℝ} (hL : 0 < L) (hε : 0 < ε) (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ∀ x ∈ Ioo 0 L, α ≤ a x)
    {H : ℝ → ℝ} (hH : ContinuousOn H (Icc 0 L))
    (hH₂ : ∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 H x)
    (hop : ∀ x ∈ Ioo 0 L, ε * deriv (deriv H) x + a x * deriv H x = 0)
    (hzero : H 0 = 1) (hend : H L = 0) :
    ∀ x ∈ Icc 0 L, 0 ≤ H x ∧ H x ≤ Real.exp (-α * x / ε) := by
  let E : ℝ → ℝ := fun x ↦ Real.exp (-α * x / ε)
  have hE : ContDiff ℝ 2 E := by dsimp [E]; fun_prop
  have hEderiv (x : ℝ) : HasDerivAt E ((-α / ε) * E x) x := by
    dsimp [E]
    cas using hε.ne'
  have hEderiv_eq : deriv E = fun x ↦ (-α / ε) * E x :=
    funext fun x ↦ (hEderiv x).deriv
  have hEsecond (x : ℝ) : deriv (deriv E) x = (α / ε) ^ 2 * E x := by
    rw [hEderiv_eq]
    have h : HasDerivAt (fun y ↦ (-α / ε) * Real.exp (-α * y / ε))
        ((α / ε) ^ 2 * E x) x := by
      dsimp [E]
      cas using hε.ne'
    exact h.deriv
  have hEop (x : ℝ) (hx : x ∈ Ioo 0 L) :
      ε * deriv (deriv E) x + a x * deriv E x ≤ 0 := by
    rw [hEsecond, (hEderiv x).deriv]
    have hid (b z : ℝ) : ε * ((α / ε) ^ 2 * z) + b * ((-α / ε) * z) =
        α * (α - b) / ε * z := by cas using hε.ne'
    rw [hid]
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hα.le (sub_nonpos.mpr (ha x hx))) hε.le)
      (Real.exp_pos _).le
  have ha₀ (x : ℝ) (hx : x ∈ Ioo 0 L) : 0 ≤ a x := hα.le.trans (ha x hx)
  have hupper := scalar_comparison hL hε a ha₀ hH hE.continuous.continuousOn hH₂
    (fun _ _ ↦ hE.contDiffAt)
    (fun x hx ↦ by rw [hop x hx]; exact hEop x hx)
    (by simp [hzero, E]) (by rw [hend]; exact (Real.exp_pos _).le)
  have hlower := scalar_comparison hL hε a ha₀ (u := fun _ ↦ 0) continuousOn_const hH
    (fun _ _ ↦ contDiffAt_const) hH₂
    (fun x hx ↦ by rw [hop x hx]; simp)
    (by simp [hzero]) (by simp [hend])
  exact fun x hx ↦ ⟨hlower x hx, hupper x hx⟩

end PDE.Elliptic.BoundaryLayer.Variable
