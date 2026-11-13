/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.OneDimensional.BoundaryLayer.Variable.Comparison
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# Constructing the two-point solution from continuous coefficients

An integrating factor produces a particular solution and a strictly positive
shooting denominator. Clamping extends interval coefficients continuously, so
no global regularity or assumed solution is needed. Nonnegative drift gives
uniqueness on the interval; a positive lower bound gives exponential localization.
-/

@[expose] public section

noncomputable section

namespace PDE.Elliptic.BoundaryLayer.Variable

open Set

/-- Continuous coefficients admit a classical solution on every finite interval, with both
Dirichlet traces enforced by a strictly positive shooting denominator. -/
theorem exists_solution_continuous {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (a f : ℝ → ℝ) (ha : Continuous a) (hf : Continuous f) (A B : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = A ∧ u L = B ∧
      ∀ x : ℝ, ε * deriv (deriv u) x + a x * deriv u x = f x := by
  have hC1 {φ φ' : ℝ → ℝ} (h : ∀ x, HasDerivAt φ (φ' x) x) (hc : Continuous φ') :
      ContDiff ℝ 1 φ :=
    contDiff_one_iff_deriv.mpr ⟨fun x ↦ (h x).differentiableAt, by
      rw [funext fun x ↦ (h x).deriv]; exact hc⟩
  let S : ℝ → ℝ := fun x ↦ ∫ t in 0..x, a t
  have hS (x : ℝ) : HasDerivAt S (a x) x := (ha.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hSc : Continuous S := Differentiable.continuous (fun x ↦ (hS x).differentiableAt)
  let k : ℝ → ℝ := fun x ↦ Real.exp (-S x / ε)
  have hk (x : ℝ) : HasDerivAt k ((-a x / ε) * k x) x :=
    (((hS x).neg.div_const ε).exp).congr_deriv (mul_comm _ _)
  have hkc : Continuous k := Differentiable.continuous (fun x ↦ (hk x).differentiableAt)
  have hkpos (x : ℝ) : 0 < k x := Real.exp_pos _
  let g : ℝ → ℝ := fun x ↦ Real.exp (S x / ε) * f x / ε
  have hgc : Continuous g := by fun_prop
  let J : ℝ → ℝ := fun x ↦ ∫ t in 0..x, g t
  have hJ (x : ℝ) : HasDerivAt J (g x) x := (hgc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hJc : Continuous J := Differentiable.continuous (fun x ↦ (hJ x).differentiableAt)
  have hcancel (x : ℝ) : k x * Real.exp (S x / ε) = 1 := by
    rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
  let p : ℝ → ℝ := fun x ↦ k x * J x
  have hpc : Continuous p := hkc.mul hJc
  have hp (x : ℝ) : HasDerivAt p ((-a x / ε) * p x + f x / ε) x := by
    convert (hk x).mul (hJ x) using 1
    linear_combination -(f x / ε) * hcancel x
  let I : ℝ → ℝ := fun x ↦ ∫ t in 0..x, k t
  let P : ℝ → ℝ := fun x ↦ ∫ t in 0..x, p t
  have hIpos : 0 < I L := intervalIntegral.integral_pos hL hkc.continuousOn
    (fun x _ ↦ (hkpos x).le) ⟨0, ⟨le_rfl, hL.le⟩, hkpos 0⟩
  let c : ℝ := (B - A - P L) / I L
  let u : ℝ → ℝ := fun x ↦ A + P x + c * I x
  have hu (x : ℝ) : HasDerivAt u (p x + c * k x) x :=
    (((hpc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add A).add
      (((hkc.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul c)
  have hueq : deriv u = fun x ↦ p x + c * k x := funext fun x ↦ (hu x).deriv
  have hu₂ : ContDiff ℝ 2 u := by
    refine (contDiff_succ_iff_deriv (n := 1)).mpr ⟨fun x ↦ (hu x).differentiableAt, by norm_num,
      ?_⟩
    rw [hueq]
    exact (hC1 hp (by fun_prop)).add ((hC1 hk (by fun_prop)).const_smul c)
  refine ⟨u, hu₂, by simp [u, P, I], ?_, fun x ↦ ?_⟩
  · dsimp [u, c]
    rw [div_mul_cancel₀ _ hIpos.ne']
    ring
  · have hd₂ : HasDerivAt (deriv u)
        ((-a x / ε) * p x + f x / ε + c * ((-a x / ε) * k x)) x := by
      rw [hueq]
      exact (hp x).add ((hk x).const_mul c)
    rw [hd₂.deriv, (hu x).deriv]
    have hid (b q r d : ℝ) :
        ε * ((-b / ε) * q + d / ε + c * ((-b / ε) * r)) + b * (q + c * r) = d := by
      cas using hε.ne'
    exact hid _ _ _ _

/-- Coefficients need only be continuous on the closed interval. Clamping constructs an
C² extension of a solution, without assuming any initial-value continuation theorem. -/
theorem exists_solution_continuousOn {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (a f : ℝ → ℝ) (ha : ContinuousOn a (Icc 0 L)) (hf : ContinuousOn f (Icc 0 L))
    (A B : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = A ∧ u L = B ∧
      ∀ x ∈ Icc 0 L, ε * deriv (deriv u) x + a x * deriv u x = f x := by
  let ae : ℝ → ℝ := IccExtend hL.le (fun x : Icc 0 L ↦ a x)
  let fe : ℝ → ℝ := IccExtend hL.le (fun x : Icc 0 L ↦ f x)
  have hae : Continuous ae := ha.domRestrict.Icc_extend'
  have hfe : Continuous fe := hf.domRestrict.Icc_extend'
  obtain ⟨u, hu, hzero, hend, hop⟩ :=
    exists_solution_continuous hL hε ae fe hae hfe A B
  refine ⟨u, hu, hzero, hend, fun x hx ↦ ?_⟩
  have haeq : ae x = a x := IccExtend_of_mem hL.le _ hx
  have hfeq : fe x = f x := IccExtend_of_mem hL.le _ hx
  simpa only [haeq, hfeq] using hop x

/-- Raw continuous interval coefficients with nonnegative drift yield existence and interval
uniqueness among all classical solutions continuous up to the endpoints. -/
theorem exists_unique_solution {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (a f : ℝ → ℝ) (ha : ContinuousOn a (Icc 0 L)) (hf : ContinuousOn f (Icc 0 L))
    (ha₀ : ∀ x ∈ Ioo 0 L, 0 ≤ a x) (A B : ℝ) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ u 0 = A ∧ u L = B ∧
      (∀ x ∈ Icc 0 L, ε * deriv (deriv u) x + a x * deriv u x = f x) ∧
      ∀ v : ℝ → ℝ, ContinuousOn v (Icc 0 L) →
        (∀ x ∈ Ioo 0 L, ContDiffAt ℝ 2 v x) → v 0 = A → v L = B →
        (∀ x ∈ Ioo 0 L, ε * deriv (deriv v) x + a x * deriv v x = f x) →
        EqOn v u (Icc 0 L) := by
  obtain ⟨u, hu, hzero, hend, hop⟩ :=
    exists_solution_continuousOn hL hε a f ha hf A B
  refine ⟨u, hu, hzero, hend, hop, fun v hv hv₂ hvzero hvend hvop ↦ ?_⟩
  exact scalar_uniqueness hL hε a ha₀ hv
    hu.continuous.continuousOn hv₂ (fun _ _ ↦ hu.contDiffAt)
    (fun x hx ↦ (hvop x hx).trans (hop x (Ioo_subset_Icc_self hx)).symm)
    (hvzero.trans hzero.symm) (hvend.trans hend.symm)

/-- The exponential localization estimate applies to a constructed homogeneous solution,
using only continuity and the positive lower bound on the drift. -/
theorem exists_localized_layer {L ε α : ℝ} (hL : 0 < L) (hε : 0 < ε) (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContinuousOn a (Icc 0 L))
    (hlower : ∀ x ∈ Ioo 0 L, α ≤ a x) :
    ∃ H : ℝ → ℝ, ContDiff ℝ 2 H ∧ H 0 = 1 ∧ H L = 0 ∧
      (∀ x ∈ Icc 0 L, ε * deriv (deriv H) x + a x * deriv H x = 0) ∧
      ∀ x ∈ Icc 0 L, 0 ≤ H x ∧ H x ≤ Real.exp (-α * x / ε) := by
  obtain ⟨H, hH, hzero, hend, hop⟩ :=
    exists_solution_continuousOn hL hε a (fun _ ↦ 0)
      ha continuousOn_const 1 0
  exact ⟨H, hH, hzero, hend, hop,
    homogeneous_bound hL hε hα a hlower
      hH.continuous.continuousOn (fun _ _ ↦ hH.contDiffAt)
      (fun x hx ↦ hop x (Ioo_subset_Icc_self hx)) hzero hend⟩

end PDE.Elliptic.BoundaryLayer.Variable
