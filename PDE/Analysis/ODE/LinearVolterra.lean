/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.PicardLindelof
import PDE.Analysis.ODE.Volterra
import CAS.IntegrationTactic

/-!
# Linear Volterra iteration on continuous curves

For a continuous coefficient in a real Banach algebra, the zero-initial-data Picard
map is linear on continuous curves. Its powers are the time-ordered integrals.
On a bounded time interval, their norms have the usual factorial bound.

When this linear map is nilpotent, repeated substitution stops after finitely
many terms. Multiplying the finite geometric sum gives an exact expansion of
the solution. The nilpotence hypothesis is the algebraic reason that no
infinite series is needed.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

noncomputable section

open _root_.ODE

namespace PDE.Analysis.ODE

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The linear part of Picard iteration, with base time zero. Its powers represent
ordered integrals of the coefficient acting by left multiplication. -/
def volterraLinearMap (K : C(ℝ, A)) : Module.End ℝ C(ℝ, A) where
  toFun f :=
    ⟨picard (fun t x ↦ K t * x) 0 0 f, by
      unfold picard
      simpa only [zero_add, Pi.mul_apply] using
        (intervalIntegral.differentiable_integral_of_continuous (a := 0)
          (K.continuous.mul f.continuous)).continuous⟩
  map_add' f g := by
    ext t
    change (0 : A) + (∫ s in 0..t, K s * (f s + g s)) =
      (0 + ∫ s in 0..t, K s * f s) + (0 + ∫ s in 0..t, K s * g s)
    simp only [zero_add, mul_add]
    cas
  map_smul' r f := by
    ext t
    change (0 : A) + (∫ s in 0..t, K s * (r • f s)) =
      r • ((0 : A) + ∫ s in 0..t, K s * f s)
    simp only [zero_add, mul_smul_comm, intervalIntegral.integral_smul]

/-- The bundled linear map uses exactly the usual interval integral. -/
theorem volterraLinearMap_apply (K f : C(ℝ, A)) (t : ℝ) :
    volterraLinearMap K f t = ∫ s in 0..t, K s * f s := by
  change (0 : A) + (∫ s in 0..t, K s * f s) =
    ∫ s in 0..t, K s * f s
  exact zero_add _

/-- Each additional power adds the next outer time integral. -/
theorem volterraLinearMap_pow_succ_apply (K f : C(ℝ, A)) (k : ℕ) (t : ℝ) :
    (volterraLinearMap K ^ (k + 1)) f t =
      ∫ s in 0..t, K s * (volterraLinearMap K ^ k) f s := by
  rw [pow_succ', Module.End.mul_apply, volterraLinearMap_apply]

/-- A uniform coefficient bound gives the factorial estimate for each ordered
integral. Only the interval from zero to the evaluation time is used. -/
theorem norm_volterraLinearMap_pow_apply_le
    (K f : C(ℝ, A)) {B C t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hK : ∀ s ∈ Icc 0 t, ‖K s‖ ≤ B)
    (hf : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ C) (k : ℕ) :
    ‖(volterraLinearMap K ^ k) f t‖ ≤ C * B ^ k * t ^ k / k.factorial := by
  classical
  let R (h : C(ℝ, A)) : C(Icc 0 t, A) := h.restrict (Icc 0 t)
  let P : C(Icc 0 t, A) → C(Icc 0 t, A) := fun u ↦
    ⟨fun s ↦ ∫ r in 0..s.1,
        K r * Set.IccExtend ht u r,
      (intervalIntegral.differentiable_integral_of_continuous
        (K.continuous.mul
          (u.continuous.Icc_extend' (h := ht)))).continuous.comp
        continuous_subtype_val⟩
  let g (u : C(Icc 0 t, A)) : ℝ → A :=
    fun r ↦ K r * Set.IccExtend ht u r
  have hg (u : C(Icc 0 t, A)) : IntegrableOn (g u) (Icc 0 t) volume :=
    (K.continuous.mul
      (u.continuous.Icc_extend' (h := ht))).integrableOn_Icc
  have hP (u : C(Icc 0 t, A)) (s : Icc 0 t) :
      P u s = (0 : A) + ∫ r in 0..s.1, g u r :=
    (zero_add _).symm
  have hLip (u v : C(Icc 0 t, A)) (s : Icc 0 t) :
      ‖g u s - g v s‖ ≤ B * dist (u s) (v s) := by
    dsimp only [g]
    rw [Set.IccExtend_of_mem ht u s.2,
      Set.IccExtend_of_mem ht v s.2,
      ← mul_sub, dist_eq_norm]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hK s s.2) (norm_nonneg _))
  -- Restriction commutes with the integral operator and hence with all its iterates.
  have hR (h : C(ℝ, A)) : R (volterraLinearMap K h) = P (R h) := by
    ext s
    change volterraLinearMap K h s.1 = ∫ r in 0..s.1,
      K r * Set.IccExtend ht (R h) r
    rw [volterraLinearMap_apply]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrI : r ∈ Icc 0 t := Set.uIcc_subset_Icc ⟨le_rfl, ht⟩ s.2 hr
    change K r * h r =
      K r * Set.IccExtend ht (R h) r
    rw [Set.IccExtend_of_mem ht (R h) hrI]
    rfl
  have hiter (n : ℕ) (h : C(ℝ, A)) :
      R ((volterraLinearMap K ^ n) h) = (P^[n]) (R h) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, hR, ih, Function.iterate_succ_apply']
  have h := PDE.Analysis.ODE.dist_iterate_volterra_apply_le
    ⟨0, le_rfl, ht⟩ P g 0 ⟨B, hB⟩ hg hP hLip (R f) (R 0) k ⟨t, ht, le_rfl⟩
  rw [← hiter k f, ← hiter k 0] at h
  have hpoint : ‖(volterraLinearMap K ^ k) f t‖ ≤
      ((B * t) ^ k / k.factorial) * dist (R f) (R 0) := by
    change dist ((volterraLinearMap K ^ k) f t)
      ((volterraLinearMap K ^ k) (0 : C(ℝ, A)) t) ≤
        ((B * |t - 0|) ^ k / k.factorial) * dist (R f) (R 0) at h
    simpa only [map_zero, ContinuousMap.zero_apply, dist_zero_right,
      sub_zero, abs_of_nonneg ht] using h
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hf 0 ⟨le_rfl, ht⟩)
  have hinit : dist (R f) (R 0) ≤ C := by
    apply (ContinuousMap.dist_le hC).2
    intro s
    change dist (f s) (0 : A) ≤ C
    simpa only [dist_zero_right] using hf s s.2
  calc
    ‖(volterraLinearMap K ^ k) f t‖ ≤
        ((B * t) ^ k / k.factorial) * dist (R f) (R 0) := hpoint
    _ ≤ ((B * t) ^ k / k.factorial) * C :=
      mul_le_mul_of_nonneg_left hinit (by positivity)
    _ = C * B ^ k * t ^ k / k.factorial := by
      rw [mul_pow]
      ring

/-- When the Volterra map is nilpotent, its fixed-point equation has a finite
time-ordered expansion. The constant term may be any continuous inhomogeneity. -/
theorem eq_sum_volterraLinearMap_pow_of_eq_add
    (K f g : C(ℝ, A)) (m : ℕ) (hnil : volterraLinearMap K ^ m = 0)
    (hf : f = g + volterraLinearMap K f) :
    f = ∑ k ∈ Finset.range m, (volterraLinearMap K ^ k) g := by
  let L := volterraLinearMap K
  have hg : (1 - L) f = g := by
    change f - L f = g
    exact sub_eq_iff_eq_add.mpr hf
  have hgeom := congrArg (fun P : Module.End ℝ C(ℝ, A) ↦ P f)
    (geom_sum_mul_neg L m)
  rw [Module.End.mul_apply, hg, hnil] at hgeom
  change (∑ i ∈ Finset.range m, L ^ i) g = f - (0 : C(ℝ, A)) at hgeom
  rw [sub_zero] at hgeom
  simpa only [LinearMap.sum_apply] using hgeom.symm

/-- The fundamental theorem of calculus supplies the integral equation from a
derivative. This lemma requires neither a preassigned integral identity nor
any existence theorem for differential equations. -/
theorem eq_const_add_volterraLinearMap_of_hasDerivAt
    (K f : C(ℝ, A)) (hf : ∀ t, HasDerivAt f (K t * f t) t) :
    f = ContinuousMap.const ℝ (f 0) + volterraLinearMap K f := by
  ext t
  have hFTC : (∫ s in 0..t, K s * f s) = f t - f 0 := by cas
  change f t = f 0 + volterraLinearMap K f t
  rw [volterraLinearMap_apply, hFTC]
  abel

end PDE.Analysis.ODE
