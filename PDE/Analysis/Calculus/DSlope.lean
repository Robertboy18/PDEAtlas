/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AveragedFDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth divided slopes

Mathlib's divided slope is the average derivative applied to the unit direction.
This identity gives smoothness through the coincident endpoints, jointly with
any parameters. Division by the linear increment loses one derivative.

At a coincident pair of endpoints, differentiating the divided slope gives half
of the second derivative. Iteration and equality of germs retain the same
regularity, ready for exact factorizations by powers of the displacement.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis

universe u v

variable {P : Type u} {E : Type v} {G : Type (max u v)}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A real divided slope is the average derivative applied to the unit direction. -/
theorem dslope_eq_averagedFDeriv
    {f : ℝ → E} (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    dslope f a b = averagedFDeriv f a b 1 := by
  rcases eq_or_ne b a with rfl | hne
  · simp only [dslope_same, averagedFDeriv_self, fderiv_apply_one_eq_deriv]
  · rw [dslope_of_ne _ hne, slope_def_module]
    apply (inv_smul_eq_iff₀ (sub_ne_zero.mpr hne)).2
    calc
      f b - f a = averagedFDeriv f a b (b - a) :=
        (averagedFDeriv_apply_sub hf a b).symm
      _ = (b - a) • averagedFDeriv f a b 1 := by
        rw [← map_smul, smul_eq_mul, mul_one]

/-- Division by a linear increment loses one derivative, including at its base point.
The regularity order can be finite or infinite. -/
theorem contDiff_dslope
    {n : ℕ∞} {f : ℝ → E} (hf : ContDiff ℝ ((n : ℕ∞ω) + 1) f) (a : ℝ) :
    ContDiff ℝ n (dslope f a) := by
  have heq : dslope f a = fun b ↦ averagedFDeriv f a b 1 :=
    funext (dslope_eq_averagedFDeriv hf.one_of_succ a)
  rw [heq]
  exact (contDiff_averagedFDeriv hf a).clm_apply contDiff_const

/-- On a parameter slice, the scalar divided slope uses the unit direction of the
last coordinate of the full derivative. -/
theorem dslope_slice_eq_averagedFDeriv
    {F : P × ℝ → G} (hF : ContDiff ℝ 1 F) (p : P) (a b : ℝ) :
    dslope (fun s ↦ F (p, s)) a b =
      averagedFDeriv F (p, a) (p, b) (0, 1) := by
  by_cases hne : b = a
  · subst b
    rw [dslope_same, averagedFDeriv_self]
    exact (((hF.differentiable one_ne_zero) (p, a)).hasFDerivAt.comp_hasDerivAt a
      ((hasDerivAt_const a p).prodMk (hasDerivAt_id a))).deriv
  · rw [dslope_of_ne _ hne, slope_def_module]
    apply (inv_smul_eq_iff₀ (sub_ne_zero.mpr hne)).2
    calc
      F (p, b) - F (p, a) =
          averagedFDeriv F (p, a) (p, b) ((p, b) - (p, a)) :=
        (averagedFDeriv_apply_sub hF (p, a) (p, b)).symm
      _ = averagedFDeriv F (p, a) (p, b) ((b - a) • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = (b - a) • averagedFDeriv F (p, a) (p, b) (0, 1) := map_smul _ _ _

/-- Divided slopes are jointly `C^n` in parameters and both scalar endpoints
when the original map is jointly `C^(n+1)`. No finite-dimensionality of the parameter
space is needed. -/
theorem contDiff_dslope_joint
    {n : ℕ∞} {F : P × ℝ → G} (hF : ContDiff ℝ ((n : ℕ∞ω) + 1) F) :
    ContDiff ℝ n (fun q : P × (ℝ × ℝ) ↦
      dslope (fun s ↦ F (q.1, s)) q.2.1 q.2.2) := by
  have heq : (fun q : P × (ℝ × ℝ) ↦
      dslope (fun s ↦ F (q.1, s)) q.2.1 q.2.2) =
      fun q ↦ averagedFDeriv F (q.1, q.2.1) (q.1, q.2.2) (0, 1) :=
    funext fun q ↦ dslope_slice_eq_averagedFDeriv hF.one_of_succ q.1 q.2.1 q.2.2
  rw [heq]
  exact ((contDiff_averagedFDeriv_joint hF).comp
    ((contDiff_fst.prodMk contDiff_snd.fst).prodMk
      (contDiff_fst.prodMk contDiff_snd.snd))).clm_apply contDiff_const

/-- The divided-slope operation preserves joint parameter regularity at a fixed
scalar base point, with a loss of one derivative. -/
theorem contDiff_dslope_snd
    {n : ℕ∞} {F : P × ℝ → G} (hF : ContDiff ℝ ((n : ℕ∞ω) + 1) F) (a : ℝ) :
    ContDiff ℝ n (fun q : P × ℝ ↦ dslope (fun s ↦ F (q.1, s)) a q.2) := by
  exact (contDiff_dslope_joint hF).comp
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd))

/-- The derivative of a divided slope at its base point is half the second
ordinary derivative of the original function. -/
theorem deriv_dslope_same
    {f : ℝ → E} (hf : ContDiff ℝ 2 f) (a : ℝ) :
    deriv (dslope f a) a = (1 / 2 : ℝ) • deriv (deriv f) a := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right le_rfl
  have heval : HasDerivAt (deriv f)
      (fderiv ℝ (fderiv ℝ f) a 1 1) a := by
    simpa only [fderiv_apply_one_eq_deriv, map_zero, add_zero] using
      ((hD.differentiable one_ne_zero) a).hasDerivAt.clm_apply
        (hasDerivAt_const a (1 : ℝ))
  have havg : HasDerivAt (fun b ↦ averagedFDeriv f a b 1)
      ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) a 1 1) a := by
    simpa only [smul_apply, map_zero, add_zero] using
      (hasFDerivAt_averagedFDeriv_self hf a).hasDerivAt.clm_apply
        (hasDerivAt_const a (1 : ℝ))
  have heq : dslope f a = fun b ↦ averagedFDeriv f a b 1 :=
    funext (dslope_eq_averagedFDeriv (hf.of_le (by norm_num)) a)
  rw [heq, havg.deriv, heval.deriv]

/-- Any fixed number of divided slopes of a smooth function is smooth. -/
theorem contDiff_iterate_dslope
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (a : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ ((Function.swap dslope a)^[k] f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_dslope (n := ⊤) (by simpa using ih) a

/-- Iteration of divided slopes preserves joint smoothness of a parameter family. -/
theorem contDiff_iterate_dslope_snd
    {F : P × ℝ → G} (hF : ContDiff ℝ ∞ F) (a : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (fun q : P × ℝ ↦
      (Function.swap dslope a)^[k] (fun s ↦ F (q.1, s)) q.2) := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
    have hnext := contDiff_dslope_snd (n := ⊤)
      (F := fun q : P × ℝ ↦
        (Function.swap dslope a)^[k] (fun s ↦ F (q.1, s)) q.2)
      (by simpa using ih) a
    simpa only [Function.iterate_succ_apply', Function.swap] using hnext

omit [CompleteSpace E] in
/-- The divided slope at a fixed point depends only on the germ there,
including its derivative value at that point. -/
theorem dslope_eventuallyEq_of_eventuallyEq
    {f g : ℝ → E} {a : ℝ} (hfg : f =ᶠ[𝓝 a] g) :
    dslope f a =ᶠ[𝓝 a] dslope g a := by
  have hbase := hfg.self_of_nhds
  have hderiv := hfg.deriv_eq
  filter_upwards [hfg] with b hb
  rcases eq_or_ne b a with rfl | hne
  · simp only [dslope_same, hderiv]
  · simp only [dslope_of_ne _ hne, slope_def_module, hb, hbase]

omit [CompleteSpace E] in
/-- Iterating divided slopes also depends only on the germ at their base point. -/
theorem iterate_dslope_eventuallyEq_of_eventuallyEq
    {f g : ℝ → E} {a : ℝ} (hfg : f =ᶠ[𝓝 a] g) (k : ℕ) :
    (Function.swap dslope a)^[k] f =ᶠ[𝓝 a] (Function.swap dslope a)^[k] g := by
  induction k with
  | zero => simpa using hfg
  | succ k ih =>
    simpa only [Function.iterate_succ_apply', Function.swap] using
      dslope_eventuallyEq_of_eventuallyEq ih

end PDE.Analysis
