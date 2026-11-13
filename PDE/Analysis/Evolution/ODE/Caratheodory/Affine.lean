/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import PDE.Analysis.Evolution.ODE.Caratheodory.Picard
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import PDE.Analysis.Evolution.Core.Gronwall
import PDE.Analysis.Evolution.Time.FundamentalTheorem

/-!
# Affine Carathéodory solutions

`AffineCaratheodorySolutionOn A f a b x₀` is an absolutely continuous solution of
`u' = A(t) u + f(t)`, `u(a) = x₀`, with the equation holding for almost every
`t ∈ (a, b]`. For strongly measurable `A` with `‖A(t)‖ ≤ M_A` and integrable `f`,
the fixed point of the affine Picard map is such a solution on every finite
interval. Any two solutions agree on `[a, b]`, by Grönwall's inequality for
`‖u - w‖`. For bounded or `L²` forcing, the right-hand
side `A(t) u(t) + f(t)` lies in `L²(a, b)`.

In the proof of Evans, §7.1.2, Theorem 1, the Galerkin coefficients solve the linear system
(19), whose coefficients `e^{kl}(t) = B[w_l, w_k; t]` are bounded and measurable, and Evans
quotes standard existence theory for a unique absolutely continuous solution satisfying (19)
for almost every `t`. `AffineCaratheodorySolutionOn.exists` and
`AffineCaratheodorySolutionOn.trajectory_eq` give this existence and uniqueness in any Banach
space.

## Main definitions

* `AffineCaratheodorySolutionOn A f a b x₀`: an absolutely continuous solution of
  `u' = A(t) u + f(t)`, `u(a) = x₀`, with the equation holding almost everywhere on `(a, b]`.

## Main results

* `AffineCaratheodorySolutionOn.exists`: existence on every finite interval.
* `AffineCaratheodorySolutionOn.trajectory_eq`: two solutions agree on `[a, b]`.
* `AffineCaratheodorySolutionOn.rhsMemLp_of_memLp`, `AffineCaratheodorySolutionOn.rhsMemLp`:
  the right-hand side lies in `L²(a, b)` for `L²` or bounded forcing.
* `AffineCaratheodorySolutionOn.hasDerivAt_comp_ae`: the image of a solution under a bounded
  linear map has the projected derivative almost everywhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 1 (Construction of approximate
  solutions) and its proof, (17)-(19), p. 376. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval Filter Function MeasureTheory Set PDE.Analysis.ODE
open scoped Topology

namespace PDE.Analysis.Evolution

section MeasurableAffinePicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/--
A Carathéodory solution of the affine system

`u'(t) = A(t)u(t) + f(t),  u(a) = x₀`

on `[a,b]`: an absolutely continuous function with
`u'(t) = A(t)u(t) + f(t)` for almost every `t ∈ (a, b]`. Its values outside
`[a, b]` are unconstrained.
-/
structure AffineCaratheodorySolutionOn
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (a b : ℝ) (x₀ : E) where
  /-- The pointwise representative of the solution. -/
  trajectory : ℝ → E
  /-- The prescribed initial value. -/
  initial_value : trajectory a = x₀
  /-- Carathéodory trajectories are absolutely continuous in time. -/
  absolutely_continuous :
    AbsolutelyContinuousOnInterval trajectory a b
  /-- The affine differential equation holds for almost every `t ∈ (a, b]`. -/
  equation_ae :
    ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt trajectory (A t (trajectory t) + f t) t

/--
Global Carathéodory existence for an affine system with bounded measurable
operator coefficient and integrable forcing on an arbitrary finite interval.

A high iterate of the Picard map is a contraction on the whole interval, so
`b - a` may be arbitrary. The forcing need only be Bochner integrable.
-/
theorem AffineCaratheodorySolutionOn.exists
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) :
    Nonempty (AffineCaratheodorySolutionOn A f a b x₀) := by
  obtain ⟨u, hu, _hunique⟩ := existsUnique_isFixedPt_affinePicardMap hab A f hA hf MA hA_bound x₀
  let g : ℝ → E := affineIntegrandOn hab A f u
  have hg : Integrable g volume := integrable_affineIntegrandOn hab hA hf MA hA_bound u
  let U : ℝ → E := fun t ↦ x₀ + ∫ s in a..t, g s
  have hUu (t : Set.Icc a b) : U t.1 = u t := by
    simpa only [U, g, affinePicardMap_apply] using congrArg (fun w : C(Set.Icc a b, E) ↦ w t) hu
  have hUac : AbsolutelyContinuousOnInterval U a b :=
    ((LipschitzWith.const x₀).lipschitzOnWith.absolutelyContinuousOnInterval.add
      (IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normedSpace
        hg.intervalIntegrable Set.left_mem_uIcc)).congr fun _ _ ↦ rfl
  have hUderivOn : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), HasDerivAt U (A t (U t) + f t) t := by
    filter_upwards [ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral
      hg.locallyIntegrable), ae_restrict_mem measurableSet_Ioc] with t ht htIoc
    have htIcc : t ∈ Set.Icc a b := ⟨htIoc.1.le, htIoc.2⟩
    have hgt : g t = A t (U t) + f t := by
      change affineIntegrandOn hab A f u t = A t (U t) + f t
      rw [affineIntegrandOn, Set.indicator_of_mem htIcc, Set.IccExtend_of_mem hab u htIcc,
        hUu ⟨t, htIcc⟩]
    rw [← hgt]
    simpa only [U] using (ht a).const_add x₀
  exact ⟨{
    trajectory := U
    initial_value := by simp [U]
    absolutely_continuous := hUac
    equation_ae := hUderivOn
  }⟩

omit [CompleteSpace E] in
/-- Square-integrable forcing gives a square-integrable derivative.
The operator is bounded, and the continuous trajectory is bounded on the finite interval. -/
theorem AffineCaratheodorySolutionOn.rhsMemLp_of_memLp
    {a b : ℝ} (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {x₀ : E}
    (U : AffineCaratheodorySolutionOn A f a b x₀)
    (hA : AEStronglyMeasurable A (volume.restrict (Ioc a b)))
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (MA : NNReal) (hA_bound : ∀ t ∈ Icc a b, ‖A t‖ ≤ MA) :
    MemLp (fun t ↦ A t (U.trajectory t) + f t) 2
      (volume.restrict (Ioc a b)) := by
  have hUcont : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  have hUmeas : AEStronglyMeasurable U.trajectory (volume.restrict (Ioc a b)) :=
    (hUcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hmeas := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hA.prodMk hUmeas)
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hUcont
  have hAu : MemLp (fun t ↦ A t (U.trajectory t)) 2
      (volume.restrict (Ioc a b)) := by
    apply MemLp.of_bound hmeas ((MA : ℝ) * R)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ((A t).le_opNorm _).trans
      (mul_le_mul (hA_bound t (Ioc_subset_Icc_self ht))
        (hR t (Ioc_subset_Icc_self ht)) (norm_nonneg _) MA.2)
  exact hAu.add hf

/--
Uniqueness of affine Carathéodory solutions in a Banach space on their prescribed
interval.

The theorem applies to any two inhabitants of `AffineCaratheodorySolutionOn`.
Subtracting the two a.e. equations eliminates the forcing. The vector-valued
absolutely continuous FTC turns the result into

`w(t) = ∫ₐᵗ A(s)w(s) ds`,

and the scalar zero-data integral Grönwall lemma applied to `‖w(t)‖` proves
that `w` vanishes. Equality is asserted on `[a,b]`, since the solution
structure imposes no conditions outside that interval.
-/
theorem AffineCaratheodorySolutionOn.trajectory_eq
    {a b : ℝ} (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {x₀ : E}
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (U W : AffineCaratheodorySolutionOn A f a b x₀) :
    ∀ t ∈ Set.Icc a b, U.trajectory t = W.trajectory t := by
  let w : ℝ → E := fun t ↦ U.trajectory t - W.trajectory t
  have hwAC : AbsolutelyContinuousOnInterval w a b :=
    (U.absolutely_continuous.sub W.absolutely_continuous).congr fun _ _ ↦ rfl
  have hwContinuous : ContinuousOn w (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab] using hwAC.continuousOn
  have hgIntegrable : IntegrableOn (fun s ↦ A s (w s)) (Set.Icc a b) volume :=
    integrableOn_operator_apply_continuousOn hab hA MA hA_bound hwContinuous
  have hwDerivative : ∀ᵐ s ∂volume.restrict (Set.Ioc a b), HasDerivAt w (A s (w s)) s := by
    filter_upwards [U.equation_ae, W.equation_ae] with s hU hW
    exact (hU.fun_sub hW).congr_deriv (by simp only [w, map_sub]; abel)
  have hwInitial : w a = 0 := by simp only [w, U.initial_value, W.initial_value, sub_self]
  have heIntegral (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ‖w t‖ ≤ (MA : ℝ) * ∫ s in a..t, ‖w s‖ := by
    have hIcc : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc_right ht.2
    have hwIntegral : w t = ∫ s in a..t, A s (w s) := by
      rw [AbsolutelyContinuousOnInterval.intervalIntegral_eq_sub_of_ae_hasDerivAt_normedSpace ht.1
        (hwAC.mono (Set.uIcc_subset_uIcc_left (by simpa only [Set.uIcc_of_le hab] using ht)))
        (hgIntegrable.mono_set hIcc)
        (ae_restrict_of_ae_restrict_of_subset (Set.Ioc_subset_Ioc_right ht.2) hwDerivative),
        hwInitial, sub_zero]
    rw [hwIntegral, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.norm_integral_le_of_norm_le ht.1
      (.of_forall fun s hs ↦ (A s).le_of_opNorm_le (hA_bound s (hIcc (Ioc_subset_Icc_self hs))) _)
      (((hwContinuous.norm.mono hIcc).intervalIntegrable_of_Icc ht.1).const_mul _)
  intro t ht
  exact sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_on_of_nonneg_le_mul_intervalIntegral hab
    hwContinuous.norm (fun _ _ ↦ norm_nonneg _) heIntegral t ht))

omit [CompleteSpace E] in
/--
The affine right-hand side of a bounded Carathéodory system is Bochner
`L²` on every finite solution interval.

The hypotheses are strong measurability of `A` and `f` with `‖A(t)‖ ≤ M_A` and
`‖f(t)‖ ≤ M_f` on `[a, b]`. The trajectory is continuous, hence bounded, on
`[a, b]`.
-/
theorem AffineCaratheodorySolutionOn.rhsMemLp
    {a b : ℝ} (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {x₀ : E}
    (U : AffineCaratheodorySolutionOn A f a b x₀)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (MA Mf : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (hf_bound : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ Mf) :
    MemLp (fun t ↦ A t (U.trajectory t) + f t) 2
      (volume.restrict (Set.Ioc a b)) := by
  have hsub : volume.restrict (Ioc a b) ≤ volume.restrict (Icc a b) :=
    volume.restrict_mono_set Ioc_subset_Icc_self
  apply U.rhsMemLp_of_memLp hab (hA.mono_measure hsub) _ MA hA_bound
  apply MemLp.of_bound (hf.mono_measure hsub) (Mf : ℝ)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hf_bound t (Ioc_subset_Icc_self ht)

end MeasurableAffinePicard

end PDE.Analysis.Evolution

namespace PDE.Analysis.Evolution

/-- Projecting a Carathéodory trajectory through a bounded linear map differentiates
the trajectory almost everywhere. -/
theorem AffineCaratheodorySolutionOn.hasDerivAt_comp_ae
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {a b : ℝ} {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {u₀ : E}
    (U : AffineCaratheodorySolutionOn A f a b u₀) (P : E →L[ℝ] G) :
    ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (fun s ↦ P (U.trajectory s))
        (P (A t (U.trajectory t)) + P (f t)) t := by
  filter_upwards [U.equation_ae] with t ht
  simpa only [map_add, Function.comp_def] using P.hasFDerivAt.comp_hasDerivAt t ht

end PDE.Analysis.Evolution
