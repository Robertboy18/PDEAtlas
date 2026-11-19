/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Pointwise bounds under weak Bochner Lp convergence

For any exponent `1 ≤ p ≤ ∞`, almost-everywhere norm bounds with a radius
varying over the measure space define a strongly closed convex subset of Lp.
Equality of the strong and weak closures of convex sets gives the same
pointwise envelope at a weak limit. No finite-measure, completeness, or
Hilbert-space hypothesis is needed.

Strong closedness uses an almost-everywhere convergent subsequence of a
strongly convergent sequence. The radius need not be measurable.
For `p = ∞`, weak convergence means the topology defined by the full dual.

A common Lp envelope also bounds the norm of an arbitrary family. The final
L²-input lemma converts an exponential energy envelope on a finite interval
into an explicit L-infinity bound.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

section BoundedFamily

variable {α E G : Type*} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedAddCommGroup E] [NormedAddCommGroup G]

/-- A common Lp envelope bounds the Bochner classes of an arbitrary family.
The envelope may take values in a different normed group, and the measure
need not be finite. -/
theorem isBounded_range_toLp_of_memLp_envelope
    {ι : Type*} (f : ι → α → E) (hf : ∀ i, MemLp (f i) p μ)
    (g : α → G) (hg : MemLp g p μ)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ ‖g x‖) :
    Bornology.IsBounded (range fun i ↦ (hf i).toLp (f i)) := by
  refine isBounded_iff_forall_norm_le.2
    ⟨‖hg.toLp g‖, forall_mem_range.2 fun i ↦ ?_⟩
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(hf i).coeFn_toLp, hg.coeFn_toLp, hbound i] with x hfx hgx hx
  simpa only [hfx, hgx] using hx

end BoundedFamily

section StrongClosure

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedAddCommGroup E]

/-- A point-dependent almost-everywhere norm bound defines a strongly closed
subset of Bochner Lp. The radius may be any real-valued function. -/
theorem isClosed_setOf_ae_norm_le (radius : α → ℝ) :
    IsClosed {u : Lp E p μ | ∀ᵐ x ∂μ, ‖u x‖ ≤ radius x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro u uLimit hu hlimit
  obtain ⟨ns, _, hpointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlimit).exists_seq_tendsto_ae
  have hbound : ∀ᵐ x ∂μ, ∀ k, ‖u (ns k) x‖ ≤ radius x :=
    ae_all_iff.2 fun k ↦ hu (ns k)
  filter_upwards [hpointwise, hbound] with x hx hbx
  exact le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hx)
    (Eventually.of_forall hbx)

end StrongClosure

section Convexity

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Point-dependent almost-everywhere norm bounds form a convex set. Negative
radii are allowed; where a bound is satisfied, the radius is nonnegative.
Convexity itself requires no lower bound on the exponent. -/
theorem convex_setOf_ae_norm_le (radius : α → ℝ) :
    Convex ℝ {u : Lp E p μ | ∀ᵐ x ∂μ, ‖u x‖ ≤ radius x} := by
  rw [convex_iff_add_mem]
  intro u hu v hv c d hc hd hcd
  filter_upwards
    [hu, hv, Lp.coeFn_add (c • u) (d • v), Lp.coeFn_smul c u, Lp.coeFn_smul d v]
    with x hux hvx hadd hcu hdv
  simp only [Pi.add_apply] at hadd
  simp only [Pi.smul_apply] at hcu hdv
  rw [hadd, hcu, hdv]
  calc
    ‖c • u x + d • v x‖ ≤ ‖c • u x‖ + ‖d • v x‖ := norm_add_le _ _
    _ = c * ‖u x‖ + d * ‖v x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd]
    _ ≤ c * radius x + d * radius x :=
      add_le_add (mul_le_mul_of_nonneg_left hux hc) (mul_le_mul_of_nonneg_left hvx hd)
    _ = radius x := by rw [← add_mul, hcd, one_mul]

end Convexity

section WeakClosure

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point-dependent almost-everywhere norm bound is weakly closed in
Bochner Lp, by equality of the strong and weak closures of a convex set. -/
theorem isClosed_toWeakSpace_image_setOf_ae_norm_le (radius : α → ℝ) :
    IsClosed ((toWeakSpace ℝ (Lp E p μ)) ''
      {u : Lp E p μ | ∀ᵐ x ∂μ, ‖u x‖ ≤ radius x}) := by
  have hclosed := isClosed_setOf_ae_norm_le (E := E) (μ := μ) (p := p) radius
  have hconvex := convex_setOf_ae_norm_le (E := E) (μ := μ) (p := p) radius
  rw [← hclosed.closure_eq, hconvex.toWeakSpace_closure ℝ]
  exact isClosed_closure

/-- A weak Bochner Lp limit inherits a fixed pointwise norm envelope. The
approximants need satisfy the bound only eventually along the weak-limit filter. -/
theorem ae_norm_le_of_tendsto_weak_Lp
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → Lp E p μ} {uLimit : Lp E p μ} (radius : α → ℝ)
    (hweak : Tendsto (fun i ↦ toWeakSpace ℝ (Lp E p μ) (u i)) l
      (𝓝 (toWeakSpace ℝ (Lp E p μ) uLimit)))
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖u i x‖ ≤ radius x) :
    ∀ᵐ x ∂μ, ‖uLimit x‖ ≤ radius x := by
  have heventually :
      ∀ᶠ i in l, toWeakSpace ℝ (Lp E p μ) (u i) ∈
        (toWeakSpace ℝ (Lp E p μ)) ''
          {v : Lp E p μ | ∀ᵐ x ∂μ, ‖v x‖ ≤ radius x} :=
    hbound.mono fun i hi ↦ ⟨u i, hi, rfl⟩
  obtain ⟨v, hv, heq⟩ :=
    (isClosed_toWeakSpace_image_setOf_ae_norm_le (p := p) radius).mem_of_tendsto
      hweak heventually
  have hvEq : v = uLimit := (toWeakSpace ℝ (Lp E p μ)).injective heq
  subst v
  exact hv

/-- Weak Bochner Lp convergence preserves the full pointwise squared-norm
energy envelope. Its nonnegativity follows from the approximating bounds;
it need not be assumed separately. -/
theorem ae_norm_sq_le_of_tendsto_weak_Lp
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → Lp E p μ} {uLimit : Lp E p μ} (energy : α → ℝ)
    (hweak : Tendsto (fun i ↦ toWeakSpace ℝ (Lp E p μ) (u i)) l
      (𝓝 (toWeakSpace ℝ (Lp E p μ) uLimit)))
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖u i x‖ ^ 2 ≤ energy x) :
    ∀ᵐ x ∂μ, ‖uLimit x‖ ^ 2 ≤ energy x := by
  have henergy : ∀ᵐ x ∂μ, 0 ≤ energy x := by
    obtain ⟨i, hi⟩ := hbound.exists
    exact hi.mono fun x hx ↦ (sq_nonneg ‖u i x‖).trans hx
  have hroot := ae_norm_le_of_tendsto_weak_Lp
    (fun x ↦ √(energy x)) hweak
    (hbound.mono fun i hi ↦ hi.mono fun x hx ↦ Real.le_sqrt_of_sq_le hx)
  filter_upwards [henergy, hroot] with x hEx hx
  exact (Real.le_sqrt (norm_nonneg _) hEx).mp hx

end WeakClosure

section EssentialBound

variable {E : Type*} [NormedAddCommGroup E] {a b : ℝ}

/-- An exponential squared-norm envelope gives both L-infinity membership
and its explicit essential-supremum bound on a finite time interval. -/
theorem memLp_top_and_eLpNorm_le_of_ae_norm_sq_le_exp
    (u : Lp E 2 (volume.restrict (Ioc a b))) {K c : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c)
    (henergy : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖u t‖ ^ 2 ≤ K * Real.exp (c * (t - a))) :
    MemLp (u : ℝ → E) ∞ (volume.restrict (Ioc a b)) ∧
      eLpNorm (u : ℝ → E) ∞ (volume.restrict (Ioc a b)) ≤
        ENNReal.ofReal (√(K * Real.exp (c * (b - a)))) := by
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖u t‖ ≤ √(K * Real.exp (c * (b - a))) := by
    filter_upwards [henergy, ae_restrict_mem measurableSet_Ioc] with t ht htab
    apply Real.le_sqrt_of_sq_le
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right htab.2 a) hc)) hK)
  refine ⟨memLp_top_of_bound (Lp.aestronglyMeasurable u) _ hbound, ?_⟩
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable u)]
  exact eLpNormEssSup_le_of_ae_bound hbound

end EssentialBound

end PDE.Analysis.Evolution
