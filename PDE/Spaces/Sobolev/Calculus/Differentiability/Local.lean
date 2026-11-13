/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PDE.Spaces.Sobolev.Calculus.Differentiability.FiniteExponent
public import PDE.Spaces.Sobolev.Inequalities.Morrey.LocalRepresentative

/-!
# Almost-everywhere differentiability of local Sobolev representatives

For every positive dimension and every `n < p ≤ ∞`, a locally `W¹ᵖ` function has
a continuous representative that is Fréchet differentiable almost everywhere. Its
classical gradient equals its weak gradient almost everywhere. This is Evans,
§5.8.3, Theorem 5.

The finite-exponent argument applies on interior balls. For `p = ∞`, finite measure allows reduction
to the exponent `n + 1`. A countable cover gives a single exceptional null set on the entire open
domain. Local integrability hypotheses are expressed by `Lᵖ` membership on compact subsets; global
boundedness and boundary regularity are not required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.3, Theorem 5, pp. 295-296: for `n < p ≤ ∞`, every
  `u ∈ W^{1,p}_loc(U)` is differentiable almost everywhere and its gradient equals its weak gradient
  almost everywhere; the proof uses Morrey's estimate (14) and Lebesgue's differentiation theorem.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Sobolev Gradient

namespace SobolevSpace

open GraphSpace

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞}
  {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} {g : ℝ^n → ℝ^n}

/-- The continuous representative of a locally supercritical Sobolev function is
Fréchet differentiable almost everywhere, with derivative given by its weak gradient.
This includes `p = ∞`, reduced locally to the finite exponent `n + 1`. -/
theorem ae_hasFDerivAt_of_continuousOn_locally_memLp_weakGradient
    (hp : (n : ℝ≥0∞) < p) (hΩ : IsOpen Ω) (hfc : ContinuousOn f Ω)
    (hf : ∀ K ⊆ Ω, IsCompact K → MemLp f p (volume.restrict K))
    (hg : ∀ K ⊆ Ω, IsCompact K → MemLp g p (volume.restrict K))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun x ↦ g x i)) :
    ∀ᵐ x ∂volume.restrict Ω, HasFDerivAt f (innerSL ℝ (g x)) x := by
  classical
  obtain ⟨q, hq, hq_top, hqp⟩ :
      ∃ q : ℝ≥0∞, (n : ℝ≥0∞) < q ∧ q ≠ ∞ ∧ q ≤ p := by
    by_cases htop : p = ∞
    · refine ⟨(n + 1 : ℕ), ?_, by simp, by simp [htop]⟩
      exact_mod_cast Nat.lt_succ_self n
    · exact ⟨p, hp, htop, le_rfl⟩
  have hqn : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast (Fact.out : 0 < n)
  have : Fact (1 ≤ q) := ⟨hqn.trans hq.le⟩
  have hlocal (x : Ω) : ∃ r : ℝ, 0 < r ∧ ball x.val r ⊆ Ω ∧
      ∀ᵐ y ∂volume.restrict (ball x.val r), HasFDerivAt f (innerSL ℝ (g y)) y := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hΩ x.val x.property
    have hr : 0 < δ / 2 := half_pos hδ
    have hclosed : closedBall x.val (δ / 2) ⊆ Ω :=
      (closedBall_subset_ball (half_lt_self hδ)).trans hsub
    have hball : ball x.val (δ / 2) ⊆ Ω := ball_subset_closedBall.trans hclosed
    have : IsFiniteMeasure (domainMeasure n (ball x.val (δ / 2))) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hfr : MemLp f q (domainMeasure n (ball x.val (δ / 2))) :=
      ((hf _ hclosed (isCompact_closedBall x.val _)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)).mono_exponent hqp
    have hgr : MemLp g q (domainMeasure n (ball x.val (δ / 2))) :=
      ((hg _ hclosed (isCompact_closedBall x.val _)).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)).mono_exponent hqp
    exact ⟨δ / 2, hr, hball,
      ae_hasFDerivAt_of_continuousOn_weakGradient hq hq_top isOpen_ball
        (hfc.mono hball) hfr hgr
        (fun i ↦ HasWeakDerivativeOn.mono measurableSet_ball hball (hweak i))⟩
  choose r hr hsub hgood using hlocal
  obtain ⟨c, hc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
      (fun x : Ω ↦ ball x.val (r x)) (fun _ ↦ isOpen_ball)
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hall : ∀ x ∈ c, ∀ᵐ y ∂volume,
      y ∈ ball x.val (r x) → HasFDerivAt f (innerSL ℝ (g y)) y :=
    fun x _ ↦ (ae_restrict_iff' measurableSet_ball).mp (hgood x)
  rw [ae_restrict_iff' hΩ.measurableSet]
  filter_upwards [ae_ball_iff hc |>.mpr hall] with y hy hyΩ
  obtain ⟨x, hxc, hyx⟩ := mem_iUnion₂.mp (hcover hyΩ)
  exact hy x hxc hyx

/-- A locally `W¹ᵖ` function with `p > n` has a continuous representative with the
specified weak gradient as its classical derivative almost everywhere. The same
representative realizes both conclusions. -/
theorem exists_continuousOn_ae_hasFDerivAt_of_locally_memLp_weakGradient
    (hp : (n : ℝ≥0∞) < p) (hΩ : IsOpen Ω)
    (hf : ∀ K ⊆ Ω, IsCompact K → MemLp f p (volume.restrict K))
    (hg : ∀ K ⊆ Ω, IsCompact K → MemLp g p (volume.restrict K))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun x ↦ g x i)) :
    ∃ F : ℝ^n → ℝ, ContinuousOn F Ω ∧ F =ᵐ[volume.restrict Ω] f ∧
      ∀ᵐ x ∂volume.restrict Ω, HasFDerivAt F (innerSL ℝ (g x)) x := by
  have hpn : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast (Fact.out : 0 < n)
  have : Fact (1 ≤ p) := ⟨hpn.trans hp.le⟩
  obtain ⟨F, hF, hrep⟩ :=
    exists_continuousOn_representative_of_locally_memLp_weakGradient hp hΩ hf hg hweak
  refine ⟨F, hF, hrep,
    ae_hasFDerivAt_of_continuousOn_locally_memLp_weakGradient hp hΩ hF ?_ hg ?_⟩
  · intro K hK hcompact
    exact (memLp_congr_ae (ae_restrict_of_ae_restrict_of_subset hK hrep)).mpr
      (hf K hK hcompact)
  · intro i
    exact (hweak i).congr_ae hrep.symm EventuallyEq.rfl

/-- The classical gradient of the continuous local Sobolev representative equals
its weak gradient almost everywhere. Differentiability holds on the same full-measure
set, so this is an identity of derivatives, not just totalized `fderiv` values. -/
theorem ae_differentiableAt_gradient_eq_of_continuousOn_locally_memLp_weakGradient
    (hp : (n : ℝ≥0∞) < p) (hΩ : IsOpen Ω) (hfc : ContinuousOn f Ω)
    (hf : ∀ K ⊆ Ω, IsCompact K → MemLp f p (volume.restrict K))
    (hg : ∀ K ⊆ Ω, IsCompact K → MemLp g p (volume.restrict K))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun x ↦ g x i)) :
    ∀ᵐ x ∂volume.restrict Ω, DifferentiableAt ℝ f x ∧ ∇ f x = g x := by
  filter_upwards
    [ae_hasFDerivAt_of_continuousOn_locally_memLp_weakGradient hp hΩ hfc hf hg hweak]
    with x hx
  exact ⟨hx.differentiableAt, (show HasGradientAt f (g x) x from hx).gradient⟩

/-- A Sobolev graph element on an arbitrary open domain has a continuous
representative whose classical gradient is its stored weak gradient almost everywhere.
The derivative and gradient identity hold on the same full-measure set. -/
theorem GraphSpace.WkpSpaceOn.exists_continuousOn_ae_differentiableAt_gradient_eq
    [Fact (1 ≤ p)] (U : W^{1,p}(Ω))
    (hp : (n : ℝ≥0∞) < p) (hΩ : IsOpen Ω) :
    ∃ F : ℝ^n → ℝ, ContinuousOn F Ω ∧
      F =ᵐ[domainMeasure n Ω] baseRepresentative U ∧
      ∀ᵐ x ∂domainMeasure n Ω,
        DifferentiableAt ℝ F x ∧ ∇ F x = ∇ U x := by
  obtain ⟨F, hF, hrep, hdiff⟩ :=
    exists_continuousOn_ae_hasFDerivAt_of_locally_memLp_weakGradient hp hΩ
      (fun _ hK _ ↦ (Lp.memLp (wkpBaseCoordinateCLM U)).mono_measure
        (domainMeasure_le hK))
      (fun _ hK _ ↦ (Lp.memLp (∇ U)).mono_measure
        (domainMeasure_le hK))
      (hasWeakDerivativeOn_wkpGradientCLM U)
  refine ⟨F, hF, hrep, ?_⟩
  filter_upwards [hdiff] with x hx
  exact ⟨hx.differentiableAt,
    (show HasGradientAt F (∇ U x) x from hx).gradient⟩

end SobolevSpace
