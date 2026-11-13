/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.ContinuousRepresentative.Linearity

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Holder
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.Estimate

/-!
# Finite-exponent Morrey embeddings

The smooth multidimensional Morrey estimate extends to the completed Sobolev
space. For `p > n`, we construct a bounded linear map

`W^{1,p}(ℝ^n) → C^{0,1-n/p}(ℝ^n)`

whose output agrees almost everywhere with the base Sobolev coordinate. On a
domain carrying `Boundary.C1ExtensionAtlas`, composition with the extension
operator and Hölder restriction gives the corresponding bounded-domain map.

Evans, PDE, §5.6.2, proves the estimate (20) for `u ∈ C¹(ℝ^n)` (Theorem 4) and obtains the
bounded-domain version (Theorem 5) from the extension of §5.4 and approximation by
`C_c^∞(ℝ^n)` functions. We follow the same route: the estimate for compactly supported
smooth functions, extension by density to `W^{1,p}(ℝ^n)`, then composition with an extension
operator.

## Main results

* `enorm_apply_le_eLpNorm_add_finiteMorrey`, `norm_compactSupportToMorreyHolder_le`: a point
  value of a `C¹` function is controlled by its `Lᵖ` norm (through a unit ball) plus its Morrey
  coefficient, so the full `C^{0,γ}` norm of a compactly supported smooth function is bounded by
  its `W^{1,p}` norm.
* `norm_compactSupportToMorreyHolder_le_embeddingConstant`, `dist_compactSupportToMorreyHolder_le`:
  the smooth-core estimate in terms of the finite `PiLp` Sobolev norm, with the explicit constant
  `finiteMorreyEmbeddingConstant n p q`, and its Lipschitz form.
* `exists_morreyHolderRepresentative`, `morreyHolderRepresentative`: every global `W^{1,p}` class
  with `p > n` has a `C^{0,1-n/p}` representative agreeing a.e. with its base coordinate, obtained
  by density from the smooth-core lifts.
* `finiteMorreyEmbedding`: the bounded linear map `W^{1,p}(ℝ^n) → C^{0,1-n/p}(ℝ^n)`, with the
  norm estimate `norm_morreyHolderRepresentative_le`.
* `finiteMorreyEmbeddingOn`: on a `C¹` extension domain, `W^{1,p}(Ω) → C^{0,1-n/p}(Ω)`, with the
  norm estimate `norm_finiteMorreyEmbeddingOn_le`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, (20), pp. 280-283, for `u ∈ C¹(ℝ^n)`, and
  Theorem 5, pp. 283-284, for a bounded `C¹` domain, proved with the extension (26) and
  approximation (27)-(28).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

/-- The unit-ball volume factor used to control one point value by the global
`Lᵖ` norm. -/
def morreyUnitBallLpFactor (n : ℕ) (p : ℝ) : ENNReal :=
  volume (Metric.ball (0 : ℝ^n) 1) ^
      (1 - 1 / (ENNReal.ofReal p).toReal) /
    volume (Metric.ball (0 : ℝ^n) 1)

/-- The part of the smooth Morrey coefficient independent of the function. -/
def finiteMorreyCoefficientE (n : ℕ) (p q : ℝ) : ENNReal :=
  2 * morreyBallAverageConstant n *
    morreyCenteredKernelConstant n q *
    (ENNReal.ofReal 2 ^
      morreyExponent n (ENNReal.ofReal p))

/-- Factorization of the smooth Morrey coefficient into its geometric factor
and the `Lᵖ` norm of the derivative. -/
theorem finiteMorreyHolderConstantE_eq
    (n : ℕ) (p q : ℝ) (u : ℝ^n → ℝ) :
    finiteMorreyHolderConstantE n p q u =
      finiteMorreyCoefficientE n p q *
        eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume :=
  rfl

/-- An explicit operator bound for the global finite-exponent Morrey
embedding. -/
def finiteMorreyEmbeddingConstant (n : ℕ) (p q : ℝ) : ℝ :=
  (morreyUnitBallLpFactor n p).toReal +
    2 * (finiteMorreyCoefficientE n p q).toReal * n

/-- A continuous function has a point in every unit ball whose value is
controlled by its global `Lᵖ` norm and the unit-ball volume factor. -/
theorem exists_ball_one_enorm_le_eLpNorm
    {n : ℕ} (u : ℝ^n → ℝ) (hu : Continuous u)
    {p : ℝ} (hp : 1 ≤ p) (x : ℝ^n) :
    ∃ z ∈ Metric.ball x 1,
      ‖u z‖ₑ ≤
        eLpNorm u (ENNReal.ofReal p) volume *
          morreyUnitBallLpFactor n p := by
  have hmeas : AEMeasurable (fun z : ℝ^n ↦ ‖u z‖ₑ) (volume.restrict (Metric.ball x 1)) :=
    hu.enorm.aemeasurable
  obtain ⟨z, hzB, hz⟩ := exists_le_setLAverage (Metric.measure_ball_pos volume x zero_lt_one).ne'
    measure_ball_lt_top.ne hmeas
  refine ⟨z, hzB, hz.trans ?_⟩
  have hum := hu.aestronglyMeasurable.mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Metric.ball x 1))
  rw [setLAverage_eq, ← eLpNorm_one_eq_lintegral_enorm hum]
  calc _ ≤ eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x 1)) *
          (volume.restrict (Metric.ball x 1)) Set.univ ^
            (1 / (1 : ENNReal).toReal - 1 / (ENNReal.ofReal p).toReal) /
          volume (Metric.ball x 1) := by
        gcongr
        exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.one_le_ofReal.mpr hp) hum
    _ ≤ eLpNorm u (ENNReal.ofReal p) volume *
          (volume.restrict (Metric.ball x 1)) Set.univ ^
            (1 / (1 : ENNReal).toReal - 1 / (ENNReal.ofReal p).toReal) /
          volume (Metric.ball x 1) := by
        gcongr
        exact Measure.restrict_le_self
    _ = _ := by
        rw [Measure.restrict_apply_univ, Measure.addHaar_ball_center]
        simp [morreyUnitBallLpFactor, div_eq_mul_inv, mul_assoc]

/-- A smooth function's value is controlled by its global `Lᵖ` norm and its
finite-exponent Morrey coefficient. -/
theorem enorm_apply_le_eLpNorm_add_finiteMorrey
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (x : ℝ^n) :
    ‖u x‖ₑ ≤
      eLpNorm u (ENNReal.ofReal p) volume *
          morreyUnitBallLpFactor n p +
        finiteMorreyHolderConstantE n p q u := by
  obtain ⟨z, hzBall, hz⟩ := exists_ball_one_enorm_le_eLpNorm u hu.continuous
    ((show (1 : ℝ) ≤ n by exact_mod_cast hn).trans hp.le) x
  have hdist : ENNReal.ofReal ‖z - x‖ ^ morreyExponent n (ENNReal.ofReal p) ≤ 1 :=
    ENNReal.rpow_le_one (ENNReal.ofReal_le_one.mpr
      (by simpa [dist_eq_norm] using (Metric.mem_ball.mp hzBall).le))
      (morreyExponent_ofReal_pos hn hp).le
  have hosc : ‖u z - u x‖ₑ ≤ finiteMorreyHolderConstantE n p q u :=
    (by simpa [finiteMorreyHolderConstantE] using
        enorm_sub_le_eLpNorm_fderiv_mul_rpow u hu hn hp hpq x z :
      ‖u z - u x‖ₑ ≤ finiteMorreyHolderConstantE n p q u *
        ENNReal.ofReal ‖z - x‖ ^ morreyExponent n (ENNReal.ofReal p)).trans
      (mul_le_of_le_one_right' hdist)
  calc ‖u x‖ₑ = ‖(u x - u z) + u z‖ₑ := by rw [sub_add_cancel]
    _ ≤ ‖u z - u x‖ₑ + ‖u z‖ₑ := by rw [enorm_sub_rev]; exact enorm_add_le _ _
    _ ≤ _ := by rw [add_comm]; gcongr

/-- The unit-ball volume factor is finite. -/
theorem morreyUnitBallLpFactor_ne_top (n : ℕ) (p : ℝ) :
    morreyUnitBallLpFactor n p ≠ ∞ := by
  have hvolume0 :
      volume (Metric.ball (0 : ℝ^n) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : ℝ^n) zero_lt_one).ne'
  have hvolumeTop :
      volume (Metric.ball (0 : ℝ^n) 1) ≠ ∞ :=
    measure_ball_lt_top.ne
  exact ENNReal.div_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero hvolume0 hvolumeTop)
    hvolume0

/-- Real-valued form of the pointwise bound for compactly supported smooth
functions. -/
theorem norm_apply_le_eLpNorm_add_finiteMorrey
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (x : ℝ^n) :
    ‖u x‖ ≤
      (eLpNorm u (ENNReal.ofReal p) volume).toReal *
          (morreyUnitBallLpFactor n p).toReal +
        (finiteMorreyHolderConstantE n p q u).toReal := by
  have hbaseTerm : eLpNorm u (ENNReal.ofReal p) volume * morreyUnitBallLpFactor n p ≠ ∞ :=
    ENNReal.mul_ne_top (hu.continuous.memLp_of_hasCompactSupport hcompact).eLpNorm_ne_top
      (morreyUnitBallLpFactor_ne_top n p)
  have hmorrey := finiteMorreyHolderConstantE_ne_top u hu hcompact hn hp hpq
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hbaseTerm, hmorrey⟩)
    (enorm_apply_le_eLpNorm_add_finiteMorrey u hu hn hp hpq x)
  rw [ENNReal.toReal_add hbaseTerm hmorrey, ENNReal.toReal_mul] at h
  simpa using h

/-- The full `C^{0,γ}` norm of a compactly supported smooth function is
controlled by its `Lᵖ` norm and smooth Morrey coefficient. -/
theorem norm_compactSupportToMorreyHolder_le
    {n : ℕ} (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    ‖compactSupportToMorreyHolder u hu hcompact hn hp hpq‖ ≤
      (eLpNorm u (ENNReal.ofReal p) volume).toReal *
          (morreyUnitBallLpFactor n p).toReal +
        2 * (finiteMorreyHolderConstantE n p q u).toReal := by
  have hsup : ‖(compactSupportToMorreyHolder u hu hcompact hn hp hpq).toBoundedContinuousFunction‖
      ≤ (eLpNorm u (ENNReal.ofReal p) volume).toReal * (morreyUnitBallLpFactor n p).toReal +
        (finiteMorreyHolderConstantE n p q u).toReal :=
    (BoundedContinuousFunction.norm_le (by positivity)).2
      (norm_apply_le_eLpNorm_add_finiteMorrey u hu hcompact hn hp hpq)
  have hsemi := NNReal.coe_le_coe.2
    (holderSeminorm_compactSupportToMorreyHolder_le u hu hcompact hn hp hpq)
  have hconst : ((finiteMorreyHolderConstant n p q u : NNReal) : ℝ) =
      (finiteMorreyHolderConstantE n p q u).toReal :=
    ENNReal.coe_toNNReal_eq_toReal _
  rw [HolderSpace.C0GammaOn.norm_def]
  linarith

/-- Quantitative Morrey bound for the smooth compactly supported core, in
terms of the finite `PiLp` Sobolev norm. -/
theorem norm_compactSupportToMorreyHolder_le_embeddingConstant
    {n : ℕ} (u : ℝ^n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    ‖compactSupportToMorreyHolder
        u (hu.of_le (by simp)) hcompact hn hp hpq‖ ≤
      finiteMorreyEmbeddingConstant n p q *
        ‖GraphSpace.mkWkpSpaceOnOfContDiff
          (n := n) (k := 1) (p := ENNReal.ofReal p)
          (Ω := (Set.univ : Set (ℝ^n))) u hu hcompact‖ := by
  let U : W^{1,(ENNReal.ofReal p)}(ℝ^n) :=
    GraphSpace.mkWkpSpaceOnOfContDiff
      (n := n) (k := 1) (p := ENNReal.ofReal p)
      (Ω := (Set.univ : Set (ℝ^n))) u hu hcompact
  have hcoord (a : GraphSpace.DerivIndex n 1) :
      (eLpNorm (fun x ↦ iteratedPartialDeriv a.toList u x) (ENNReal.ofReal p) volume).toReal ≤
        ‖U‖ := by
    have h := GraphSpace.norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal (n := n)
      (k := 1) (p := ENNReal.ofReal p) (Ω := (Set.univ : Set (ℝ^n))) u hu hcompact a
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h ▸ PiLp.norm_apply_le (U : GraphSpace.WkpAmbientOn n 1 (ENNReal.ofReal p) Set.univ) a
  have hbase : (eLpNorm u (ENNReal.ofReal p) volume).toReal ≤ ‖U‖ := by
    simpa [iteratedPartialDeriv] using hcoord (GraphSpace.baseIndex n 1)
  have hpartial (i : Fin n) :
      (eLpNorm (fun x ↦ (∂[i] u) x) (ENNReal.ofReal p) volume).toReal ≤ ‖U‖ := by
    simpa [iteratedPartialDeriv] using hcoord (GraphSpace.singleDerivIndex n i)
  have hfinite (i : Fin n) : eLpNorm (fun x ↦ (∂[i] u) x) (ENNReal.ofReal p) volume ≠ ∞ := by
    have hsmooth := PDE.contDiff_top_iteratedPartialDeriv (n := n) (f := u) hu [i]
    have hsupport :=
      SobolevSpace.hasCompactSupport_iteratedPartialDeriv (n := n) (f := u) hcompact [i]
    simpa [iteratedPartialDeriv] using (hsmooth.continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure (ℝ^n))) (p := ENNReal.ofReal p) hsupport).eLpNorm_ne_top
  have hgradient : (eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume).toReal ≤ n * ‖U‖ :=
    calc _ ≤ ∑ i : Fin n, (eLpNorm (fun x ↦ (∂[i] u) x) (ENNReal.ofReal p) volume).toReal := by
          rw [← ENNReal.toReal_sum fun i _ ↦ hfinite i]
          exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ ↦ hfinite i)
            (Inequalities.eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv (hu := hu.of_le (by simp)))
      _ ≤ ∑ _i : Fin n, ‖U‖ := Finset.sum_le_sum fun i _ ↦ hpartial i
      _ = n * ‖U‖ := by simp
  have hcore := norm_compactSupportToMorreyHolder_le u (hu.of_le (by simp)) hcompact hn hp hpq
  rw [finiteMorreyHolderConstantE_eq, ENNReal.toReal_mul] at hcore
  calc _ ≤ _ := hcore
    _ ≤ ‖U‖ * (morreyUnitBallLpFactor n p).toReal +
          2 * ((finiteMorreyCoefficientE n p q).toReal * (n * ‖U‖)) := by gcongr
    _ = finiteMorreyEmbeddingConstant n p q * ‖U‖ := by
      rw [finiteMorreyEmbeddingConstant]
      ring

/-- Bundling the difference of smooth functions commutes with subtraction in
the Hölder space. -/
theorem compactSupportToMorreyHolder_sub
    {n : ℕ} (u v : ℝ^n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hcompactU : HasCompactSupport u)
    (hcompactV : HasCompactSupport v)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    compactSupportToMorreyHolder
        (fun x ↦ u x - v x)
        ((hu.sub hv).of_le (by simp))
        (hcompactU.sub hcompactV)
        hn hp hpq =
      compactSupportToMorreyHolder
          u (hu.of_le (by simp)) hcompactU hn hp hpq -
        compactSupportToMorreyHolder
          v (hv.of_le (by simp)) hcompactV hn hp hpq := by
  apply HolderSpace.C0GammaOn.ext
  intro x
  rfl

/-- The smooth Morrey lift is Lipschitz with respect to the first-order
Sobolev norm. -/
theorem dist_compactSupportToMorreyHolder_le
    {n : ℕ} (u v : ℝ^n → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hcompactU : HasCompactSupport u)
    (hcompactV : HasCompactSupport v)
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    dist
        (compactSupportToMorreyHolder
          u (hu.of_le (by simp)) hcompactU hn hp hpq)
        (compactSupportToMorreyHolder
          v (hv.of_le (by simp)) hcompactV hn hp hpq) ≤
      finiteMorreyEmbeddingConstant n p q *
        dist
          (GraphSpace.mkWkpSpaceOnOfContDiff
            (n := n) (k := 1) (p := ENNReal.ofReal p)
            (Ω := (Set.univ : Set (ℝ^n))) u hu hcompactU)
          (GraphSpace.mkWkpSpaceOnOfContDiff
            (n := n) (k := 1) (p := ENNReal.ofReal p)
            (Ω := (Set.univ : Set (ℝ^n))) v hv hcompactV) := by
  rw [dist_eq_norm, dist_eq_norm,
    ← compactSupportToMorreyHolder_sub
      u v hu hv hcompactU hcompactV hn hp hpq,
    ← GraphSpace.mkWkpSpaceOnOfContDiff_sub
      u v hu hv hcompactU hcompactV]
  exact norm_compactSupportToMorreyHolder_le_embeddingConstant
    (fun x ↦ u x - v x) (hu.sub hv)
    (hcompactU.sub hcompactV)
    hn hp hpq

/-- The explicit finite-exponent Morrey embedding constant is nonnegative. -/
theorem finiteMorreyEmbeddingConstant_nonneg
    (n : ℕ) (p q : ℝ) :
    0 ≤ finiteMorreyEmbeddingConstant n p q := by
  simp only [finiteMorreyEmbeddingConstant]
  positivity

/-- Every global `W^{1,p}` function with `p > n` has a Hölder representative
that agrees almost everywhere with its base coordinate and satisfies the
explicit norm estimate. -/
theorem exists_morreyHolderRepresentative
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    ∃ F : HolderSpace.C0GammaOn (ℝ^n)
        (finiteMorreyHolderExponent n p hn hp),
      (fun x ↦ F x) =ᵐ[volume]
        (((U : GraphSpace.WkpAmbientOn n 1 (ENNReal.ofReal p) Set.univ)
          (GraphSpace.baseIndex n 1) :
          GraphSpace.DerivLp n (ENNReal.ofReal p) Set.univ) :
          ℝ^n → ℝ) ∧
      ‖F‖ ≤ finiteMorreyEmbeddingConstant n p q * ‖U‖ :=
  GraphSpace.exists_boundedRepresentative_of_smoothCore (n := n) (p := ENNReal.ofReal p)
    (Approximation.standardMollifier n) ENNReal.ofReal_ne_top 1
    (fun u hu hcompact ↦ compactSupportToMorreyHolder u (hu.of_le (by simp)) hcompact hn hp hpq)
    (fun x ↦ HolderSpace.C0GammaOn.evalCLM x) (finiteMorreyEmbeddingConstant n p q)
    (finiteMorreyEmbeddingConstant_nonneg n p q) (by intros; rfl)
    (fun u v hu hv hcompactU hcompactV ↦
      dist_compactSupportToMorreyHolder_le u v hu hv hcompactU hcompactV hn hp hpq)
    (fun u hu hcompact ↦
      norm_compactSupportToMorreyHolder_le_embeddingConstant u hu hcompact hn hp hpq)
    U

/-- The unique continuous Morrey representative of a global `W^{1,p}`
element for `p > n`. -/
noncomputable def morreyHolderRepresentative
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    HolderSpace.C0GammaOn (ℝ^n)
      (finiteMorreyHolderExponent n p hn hp) :=
  Classical.choose
    (exists_morreyHolderRepresentative hn hp hpq U)

/-- The selected global Hölder representative agrees almost everywhere with
the Sobolev base coordinate. -/
theorem morreyHolderRepresentative_ae
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    (fun x ↦ morreyHolderRepresentative hn hp hpq U x) =ᵐ[volume]
      GraphSpace.baseRepresentative U :=
  (Classical.choose_spec
    (exists_morreyHolderRepresentative hn hp hpq U)).1

/-- Norm estimate for the selected global Hölder representative. -/
theorem norm_morreyHolderRepresentative_le
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    ‖morreyHolderRepresentative hn hp hpq U‖ ≤
      finiteMorreyEmbeddingConstant n p q * ‖U‖ :=
  (Classical.choose_spec
    (exists_morreyHolderRepresentative hn hp hpq U)).2

/-- The selected Morrey representative is additive. -/
theorem morreyHolderRepresentative_add
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U V : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    morreyHolderRepresentative hn hp hpq (U + V) =
      morreyHolderRepresentative hn hp hpq U +
        morreyHolderRepresentative hn hp hpq V := by
  have hbase := GraphSpace.baseRepresentative_add_ae U V
  simp only [domainMeasure, Measure.restrict_univ] at hbase
  apply HolderSpace.C0GammaOn.ext
  exact congrFun (map_add_of_continuous_ae_eq
    (fun W ↦ (morreyHolderRepresentative hn hp hpq W).continuous)
    (morreyHolderRepresentative_ae hn hp hpq) hbase)

/-- The selected Morrey representative respects scalar multiplication. -/
theorem morreyHolderRepresentative_smul
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (c : ℝ) (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    morreyHolderRepresentative hn hp hpq (c • U) =
      c • morreyHolderRepresentative hn hp hpq U := by
  have hbase := GraphSpace.baseRepresentative_smul_ae c U
  simp only [domainMeasure, Measure.restrict_univ] at hbase
  apply HolderSpace.C0GammaOn.ext
  exact congrFun (map_smul_of_continuous_ae_eq
    (fun W ↦ (morreyHolderRepresentative hn hp hpq W).continuous)
    (morreyHolderRepresentative_ae hn hp hpq) hbase)

/-- The global bounded linear Morrey embedding
`W^{1,p}(ℝ^n) → C^{0,1-n/p}(ℝ^n)` for finite `p > n`. -/
noncomputable def finiteMorreyEmbedding
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) :
    W^{1,(ENNReal.ofReal p)}(ℝ^n) →L[ℝ]
      HolderSpace.C0GammaOn (ℝ^n)
        (finiteMorreyHolderExponent n p hn hp) :=
  LinearMap.mkContinuous
    { toFun := morreyHolderRepresentative hn hp hpq
      map_add' := morreyHolderRepresentative_add hn hp hpq
      map_smul' := morreyHolderRepresentative_smul hn hp hpq }
    (finiteMorreyEmbeddingConstant n p q)
    (norm_morreyHolderRepresentative_le hn hp hpq)

/-- As a function, the Morrey embedding is `morreyHolderRepresentative`; the continuous linear
map adds linearity and the bound `finiteMorreyEmbeddingConstant n p q`. -/
@[simp]
theorem finiteMorreyEmbedding_apply
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    finiteMorreyEmbedding hn hp hpq U =
      morreyHolderRepresentative hn hp hpq U :=
  rfl

/-- The global Morrey embedding agrees almost everywhere with the base
Sobolev coordinate. -/
theorem finiteMorreyEmbedding_ae
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q)
    (U : W^{1,(ENNReal.ofReal p)}(ℝ^n)) :
    (fun x ↦ finiteMorreyEmbedding hn hp hpq U x) =ᵐ[volume]
      GraphSpace.baseRepresentative U :=
  morreyHolderRepresentative_ae hn hp hpq U

/-- The bounded-domain finite-exponent Morrey embedding, obtained by global
extension followed by restriction of the Hölder representative. -/
noncomputable def finiteMorreyEmbeddingOn
    {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q) :
    W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      HolderSpace.C0GammaOn Ω
        (finiteMorreyHolderExponent n p Fact.out hp) :=
  (HolderSpace.C0GammaOn.restrictCLM Ω).comp
    ((finiteMorreyEmbedding Fact.out hp hpq).comp
      (Extension.C1.extensionCLM
        (n := n) (p := ENNReal.ofReal p) (Ω := Ω)))

/-- On a domain, the embedding is the global Hölder representative of the extension `E U`,
restricted to points of `Ω`. -/
@[simp]
theorem finiteMorreyEmbeddingOn_apply
    {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{1,ENNReal.ofReal p}(Ω))
    (x : Ω) :
    finiteMorreyEmbeddingOn hp hpq U x =
      finiteMorreyEmbedding Fact.out hp hpq
        (Extension.C1.extensionCLM
          (n := n) (p := ENNReal.ofReal p) (Ω := Ω) U) x :=
  rfl

/-- The bounded-domain Morrey embedding agrees almost everywhere with the
Sobolev base coordinate on the domain. -/
theorem finiteMorreyEmbeddingOn_ae
    {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{1,ENNReal.ofReal p}(Ω)) :
    (fun x ↦
      finiteMorreyEmbedding Fact.out hp hpq
        (Extension.C1.extensionCLM
          (n := n) (p := ENNReal.ofReal p) (Ω := Ω) U) x) =ᵐ[
      domainMeasure n Ω]
        (((U : GraphSpace.WkpAmbientOn n 1 (ENNReal.ofReal p) Ω)
          (GraphSpace.baseIndex n 1) :
          GraphSpace.DerivLp n (ENNReal.ofReal p) Ω) :
          ℝ^n → ℝ) := by
  have hglobal :=
    finiteMorreyEmbedding_ae Fact.out hp hpq
      (Extension.C1.extensionCLM
        (n := n) (p := ENNReal.ofReal p) (Ω := Ω) U)
  have hglobalΩ :=
    MeasureTheory.ae_restrict_of_ae (s := Ω) hglobal
  filter_upwards
    [hglobalΩ,
      Extension.C1.extensionCLM_agree_ae
        (n := n) (p := ENNReal.ofReal p) (Ω := Ω) U] with x hx hE
  exact hx.trans hE

/-- Explicit norm estimate for the bounded-domain finite-exponent Morrey
embedding. -/
theorem norm_finiteMorreyEmbeddingOn_le
    {n : ℕ} {Ω : Set (ℝ^n)} {p q : ℝ}
    [Fact (0 < n)] [Fact (1 ≤ ENNReal.ofReal p)]
    [Boundary.C1ExtensionAtlas n Ω]
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖finiteMorreyEmbeddingOn hp hpq U‖ ≤
      finiteMorreyEmbeddingConstant n p q *
        ‖Extension.C1.extensionCLM
          (n := n) (p := ENNReal.ofReal p) (Ω := Ω)‖ * ‖U‖ := by
  calc
    ‖finiteMorreyEmbeddingOn hp hpq U‖
        ≤ ‖finiteMorreyEmbedding Fact.out hp hpq
            (Extension.C1.extensionCLM
              (n := n) (p := ENNReal.ofReal p) (Ω := Ω) U)‖ :=
      HolderSpace.C0GammaOn.norm_restrict_le Ω _
    _ ≤ finiteMorreyEmbeddingConstant n p q *
          ‖Extension.C1.extensionCLM
            (n := n) (p := ENNReal.ofReal p) (Ω := Ω) U‖ :=
      norm_morreyHolderRepresentative_le Fact.out hp hpq _
    _ ≤ finiteMorreyEmbeddingConstant n p q *
          (‖Extension.C1.extensionCLM
            (n := n) (p := ENNReal.ofReal p) (Ω := Ω)‖ * ‖U‖) := by
      exact mul_le_mul_of_nonneg_left
        ((Extension.C1.extensionCLM
          (n := n) (p := ENNReal.ofReal p) (Ω := Ω)).le_opNorm U)
        (finiteMorreyEmbeddingConstant_nonneg n p q)
    _ = _ := by ring

end SobolevSpace
