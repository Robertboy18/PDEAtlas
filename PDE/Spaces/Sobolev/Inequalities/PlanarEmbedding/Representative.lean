/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.SmoothCompact
import PDE.Spaces.Sobolev.Approximation.Density.Global
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Continuous and Hölder representatives of planar Sobolev classes

Every whole-plane `W^{2,2}` class has a bounded continuous representative,
with pointwise bound `3 / (2√π)` times its bundled norm. Any continuous
representative satisfies the same bound. For each `0 < γ < 1`, the class
also has a representative satisfying the explicit global Hölder estimate.

Smooth compact approximation gives a uniform limit; convergence in `L²`
identifies that limit with the base coordinate almost everywhere. The
pointwise constant is inherited from the smooth Fourier estimate: it is the
Bessel constant multiplied by a nonsharp factor `3`. A separate theorem
expresses the bound directly in terms of prescribed weak-derivative rows.

## Main results

* `SobolevSpace.orderTwoSobolev_continuousRepresentative`: a continuous representative with
  `|f x| ≤ (3 / (2√π)) ‖u‖`.
* `SobolevSpace.orderTwoSobolev_pointwise_of_continuous_ae`: the same bound for every
  continuous representative.
* `SobolevSpace.continuousWeakRows_orderTwo_pointwise`: the bound in terms of prescribed `L²`
  weak-derivative rows.
* `SobolevSpace.orderTwoSobolev_holderRepresentative`: a Hölder representative of exponent `γ`
  for each `0 < γ < 1`.

## How it works

Evans proves the embedding of `W^{2,2}` into `C^{0,γ}` on bounded `C¹` domains by iterating the
Gagliardo-Nirenberg-Sobolev inequality and then applying Morrey's inequality. On the whole plane
we follow the Fourier route instead. The smooth compact estimates
`smoothCompact_orderTwo_pointwise` and `smoothCompact_orderTwo_holder` hold with explicit
constants, and `GraphSpace.globalApproximation_WkpSpace` gives smooth compact approximants that
converge in `W^{2,2}`. The pointwise bound makes the approximants uniformly Cauchy, so they have
a continuous uniform limit. Along a subsequence they also converge almost everywhere to the base
coordinate, which identifies the limit as a representative. The main proof is
`orderTwoSobolev_continuousRepresentative`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6, pp. 284-285, for the embedding of
  `W^{2,2}` into `C^{0,γ}` for `0 < γ < 1` in two dimensions on bounded domains, and §5.10, Problem
  20, p. 309, for the whole-space bound `‖u‖_{L^∞(ℝⁿ)} ≤ C ‖u‖_{H^s(ℝⁿ)}` for `s > n/2`.
  <https://doi.org/10.1090/gsm/019>
* C. Morosi and L. Pizzocchero, "On the constants for some Sobolev imbeddings", *J. Inequal. Appl.*
  6 (2001), no. 6, 665-679, numbering of arXiv:math/0011141v1, Propositions 2.1 and 3.1, for the
  sharp Bessel-norm constant `1 / (2√π)`.
  <https://arxiv.org/abs/math/0011141v1>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.1, Proposition 6,
  Appendix B.2, (241), and Appendix B.4, Proposition 9.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Filter
open PDE.FDeriv
open PDE.Analysis.Fourier
open LineDeriv
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap Topology Sobolev

namespace SobolevSpace

/-- Smooth compactly supported approximants of a whole-plane `W^{2,2}` class converge to it,
and a subsequence converges almost everywhere to its base coordinate. -/
private theorem exists_smooth_tendsto_ae (u : W^{2,2}((Set.univ : Set (ℝ^2)))) :
    ∃ f_m : ℕ → (ℝ^2 → ℝ), ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
    ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
      Filter.Tendsto (fun m ↦ GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
        (Ω := Set.univ) (f_m m) (hf_m m) (hcs_m m)) Filter.atTop (nhds u) ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂volume,
        Filter.Tendsto (fun i ↦ f_m (ns i) x) Filter.atTop
          (nhds ((((u : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
            (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ) x)) := by
  obtain ⟨f_m, hf_m, hcs_m, hconv⟩ := GraphSpace.globalApproximation_WkpSpace
    (SobolevSpace.Approximation.standardMollifier 2) (by norm_num) 2 u
  let U : ℕ → W^{2,2}((Set.univ : Set (ℝ^2))) := fun m ↦
    GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
      (Ω := Set.univ) (f_m m) (hf_m m) (hcs_m m)
  have hUconv : Filter.Tendsto U Filter.atTop (nhds u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [U] using hconv
  let P : GraphSpace.WkpAmbientOn 2 2 2 Set.univ →L[ℝ] GraphSpace.DerivLp 2 2 Set.univ :=
    PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : GraphSpace.DerivIndex 2 2 ↦ GraphSpace.DerivLp 2 2 Set.univ)
      (GraphSpace.baseIndex 2 2)
  obtain ⟨ns, hns, hnsAe⟩ := (MeasureTheory.tendstoInMeasure_of_tendsto_Lp
    ((P.continuous.tendsto _).comp
      ((continuous_subtype_val.tendsto u).comp hUconv))).exists_seq_tendsto_ae
  refine ⟨f_m, hf_m, hcs_m, hUconv, ns, hns, ?_⟩
  have hmAe : ∀ᵐ x ∂SobolevSpace.domainMeasure 2 Set.univ, ∀ i : ℕ,
      ((P (U (ns i) : GraphSpace.WkpAmbientOn 2 2 2 Set.univ) :
        GraphSpace.DerivLp 2 2 Set.univ) : (ℝ^2) → ℝ) x = f_m (ns i) x :=
    ae_all_iff.2 fun i ↦ (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae (n := 2) (k := 2) (p := 2)
      (Ω := Set.univ) (f_m (ns i)) (hf_m (ns i)) (hcs_m (ns i))
      (GraphSpace.baseIndex 2 2)).mono fun x hx ↦ by
        simpa [U, P, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using hx
  have h : ∀ᵐ x ∂SobolevSpace.domainMeasure 2 Set.univ,
      Filter.Tendsto (fun i ↦ f_m (ns i) x) Filter.atTop
        (nhds (((P (u : GraphSpace.WkpAmbientOn 2 2 2 Set.univ) :
          GraphSpace.DerivLp 2 2 Set.univ) : (ℝ^2) → ℝ) x)) := by
    filter_upwards [hnsAe, hmAe] with x hxlim hxeq
    exact (Filter.tendsto_congr hxeq).1 hxlim
  simpa [SobolevSpace.domainMeasure, P] using h

/--
The order-two whole-plane Sobolev class has a continuous representative with
the explicit endpoint constant `3 / (2√π)`, which is the
sharp Bessel constant times a loose factor `3` (see the module docstring).
The base coordinate of `u` is the underlying `L²` function of the graph-space
model.

The proof passes from smooth compact approximants to a uniform limit and
identifies that limit almost everywhere with the base coordinate of the
completed `H²(ℝ²)` class.
-/
theorem orderTwoSobolev_continuousRepresentative
    (u : W^{2,2}((Set.univ : Set (ℝ^2)))) :
    ∃ f : (ℝ^2) → ℝ,
      Continuous f ∧
      f =ᵐ[volume]
        ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
          (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) ∧
      ∀ x : (ℝ^2),
        |f x| ≤ (3 / (2 * √Real.pi)) * ‖u‖ := by
  let C : ℝ := 3 / (2 * √Real.pi)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  obtain ⟨f_m, hf_m, hcs_m, hUconv, ns, hns, hae⟩ := exists_smooth_tendsto_ae u
  let U : ℕ → W^{2,2}((Set.univ : Set (ℝ^2))) := fun m ↦
    GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
      (Ω := Set.univ) (f_m m) (hf_m m) (hcs_m m)
  have huniform : UniformCauchySeqOn f_m Filter.atTop Set.univ := by
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hUconv.cauchySeq (ε / C) (div_pos hε hC)
    refine ⟨N, fun m hm n hn x _ ↦ ?_⟩
    have hend := smoothCompact_orderTwo_pointwise (f_m m - f_m n)
      ((hf_m m).sub (hf_m n)) ((hcs_m m).sub (hcs_m n)) x
    rw [GraphSpace.mkWkpSpaceOnOfContDiff_sub] at hend
    calc dist (f_m m x) (f_m n x) = |(f_m m - f_m n) x| := by simp [Real.dist_eq]
      _ ≤ C * ‖U m - U n‖ := by simpa [C, U] using hend
      _ < C * (ε / C) :=
        mul_lt_mul_of_pos_left (by simpa [dist_eq_norm, U] using hN m hm n hn) hC
      _ = ε := by field_simp
  choose f hf using fun x : (ℝ^2) ↦
    cauchySeq_tendsto_of_complete (huniform.cauchySeq (Set.mem_univ x))
  refine ⟨f, (tendstoUniformlyOn_univ.mp (huniform.tendstoUniformlyOn_of_tendsto
      fun x _ ↦ hf x)).continuous
        (Filter.Eventually.of_forall fun m ↦ (hf_m m).continuous).frequently,
    hae.mono fun x hx ↦ tendsto_nhds_unique ((hf x).comp hns.tendsto_atTop) hx, fun x ↦ ?_⟩
  exact le_of_tendsto_of_tendsto' (hf x).abs (hUconv.norm.const_mul C) fun m ↦ by
    simpa [C] using smoothCompact_orderTwo_pointwise (f_m m) (hf_m m) (hcs_m m) x

/-- A prescribed continuous representative of a whole-plane `W^{2,2}` class
inherits the explicit endpoint estimate. This is the form needed for weak parity
reflection: no classical second derivative across the reflecting interface is
required.
-/
theorem orderTwoSobolev_pointwise_of_continuous_ae
    (u : W^{2,2}((Set.univ : Set (ℝ^2))))
    (f : (ℝ^2) → ℝ) (hf : Continuous f)
    (hrep : f =ᵐ[volume]
      ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ))) :
    ∀ x : (ℝ^2),
      |f x| ≤ (3 / (2 * √Real.pi)) * ‖u‖ := by
  obtain ⟨g, hg, hgrep, hbound⟩ :=
    orderTwoSobolev_continuousRepresentative u
  have hgf : g = f := MeasureTheory.Measure.eq_of_ae_eq
    (hgrep.trans hrep.symm) hg hf
  intro x
  simpa [hgf] using hbound x

/-- Explicit order-two endpoint for a continuous function equipped with
`L²` weak-derivative rows.  The right side is the exact intrinsic six-row
Sobolev sum, not an abstract comparison norm.
-/
theorem continuousWeakRows_orderTwo_pointwise
    (f : (ℝ^2) → ℝ)
    (d : SobolevSpace.GraphSpace.DerivIndex 2 2 → (ℝ^2) → ℝ)
    (hbase : d (SobolevSpace.GraphSpace.baseIndex 2 2) = f)
    (hf : Continuous f)
    (hmem : ∀ a : SobolevSpace.GraphSpace.DerivIndex 2 2,
      MemLp (d a) 2 volume)
    (hweak : ∀ a : SobolevSpace.GraphSpace.DerivIndex 2 2,
      SobolevSpace.HasWeakDerivativeOn (n := 2) Set.univ a.toList f (d a)) :
    ∀ x : (ℝ^2),
      |f x| ≤ (3 / (2 * √Real.pi)) *
        √(∑ a : SobolevSpace.GraphSpace.DerivIndex 2 2,
          ∫ y : (ℝ^2), (d a y) ^ 2) := by
  let U : W^{2,2}((Set.univ : Set (ℝ^2))) :=
    SobolevSpace.GraphSpace.mkWkpSpaceOnOfWeakDerivatives
      (n := 2) (k := 2) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
      f d hbase (by simpa [SobolevSpace.domainMeasure] using hmem) hweak
  have hrep : f =ᵐ[volume]
      ((((U : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) := by
    simpa [SobolevSpace.domainMeasure, hbase] using
      (SobolevSpace.GraphSpace.mkWkpSpaceOnOfWeakDerivatives_apply_ae
        (n := 2) (k := 2) (p := (2 : ℝ≥0∞)) (Ω := Set.univ) f d hbase
        (by simpa [SobolevSpace.domainMeasure] using hmem) hweak
        (SobolevSpace.GraphSpace.baseIndex 2 2)).symm
  have hnorm : ‖U‖ = √(∑ a : SobolevSpace.GraphSpace.DerivIndex 2 2,
      ∫ y : (ℝ^2), (d a y) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg U)]
    congr 1
    simpa [U, SobolevSpace.domainMeasure] using
      SobolevSpace.GraphSpace.norm_sq_mkWkpSpaceOnOfWeakDerivatives (n := 2) (k := 2)
        (Ω := Set.univ) f d hbase (by simpa [SobolevSpace.domainMeasure] using hmem) hweak
  exact fun x ↦ hnorm ▸ orderTwoSobolev_pointwise_of_continuous_ae U f hf hrep x

/-- For `0 < γ < 1`, every whole-plane `W^{2,2}` class `u` has a continuous representative `f`
of its base coordinate with `|f x - f y| ≤ (3 / π) ‖K_γ‖_{L²} ‖u‖ ‖x - y‖ ^ γ` for all `x` and
`y`, where `K_γ` is `orderTwoHolderKernel γ`.
-/
theorem orderTwoSobolev_holderRepresentative
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (u : W^{2,2}((Set.univ : Set (ℝ^2)))) :
    ∃ f : (ℝ^2) → ℝ,
      Continuous f ∧
      f =ᵐ[volume]
        ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
          (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) ∧
      ∀ x y : (ℝ^2),
        |f x - f y| ≤
          (3 / Real.pi) * √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
            ‖u‖ * ‖x - y‖ ^ γ := by
  obtain ⟨f, hf, hrep, -⟩ := orderTwoSobolev_continuousRepresentative u
  obtain ⟨f_m, hf_m, hcs_m, hUconv, ns, hns, hae⟩ := exists_smooth_tendsto_ae u
  let S : Set (ℝ^2) := {x | Filter.Tendsto (fun i ↦ f_m (ns i) x) Filter.atTop (nhds (f x))}
  have hSdense : Dense S := (volume : Measure (ℝ^2)).dense_of_ae <| by
    filter_upwards [hae, hrep] with x hx hxrep
    rw [hxrep]
    exact hx
  let Cγ : ℝ := (3 / Real.pi) * √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2)
  let T : Set ((ℝ^2) × (ℝ^2)) := {q | |f q.1 - f q.2| ≤ Cγ * ‖u‖ * ‖q.1 - q.2‖ ^ γ}
  have hTclosed : IsClosed T := by
    apply isClosed_le
    · fun_prop
    · dsimp only [Cγ]
      fun_prop (disch := positivity)
  have hST : S ×ˢ S ⊆ T := fun q hq ↦
    le_of_tendsto_of_tendsto' (hq.1.sub hq.2).abs
      (((hUconv.norm.const_mul Cγ).mul_const (‖q.1 - q.2‖ ^ γ)).comp hns.tendsto_atTop)
      fun i ↦ by
        simpa [Cγ] using smoothCompact_orderTwo_holder γ hγ0 hγ1
          (f_m (ns i)) (hf_m (ns i)) (hcs_m (ns i)) q.1 q.2
  refine ⟨f, hf, hrep, fun x y ↦ ?_⟩
  simpa [T, Cγ] using closure_minimal hST hTclosed
    ((hSdense.prod hSdense).closure_eq ▸ Set.mem_univ (x, y))

end SobolevSpace
