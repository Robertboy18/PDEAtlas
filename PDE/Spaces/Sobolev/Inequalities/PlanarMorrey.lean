/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.Representative
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.SecondOrder.Planar
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Embedding
import CAS.ExactTactic
public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic

/-!
# Morrey estimates in the plane

Morrey's inequality in the plane: for `p > 2`, a function in `W^{1,p}(ℝ²)` has
a Hölder continuous representative with exponent `1 - 2/p`, and
`|f(x) - f(y)| ≤ C ‖f‖_{W^{1,p}} |x - y|^{1 - 2/p}`. We obtain the planar
embedding as the `n = 2` instance of the finite-exponent Morrey
theory and derive the bounded-domain consequences: the `W^{1,p}` Hölder
representative on a bounded `C¹`
domain, and the `H² ⊂ C^{0,γ} ∩ L^∞` embedding for every `0 < γ < 1` in two
dimensions.

The analytic content is dimension-independent. The smooth Morrey inequality is
`SobolevSpace.norm_compactSupportToMorreyHolder_le_embeddingConstant`, the
whole-space Hölder representative is
`SobolevSpace.exists_morreyHolderRepresentative`, and the bounded-domain
representative is `SobolevSpace.finiteMorreyEmbeddingOn`, the global
representative of the bounded `C¹` extension; these carry out the kernel
estimate, the density argument, and the extension step in every dimension.
The theorems here specialise them to the plane, convert the extended-real
exponent `p : ℝ≥0∞` and the bundled Hölder exponent `1 - 2/p` to the real
exponent form, and record the constants existentially.

## Main results

* `smoothCompact_morreyHolder`: Morrey's inequality for smooth compactly
  supported functions, with a constant depending only on `p`.
* `wholePlane_morreyRepresentativeOn`: every `W^{1,p}(ℝ²)` class with
  `2 < p < ∞` has a representative that is continuous on a given set and
  satisfies the Hölder bound there.
* `morrey_boundedC1Domain`: the same on a domain `Ω` carrying a
  `C1ExtensionAtlas`, with continuity up to the closure and the sup bound.
* `sobolev_H2_holder_of_extension`, `sobolev_H2_boundedC1Domain`: the planar
  `H² → C^{0,γ} ∩ L^∞` embedding, first from a bounded `W^{2,2}` extension
  operator and then on a `C1ExtensionAtlas` domain.

## Implementation notes

The two bounded-domain theorems (`morrey_boundedC1Domain`,
`sobolev_H2_boundedC1Domain`) are parametrised by
the operational class `SobolevSpace.Boundary.C1ExtensionAtlas 2 Ω`, which
records a finite boundary cover by `C¹` flattening charts together with an
interior cutoff. A caller supplies the atlas, for example from explicit
chart data via `C1FlatteningCharts.toC1ExtensionAtlas`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, pp. 280-283, for Morrey's inequality,
  §5.6.2, Theorem 5, pp. 283-284, for the Hölder version of a `W^{1,p}` function on a bounded `C¹`
  domain, §5.6.3, Theorem 6, pp. 284-285, for the embedding of `H²` into `C^{0,γ}` for `0 < γ < 1`
  in two dimensions, §5.4, Theorem 1, pp. 268-271, for extensions, and §5.3, pp. 264-268, for
  approximation by smooth functions.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7, Sobolev Spaces.
  <https://doi.org/10.1007/978-3-642-61798-0>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.2, Theorems 4-6 and
  (241), where these statements are recorded for the stability argument.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open LineDeriv
open scoped ENNReal RealInnerProductSpace Topology Sobolev

namespace SobolevSpace


/-- For finite `p > 2` there is `C > 0` such that every smooth compactly supported `f` on `ℝ²`
satisfies `|f x - f y| ≤ C ‖f‖_{W^{1,p}} ‖x - y‖ ^ (1 - 2/p)`. This is the planar case of
`SobolevSpace.norm_compactSupportToMorreyHolder_le_embeddingConstant`; the proof takes
`C = max 1 (finiteMorreyEmbeddingConstant 2 p (p / (p - 1)))`, which depends only on `p`.
-/
theorem smoothCompact_morreyHolder
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
        (hcs : HasCompactSupport f),
        ∀ x y : (ℝ^2),
          |f x - f y| ≤ C *
            ‖GraphSpace.mkWkpSpaceOnOfContDiff
              (n := 2) (k := 1) (p := p) (Ω := Set.univ) f hf hcs‖ *
            ‖x - y‖ ^ (1 - 2 / p.toReal) := by
  have hpTop : p ≠ ∞ :=
    (ENNReal.toReal_pos_iff.mp (lt_trans zero_lt_two hp)).2.ne
  obtain ⟨r, hr0, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ p = ENNReal.ofReal r :=
    ⟨p.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hpTop).symm⟩
  rw [ENNReal.toReal_ofReal hr0] at hp ⊢
  have hn : 0 < 2 := by norm_num
  have hp2 : ((2 : ℕ) : ℝ) < r := by exact_mod_cast hp
  have hpq : r.HolderConjugate (r / (r - 1)) :=
    Real.HolderConjugate.conjExponent (by linarith)
  have hγ : ((finiteMorreyHolderExponent 2 r hn hp2 : NNReal) : ℝ) = 1 - 2 / r := by
    rw [finiteMorreyHolderExponent_coe,
      Real.coe_toNNReal _ (morreyExponent_ofReal_pos hn hp2).le, morreyExponent_ofReal 2 hr0]
    norm_num
  refine ⟨max 1 (finiteMorreyEmbeddingConstant 2 r (r / (r - 1))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro f hf hcs x y
  have hF : |f x - f y| ≤
      ‖compactSupportToMorreyHolder f (hf.of_le (by simp)) hcs hn hp2 hpq‖ *
        ‖x - y‖ ^ (1 - 2 / r) := by
    have h :=
      (compactSupportToMorreyHolder f (hf.of_le (by simp)) hcs hn hp2 hpq).holderWith.dist_le x y
    rw [Real.dist_eq, dist_eq_norm, hγ] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (HolderSpace.C0GammaOn.holderSeminorm_le_norm _) (Real.rpow_nonneg (norm_nonneg _) _))
  have hFnorm :=
    norm_compactSupportToMorreyHolder_le_embeddingConstant f hf hcs hn hp2 hpq
  calc
    |f x - f y|
        ≤ ‖compactSupportToMorreyHolder f (hf.of_le (by simp)) hcs hn hp2 hpq‖ *
          ‖x - y‖ ^ (1 - 2 / r) := hF
    _ ≤ (finiteMorreyEmbeddingConstant 2 r (r / (r - 1)) *
          ‖GraphSpace.mkWkpSpaceOnOfContDiff
            (n := 2) (k := 1) (p := ENNReal.ofReal r) (Ω := Set.univ) f hf hcs‖) *
          ‖x - y‖ ^ (1 - 2 / r) := by gcongr
    _ ≤ max 1 (finiteMorreyEmbeddingConstant 2 r (r / (r - 1))) *
          ‖GraphSpace.mkWkpSpaceOnOfContDiff
            (n := 2) (k := 1) (p := ENNReal.ofReal r) (Ω := Set.univ) f hf hcs‖ *
          ‖x - y‖ ^ (1 - 2 / r) := by
      gcongr
      exact le_max_right _ _

/-- For finite `p > 2` and a set `S ⊆ ℝ²`, there is `C > 0` such that every `u ∈ W^{1,p}(ℝ²)`
has a representative `f` that is continuous on `S`, agrees with the bundled base coordinate
almost everywhere on `S`, and satisfies `|f x - f y| ≤ C ‖u‖ ‖x - y‖ ^ (1 - 2/p)` for `x` and
`y` in `S`. It is the planar case
of `SobolevSpace.exists_morreyHolderRepresentative`, whose
representative is continuous on the whole plane.
-/
theorem wholePlane_morreyRepresentativeOn
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal) (S : Set (ℝ^2)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : W^{1,p}((Set.univ : Set (ℝ^2))),
        ∃ f : (ℝ^2) → ℝ,
          ContinuousOn f S ∧
          f =ᵐ[volume.restrict S]
            ((((u : GraphSpace.WkpAmbientOn 2 1 p Set.univ)
              (GraphSpace.baseIndex 2 1)) : (ℝ^2) → ℝ)) ∧
          ∀ x ∈ S, ∀ y ∈ S,
            |f x - f y| ≤ C * ‖u‖ * ‖x - y‖ ^ (1 - 2 / p.toReal) := by
  have hpTop : p ≠ ∞ :=
    (ENNReal.toReal_pos_iff.mp (lt_trans zero_lt_two hp)).2.ne
  obtain ⟨r, hr0, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ p = ENNReal.ofReal r :=
    ⟨p.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hpTop).symm⟩
  rw [ENNReal.toReal_ofReal hr0] at hp ⊢
  have hn : 0 < 2 := by norm_num
  have hp2 : ((2 : ℕ) : ℝ) < r := by exact_mod_cast hp
  have hpq : r.HolderConjugate (r / (r - 1)) :=
    Real.HolderConjugate.conjExponent (by linarith)
  have hγ : ((finiteMorreyHolderExponent 2 r hn hp2 : NNReal) : ℝ) = 1 - 2 / r := by
    rw [finiteMorreyHolderExponent_coe,
      Real.coe_toNNReal _ (morreyExponent_ofReal_pos hn hp2).le, morreyExponent_ofReal 2 hr0]
    norm_num
  refine ⟨max 1 (finiteMorreyEmbeddingConstant 2 r (r / (r - 1))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u
  obtain ⟨F, hFae, hFnorm⟩ := exists_morreyHolderRepresentative hn hp2 hpq u
  refine ⟨fun x ↦ F x, F.continuous.continuousOn, ae_restrict_of_ae hFae, ?_⟩
  intro x _hx y _hy
  have hF : |F x - F y| ≤ ‖F‖ * ‖x - y‖ ^ (1 - 2 / r) := by
    have h := F.holderWith.dist_le x y
    rw [Real.dist_eq, dist_eq_norm, hγ] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (HolderSpace.C0GammaOn.holderSeminorm_le_norm _) (Real.rpow_nonneg (norm_nonneg _) _))
  calc
    |F x - F y| ≤ ‖F‖ * ‖x - y‖ ^ (1 - 2 / r) := hF
    _ ≤ (finiteMorreyEmbeddingConstant 2 r (r / (r - 1)) * ‖u‖) *
          ‖x - y‖ ^ (1 - 2 / r) := by gcongr
    _ ≤ max 1 (finiteMorreyEmbeddingConstant 2 r (r / (r - 1))) * ‖u‖ *
          ‖x - y‖ ^ (1 - 2 / r) := by
      gcongr
      exact le_max_right _ _

/--
For finite `p > 2` and a domain `Ω ⊆ ℝ²` carrying an operational `C1ExtensionAtlas` (which
includes openness and boundedness), there is `C > 0` such that every `u ∈ W^{1,p}(Ω)` has a
representative `f` that is continuous on `closure Ω` and satisfies `|f x| ≤ C ‖u‖` and
`|f x - f y| ≤ C ‖u‖ ‖x - y‖ ^ (1 - 2/p)` there.

The representative is `SobolevSpace.finiteMorreyEmbeddingOn`:
the global Hölder representative of the bounded `C¹` extension of `u`, which is
continuous on the whole plane and agrees with `u` almost everywhere on `Ω`.
Constructing the atlas from the geometric condition of `C¹` boundary is a
separate obligation.
-/
theorem morrey_boundedC1Domain
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (Ω : Set (ℝ^2)) [SobolevSpace.Boundary.C1ExtensionAtlas 2 Ω] :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : W^{1,p}(Ω),
        ∃ f : (ℝ^2) → ℝ,
          ContinuousOn f (closure Ω) ∧
          f =ᵐ[SobolevSpace.domainMeasure 2 Ω]
            ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 1 p Ω)
              (SobolevSpace.GraphSpace.baseIndex 2 1)) : (ℝ^2) → ℝ)) ∧
          (∀ x ∈ closure Ω, |f x| ≤ C * ‖u‖) ∧
          ∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
            |f x - f y| ≤ C * ‖u‖ * ‖x - y‖ ^ (1 - 2 / p.toReal) := by
  have hpTop : p ≠ ∞ :=
    (ENNReal.toReal_pos_iff.mp (lt_trans zero_lt_two hp)).2.ne
  obtain ⟨r, hr0, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ p = ENNReal.ofReal r :=
    ⟨p.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hpTop).symm⟩
  rw [ENNReal.toReal_ofReal hr0] at hp ⊢
  have : Fact (0 < 2) := ⟨by norm_num⟩
  have hp2 : ((2 : ℕ) : ℝ) < r := by exact_mod_cast hp
  have hpq : r.HolderConjugate (r / (r - 1)) :=
    Real.HolderConjugate.conjExponent (by linarith)
  have hγ : ((finiteMorreyHolderExponent 2 r Fact.out hp2 : NNReal) : ℝ) = 1 - 2 / r := by
    rw [finiteMorreyHolderExponent_coe,
      Real.coe_toNNReal _ (morreyExponent_ofReal_pos Fact.out hp2).le,
      morreyExponent_ofReal 2 hr0]
    norm_num
  let E := Extension.C1.extensionCLM (n := 2) (p := ENNReal.ofReal r) (Ω := Ω)
  let K : ℝ := finiteMorreyEmbeddingConstant 2 r (r / (r - 1)) * ‖E‖
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u
  have hFnorm : ‖finiteMorreyEmbedding Fact.out hp2 hpq (E u)‖ ≤ K * ‖u‖ := by
    calc
      ‖finiteMorreyEmbedding Fact.out hp2 hpq (E u)‖
          ≤ finiteMorreyEmbeddingConstant 2 r (r / (r - 1)) * ‖E u‖ :=
        norm_morreyHolderRepresentative_le Fact.out hp2 hpq (E u)
      _ ≤ finiteMorreyEmbeddingConstant 2 r (r / (r - 1)) * (‖E‖ * ‖u‖) := by
        gcongr
        · exact finiteMorreyEmbeddingConstant_nonneg 2 r (r / (r - 1))
        · exact E.le_opNorm u
      _ = K * ‖u‖ := by ring
  refine ⟨fun x ↦ finiteMorreyEmbedding Fact.out hp2 hpq (E u) x,
    (finiteMorreyEmbedding Fact.out hp2 hpq (E u)).continuous.continuousOn,
    finiteMorreyEmbeddingOn_ae hp2 hpq u, ?_, ?_⟩
  · intro x _hx
    calc
      |finiteMorreyEmbedding Fact.out hp2 hpq (E u) x|
          ≤ ‖finiteMorreyEmbedding Fact.out hp2 hpq (E u)‖ :=
        (finiteMorreyEmbedding Fact.out hp2 hpq (E u)).norm_apply_le x
      _ ≤ K * ‖u‖ := hFnorm
      _ ≤ max 1 K * ‖u‖ := by
        gcongr
        exact le_max_right _ _
  · intro x _hx y _hy
    have hF : |finiteMorreyEmbedding Fact.out hp2 hpq (E u) x -
        finiteMorreyEmbedding Fact.out hp2 hpq (E u) y| ≤
          ‖finiteMorreyEmbedding Fact.out hp2 hpq (E u)‖ * ‖x - y‖ ^ (1 - 2 / r) := by
      have h := (finiteMorreyEmbedding Fact.out hp2 hpq (E u)).holderWith.dist_le x y
      rw [Real.dist_eq, dist_eq_norm, hγ] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (HolderSpace.C0GammaOn.holderSeminorm_le_norm _) (Real.rpow_nonneg (norm_nonneg _) _))
    calc
      |finiteMorreyEmbedding Fact.out hp2 hpq (E u) x -
          finiteMorreyEmbedding Fact.out hp2 hpq (E u) y|
          ≤ ‖finiteMorreyEmbedding Fact.out hp2 hpq (E u)‖ * ‖x - y‖ ^ (1 - 2 / r) := hF
      _ ≤ (K * ‖u‖) * ‖x - y‖ ^ (1 - 2 / r) := by gcongr
      _ ≤ max 1 K * ‖u‖ * ‖x - y‖ ^ (1 - 2 / r) := by
        gcongr
        exact le_max_right _ _

/-- If `E` is a bounded extension operator from `W^{2,2}(Ω)` to `W^{2,2}(ℝ²)`, there is `C > 0`
such that every `u ∈ W^{2,2}(Ω)` agrees almost everywhere on `Ω` with a continuous
`f : ℝ² → ℝ` satisfying `|f x| ≤ C ‖u‖` for all `x`; the proof takes
`C = (3 / (2√π)) max 1 ‖E‖`. The Hölder
estimate is `sobolev_H2_holder_of_extension`.
-/
theorem sobolev_H2_continuousLInfinity_of_extension
    (Ω : Set (ℝ^2))
    (E : SobolevSpace.Extension.GraphSpace.Operator 2 2 2 Ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : W^{2,2}(Ω),
        ∃ f : (ℝ^2) → ℝ,
          Continuous f ∧
          f =ᵐ[SobolevSpace.domainMeasure 2 Ω]
            ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Ω)
              (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) ∧
          ∀ x : (ℝ^2), |f x| ≤ C * ‖u‖ := by
  let C0 : ℝ := 3 / (2 * Real.sqrt Real.pi)
  let C : ℝ := C0 * max 1 ‖E.toContinuousLinearMap‖
  have hC0 : 0 < C0 := by
    dsimp [C0]
    positivity
  have hmax : 0 < max 1 ‖E.toContinuousLinearMap‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := mul_pos hC0 hmax
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨f, hf, hrep, hpoint⟩ :=
    orderTwoSobolev_continuousRepresentative (E.toContinuousLinearMap u)
  have hrepΩ : f =ᵐ[domainMeasure 2 Ω]
      ((((E.toContinuousLinearMap u : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) := by
    filter_upwards [ae_restrict_of_ae (s := Ω) hrep] with x hx
    exact hx
  have hagree := E.agree_ae u
  have hrepU : f =ᵐ[domainMeasure 2 Ω]
      ((((u : GraphSpace.WkpAmbientOn 2 2 2 Ω)
        (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) := hrepΩ.trans hagree
  refine ⟨f, hf, hrepU, ?_⟩
  intro x
  calc
    |f x| ≤ C0 * ‖E.toContinuousLinearMap u‖ := by simpa [C0] using hpoint x
    _ ≤ C0 * (‖E.toContinuousLinearMap‖ * ‖u‖) := by
      exact mul_le_mul_of_nonneg_left (E.toContinuousLinearMap.le_opNorm u) hC0.le
    _ ≤ C0 * (max 1 ‖E.toContinuousLinearMap‖ * ‖u‖) := by
      gcongr
      exact le_max_right _ _
    _ = C * ‖u‖ := by simp [C]; ring

/-- If `E` is a bounded extension operator from `W^{2,2}(Ω)` to `W^{2,2}(ℝ²)` and `0 < γ < 1`,
there is `C > 0` such that every `u ∈ W^{2,2}(Ω)` agrees almost everywhere on `Ω` with a
continuous `f : ℝ² → ℝ` satisfying `|f x| ≤ C ‖u‖` and `|f x - f y| ≤ C ‖u‖ ‖x - y‖ ^ γ` for all
`x` and `y`.
-/
theorem sobolev_H2_holder_of_extension
    (Ω : Set (ℝ^2))
    (E : SobolevSpace.Extension.GraphSpace.Operator 2 2 2 Ω)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : W^{2,2}(Ω),
        ∃ f : (ℝ^2) → ℝ,
          Continuous f ∧
          f =ᵐ[SobolevSpace.domainMeasure 2 Ω]
            ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Ω)
              (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) ∧
          (∀ x : (ℝ^2), |f x| ≤ C * ‖u‖) ∧
          ∀ x y : (ℝ^2),
            |f x - f y| ≤ C * ‖u‖ * ‖x - y‖ ^ γ := by
  let Cpoint : ℝ := 3 / (2 * Real.sqrt Real.pi)
  let Cholder : ℝ :=
    (3 / Real.pi) * Real.sqrt (∫ ξ : (ℝ^2), PDE.Analysis.Fourier.orderTwoHolderKernel γ ξ ^ 2)
  let C0 : ℝ := max Cpoint Cholder
  let C : ℝ := C0 * max 1 ‖E.toContinuousLinearMap‖
  have hCpoint : 0 < Cpoint := by dsimp [Cpoint]; positivity
  have hC0 : 0 < C0 := lt_of_lt_of_le hCpoint (le_max_left _ _)
  have hmax : 0 < max 1 ‖E.toContinuousLinearMap‖ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := mul_pos hC0 hmax
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨f, hf, hrep, hholder⟩ :=
    orderTwoSobolev_holderRepresentative γ hγ0 hγ1 (E.toContinuousLinearMap u)
  have hpoint := orderTwoSobolev_pointwise_of_continuous_ae
    (E.toContinuousLinearMap u) f hf hrep
  have hrepΩ : f =ᵐ[domainMeasure 2 Ω]
      ((((E.toContinuousLinearMap u : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)
        (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) := by
    filter_upwards [ae_restrict_of_ae (s := Ω) hrep] with x hx
    exact hx
  have hrepU : f =ᵐ[domainMeasure 2 Ω]
      ((((u : GraphSpace.WkpAmbientOn 2 2 2 Ω)
        (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) :=
    hrepΩ.trans (E.agree_ae u)
  have hEnorm : ‖E.toContinuousLinearMap u‖ ≤ max 1 ‖E.toContinuousLinearMap‖ * ‖u‖ := by
    calc
      ‖E.toContinuousLinearMap u‖ ≤
          ‖E.toContinuousLinearMap‖ * ‖u‖ :=
        E.toContinuousLinearMap.le_opNorm u
      _ ≤ max 1 ‖E.toContinuousLinearMap‖ * ‖u‖ := by
        gcongr
        exact le_max_right _ _
  refine ⟨f, hf, hrepU, ?_, ?_⟩
  · intro x
    calc
      |f x| ≤ Cpoint * ‖E.toContinuousLinearMap u‖ := by simpa [Cpoint] using hpoint x
      _ ≤ Cpoint * (max 1 ‖E.toContinuousLinearMap‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left hEnorm hCpoint.le
      _ ≤ C0 * (max 1 ‖E.toContinuousLinearMap‖ * ‖u‖) := by
        gcongr
        exact le_max_left _ _
      _ = C * ‖u‖ := by simp [C]; ring
  · intro x y
    have hCholder : 0 ≤ Cholder := by dsimp [Cholder]; positivity
    have hD : 0 ≤ ‖x - y‖ ^ γ := Real.rpow_nonneg (norm_nonneg _) _
    calc
      |f x - f y| ≤ Cholder * ‖E.toContinuousLinearMap u‖ * ‖x - y‖ ^ γ := by
        simpa [Cholder] using hholder x y
      _ ≤ Cholder * (max 1 ‖E.toContinuousLinearMap‖ * ‖u‖) * ‖x - y‖ ^ γ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEnorm hCholder) hD
      _ ≤ C0 * (max 1 ‖E.toContinuousLinearMap‖ * ‖u‖) * ‖x - y‖ ^ γ := by
        gcongr
        exact le_max_right _ _
      _ = C * ‖u‖ * ‖x - y‖ ^ γ := by
        dsimp only [C]
        ring

/-- Choosing `q = 2/(2-γ)` makes its planar Sobolev conjugate equal to
`2/(1-γ)`, whose Morrey exponent is exactly `γ`.
-/
theorem sobolevHolderParameters (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    let q : NNReal := ⟨2 / (2 - γ), by
      have : 0 < 2 - γ := by linarith
      positivity⟩
    let p : ℝ≥0∞ := SobolevSpace.Inequalities.pStar 2 q
    (1 : NNReal) ≤ q ∧ (q : ℝ) < 2 ∧
      2 < p.toReal ∧ p ≠ ∞ ∧ 1 - 2 / p.toReal = γ := by
  dsimp
  let q : NNReal := ⟨2 / (2 - γ), by
    have : 0 < 2 - γ := by linarith
    positivity⟩
  have hden : 0 < 2 - γ := by linarith
  have hpEq : (2 / (2 - γ)) * 2 / (2 - 2 / (2 - γ)) = 2 / (1 - γ) := by cas
  have hγEq : 1 - 2 / (2 / (1 - γ)) = γ := by cas
  have hq1 : (1 : NNReal) ≤ q := by
    apply NNReal.coe_le_coe.mp
    change (1 : ℝ) ≤ 2 / (2 - γ)
    rw [le_div_iff₀ hden]
    linarith
  have hq2 : (q : ℝ) < 2 := by
    change 2 / (2 - γ) < (2 : ℝ)
    rw [div_lt_iff₀ hden]
    nlinarith
  have hpcoe := SobolevSpace.Inequalities.pStar_coe
    (n := 2) (p := q) (by norm_num) hq2
  have hpReal :
      ((SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞)).toReal =
        2 / (1 - γ) := by
    change (SobolevSpace.Inequalities.pStar 2 q : ℝ) = 2 / (1 - γ)
    rw [hpcoe]
    exact hpEq
  refine ⟨hq1, hq2, ?_, by simp, ?_⟩
  · change 2 < ((SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞)).toReal
    rw [hpReal]
    rw [lt_div_iff₀ (sub_pos.mpr hγ1)]
    linarith
  · change 1 - 2 / ((SobolevSpace.Inequalities.pStar 2 q : ℝ≥0∞)).toReal = γ
    rw [hpReal]
    exact hγEq

/-- `sobolev_H2_boundedC1Domain` for a positive exponent. -/
private theorem sobolev_H2_boundedC1Domain_of_pos
    (Ω : Set (ℝ^2)) [SobolevSpace.Boundary.C1ExtensionAtlas 2 Ω]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : W^{2,2}(Ω),
        ∃ f : (ℝ^2) → ℝ,
          ContinuousOn f (closure Ω) ∧
          f =ᵐ[SobolevSpace.domainMeasure 2 Ω]
            ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Ω)
              (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) ∧
          (∀ x ∈ closure Ω, |f x| ≤ C * ‖u‖) ∧
          ∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
            |f x - f y| ≤ C * ‖u‖ * ‖x - y‖ ^ γ := by
  let q : NNReal := ⟨2 / (2 - γ), by
    have : 0 < 2 - γ := by linarith
    positivity⟩
  let p : ℝ≥0∞ := SobolevSpace.Inequalities.pStar 2 q
  obtain ⟨hq1, hq2, hp2, _hpTop, hexp⟩ :=
    sobolevHolderParameters γ hγ0 hγ1
  have _ : Fact (1 ≤ p) := ⟨by
    dsimp [p]
    exact_mod_cast SobolevSpace.Inequalities.one_le_pStar
      (n := 2) (p := q) (by norm_num) hq1 hq2⟩
  let CB : ℝ := ‖GraphSpace.h2ToW1pOfC1ExtensionAtlasCLM
    (Ω := Ω) hq1 hq2 (p := p) (le_refl p)‖
  have hCB : 0 ≤ CB := by
    dsimp [CB]
    exact norm_nonneg (GraphSpace.h2ToW1pOfC1ExtensionAtlasCLM
      (Ω := Ω) hq1 hq2 (p := p) (le_refl p))
  have hbridge (u : W^{2,2}(Ω)) :
      ‖GraphSpace.h2ToW1pOfC1ExtensionAtlas
        (Ω := Ω) hq1 hq2 (p := p) (le_refl p) u‖ ≤ CB * ‖u‖ := by
    simpa [CB] using GraphSpace.norm_h2ToW1pOfC1ExtensionAtlas_le
      (Ω := Ω) hq1 hq2 (p := p) (le_refl p) u
  obtain ⟨CM, hCM, hmorrey⟩ :=
    morrey_boundedC1Domain p hp2 Ω
  let B : ℝ := max 1 CB
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let C : ℝ := CM * B
  have hC : 0 < C := mul_pos hCM hB
  refine ⟨C, hC, ?_⟩
  intro u
  let W : W^{1,p}(Ω) :=
    GraphSpace.h2ToW1pOfC1ExtensionAtlas (Ω := Ω) hq1 hq2 (le_refl p) u
  have hWnorm : ‖W‖ ≤ B * ‖u‖ := by
    calc
      ‖W‖ ≤ CB * ‖u‖ := by simpa [W] using hbridge u
      _ ≤ B * ‖u‖ := by
        gcongr
        exact le_max_right _ _
  obtain ⟨f, hfcont, hfrepW, hfpoint, hfholder⟩ := hmorrey W
  have hWU :
      ((((W : GraphSpace.WkpAmbientOn 2 1 p Ω)
        (GraphSpace.baseIndex 2 1)) : (ℝ^2) → ℝ)) =ᵐ[domainMeasure 2 Ω]
        ((((u : GraphSpace.WkpAmbientOn 2 2 2 Ω)
          (GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) := by
    have hcoord := GraphSpace.h2ToW1pOfC1ExtensionAtlas_apply_ae
      (Ω := Ω) hq1 hq2 (p := p) (le_refl p) u (GraphSpace.baseIndex 2 1)
    simpa [W, GraphSpace.derivativeSliceIndex, GraphSpace.baseIndex_toList] using hcoord
  refine ⟨f, hfcont, hfrepW.trans hWU, ?_, ?_⟩
  · intro x hx
    calc
      |f x| ≤ CM * ‖W‖ := hfpoint x hx
      _ ≤ CM * (B * ‖u‖) := mul_le_mul_of_nonneg_left hWnorm hCM.le
      _ = C * ‖u‖ := by dsimp only [C]; ring
  · intro x hx y hy
    have hpow : 0 ≤ ‖x - y‖ ^ γ := Real.rpow_nonneg (norm_nonneg _) _
    calc
      |f x - f y| ≤ CM * ‖W‖ * ‖x - y‖ ^ (1 - 2 / p.toReal) :=
        hfholder x hx y hy
      _ = CM * ‖W‖ * ‖x - y‖ ^ γ := by rw [hexp]
      _ ≤ CM * (B * ‖u‖) * ‖x - y‖ ^ γ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWnorm hCM.le) hpow
      _ = C * ‖u‖ * ‖x - y‖ ^ γ := by dsimp only [C]; ring

/--
For `γ < 1` and a domain `Ω ⊆ ℝ²` carrying an operational `C1ExtensionAtlas`, there is `C > 0`
such that every `u ∈ W^{2,2}(Ω)` has a representative `f`, continuous on `closure Ω`, with
`|f x| ≤ C ‖u‖` and `|f x - f y| ≤ C ‖u‖ ‖x - y‖ ^ γ` on `closure Ω`.

The proof first obtains a bounded coordinate-preserving inclusion
`H²(Ω) → W¹ᵖ(Ω)` from the closed graph theorem and then applies the completed
Morrey theorem at the exponent `p = 2/(1-γ)`. The atlas supplies openness and
boundedness; `HasC1GraphBoundary.nonempty_c1ExtensionAtlas` builds it from a `C¹` graph
boundary. For `γ ≤ 0` the exponent `1/2` and the finite diameter of `Ω` give the bound.
-/
theorem sobolev_H2_boundedC1Domain
    (Ω : Set (ℝ^2)) [SobolevSpace.Boundary.C1ExtensionAtlas 2 Ω]
    (γ : ℝ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : W^{2,2}(Ω),
        ∃ f : (ℝ^2) → ℝ,
          ContinuousOn f (closure Ω) ∧
          f =ᵐ[SobolevSpace.domainMeasure 2 Ω]
            ((((u : SobolevSpace.GraphSpace.WkpAmbientOn 2 2 2 Ω)
              (SobolevSpace.GraphSpace.baseIndex 2 2)) : (ℝ^2) → ℝ)) ∧
          (∀ x ∈ closure Ω, |f x| ≤ C * ‖u‖) ∧
          ∀ x ∈ closure Ω, ∀ y ∈ closure Ω,
            |f x - f y| ≤ C * ‖u‖ * ‖x - y‖ ^ γ := by
  rcases lt_or_ge 0 γ with hγ0 | hγ0
  · exact sobolev_H2_boundedC1Domain_of_pos Ω γ hγ0 hγ1
  obtain ⟨C₀, hC₀, h₀⟩ := sobolev_H2_boundedC1Domain_of_pos Ω (1 / 2) (by norm_num) (by norm_num)
  have hbdd : Bornology.IsBounded (closure Ω) :=
    (SobolevSpace.Boundary.C1ExtensionAtlas.bounded (n := 2) (Ω := Ω)).closure
  set D := max 1 (Metric.diam (closure Ω))
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hDγ : 0 < D ^ γ := Real.rpow_pos_of_pos hD γ
  have hm1 : 1 ≤ max 1 (2 / D ^ γ) := le_max_left _ _
  refine ⟨C₀ * max 1 (2 / D ^ γ), mul_pos hC₀ (lt_of_lt_of_le one_pos hm1), fun u ↦ ?_⟩
  obtain ⟨f, hfc, hfae, hfb, -⟩ := h₀ u
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  refine ⟨f, hfc, hfae, fun x hx ↦ (hfb x hx).trans
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₀.le hm1) hu0), fun x hx y hy ↦ ?_⟩
  have hsum : |f x - f y| ≤ 2 * C₀ * ‖u‖ := by
    have h1 := hfb x hx
    have h2 := hfb y hy
    calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ 2 * C₀ * ‖u‖ := by linarith
  rcases eq_or_ne x y with rfl | hxy
  · rw [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_pos hC₀ (lt_of_lt_of_le one_pos hm1)).le hu0)
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hdist : ‖x - y‖ ≤ D := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem hbdd hx hy).trans (le_max_right _ _)
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hpow : D ^ γ ≤ ‖x - y‖ ^ γ := Real.rpow_le_rpow_of_nonpos hpos hdist hγ0
  have hcancel : 2 / D ^ γ * D ^ γ = 2 := div_mul_cancel₀ 2 hDγ.ne'
  calc |f x - f y| ≤ 2 * C₀ * ‖u‖ := hsum
    _ = C₀ * (2 / D ^ γ) * ‖u‖ * D ^ γ := by
      rw [show C₀ * (2 / D ^ γ) * ‖u‖ * D ^ γ = C₀ * ‖u‖ * (2 / D ^ γ * D ^ γ) by ring,
        hcancel]
      ring
    _ ≤ C₀ * max 1 (2 / D ^ γ) * ‖u‖ * ‖x - y‖ ^ γ := by
      gcongr
      exact le_max_right _ _

end SobolevSpace
