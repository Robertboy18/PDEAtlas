/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
public import PDE.Analysis.MeasureTheory.LpNorm
public import PDE.Analysis.MeasureTheory.Lp.CompactEmbedding
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension
import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness -- shake: keep

/-!
# Rellich-Kondrachov compact embeddings

We prove the exponent-independent part of the Rellich–Kondrachov theorem (Evans, §5.7,
Theorem 1). The source is the weak-derivative graph space `WkpSpaceOn n 1 p Ω`; the target is
the ordinary `L^q(Ω)` space.

There are two logically distinct ingredients.

* Sobolev embedding and the closed graph theorem give a bounded linear
  inclusion `W^{1,p}(Ω) → L^q(Ω)` for every `q ≤ p*`.
* Compactness at the base exponent `q = p`, together with the strict
  inequality `q < p*`, upgrades compactness to every subcritical exponent.

The exponent-dependent input is compactness at one exponent, proved by finite-rank grid
approximation in the manner of the Kolmogorov–Riesz–Fréchet criterion; `Rellich` gives it at
`p = 2`. We prove the strict-subcritical transfer and the range `2 ≤ p < n`.
`RellichKondrachov.Endpoint.C1Domain.CompactEmbedding` treats `p = 1` and then obtains all
`1 ≤ p < n`, `1 ≤ q < p*`, the range of Evans §5.7, Theorem 1. Evans passes from `L¹` to `L^q`
estimates with the interpolation inequality for `L^p` norms and the Gagliardo–Nirenberg–Sobolev
inequality (step 4 of his proof); we use uniform integrability in `L^{p*}` and Vitali's
theorem.

## Main results

* `inclusion`: the bounded inclusion `W^{1,p}(Ω) → L^q(Ω)` for `q ≤ p*`,
  obtained from Sobolev membership by the closed graph theorem, with
  `inclusion_apply_ae`.
* `inclusion_isCompactOperator_of_compact_lower`,
  `inclusion_isCompactOperator_of_compact_base`: compactness at one target
  exponent `s ≤ p*` (in particular at `s = p`) implies compactness for every
  `q < p*`, by uniform integrability in `L^{p*}` and Vitali's theorem.
* `inclusion_toL2_isCompactOperator_of_two_le`: compactness into `L²(Ω)` in the
  range `2 ≤ p < n`, obtained by lowering to `H¹(Ω)` and using the `L²` Rellich
  theorem. Together with `inclusion_isCompactOperator_of_compact_lower` it gives
  every `1 ≤ q < p*`; the full range `1 ≤ p < n` is
  `inclusion_isCompactOperator_of_c1Domain` in `Endpoint.C1Domain.CompactEmbedding`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1, pp. 286-288; step 4 of the proof, p. 288,
  passes from `L¹` to `L^q`, `q < p*`, by the interpolation inequality and the
  Gagliardo–Nirenberg–Sobolev inequality.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace RellichKondrachov

open Filter Function MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-! ## Continuous subcritical inclusions -/

section Inclusion

variable {p q : NNReal}
variable (hp_lt : (p : ℝ) < (n : ℝ))
variable (hqStar : q ≤ Inequalities.pStar n p)
variable [hpNN : Fact ((1 : NNReal) ≤ p)]
variable [hqNN : Fact ((1 : NNReal) ≤ q)]
variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

include hp_lt hqStar

omit hqNN in
/-- The base representative of a `W^{1,p}(Ω)` value belongs to every
`L^q(Ω)` with `1 ≤ q ≤ p*` on a bounded operational `C¹` domain. -/
theorem baseRepresentative_memLp_of_le_pStar
    (U : W^{1,(p : ℝ≥0∞)}(Ω)) :
    MemLp (baseRepresentative U)
      (q : ℝ≥0∞) (domainMeasure n Ω) := by
  exact Extension.C1.memLp_of_le_pStar_of_sobolevSpaceOn
    (n := n) (Ω := Ω)
    hpNN.out hp_lt (toRepresentative U) (by exact_mod_cast hqStar)

/-- The algebraic inclusion `W^{1,p}(Ω) → L^q(Ω)` sending a Sobolev element to
its base representative. -/
noncomputable def inclusionLinearMap :
    W^{1,(p : ℝ≥0∞)}(Ω) →ₗ[ℝ]
      DerivLp n (q : ℝ≥0∞) Ω where
  toFun U := (baseRepresentative_memLp_of_le_pStar hp_lt hqStar U).toLp
    (baseRepresentative U)
  map_add' U V := by
    rw [← MemLp.toLp_add
      (baseRepresentative_memLp_of_le_pStar hp_lt hqStar U)
      (baseRepresentative_memLp_of_le_pStar hp_lt hqStar V)]
    apply MemLp.toLp_congr
    exact baseRepresentative_add_ae U V
  map_smul' c U := by
    change (baseRepresentative_memLp_of_le_pStar hp_lt hqStar (c • U)).toLp
      (baseRepresentative (c • U)) =
        c • (baseRepresentative_memLp_of_le_pStar hp_lt hqStar U).toLp
          (baseRepresentative U)
    rw [← MemLp.toLp_const_smul c
      (baseRepresentative_memLp_of_le_pStar hp_lt hqStar U)]
    apply MemLp.toLp_congr
    exact baseRepresentative_smul_ae c U

omit hqNN in
private theorem inclusionLinearMap_apply_ae
    (U : W^{1,(p : ℝ≥0∞)}(Ω)) :
    ((inclusionLinearMap hp_lt hqStar U :
      DerivLp n (q : ℝ≥0∞) Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        baseRepresentative U :=
  (baseRepresentative_memLp_of_le_pStar hp_lt hqStar U).coeFn_toLp

/-- The subcritical algebraic inclusion has sequentially closed graph.
Convergence in the Sobolev norm gives convergence of the base coordinate in
`L^p`; convergence in the target gives convergence in `L^q`.  Both imply
convergence in measure, whose limit is unique almost everywhere. -/
theorem inclusionLinearMap_seq_closed_graph
    (U : ℕ → W^{1,(p : ℝ≥0∞)}(Ω))
    (Ulim : W^{1,(p : ℝ≥0∞)}(Ω))
    (v : DerivLp n (q : ℝ≥0∞) Ω)
    (hU : Tendsto U atTop (𝓝 Ulim))
    (hv : Tendsto (inclusionLinearMap hp_lt hqStar ∘ U)
      atTop (𝓝 v)) :
    v = inclusionLinearMap hp_lt hqStar Ulim := by
  let baseP :=
    wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)
  have hbaseP : Tendsto (baseP ∘ U) atTop (𝓝 (baseP Ulim)) :=
    baseP.continuous.continuousAt.tendsto.comp hU
  have hpMeasure :
      TendstoInMeasure (domainMeasure n Ω)
        (fun m ↦ (baseP (U m) : ℝ^n → ℝ)) atTop
        (baseP Ulim : ℝ^n → ℝ) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hbaseP
  have hqMeasure :
      TendstoInMeasure (domainMeasure n Ω)
        (fun m ↦
          (inclusionLinearMap hp_lt hqStar (U m) :
            ℝ^n → ℝ)) atTop (v : ℝ^n → ℝ) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hv
  have hsame :
      (v : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        (baseP Ulim : ℝ^n → ℝ) := by
    have hseq (m : ℕ) :
        (baseP (U m) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          (inclusionLinearMap hp_lt hqStar (U m) : ℝ^n → ℝ) := by
      change baseRepresentative (U m) =ᵐ[domainMeasure n Ω]
        (inclusionLinearMap hp_lt hqStar (U m) : ℝ^n → ℝ)
      exact (inclusionLinearMap_apply_ae hp_lt hqStar (U m)).symm
    have hpMeasure' :
        TendstoInMeasure (domainMeasure n Ω)
          (fun m ↦
            (inclusionLinearMap hp_lt hqStar (U m) : ℝ^n → ℝ))
          atTop (baseP Ulim : ℝ^n → ℝ) :=
      hpMeasure.congr hseq Filter.EventuallyEq.rfl
    exact MeasureTheory.tendstoInMeasure_ae_unique hqMeasure hpMeasure'
  apply MeasureTheory.Lp.ext
  exact hsame.trans
    (inclusionLinearMap_apply_ae hp_lt hqStar Ulim).symm

/-- The continuous inclusion `W^{1,p}(Ω) → L^q(Ω)` for
`1 ≤ p < n` and `1 ≤ q ≤ p*`.

The closed graph theorem supplies the operator bound from the
Sobolev membership theorem. -/
noncomputable def inclusion :
    W^{1,(p : ℝ≥0∞)}(Ω) →L[ℝ]
      DerivLp n (q : ℝ≥0∞) Ω :=
  ContinuousLinearMap.ofSeqClosedGraph
    (inclusionLinearMap_seq_closed_graph hp_lt hqStar)

/-- The continuous Sobolev inclusion preserves the base representative
almost everywhere. -/
theorem inclusion_apply_ae
    (U : W^{1,(p : ℝ≥0∞)}(Ω)) :
    ((inclusion hp_lt hqStar U :
      DerivLp n (q : ℝ≥0∞) Ω) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        baseRepresentative U :=
  inclusionLinearMap_apply_ae hp_lt hqStar U

end Inclusion

/-! ## Strict-subcritical compactness -/

section Compactness

variable {p q : NNReal}
variable (hp_lt : (p : ℝ) < (n : ℝ))
variable (hq_lt : q < Inequalities.pStar n p)
variable [hpNN : Fact ((1 : NNReal) ≤ p)]
variable [hqNN : Fact ((1 : NNReal) ≤ q)]
variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

include hp_lt hq_lt

/-- Strict-subcritical compactness from compactness at any lower target.

Assume `W^{1,p}(Ω) → L^s(Ω)` is compact for one exponent
`1 ≤ s ≤ p*`.  Then the inclusion into `L^q(Ω)` is compact for every
`1 ≤ q < p*`.

The proof is the standard Rellich-Kondrachov upgrade.  A bounded Sobolev
sequence has an `L^s`-convergent subsequence by the compactness hypothesis.
Sobolev embedding bounds that subsequence in `L^{p*}`.  Since `q < p*`,
the preceding uniform-integrability estimate and Vitali's theorem improve
convergence in measure to convergence in `L^q`. -/
theorem inclusion_isCompactOperator_of_compact_lower
    {s : NNReal} [hsNN : Fact ((1 : NNReal) ≤ s)]
    (hsStar : s ≤ Inequalities.pStar n p)
    (hbase :
      IsCompactOperator
        (inclusion (n := n) (Ω := Ω) (p := p) (q := s)
          hp_lt hsStar)) :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω) (p := p) (q := q)
        hp_lt hq_lt.le) := by
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hsNN.out⟩
  have hstar : (1 : NNReal) ≤ Inequalities.pStar n p :=
    Inequalities.one_le_pStar (n := n) hn.out hpNN.out hp_lt
  have : Fact ((1 : NNReal) ≤ Inequalities.pStar n p) := ⟨hstar⟩
  have : Fact (1 ≤ (Inequalities.pStar n p : ℝ≥0∞)) := ⟨by exact_mod_cast hstar⟩
  exact hbase.into_Lp_of_higher_exponent
    (inclusion hp_lt hq_lt.le) (inclusion hp_lt le_rfl) hq_lt
    (fun u ↦ (inclusion_apply_ae hp_lt hsStar u).trans
      (inclusion_apply_ae hp_lt hq_lt.le u).symm)
    (fun u ↦ (inclusion_apply_ae hp_lt le_rfl u).trans
      (inclusion_apply_ae hp_lt hq_lt.le u).symm)

/-- Compactness of the base inclusion `W^{1,p}(Ω) → L^p(Ω)` implies every
strict-subcritical Rellich-Kondrachov embedding. -/
theorem inclusion_isCompactOperator_of_compact_base
    (hbase :
      IsCompactOperator
        (inclusion (n := n) (Ω := Ω) (p := p) (q := p) hp_lt
          (Inequalities.le_pStar (n := n) hn.out hp_lt))) :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω) (p := p) (q := q)
        hp_lt hq_lt.le) :=
  inclusion_isCompactOperator_of_compact_lower hp_lt hq_lt
    (Inequalities.le_pStar (n := n) hn.out hp_lt) hbase

end Compactness

/-! ## The range `2 ≤ p < n` -/

section AtLeastTwoSource

variable {p q : NNReal}
variable (hp_two : (2 : NNReal) ≤ p)
variable (hp_lt : (p : ℝ) < (n : ℝ))
variable (hq_lt : q < Inequalities.pStar n p)
variable [hpNN : Fact ((1 : NNReal) ≤ p)]
variable [hqNN : Fact ((1 : NNReal) ≤ q)]
variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

include hp_two hp_lt

/-- For `2 ≤ p < n`, the inclusion `W^{1,p}(Ω) → L²(Ω)` is compact.

The source first lowers continuously to `H¹(Ω)`; the
operational-domain Rellich theorem then compactly forgets the derivative
coordinates. -/
theorem inclusion_toL2_isCompactOperator_of_two_le :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω) (p := p) (q := (2 : NNReal))
        hp_lt
        (hp_two.trans
          (Inequalities.le_pStar (n := n) hn.out hp_lt))) := by
  have hp_twoE :
      ((2 : NNReal) : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by
    exact_mod_cast hp_two
  let lower :
      W^{1,(p : ℝ≥0∞)}(Ω) →L[ℝ] H¹(Ω) :=
    lowerExponentOfFiniteMeasureCLM
      (n := n) (k := 1) (Ω := Ω) hp_twoE
  let compactTwo :
      W^{1,(p : ℝ≥0∞)}(Ω) →L[ℝ]
        DerivLp n 2 Ω :=
    (wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 2) (Ω := Ω)).comp lower
  have hcompactTwo : IsCompactOperator compactTwo :=
    Rellich.baseCoordinateL2_isCompactOperator_of_c1Domain.comp_clm lower
  have heq :
      inclusion (n := n) (Ω := Ω) (p := p) (q := (2 : NNReal))
          hp_lt
          (hp_two.trans
            (Inequalities.le_pStar (n := n) hn.out hp_lt)) =
        compactTwo := by
    ext U
    have hinc :=
      inclusion_apply_ae (n := n) (Ω := Ω)
        (p := p) (q := (2 : NNReal)) hp_lt
        (hp_two.trans
          (Inequalities.le_pStar (n := n) hn.out hp_lt)) U
    have hlower :=
      lowerExponentOfFiniteMeasure_apply_ae
        (n := n) (k := 1) (Ω := Ω) hp_twoE U (baseIndex n 1)
    have hlowerValue :
        lower U = lowerExponentOfFiniteMeasure hp_twoE U := by
      exact lowerExponentOfFiniteMeasureCLM_apply hp_twoE U
    have hright :
        baseRepresentative U =ᵐ[domainMeasure n Ω]
          ((compactTwo U : DerivLp n 2 Ω) : ℝ^n → ℝ) := by
      dsimp only [compactTwo, ContinuousLinearMap.comp_apply]
      change
        (((U : WkpAmbientOn n 1 (p : ℝ≥0∞) Ω)
            (baseIndex n 1) : DerivLp n (p : ℝ≥0∞) Ω) :
              ℝ^n → ℝ)
          =ᵐ[domainMeasure n Ω]
            ((((lower U : H¹(Ω)) :
                  WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
                    DerivLp n 2 Ω) : ℝ^n → ℝ)
      rw [hlowerValue]
      exact hlower.symm
    exact hinc.trans hright
  rw [heq]
  exact hcompactTwo

end AtLeastTwoSource

end RellichKondrachov
end GraphSpace
end SobolevSpace
