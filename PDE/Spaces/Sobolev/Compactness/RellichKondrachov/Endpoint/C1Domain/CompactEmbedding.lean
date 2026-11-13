/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Subcritical.CompactEmbedding
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.L1.TranslationEstimate
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.L1.Compactness

/-!
# Rellich-Kondrachov on operational C¹ domains

The Rellich–Kondrachov theorem (Evans, §5.7, Theorem 1) states that for a bounded domain `Ω ⊆ ℝ^n`
with `C¹` boundary and `1 ≤ p < n`, the inclusion `W^{1,p}(Ω) ↪ L^q(Ω)` is compact for every
`q < p* = np/(n - p)`. We prove this for domains carrying the operational
`Boundary.C1ExtensionAtlas` data (the chart-and-cutoff hypothesis under which the `C¹` extension
theorem is proved in this library).

## Main results

* `supportedExtensionBaseCoordinateL1_isCompactOperator`: compactness of the
  supported extension followed by the base coordinate, into `L¹(ℝ^n)`.
* `baseCoordinateL1_isCompactOperator_of_c1Domain`,
  `inclusion_toL1_isCompactOperator_of_c1Domain`: the endpoint
  `W^{1,1}(Ω) → L¹(Ω)` is compact.
* `inclusion_isCompactOperator_of_compact_w11`: compactness of the `W^{1,1}`
  endpoint alone implies compactness of `W^{1,p}(Ω) → L^q(Ω)` for
  `1 ≤ p < n`, `1 ≤ q < p*`.
* `inclusion_isCompactOperator_of_c1Domain`: the full subcritical range with no
  compactness hypothesis.
* `inclusion_fromH1_isCompactOperator_of_c1Domain`: the Hilbert case
  `H¹(Ω) ↪ L^q(Ω)`, `q < 2*`, for `n > 2`.

## How it works

We go through the endpoint `p = 1`. The supported extension operator sends `W^{1,1}(Ω)` into
`W^{1,1}(ℝ^n)` with support in a fixed ball; the global `W^{1,1}` translation estimate and the
finite-rank cell averages of `Endpoint.L1.CellAverages` and `Endpoint.L1.GridApproximation` then
show that the image of the unit ball in `L¹(ℝ^n)` is totally bounded, which is the
Kolmogorov–Riesz–Fréchet mechanism. Restricting back gives compactness of `W^{1,1}(Ω) → L¹(Ω)`. For
general `p` we lower the exponent to `1`, use the endpoint, and upgrade `L¹` convergence to `L^q`
convergence for `q < p*` by the Vitali argument of `Subcritical.CompactEmbedding`, which relies on
the Gagliardo–Nirenberg–Sobolev bound in `L^{p*}`. Evans instead bounds the mollification error in
`L¹` uniformly in `m`, upgrades it to `L^q` with the interpolation inequality and the
Gagliardo–Nirenberg–Sobolev inequality, and concludes with the Arzelà–Ascoli theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1, pp. 286-288; the proof extends to compact
  support in a bounded set `V` (step 2), bounds `‖u_m^ε - u_m‖_{L¹(V)} ≤ ε C ‖Du_m‖_{L^p(V)}` (step
  4), interpolates to `L^q` and applies the Arzelà–Ascoli theorem (steps 5-6).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace
namespace GraphSpace
namespace RellichKondrachov

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-! ## Endpoint compactness on operational `C¹` extension domains -/

section C1Endpoint

variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- For a ball `B(0, R)` containing `closure Ω`, the supported global base coordinate of the
operational `C¹` extension is compact as a map into global `L¹`. This is the `L¹` endpoint,
proved by finite-rank grid approximation in the manner of the Kolmogorov–Riesz–Fréchet
criterion. -/
theorem supportedExtensionBaseCoordinateL1_isCompactOperator
    (R : ℝ) (hKR : closure Ω ⊆ Metric.ball (0 : ℝ^n) R) :
    let V : Set (ℝ^n) := Metric.ball (0 : ℝ^n) R
    let E : W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ]
        W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
      (Extension.C1.supportedOperator
        (n := n) (p := (1 : ℝ≥0∞)) (Ω := Ω)
        V Metric.isOpen_ball hKR).toOperator.toContinuousLinearMap
    IsCompactOperator
      ((wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := 1) (Ω := Set.univ)).comp E) := by
  dsimp only
  let V : Set (ℝ^n) := Metric.ball (0 : ℝ^n) R
  have hVopen : IsOpen V := Metric.isOpen_ball
  let supported :=
    Extension.C1.supportedOperator
      (n := n) (p := (1 : ℝ≥0∞)) (Ω := Ω)
      V hVopen hKR
  let E : W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ]
      W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
    supported.toOperator.toContinuousLinearMap
  let F : W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ]
      DerivLp n 1 Set.univ :=
    (wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 1) (Ω := Set.univ)).comp E
  let S : Set (DerivLp n 1 Set.univ) :=
    F '' Metric.closedBall
      (0 : W^{1,(1 : ℝ≥0∞)}(Ω)) 1
  have hSbounded : Bornology.IsBounded S :=
    Metric.isBounded_closedBall.image F
  have hsupport (U : W^{1,(1 : ℝ≥0∞)}(Ω)) :
      ∀ᵐ x ∂MeasureTheory.volume,
        x ∉ V → (F U : DerivLp n 1 Set.univ) x = 0 := by
    have hsupp := supported.supported_ae U
    have hsuppVol :
        V.indicator (fun x ↦ (F U : DerivLp n 1 Set.univ) x)
          =ᵐ[MeasureTheory.volume]
            fun x ↦ (F U : DerivLp n 1 Set.univ) x := by
      simpa [F, E, supported, wkpBaseCoordinateCLM,
        wkpCoordinateCLM, domainMeasure] using hsupp
    filter_upwards [hsuppVol] with x hx hxV
    rw [← hx, Set.indicator_of_notMem hxV]
  have htot : TotallyBounded S := by
    apply totallyBounded_L1_of_bounded_support_translation
      S hSbounded R ‖E‖ (norm_nonneg E)
    · rintro f ⟨U, _, rfl⟩
      exact hsupport U
    · rintro f ⟨U, hU, rfl⟩ h
      have hUnorm : ‖U‖ ≤ 1 := mem_closedBall_zero_iff.mp hU
      calc
        ‖Rellich.translateLp 1 h (F U) - F U‖ ≤ ‖h‖ * ‖E U‖ :=
          globalTranslationDefectL1.norm_le (n := n) h (E U)
        _ ≤ ‖h‖ * (‖E‖ * ‖U‖) :=
          mul_le_mul_of_nonneg_left (E.le_opNorm U) (norm_nonneg _)
        _ ≤ ‖h‖ * ‖E‖ := by
          exact mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_left hUnorm (norm_nonneg E)).trans_eq
              (mul_one ‖E‖)) (norm_nonneg _)
  change IsCompactOperator
    (F : W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ]
      DerivLp n 1 Set.univ)
  apply
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image F).2
  refine ⟨Metric.closedBall 0 1,
    Metric.closedBall_mem_nhds 0 (by norm_num), ?_⟩
  simpa [S] using
    htot.closure.isCompact_of_isClosed isClosed_closure

/-- **Rellich-Kondrachov endpoint on an operational `C¹` domain.**

The order-zero inclusion `W^{1,1}(Ω) → L¹(Ω)` is compact.  The proof uses
the supported extension furnished by the atlas, the global
`W^{1,1}` translation estimate, and finite-rank cell averages. -/
theorem baseCoordinateL1_isCompactOperator_of_c1Domain :
    IsCompactOperator
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := 1) (Ω := Ω)) := by
  let K : Set (ℝ^n) := closure Ω
  obtain ⟨R, hKR⟩ :=
    hΩ.bounded.isCompact_closure.isBounded.subset_ball (0 : ℝ^n)
  let V : Set (ℝ^n) := Metric.ball (0 : ℝ^n) R
  have hVopen : IsOpen V := Metric.isOpen_ball
  let supported :=
    Extension.C1.supportedOperator
      (n := n) (p := (1 : ℝ≥0∞)) (Ω := Ω)
      V hVopen hKR
  let E : W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ]
      W^{1,(1 : ℝ≥0∞)}(ℝ^n) :=
    supported.toOperator.toContinuousLinearMap
  let F : W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ]
      DerivLp n 1 Set.univ :=
    (wkpBaseCoordinateCLM
      (n := n) (m := 1) (p := 1) (Ω := Set.univ)).comp E
  have hFcompact : IsCompactOperator F := by
    simpa [F, E, supported, V] using
      supportedExtensionBaseCoordinateL1_isCompactOperator
        (n := n) (Ω := Ω) R hKR
  let restrict :
      DerivLp n 1 Set.univ →L[ℝ] DerivLp n 1 Ω :=
    restrictDerivLp (n := n) (p := (1 : ℝ≥0∞)) (subset_univ Ω)
  let compactMap :
      W^{1,(1 : ℝ≥0∞)}(Ω) →L[ℝ] DerivLp n 1 Ω :=
    restrict.comp F
  have hcompact : IsCompactOperator compactMap :=
    hFcompact.clm_comp restrict
  have heq :
      wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := 1) (Ω := Ω) =
        compactMap := by
    ext U
    have hagree := supported.toOperator.agree_ae U
    have hrestrict :=
      restrictDerivLp_apply_ae
        (n := n) (p := (1 : ℝ≥0∞)) (subset_univ Ω) (F U)
    filter_upwards [hagree, hrestrict] with x hagreeX hrestrictX
    simpa [compactMap, restrict, F, E, supported,
      wkpBaseCoordinateCLM, wkpCoordinateCLM] using
        (hrestrictX.trans hagreeX).symm
  rw [heq]
  exact hcompact

/-- Endpoint compactness stated through the general inclusion API. -/
theorem inclusion_toL1_isCompactOperator_of_c1Domain
    (hone_lt : (1 : ℝ) < (n : ℝ)) :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω)
        (p := (1 : NNReal)) (q := (1 : NNReal))
        hone_lt
        (Inequalities.le_pStar (n := n) hn.out hone_lt)) := by
  have heq :
      inclusion (n := n) (Ω := Ω)
          (p := (1 : NNReal)) (q := (1 : NNReal))
          hone_lt
          (Inequalities.le_pStar (n := n) hn.out hone_lt) =
        wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := 1) (Ω := Ω) := by
    ext U
    exact
      (inclusion_apply_ae (n := n) (Ω := Ω)
        (p := (1 : NNReal)) (q := (1 : NNReal))
        hone_lt
        (Inequalities.le_pStar (n := n) hn.out hone_lt) U).trans
        EventuallyEq.rfl
  rw [heq]
  exact baseCoordinateL1_isCompactOperator_of_c1Domain
    (n := n) (Ω := Ω)

end C1Endpoint

/-! ## Reduction to the `W^{1,1}` endpoint -/

section EndpointReduction

variable {p q : NNReal}
variable (hp_lt : (p : ℝ) < (n : ℝ))
variable (hq_lt : q < Inequalities.pStar n p)
variable [hpNN : Fact ((1 : NNReal) ≤ p)]
variable [hqNN : Fact ((1 : NNReal) ≤ q)]
variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

include hp_lt hq_lt

/-- On a domain with an operational `Boundary.C1ExtensionAtlas`, compactness of
`W^{1,1}(Ω) → L¹(Ω)` gives compactness of `W^{1,p}(Ω) → L^q(Ω)` whenever
`1 ≤ p < n` and `1 ≤ q < p*`, where `p* = np/(n - p)`.

Exponent lowering sends `W^{1,p}` continuously into `W^{1,1}`, so the endpoint
hypothesis gives convergence in `L¹`. The critical-exponent bound and the
strict-subcritical Vitali transfer upgrade this to convergence in `L^q`.
The concrete endpoint above supplies the hypothesis in the next theorem. -/
theorem inclusion_isCompactOperator_of_compact_w11
    (hW11 :
      IsCompactOperator
        (inclusion (n := n) (Ω := Ω)
          (p := (1 : NNReal)) (q := (1 : NNReal))
          (show (1 : ℝ) < (n : ℝ) by
            exact lt_of_le_of_lt
              (by exact_mod_cast hpNN.out) hp_lt)
          (Inequalities.le_pStar (n := n) hn.out
            (show (1 : ℝ) < (n : ℝ) by
              exact lt_of_le_of_lt
                (by exact_mod_cast hpNN.out) hp_lt)))) :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω) (p := p) (q := q)
        hp_lt hq_lt.le) := by
  have hone_lt : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast hpNN.out) hp_lt
  have hp_oneE :
      ((1 : NNReal) : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by
    exact_mod_cast hpNN.out
  let lower :
      W^{1,(p : ℝ≥0∞)}(Ω) →L[ℝ]
        W^{1,((1 : NNReal) : ℝ≥0∞)}(Ω) :=
    lowerExponentOfFiniteMeasureCLM
      (n := n) (k := 1) (Ω := Ω) hp_oneE
  let endpoint :
      W^{1,((1 : NNReal) : ℝ≥0∞)}(Ω) →L[ℝ]
        DerivLp n ((1 : NNReal) : ℝ≥0∞) Ω :=
    inclusion (n := n) (Ω := Ω)
      (p := (1 : NNReal)) (q := (1 : NNReal)) hone_lt
      (Inequalities.le_pStar (n := n) hn.out hone_lt)
  let compactOne :
      W^{1,(p : ℝ≥0∞)}(Ω) →L[ℝ]
        DerivLp n ((1 : NNReal) : ℝ≥0∞) Ω :=
    endpoint.comp lower
  have hcompactOne : IsCompactOperator compactOne :=
    hW11.comp_clm lower
  have hOneEq :
      inclusion (n := n) (Ω := Ω) (p := p) (q := (1 : NNReal))
          hp_lt
          ((show (1 : NNReal) ≤ p from hpNN.out).trans
            (Inequalities.le_pStar (n := n) hn.out hp_lt)) =
        compactOne := by
    ext U
    have hinc :=
      inclusion_apply_ae (n := n) (Ω := Ω)
        (p := p) (q := (1 : NNReal)) hp_lt
        (hpNN.out.trans
          (Inequalities.le_pStar (n := n) hn.out hp_lt)) U
    have hlower :=
      lowerExponentOfFiniteMeasure_apply_ae
        (n := n) (k := 1) (Ω := Ω) hp_oneE U (baseIndex n 1)
    have hlowerValue :
        lower U = lowerExponentOfFiniteMeasure hp_oneE U := by
      exact lowerExponentOfFiniteMeasureCLM_apply hp_oneE U
    have hendpoint :=
      inclusion_apply_ae (n := n) (Ω := Ω)
        (p := (1 : NNReal)) (q := (1 : NNReal))
        hone_lt
        (Inequalities.le_pStar (n := n) hn.out hone_lt)
        (lower U)
    have hlowerBase :
        baseRepresentative U =ᵐ[domainMeasure n Ω]
          baseRepresentative (lower U) := by
      rw [hlowerValue]
      exact hlower.symm
    have htail :
        baseRepresentative (lower U) =ᵐ[domainMeasure n Ω]
          ((compactOne U :
            DerivLp n ((1 : NNReal) : ℝ≥0∞) Ω) :
              ℝ^n → ℝ) := by
      dsimp only [compactOne, ContinuousLinearMap.comp_apply]
      exact hendpoint.symm
    exact hinc.trans (hlowerBase.trans htail)
  apply inclusion_isCompactOperator_of_compact_lower
    (n := n) (Ω := Ω) (p := p) (q := q)
    (s := (1 : NNReal)) hp_lt hq_lt
    (hpNN.out.trans
      (Inequalities.le_pStar (n := n) hn.out hp_lt))
  rw [hOneEq]
  exact hcompactOne

end EndpointReduction

/-! ## The full subcritical range -/

section FullRange

variable {p q : NNReal}
variable (hp_lt : (p : ℝ) < (n : ℝ))
variable (hq_lt : q < Inequalities.pStar n p)
variable [hpNN : Fact ((1 : NNReal) ≤ p)]
variable [hqNN : Fact ((1 : NNReal) ≤ q)]
variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

include hp_lt hq_lt

/-- **Rellich-Kondrachov in the full first-order subcritical range.**

On a bounded domain carrying the operational `Boundary.C1ExtensionAtlas`,

`W^{1,p}(Ω) ↪ L^q(Ω)`

is compact whenever `1 ≤ p < n` and `1 ≤ q < p*`, with `p* = np/(n - p)`.
This is the range of Evans §5.7, Theorem 1, including the endpoint exponents
`p = 1` and `q = 1`.  The proof lowers the
source exponent to `1`, invokes the concrete `W^{1,1} → L¹` endpoint proved by
supported extension and finite-cell averaging, and then applies the
strict-subcritical Vitali transfer. -/
theorem inclusion_isCompactOperator_of_c1Domain :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω) (p := p) (q := q)
        hp_lt hq_lt.le) := by
  have hone_lt : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast hpNN.out) hp_lt
  apply inclusion_isCompactOperator_of_compact_w11
    (n := n) (Ω := Ω) (p := p) (q := q) hp_lt hq_lt
  exact inclusion_toL1_isCompactOperator_of_c1Domain
    (n := n) (Ω := Ω) hone_lt

end FullRange

/-! ## The concrete `p = 2` Rellich-Kondrachov theorem -/

section HilbertBase

variable {q : NNReal}
variable (hn2 : (2 : ℝ) < (n : ℝ))
variable (hq_lt : q < Inequalities.pStar n (2 : NNReal))
variable [hqNN : Fact ((1 : NNReal) ≤ q)]
variable [hn : Fact (0 < n)]
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

include hn2 hq_lt

/-- **Rellich-Kondrachov on an operational `C¹` domain, Hilbert source.**

If `n > 2`, then

`H¹(Ω) ↪ L^q(Ω)`

is compact for every `1 ≤ q < 2* = 2n / (n - 2)`.

The compact base-coordinate map into `L²(Ω)`, together with
`inclusion_isCompactOperator_of_compact_base`, supplies every
strict-subcritical
target exponent. -/
theorem inclusion_fromH1_isCompactOperator_of_c1Domain :
    IsCompactOperator
      (inclusion (n := n) (Ω := Ω)
        (p := (2 : NNReal)) (q := q)
        hn2 hq_lt.le) := by
  have hbaseEq :
      inclusion (n := n) (Ω := Ω)
          (p := (2 : NNReal)) (q := (2 : NNReal))
          hn2 (Inequalities.le_pStar (n := n) hn.out hn2) =
        wkpBaseCoordinateCLM
          (n := n) (m := 1) (p := 2) (Ω := Ω) := by
    ext U
    exact
      (inclusion_apply_ae (n := n) (Ω := Ω)
        (p := (2 : NNReal)) (q := (2 : NNReal))
        hn2
        (Inequalities.le_pStar (n := n) (p := (2 : NNReal))
          hn.out hn2) U).trans
        EventuallyEq.rfl
  apply inclusion_isCompactOperator_of_compact_base
    (n := n) (Ω := Ω) (p := (2 : NNReal)) (q := q)
    hn2 hq_lt
  rw [hbaseEq]
  exact Rellich.baseCoordinateL2_isCompactOperator_of_c1Domain

end HilbertBase

end RellichKondrachov
end GraphSpace
end SobolevSpace
