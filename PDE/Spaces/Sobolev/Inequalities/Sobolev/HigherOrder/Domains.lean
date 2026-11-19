/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.OneDimensionalCritical
import PDE.Spaces.Sobolev.Localization.Cutoff.ExponentRestriction

/-!
# Higher-order Sobolev embeddings on domains

For `u ∈ W^{k,p}(Ω)` with `kp < n`, the general Sobolev inequality gives `u ∈ L^q(Ω)` with
`1/q = 1/p - k/n`, and on a bounded domain `u ∈ L^r(Ω)` for every `r ≤ q`. At the critical
relation `kp = n`, with `n ≥ 1` and `Ω` bounded, one gets `u ∈ L^q(Ω)` and a uniform norm bound
for every `1 ≤ q < ∞`. We prove these statements for the graph-space model `WkpSpaceOn`:
the boundary regularity of `Ω` enters only through a bounded extension operator
`E : W^{k,p}(Ω) → W^{k,p}(ℝ^n)` agreeing with `u` almost everywhere on `Ω`. Whole-space
embeddings, compactly supported localization, and restriction give the domain conclusions.

The extension operator is a hypothesis (`Extension.GraphSpace.Operator n k p Ω`) in the general
theorems. For domains carrying `Boundary.C1ExtensionAtlas` the library constructs the first-order
extension itself, and the `_of_c1ExtensionAtlas` corollaries take no extension argument.

Evans, PDE, §5.6.3, Theorem 6(i), proves the subcritical case on a bounded `C¹` domain by applying
the Gagliardo-Nirenberg-Sobolev inequality on the domain to the derivatives of order `k - 1`, then
`k - 2`, and so on; we use a `W^{k,p}` extension operator and the whole-space embedding instead. The
critical case `kp = n` is handled by localizing a global first-order field to `W^{1,s}(ℝ^n)` for
`1 ≤ s < n` and applying the Gagliardo-Nirenberg-Sobolev inequality.

## Main results

* `memLp_higherOrderExponent_of_extension`, `memLp_of_inv_eq_of_extension`,
  `memLp_of_le_higherOrderExponent_of_extension`: the subcritical case `kp < n`, at the endpoint
  exponent `np/(n-kp)` and, on bounded domains, at every lower exponent.
* `norm_extended_subcritical_le`: the operator-norm estimate for the subcritical embedding
  composed with the extension.
* `memLp_critical_dimension_of_extension`, `memLp_pStar_of_critical_extension`,
  `memLp_critical_finite_of_extension`: the critical case `kp = n`, giving `L^n`, then `L^{s*}`
  for each `1 ≤ s < n`, and finally every finite `q ≥ 1`. In dimension one, the bounded
  continuous representative gives the stronger `L∞` conclusion.
* `memLp_top_of_oneDimensional_extension`: `W^{1,1}(Ω) ⊆ L∞(Ω)` on a one-dimensional
  extension domain, without assuming boundedness of `Ω`.
* `criticalEmbeddingCLM`, `eLpNorm_critical_le`,
  `exists_pos_critical_eLpNorm_bound_of_extension`: the bounded critical inclusion and its
  uniform norm estimate for every finite `q ≥ 1`.
* `exists_pos_critical_dimension_eLpNorm_bound_of_extension`: the `L^n` norm estimate,
  requiring neither boundedness of the domain nor `n ≥ 2`.
* `memLp_critical_firstOrder_of_c1ExtensionAtlas`,
  `memLp_firstOrderSobolevExponent_of_c1ExtensionAtlas`,
  `memLp_of_le_firstOrderSobolevExponent_of_c1ExtensionAtlas`: first-order corollaries on `C¹`
  extension domains, with the extension built from the atlas.

## Implementation notes

The critical proof first places the global extension in `W^{1,n}`. A smooth cutoff equal
to one near the bounded domain gives finite-measure support, permitting exponent restriction
to `W^{1,s}` and the global first-order embedding. Thus the general critical theorems require
only boundedness and the extension operator, with no boundary atlas.

The closed graph theorem upgrades the membership to a bounded map: convergence in
both Sobolev and target norms implies convergence in measure of the same base function.
Its operator norm supplies the constant, without a numerical formula. On open domains,
uniqueness of weak derivatives makes this map injective.

Some membership statements allow exponents below `1`, because the raw predicate
`MeasureTheory.MemLp` makes sense there. The bounded inclusions use the Banach range `q ≥ 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6(i), (29)-(30), pp. 284-285, and step 1 of
  its proof, p. 285.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Inequalities

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

section Domains

open SobolevSpace.GraphSpace

variable {n k : ℕ} {p : NNReal} {Ω : Set (ℝ^n)}

/-- Bounded-domain higher-order Sobolev embedding under an explicit
order-`k` extension operator.

This is Evans §5.6.3, Theorem 6(i), with the geometric boundary hypothesis
factored through the precise analytic object it supplies: a bounded linear
extension `W^{k,p}(Ω) → W^{k,p}(ℝ^n)` agreeing with the original function
almost everywhere on `Ω`. -/
theorem memLp_higherOrderExponent_of_extension
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      (higherOrderExponent n k p : ℝ≥0∞)
      (domainMeasure n Ω) := by
  have hglobal :=
    memLp_higherOrderExponent hp hn hsub (E.toContinuousLinearMap U)
  have hrestricted :
      MemLp
        ((((E.toContinuousLinearMap U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ)
          (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Set.univ) :
            ℝ^n → ℝ))
        (higherOrderExponent n k p : ℝ≥0∞)
        (domainMeasure n Ω) := by
    simpa [domainMeasure] using hglobal.restrict Ω
  exact (memLp_congr_ae (E.agree_ae U)).mp hrestricted

/-- Domain embedding under an order-`k` extension operator, with the target
exponent specified by `1/q = 1/p - k/n`. -/
theorem memLp_of_inv_eq_of_extension
    {q : NNReal}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    (hq : (q : ℝ)⁻¹ =
      (p : ℝ)⁻¹ - (k : ℝ) * (n : ℝ)⁻¹)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      (q : ℝ≥0∞) (domainMeasure n Ω) := by
  have hp0nn : (0 : NNReal) < p :=
    lt_of_lt_of_le (by norm_num) hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp0nn
  rw [eq_higherOrderExponent_of_inv_eq hp0 hsub hq]
  exact memLp_higherOrderExponent_of_extension
     hp hn hsub E U

/-- On a bounded domain, the extension argument gives every lower
integrability exponent as well.

This contains the full Banach-space range in Evans, *Partial Differential
Equations*, 2nd ed., §5.6.3, Theorem 6(i): after obtaining the endpoint
`q = np/(n-kp)`, finite measure gives all `1 ≤ r ≤ q`. Because the conclusion
is the raw Mathlib predicate `MemLp`, the theorem remains valid for exponents
`r < 1`; interpreting it as a Banach-space embedding requires `1 ≤ r`. -/
theorem memLp_of_le_higherOrderExponent_of_extension
    {r : ℝ≥0∞}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    (hΩ : Bornology.IsBounded Ω)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω))
    (hr : r ≤ (higherOrderExponent n k p : ℝ≥0∞)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      r (domainMeasure n Ω) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hΩ
  exact
    (memLp_higherOrderExponent_of_extension
       hp hn hsub E U).mono_exponent hr

/-- Quantitative estimate for the chosen global extension of a
bounded-domain Sobolev field.

Together with a.e. agreement on `Ω` and monotonicity under restriction,
this is the completed-space norm estimate produced by the operational
extension method:

`‖I (E u)‖_{L^q(ℝ^n)} ≤ ‖I‖ ‖E‖ ‖u‖_{W^{k,p}(Ω)}`.

Here `q = np/(n-kp)`, and both constants are operator norms of the continuous
linear maps `I` and `E`. -/
theorem norm_extended_subcritical_le
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n k p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    ‖subcriticalEmbeddingCLM hp hn hsub (E.toContinuousLinearMap U)‖ ≤
      ‖subcriticalEmbeddingCLM hp hn hsub‖ *
        ‖E.toContinuousLinearMap‖ * ‖U‖ := by
  calc
    ‖subcriticalEmbeddingCLM hp hn hsub (E.toContinuousLinearMap U)‖
        ≤ ‖subcriticalEmbeddingCLM hp hn hsub‖ * ‖E.toContinuousLinearMap U‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖subcriticalEmbeddingCLM hp hn hsub‖ *
          (‖E.toContinuousLinearMap‖ * ‖U‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm E.toContinuousLinearMap U
    _ = ‖subcriticalEmbeddingCLM hp hn hsub‖ *
          ‖E.toContinuousLinearMap‖ * ‖U‖ := by ring

/-- Critical higher-order embedding into a first-order Sobolev-conjugate space.

If `kp=n` and `1 ≤ s<n`, an order-`k` extension supplies a global `W^{1,n}`
field. A smooth cutoff equal to one near the bounded domain gives all its
coordinates finite-measure support, so they belong to `L^s`. The whole-space
first-order embedding then yields `L^{s*}` on the domain. No boundary atlas
is required once the extension operator is supplied. -/
theorem memLp_pStar_of_critical_extension
    {s : NNReal}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n)
    (hs1 : (1 : NNReal) ≤ s) (hsn : (s : ℝ) < n)
    (hΩ : Bornology.IsBounded Ω)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    MemLp (baseRepresentative U) (pStar n s : ℝ≥0∞) (domainMeasure n Ω) := by
  have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1⟩
  have : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast hn⟩
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hp
  have hpred : ((k - 1 : ℕ) : ℝ) * p < n := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    nlinarith
  have hexponent := higherOrderExponent_pred_eq_dimension hk hp0 hcrit
  let EU := E.toContinuousLinearMap U
  let d : DerivIndex n 1 → ℝ^n → ℝ := fun a ↦
    ((EU : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ)
      (a.castOrder (by omega)) : DerivLp n (p : ℝ≥0∞) Set.univ)
  have hmem (a : DerivIndex n 1) :
      MemLp (d a) (n : ℝ≥0∞) (domainMeasure n Set.univ) := by
    have hword : a.toList.length + (k - 1) ≤ k := by
      have := a.toList_length_le
      omega
    have hglobal := memLp_derivativeWord_higherOrderExponent
      hp hn hpred a.toList hword EU
    rw [hexponent] at hglobal
    have hindex : derivIndexOfList (n := n) a.toList (by omega) =
        a.castOrder (by omega : 1 ≤ k) :=
      derivIndexOfList_toList (a.castOrder (by omega)) _
    simpa [d, domainMeasure, hindex] using hglobal
  have hweak (a : DerivIndex n 1) :
      HasWeakDerivativeOn (n := n) Set.univ a.toList (d (baseIndex n 1)) (d a) := by
    have ha := EU.property (a.castOrder (by omega : 1 ≤ k))
    rw [DerivIndex.castOrder_toList] at ha
    simpa [d] using ha
  let V : W^{1,(n : ℝ≥0∞)}(ℝ^n) :=
    mkWkpSpaceOnOfWeakDerivatives (d (baseIndex n 1)) d rfl hmem hweak
  have hV : baseRepresentative V =ᵐ[domainMeasure n Set.univ] baseRepresentative EU := by
    simpa [V, d, baseRepresentative] using
      mkWkpSpaceOnOfWeakDerivatives_apply_ae
        (d (baseIndex n 1)) d rfl hmem hweak (baseIndex n 1)
  obtain ⟨ψ, -, hψone, -⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ hΩ.isCompact_closure (Set.subset_univ (closure Ω))
  have hsnE : (s : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hsn.le
  let W := lowerExponentOfFiniteMeasureSupport hsnE (tsupport ψ.toFun)
    (cutoff_tsupport_measure_ne_top ψ)
    (cutoffCLM (Ω := Set.univ) ψ V) (cutoff_all_coordinates_supported ψ V)
  have hW : baseRepresentative W =ᵐ[domainMeasure n Set.univ]
      fun x ↦ ψ.toFun x * baseRepresentative EU x := by
    have hrestrict := lowerExponentOfFiniteMeasureSupport_apply_ae
      hsnE (tsupport ψ.toFun) (cutoff_tsupport_measure_ne_top ψ)
      (cutoffCLM (Ω := Set.univ) ψ V) (cutoff_all_coordinates_supported ψ V)
      (baseIndex n 1)
    filter_upwards [hrestrict, cutoffCLM_base_apply_ae ψ V, hV] with x hx hcut hbase
    exact hx.trans (hcut.trans (congrArg (ψ.toFun x * ·) hbase))
  have hs0 : 0 < (s : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hs1
  have hglobal := memLp_of_inv_eq (k := 1) hs1 hn (by simpa using hsn)
    (by simpa using inv_pStar_eq hn hs0 hsn) W
  have hWΩ : baseRepresentative W =ᵐ[domainMeasure n Ω] baseRepresentative U := by
    have hW' : baseRepresentative W =ᵐ[volume]
        fun x ↦ ψ.toFun x * baseRepresentative EU x := by
      simpa [domainMeasure] using hW
    have hone : ∀ᵐ x ∂domainMeasure n Ω, ψ.toFun x = 1 :=
      ae_restrict_of_ae_restrict_of_subset subset_closure
        (ae_restrict_of_forall_mem isClosed_closure.measurableSet hψone)
    filter_upwards [hW'.restrict (s := Ω), hone, E.agree_ae U] with x hx hψ hE
    simpa only [hψ, one_mul, baseRepresentative] using
      hx.trans (congrArg (ψ.toFun x * ·) hE)
  exact (memLp_congr_ae hWΩ).mp (by
    simpa [globalBaseFunction, baseRepresentative, domainMeasure] using hglobal.restrict Ω)

/-- At the critical relation `kp=n`, every extended order-`k` field belongs
to `L^n` on the domain.

This is the `(k-1)`-order subcritical embedding applied to the base
coordinate. No boundedness assumption on `Ω` is needed for this endpoint. -/
theorem memLp_critical_dimension_of_extension
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      (n : ℝ≥0∞) (domainMeasure n Ω) := by
  have hp0nn : (0 : NNReal) < p :=
    lt_of_lt_of_le (by norm_num) hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp0nn
  have hpred : ((k - 1 : ℕ) : ℝ) * p < n := by
    have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))]
      norm_num
    rw [hkcast]
    nlinarith
  have hexponent :
      higherOrderExponent n (k - 1) p = (n : NNReal) :=
    higherOrderExponent_pred_eq_dimension hk hp0 hcrit
  have hword : ([] : List (Fin n)).length + (k - 1) ≤ k := by
    simp
  have hglobal :=
    memLp_derivativeWord_higherOrderExponent
      (n := n) (p := p) (m := k) (r := k - 1)
       hp hn hpred ([] : List (Fin n)) hword (E.toContinuousLinearMap U)
  rw [hexponent] at hglobal
  have hrestricted :
      MemLp
        ((((E.toContinuousLinearMap U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ)
          (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Set.univ) :
            ℝ^n → ℝ))
        (n : ℝ≥0∞) (domainMeasure n Ω) := by
    simpa [domainMeasure] using hglobal.restrict Ω
  exact (memLp_congr_ae (E.agree_ae U)).mp hrestricted

/-- At `kp=n`, the `L^n` norm has a uniform bound even on unbounded extension
domains. This endpoint holds in every positive dimension. -/
theorem exists_pos_critical_dimension_eLpNorm_bound_of_extension
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,(p : ℝ≥0∞)}(Ω),
      eLpNorm (baseRepresentative U) (n : ℝ≥0∞) (domainMeasure n Ω) ≤
        ENNReal.ofReal (C * ‖U‖) := by
  have : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast hn⟩
  apply exists_pos_eLpNorm_bound_of_memLp
  intro U
  simpa only [baseRepresentative] using
    memLp_critical_dimension_of_extension hp hn hk hcrit E U

/-- The low-exponent half of the critical conclusion on bounded domains:
`kp=n` implies membership in every `L^q` with `q≤n`.

The `MemLp` conclusion holds for every such `q`, including `q < 1`. -/
theorem memLp_critical_of_le_dimension_of_extension
    {q : ℝ≥0∞}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n)
    (hΩ : Bornology.IsBounded Ω)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω))
    (hq : q ≤ (n : ℝ≥0∞)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      q (domainMeasure n Ω) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hΩ
  exact
    (memLp_critical_dimension_of_extension
       hp hn hk hcrit E U).mono_exponent hq

/-- In dimension one an extension gives a bounded representative even at
`p=1`. No boundedness of the domain is required for the `L∞` conclusion. -/
theorem memLp_top_of_oneDimensional_extension
    {Ω : Set (ℝ^1)}
    (E : Extension.GraphSpace.Operator 1 1 1 Ω)
    (U : W^{1,1}(Ω)) :
    MemLp (baseRepresentative U) ∞ (domainMeasure 1 Ω) := by
  obtain ⟨F, hF, _⟩ :=
    CriticalOneDimensional.exists_boundedContinuousRepresentative (E.toContinuousLinearMap U)
  have hmem : MemLp (fun x ↦ F x) ∞ (domainMeasure 1 Ω) :=
    memLp_top_of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall F.norm_coe_le_norm)
  exact hmem.ae_eq ((hF.restrict (s := Ω)).trans (E.agree_ae U))

/-- The critical case `kp = n` of the general Sobolev inequalities (Evans §5.6.3).

Let `n≥1`, `k>0`, `1≤p`, and `kp=n`. On a bounded domain with a supplied
order-`k` extension operator, every `W^{k,p}` field belongs to `L^q(Ω)`
for every finite `q≥1`.

When `n=1`, criticality forces `k=p=1`, and the bounded representative supplies
every finite exponent. In higher dimensions, finite-measure monotonicity handles
`q≤n`. For `q>n`, the choice `s=nq/(n+q)` gives `1≤s<n`; the localized global
`W^{1,s}` field then satisfies the first-order Sobolev theorem.
The bounded inclusion and norm estimate are given below by
`criticalEmbeddingCLM` and `exists_pos_critical_eLpNorm_bound_of_extension`. -/
theorem memLp_critical_finite_of_extension
    {q : NNReal}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n)
    (hq1 : (1 : NNReal) ≤ q)
    (hΩ : Bornology.IsBounded Ω)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      (q : ℝ≥0∞) (domainMeasure n Ω) := by
  by_cases hn1 : n = 1
  · subst n
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hk1 : k = 1 := by
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hkR' : (k : ℝ) ≤ 1 := by
        norm_num at hcrit
        nlinarith
      have : k ≤ 1 := by exact_mod_cast hkR'
      omega
    subst k
    have hp1 : p = 1 := by
      apply NNReal.coe_injective
      simpa using hcrit
    subst p
    have : IsFiniteMeasure (domainMeasure 1 Ω) :=
      isFiniteMeasure_domainMeasure_of_isBounded hΩ
    exact (memLp_top_of_oneDimensional_extension E U).mono_exponent le_top
  have hn2 : 2 ≤ n := by omega
  by_cases hqn : q ≤ (n : NNReal)
  · exact memLp_critical_of_le_dimension_of_extension
       hp hn hk hcrit hΩ E U
        (by exact_mod_cast hqn)
  · have hnq : (n : ℝ) < q := by
      exact_mod_cast lt_of_not_ge hqn
    have hq0 : 0 < (q : ℝ) := by
      have hq0nn : (0 : NNReal) < q :=
        lt_of_lt_of_le (by norm_num) hq1
      exact_mod_cast hq0nn
    let s := pStarPreimage n q
    have hs1 : (1 : NNReal) ≤ s :=
      one_le_pStarPreimage hn2 hnq
    have hsn : (s : ℝ) < n :=
      pStarPreimage_lt_dimension hn hq0
    rw [← pStar_pStarPreimage hn hq0]
    exact memLp_pStar_of_critical_extension
       hp hn hk hcrit hs1 hsn hΩ E U

/-- The critical inclusion `W^{k,p}(Ω) → L^q(Ω)` for every `1 ≤ q < ∞`,
under `kp=n`, `n≥1`, boundedness of `Ω`, and a supplied order-`k` extension.
Continuity follows from the closed graph theorem after the whole-space
embedding and cutoff argument establish membership. -/
def criticalEmbeddingCLM
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n) (hΩ : Bornology.IsBounded Ω)
    (hq : q ≠ ∞)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω) :
    W^{k,(p : ℝ≥0∞)}(Ω) →L[ℝ] Lp ℝ q (domainMeasure n Ω) :=
  embeddingCLMOfMemLp fun U ↦ by
    have hq1 : (1 : NNReal) ≤ q.toNNReal := by
      apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_one, ENNReal.coe_toNNReal hq] using
        (Fact.out : 1 ≤ q)
    simpa only [ENNReal.coe_toNNReal hq, baseRepresentative] using
      memLp_critical_finite_of_extension hp hn hk hcrit hq1 hΩ E U

/-- The critical inclusion represents the original Sobolev function. -/
@[simp]
theorem criticalEmbeddingCLM_apply
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n) (hΩ : Bornology.IsBounded Ω)
    (hq : q ≠ ∞)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    (criticalEmbeddingCLM hp hn hk hcrit hΩ hq E U : ℝ^n → ℝ) =
      baseRepresentative U :=
  rfl

/-- On an open domain, the critical map is an inclusion: its base function
determines all weak derivatives. -/
theorem criticalEmbeddingCLM_injective
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n) (hΩ : Bornology.IsBounded Ω)
    (hq : q ≠ ∞) (hΩopen : IsOpen Ω)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω) :
    Function.Injective (criticalEmbeddingCLM hp hn hk hcrit hΩ hq E) := by
  intro U V h
  have hbase : baseRepresentative U = baseRepresentative V := by
    simpa only [criticalEmbeddingCLM_apply] using
      congrArg (fun f : Lp ℝ q (domainMeasure n Ω) ↦ (f : ℝ^n → ℝ)) h
  apply wkpBaseCoordinateCLM_injective hΩopen
  apply Lp.ext
  filter_upwards [] with x
  exact congrFun hbase x

/-- Evans's critical norm estimate with the norm of the constructed inclusion.
The constant depends on the domain and exponents, and is uniform in `U`. -/
theorem eLpNorm_critical_le
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n) (hΩ : Bornology.IsBounded Ω)
    (hq : q ≠ ∞)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    eLpNorm (baseRepresentative U) q (domainMeasure n Ω) ≤
      ENNReal.ofReal (‖criticalEmbeddingCLM hp hn hk hcrit hΩ hq E‖ * ‖U‖) :=
  eLpNorm_le_embeddingCLMOfMemLp _ U

/-- At `kp=n`, each finite `q≥1` admits a positive constant `C` such that
`‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{k,p}(Ω)}` for every `u`. The extension remains
explicit; the norm bound is a conclusion of the embedding. -/
theorem exists_pos_critical_eLpNorm_bound_of_extension
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hk : 0 < k)
    (hcrit : (k : ℝ) * p = n) (hΩ : Bornology.IsBounded Ω)
    (hq : q ≠ ∞)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n k (p : ℝ≥0∞) Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,(p : ℝ≥0∞)}(Ω),
      eLpNorm (baseRepresentative U) q (domainMeasure n Ω) ≤
        ENNReal.ofReal (C * ‖U‖) :=
  exists_pos_eLpNorm_bound_of_memLp fun U ↦ by
    simpa only [criticalEmbeddingCLM_apply] using
      Lp.memLp (criticalEmbeddingCLM hp hn hk hcrit hΩ hq E U)

/-- The critical first-order embedding on a domain carrying `Boundary.C1ExtensionAtlas`.

The extension operator is the one constructed from the atlas (Evans §5.4), so it is not a
hypothesis. Thus `W^{1,n}(Ω) ⊆ L^q(Ω)` for every finite `q≥1` in every positive dimension. -/
theorem memLp_critical_firstOrder_of_c1ExtensionAtlas
    {q : NNReal}
    (hq1 : (1 : NNReal) ≤ q)
    [Fact (0 < n)]
    [Fact (1 ≤ (n : ℝ≥0∞))]
    [hAtlas : Boundary.C1ExtensionAtlas n Ω]
    (U : W^{1,(n : ℝ≥0∞)}(Ω)) :
    MemLp
      (((U : WkpAmbientOn n 1 (n : ℝ≥0∞) Ω)
        (baseIndex n 1) : DerivLp n (n : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      (q : ℝ≥0∞) (domainMeasure n Ω) := by
  have hn1 : (1 : NNReal) ≤ (n : NNReal) := by
    exact_mod_cast (Fact.out : 0 < n)
  have : Fact (1 ≤ ((n : NNReal) : ℝ≥0∞)) :=
    ⟨by exact_mod_cast hn1⟩
  apply memLp_critical_finite_of_extension
    (n := n) (k := 1) (p := (n : NNReal)) (Ω := Ω)
     hn1 Fact.out (by omega) (by norm_num) hq1 hAtlas.bounded
    (Extension.C1.operator
      (n := n) (p := (n : ℝ≥0∞)) (Ω := Ω)) U

/-- The first-order Sobolev embedding on a bounded domain with an atlas.

For a domain carrying a `Boundary.C1ExtensionAtlas`, Evans's
reflection-and-partition construction supplies the extension operator, so it
is not an additional hypothesis. -/
theorem memLp_firstOrderSobolevExponent_of_c1ExtensionAtlas
    (hp : (1 : NNReal) ≤ p)
    (hsub : (p : ℝ) < n)
    [Fact (0 < n)] [Fact (1 ≤ (p : ℝ≥0∞))]
    [Boundary.C1ExtensionAtlas n Ω]
    (U : W^{1,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      (((U : WkpAmbientOn n 1 (p : ℝ≥0∞) Ω)
        (baseIndex n 1) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      (higherOrderExponent n 1 p : ℝ≥0∞)
      (domainMeasure n Ω) := memLp_higherOrderExponent_of_extension
     hp Fact.out (by simpa using hsub)
      (Extension.C1.operator
        (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)) U

/-- Every lower finite-measure exponent is available from the concrete
first-order `C¹` extension construction. -/
theorem memLp_of_le_firstOrderSobolevExponent_of_c1ExtensionAtlas
    {r : ℝ≥0∞}
    (hp : (1 : NNReal) ≤ p)
    (hsub : (p : ℝ) < n)
    [Fact (0 < n)] [Fact (1 ≤ (p : ℝ≥0∞))]
    [hAtlas : Boundary.C1ExtensionAtlas n Ω]
    (U : W^{1,(p : ℝ≥0∞)}(Ω))
    (hr : r ≤ (higherOrderExponent n 1 p : ℝ≥0∞)) :
    MemLp
      (((U : WkpAmbientOn n 1 (p : ℝ≥0∞) Ω)
        (baseIndex n 1) : DerivLp n (p : ℝ≥0∞) Ω) :
          ℝ^n → ℝ)
      r (domainMeasure n Ω) := memLp_of_le_higherOrderExponent_of_extension
     hp Fact.out (by simpa using hsub) hAtlas.bounded
      (Extension.C1.operator
        (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)) U hr

end Domains

end Inequalities
end SobolevSpace
