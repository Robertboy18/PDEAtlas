/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.Domain
public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent

/-!
# The boundary-distance quotient on `W^{1,p}_0`

For every real `p > 1`, the smooth-core estimate in `Hardy.Domain` extends division
by distance to the frontier to a bounded linear map from `W^{1,p}_0(Ω)` to `Lᵖ(Ω)`.
The domain carries the same operational `C¹` atlas as the smooth-core theorem.

The extension preserves every admissible graph-norm constant. Almost-everywhere
convergent subsequences of both the function and its quotient identify the completed
operator with literal division of the Sobolev representative by boundary distance.
Poincaré then gives a bound involving only the vector-valued weak gradient.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Hardy

open MeasureTheory Set Filter
open GraphSpace
open scoped ENNReal NNReal Topology Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The smooth-core Hardy estimate makes the boundary-distance quotient an `Lᵖ` function. -/
theorem memLp_domainDistanceQuotient (hp : 1 < p) (φ : TestFunctionOn n Ω) :
    MemLp (domainDistanceQuotient φ) (ENNReal.ofReal p) (domainMeasure n Ω) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eLpNorm_domainDistanceQuotient_le_graphNorm (n := n) (Ω := Ω) hp
  exact (hbound φ).trans_lt (ENNReal.mul_lt_top hC.lt_top enorm_lt_top)

/-- Literal division by boundary distance on the smooth core, as an `Lᵖ(Ω)` class. -/
noncomputable def hardyDomainTestQuotient (hp : 1 < p) (φ : TestFunctionOn n Ω) :
    Lp ℝ (ENNReal.ofReal p) (domainMeasure n Ω) :=
  (memLp_domainDistanceQuotient hp φ).toLp (domainDistanceQuotient φ)

/-- The smooth-core quotient class has the expected almost-everywhere representative. -/
theorem hardyDomainTestQuotient_apply_ae (hp : 1 < p) (φ : TestFunctionOn n Ω) :
    (hardyDomainTestQuotient hp φ : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      domainDistanceQuotient φ :=
  (memLp_domainDistanceQuotient hp φ).coeFn_toLp

/-- The `Lᵖ` norm of the smooth quotient is its literal quotient seminorm. -/
theorem norm_hardyDomainTestQuotient (hp : 1 < p) (φ : TestFunctionOn n Ω) :
    ‖hardyDomainTestQuotient hp φ‖ =
      (eLpNorm (domainDistanceQuotient φ) (ENNReal.ofReal p)
        (domainMeasure n Ω)).toReal :=
  Lp.norm_toLp _ _

/-- Division by boundary distance is linear on the smooth supported core. -/
noncomputable def hardyDomainTestQuotientLinear (hp : 1 < p) :
    TestFunctionOn n Ω →ₗ[ℝ] Lp ℝ (ENNReal.ofReal p) (domainMeasure n Ω) where
  toFun := hardyDomainTestQuotient hp
  map_add' φ ψ := by
    apply Lp.ext
    filter_upwards [hardyDomainTestQuotient_apply_ae hp (φ + ψ),
      hardyDomainTestQuotient_apply_ae hp φ, hardyDomainTestQuotient_apply_ae hp ψ,
      Lp.coeFn_add (hardyDomainTestQuotient hp φ) (hardyDomainTestQuotient hp ψ)]
      with x hsum hφ hψ hadd
    rw [hsum, hadd, Pi.add_apply, hφ, hψ]
    exact add_div _ _ _
  map_smul' c φ := by
    apply Lp.ext
    filter_upwards [hardyDomainTestQuotient_apply_ae hp (c • φ),
      hardyDomainTestQuotient_apply_ae hp φ,
      Lp.coeFn_smul c (hardyDomainTestQuotient hp φ)] with x hsmul hφ hcoe
    rw [hsmul, RingHom.id_apply, hcoe, Pi.smul_apply, hφ]
    exact mul_div_assoc _ _ _

/-- A finite smooth-core constant also bounds the quotient as a map into `Lᵖ`. -/
theorem hardyDomainTestQuotientLinear_bound (hp : 1 < p) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ φ : TestFunctionOn n Ω,
      eLpNorm (domainDistanceQuotient φ) (ENNReal.ofReal p) (domainMeasure n Ω) ≤
        C * ‖testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ‖ₑ)
    (φ : TestFunctionOn n Ω) :
    ‖hardyDomainTestQuotientLinear hp φ‖ ≤
      C.toReal * ‖testFunctionToWkp0 (k := 1) (p := ENNReal.ofReal p) φ‖ := by
  change ‖hardyDomainTestQuotient hp φ‖ ≤
    C.toReal * ‖testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ‖
  rw [norm_hardyDomainTestQuotient]
  simpa only [ENNReal.toReal_mul, toReal_enorm] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hC enorm_ne_top) (hbound φ)

/-- The boundary-distance quotient on the completed zero-boundary Sobolev space. -/
noncomputable def hardyDomainW1p0Quotient (hp : 1 < p) :
    W₀^{1,(ENNReal.ofReal p)}(Ω) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (domainMeasure n Ω) :=
  (hardyDomainTestQuotientLinear hp).extendOfNorm
    (testFunctionToWkp0Linear (n := n) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω))

/-- The completed quotient agrees with the original quotient on every test function. -/
theorem hardyDomainW1p0Quotient_testFunction (hp : 1 < p) (φ : TestFunctionOn n Ω) :
    hardyDomainW1p0Quotient hp
        (testFunctionToWkp0 (k := 1) (p := ENNReal.ofReal p) φ) =
      hardyDomainTestQuotient hp φ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eLpNorm_domainDistanceQuotient_le_graphNorm (n := n) (Ω := Ω) hp
  exact LinearMap.extendOfNorm_eq
    (denseRange_testFunctionToWkp0Linear (n := n) (k := 1)
      (p := ENNReal.ofReal p) (Ω := Ω))
    ⟨C.toReal, hardyDomainTestQuotientLinear_bound hp hC hbound⟩ φ

/-- Completion preserves any finite graph-norm constant from the smooth-core estimate. -/
theorem norm_hardyDomainW1p0Quotient_le_of_testFunctions (hp : 1 < p)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ φ : TestFunctionOn n Ω,
      eLpNorm (domainDistanceQuotient φ) (ENNReal.ofReal p) (domainMeasure n Ω) ≤
        C * ‖testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ‖ₑ)
    (u : W₀^{1,(ENNReal.ofReal p)}(Ω)) :
    ‖hardyDomainW1p0Quotient hp u‖ ≤ C.toReal * ‖u‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (denseRange_testFunctionToWkp0Linear (n := n) (k := 1)
      (p := ENNReal.ofReal p) (Ω := Ω)) C.toReal
    (hardyDomainTestQuotientLinear_bound hp hC hbound) u

/-- The completed operator is almost everywhere the quotient of the Sobolev
representative by distance to the frontier. -/
theorem hardyDomainW1p0Quotient_apply_ae (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}(Ω)) :
    (hardyDomainW1p0Quotient hp u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ baseRepresentative (u : W^{1,ENNReal.ofReal p}(Ω)) x /
        Metric.infDist x (frontier Ω) := by
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_testFunctionToWkp0Linear (n := n) (k := 1)
      (p := ENNReal.ofReal p) (Ω := Ω) u)
  choose φ hφ using hv
  have hlim : Tendsto
      (fun j ↦ testFunctionToWkp0 (k := 1) (p := ENNReal.ofReal p) (φ j))
      atTop (𝓝 u) := by
    change Tendsto (fun j ↦ v j) atTop (𝓝 u) at hvlim
    simpa only [← hφ, testFunctionToWkp0Linear, LinearMap.coe_mk, AddHom.coe_mk] using hvlim
  have hbase := ((wkpBaseCoordinateCLM (n := n) (m := 1)
    (p := ENNReal.ofReal p) (Ω := Ω)).continuous.tendsto u.val).comp
      (continuous_subtype_val.tendsto u |>.comp hlim)
  obtain ⟨s, hs, hbaseAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hbase).exists_seq_tendsto_ae
  have hquot := ((hardyDomainW1p0Quotient (n := n) (Ω := Ω) hp).continuous.tendsto u).comp
    (hlim.comp hs.tendsto_atTop)
  obtain ⟨t, ht, hquotAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hquot).exists_seq_tendsto_ae
  have hcore (j : ℕ) :
      (hardyDomainW1p0Quotient hp
          (testFunctionToWkp0 (k := 1) (p := ENNReal.ofReal p) (φ j)) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ wkpBaseCoordinateCLM
          (testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) (φ j)) x /
            Metric.infDist x (frontier Ω) := by
    rw [hardyDomainW1p0Quotient_testFunction]
    have hb := testFunctionToWkp_coordinate_ae (k := 1) (p := ENNReal.ofReal p)
      (φ j) (baseIndex n 1)
    filter_upwards [hardyDomainTestQuotient_apply_ae hp (φ j), hb] with x hq hb
    simp only [baseIndex_toList, iteratedPartialDeriv] at hb
    simpa only [domainDistanceQuotient, wkpBaseCoordinateCLM_apply, hb] using hq
  filter_upwards [hbaseAE, hquotAE, ae_all_iff.mpr hcore] with x hb hq hc
  apply tendsto_nhds_unique hq
  exact ((hb.comp ht.tendsto_atTop).div_const (Metric.infDist x (frontier Ω))).congr'
    (Eventually.of_forall fun j ↦ (hc (s (t j))).symm)

/-- The literal boundary-distance quotient of every zero-boundary Sobolev function
belongs to `Lᵖ(Ω)`. -/
theorem memLp_div_infDist_frontier (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}(Ω)) :
    MemLp
      (fun x ↦ baseRepresentative (u : W^{1,ENNReal.ofReal p}(Ω)) x /
        Metric.infDist x (frontier Ω))
      (ENNReal.ofReal p) (domainMeasure n Ω) :=
  (memLp_congr_ae (hardyDomainW1p0Quotient_apply_ae hp u)).mp
    (Lp.memLp (hardyDomainW1p0Quotient hp u))

/-- The norm of the quotient class is the seminorm of the literal quotient. -/
theorem eLpNorm_div_infDist_frontier_eq_enorm (hp : 1 < p)
    (u : W₀^{1,(ENNReal.ofReal p)}(Ω)) :
    eLpNorm
      (fun x ↦ baseRepresentative (u : W^{1,ENNReal.ofReal p}(Ω)) x /
        Metric.infDist x (frontier Ω))
      (ENNReal.ofReal p) (domainMeasure n Ω) =
        ‖hardyDomainW1p0Quotient hp u‖ₑ := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae (hardyDomainW1p0Quotient_apply_ae hp u).symm

/-- The literal completed quotient satisfies the same graph-norm estimate as the
smooth core, with no enlargement of the constant. -/
theorem eLpNorm_div_infDist_frontier_le_of_testFunctions (hp : 1 < p)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ φ : TestFunctionOn n Ω,
      eLpNorm (domainDistanceQuotient φ) (ENNReal.ofReal p) (domainMeasure n Ω) ≤
        C * ‖testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ‖ₑ)
    (u : W₀^{1,(ENNReal.ofReal p)}(Ω)) :
    eLpNorm
      (fun x ↦ baseRepresentative (u : W^{1,ENNReal.ofReal p}(Ω)) x /
        Metric.infDist x (frontier Ω))
      (ENNReal.ofReal p) (domainMeasure n Ω) ≤ C * ‖u‖ₑ := by
  rw [eLpNorm_div_infDist_frontier_eq_enorm hp]
  simpa only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ofReal_norm (hardyDomainW1p0Quotient hp u), ofReal_norm u,
    ENNReal.ofReal_toReal hC] using! ENNReal.ofReal_le_ofReal
      (norm_hardyDomainW1p0Quotient_le_of_testFunctions hp hC hbound u)

/-- The boundary-distance Hardy inequality on the completed space, at every finite
real exponent `p > 1`, with the full Sobolev graph norm. -/
theorem exists_eLpNorm_div_infDist_frontier_le_graphNorm (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : W₀^{1,(ENNReal.ofReal p)}(Ω),
      eLpNorm
        (fun x ↦ baseRepresentative (u : W^{1,ENNReal.ofReal p}(Ω)) x /
          Metric.infDist x (frontier Ω))
        (ENNReal.ofReal p) (domainMeasure n Ω) ≤ C * ‖u‖ₑ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eLpNorm_domainDistanceQuotient_le_graphNorm (n := n) (Ω := Ω) hp
  exact ⟨C, hC, eLpNorm_div_infDist_frontier_le_of_testFunctions hp hC hbound⟩

/-- On the bounded atlas domain, Poincaré removes the zeroth-order term from the
completed Hardy estimate. The gradient is a single Euclidean-valued `Lᵖ` field. -/
theorem exists_norm_hardyDomainW1p0Quotient_le_gradient (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W₀^{1,(ENNReal.ofReal p)}(Ω),
      ‖hardyDomainW1p0Quotient hp u‖ ≤
        (C : ℝ) * ‖∇ (u : W^{1,ENNReal.ofReal p}(Ω))‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eLpNorm_domainDistanceQuotient_le_graphNorm (n := n) (Ω := Ω) hp
  have hP : ∃ K : ℝ≥0, ∀ u : W₀^{1,(ENNReal.ofReal p)}(Ω),
      ‖u‖ ≤ (K : ℝ) * ‖∇ u.val‖ := by
    have hpNN : 1 ≤ p.toNNReal := Real.one_le_toNNReal.mpr hp.le
    have : Fact (1 ≤ (p.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hpNN⟩
    convert! (exists_norm_le_wkpGradientCLM (Fact.out : 0 < n) hΩ.bounded hpNN) using 1
  obtain ⟨K, hK⟩ := hP
  refine ⟨C.toNNReal * K, fun u ↦ ?_⟩
  calc
    ‖hardyDomainW1p0Quotient hp u‖ ≤ C.toReal * ‖u‖ :=
      norm_hardyDomainW1p0Quotient_le_of_testFunctions hp hC hbound u
    _ ≤ C.toReal * ((K : ℝ) * ‖∇ u.val‖) :=
      mul_le_mul_of_nonneg_left (hK u) ENNReal.toReal_nonneg
    _ = (↑(C.toNNReal * K) : ℝ) * ‖∇ u.val‖ := by
      rw [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal, mul_assoc]

/-- The general-domain Hardy inequality for the literal quotient, controlled only
by the weak gradient, for every `u ∈ W^{1,p}_0(Ω)` and real `p > 1`. -/
theorem exists_eLpNorm_div_infDist_frontier_le_gradient (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W₀^{1,(ENNReal.ofReal p)}(Ω),
      eLpNorm
        (fun x ↦ baseRepresentative (u : W^{1,ENNReal.ofReal p}(Ω)) x /
          Metric.infDist x (frontier Ω))
        (ENNReal.ofReal p) (domainMeasure n Ω) ≤
          C * ‖∇ (u : W^{1,ENNReal.ofReal p}(Ω))‖ₑ := by
  obtain ⟨C, hC⟩ := exists_norm_hardyDomainW1p0Quotient_le_gradient (n := n) (Ω := Ω) hp
  refine ⟨C, fun u ↦ ?_⟩
  rw [eLpNorm_div_infDist_frontier_eq_enorm hp]
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hC u)

end SobolevSpace.Hardy
