/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.ExponentLift
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.WkpExtensionByZero
public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge

/-!
# Sobolev inequality with zero boundary values

For bounded open `Ω`, `1 ≤ p < n`, and `1 ≤ q ≤ np/(n-p)`, the weak gradient
controls the `Lᑫ(Ω)` norm of every element of `W^{1,p}_0(Ω)`. This is Evans
§5.6.1, Theorem 3, including `p = 1` and the critical target exponent.

The source is the closure of compactly supported smooth functions in
the Sobolev graph norm. Its zero extension and the global GNS theorem
give `L^{p*}` membership of the original representative. Finite measure gives
the lower exponents. The closed graph theorem makes this inclusion continuous,
and the finite-exponent Poincaré inequality removes the zeroth-order norm.
No boundary regularity is required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, Theorem 3, pp. 279-280.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- Zero boundary values give the critical Sobolev integrability on any
measurable domain, including the source exponent `p = 1`. -/
theorem memLp_baseRepresentative_Wkp0_pStar
    (hΩ : MeasurableSet Ω) (hp : 1 ≤ p) (hpn : (p : ℝ) < n)
    (u : W₀^{1,p}(Ω)) :
    MemLp (baseRepresentative (u : W^{1,p}(Ω)))
      (Inequalities.pStar n p) (domainMeasure n Ω) := by
  have hn : 0 < n := by exact_mod_cast p.2.trans_lt hpn
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  have hglobal := Inequalities.memLp_pStar_of_sobolevSpace hp hn
    (Inequalities.inv_pStar_eq hn hp0 hpn)
    (toRepresentative (ZeroTrace.zeroExtendWkp0 hΩ u))
  have hbase := restrictDerivLp_apply_ae (subset_univ Ω)
    (wkpCoordinateCLM (baseIndex n 1) (ZeroTrace.zeroExtendWkp0 hΩ u))
  rw [ZeroTrace.restrict_zeroExtendWkp0_coordinate] at hbase
  exact MemLp.ae_eq hbase.symm (hglobal.mono_measure Measure.restrict_le_self)

/-- On a measurable domain of finite measure, every exponent below the
critical Sobolev exponent is attained by the same zero-boundary representative. -/
theorem memLp_baseRepresentative_Wkp0
    (hΩ : MeasurableSet Ω) [IsFiniteMeasure (domainMeasure n Ω)]
    (hp : 1 ≤ p) (hpn : (p : ℝ) < n) {q : ℝ≥0∞}
    (hq : q ≤ Inequalities.pStar n p) (u : W₀^{1,p}(Ω)) :
    MemLp (baseRepresentative (u : W^{1,p}(Ω))) q (domainMeasure n Ω) :=
  (memLp_baseRepresentative_Wkp0_pStar hΩ hp hpn u).mono_exponent hq

/-- The Sobolev inclusion of `W^{1,p}_0(Ω)` into `Lᑫ(Ω)` as a bounded linear map.
Its continuity follows from GNS integrability and the closed graph theorem. -/
def wkp0LpEmbedding
    (hΩ : MeasurableSet Ω) [IsFiniteMeasure (domainMeasure n Ω)]
    (hp : 1 ≤ p) (hpn : (p : ℝ) < n) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≤ Inequalities.pStar n p) :
    W₀^{1,p}(Ω) →L[ℝ] DerivLp n q Ω :=
  let J : W₀^{1,p}(Ω) →L[ℝ] DerivLp n p Ω :=
    wkpBaseCoordinateCLM.comp
    (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := 1) (p := p)
      (Ω := Ω)).toSubmodule)
  ContinuousLinearMap.liftLpExponent (α := ℝ^n) (𝕜 := ℝ)
    (E := W₀^{1,p}(Ω)) (F := ℝ) (μ := domainMeasure n Ω) (p := p) (q := q) J
    (fun u ↦ memLp_baseRepresentative_Wkp0 hΩ hp hpn hq u)

/-- The Sobolev inclusion preserves the original function almost everywhere. -/
theorem wkp0LpEmbedding_ae
    (hΩ : MeasurableSet Ω) [IsFiniteMeasure (domainMeasure n Ω)]
    (hp : 1 ≤ p) (hpn : (p : ℝ) < n) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≤ Inequalities.pStar n p) (u : W₀^{1,p}(Ω)) :
    (wkp0LpEmbedding hΩ hp hpn hq u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      baseRepresentative (u : W^{1,p}(Ω)) :=
  (memLp_baseRepresentative_Wkp0 hΩ hp hpn hq u).coeFn_toLp

/-- The norm of the Sobolev inclusion is the `Lᑫ` norm of the original representative. -/
theorem norm_wkp0LpEmbedding
    (hΩ : MeasurableSet Ω) [IsFiniteMeasure (domainMeasure n Ω)]
    (hp : 1 ≤ p) (hpn : (p : ℝ) < n) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≤ Inequalities.pStar n p) (u : W₀^{1,p}(Ω)) :
    ‖wkp0LpEmbedding hΩ hp hpn hq u‖ =
      (eLpNorm (baseRepresentative (u : W^{1,p}(Ω)))
        q (domainMeasure n Ω)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (wkp0LpEmbedding_ae hΩ hp hpn hq u)]

/-- Evans §5.6.1, Theorem 3: if `Ω` is bounded and open, `1 ≤ p < n` and `1 ≤ q ≤ p*`, there is
`C > 0` such that every `u ∈ W^{1,p}_0(Ω)` lies in `Lᑫ(Ω)` with `‖u‖_{Lᑫ(Ω)} ≤ C * ‖∇ u‖`. -/
theorem exists_eLpNorm_le_wkpGradientCLM_Wkp0
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hp : 1 ≤ p) (hpn : (p : ℝ) < n) {q : ℝ≥0∞} (hq1 : 1 ≤ q)
    (hq : q ≤ Inequalities.pStar n p) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : W₀^{1,p}(Ω),
      MemLp (baseRepresentative (u : W^{1,p}(Ω))) q (domainMeasure n Ω) ∧
      eLpNorm (baseRepresentative (u : W^{1,p}(Ω))) q (domainMeasure n Ω) ≤
        ENNReal.ofReal (C * ‖∇ (u : W^{1,p}(Ω))‖) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hn : 0 < n := by exact_mod_cast p.2.trans_lt hpn
  obtain ⟨C, hC⟩ := exists_norm_le_wkpGradientCLM hn hΩb hp
  let J := wkp0LpEmbedding hΩ.measurableSet hp hpn hq
  -- Use the normed subspace's seminorm when applying the semilinear bound.
  let : SeminormedAddCommGroup (W₀^{1,p}(Ω)) :=
    (inferInstance : NormedAddCommGroup (W₀^{1,p}(Ω))).toSeminormedAddCommGroup
  obtain ⟨D, hD0, hD⟩ := ContinuousLinearMap.bound
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := W₀^{1,p}(Ω)) (F := DerivLp n q Ω)
    (σ₁₂ := RingHom.id ℝ) J
  refine ⟨D * (C + 1), mul_pos hD0 (by positivity), fun u ↦ ?_⟩
  have hmem := memLp_baseRepresentative_Wkp0 hΩ.measurableSet hp hpn hq u
  refine ⟨hmem, ?_⟩
  have hnorm : ‖J u‖ ≤ (D * (C + 1)) *
      ‖∇ (u : W^{1,p}(Ω))‖ :=
    (hD u).trans <| calc
      D * ‖u‖ ≤ D * (C * ‖∇ (u : W^{1,p}(Ω))‖) :=
        mul_le_mul_of_nonneg_left (hC u) hD0.le
      _ ≤ (D * (C + 1)) *
          ‖∇ (u : W^{1,p}(Ω))‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD0.le) (norm_nonneg _)
  rw [norm_wkp0LpEmbedding hΩ.measurableSet hp hpn hq u] at hnorm
  simpa only [ENNReal.ofReal_toReal hmem.eLpNorm_ne_top] using
    ENNReal.ofReal_le_ofReal hnorm

end SobolevSpace.GraphSpace
