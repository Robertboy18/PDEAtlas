/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration
import PDE.Analysis.Normed.PiLp.CompareExp
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Quantitative Sobolev steps on extension domains

The smooth first-order Gagliardo–Nirenberg–Sobolev constant also bounds the
completed-space inclusion. Smooth approximation and continuity of the
inclusion pass the estimate to the limit. Composing with the
operational C¹ extension retains the extension norm in the domain estimate.

The factor `n` compares the sum of coordinate derivative norms with the Sobolev
graph norm.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : NNReal}

/-- The first-order Gagliardo–Nirenberg–Sobolev constant after bounding each
coordinate derivative by the full Sobolev graph norm. -/
def firstOrderGraphConstant (n : ℕ) (p : NNReal) : ℝ :=
  (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) (p : ℝ) : ℝ) * n

/-- The graph-norm constant is nonnegative, including in dimension zero. -/
theorem firstOrderGraphConstant_nonneg : 0 ≤ firstOrderGraphConstant n p := by
  unfold firstOrderGraphConstant
  positivity

/-- The completed whole-space first-order inclusion satisfies the same bound
as the smooth core, with an explicit dimension factor. -/
theorem norm_subcriticalEmbeddingCLM_firstOrder_le
    (hp : 1 ≤ p) (hn : 0 < n) (hsub : (p : ℝ) < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n 1 p : ℝ≥0∞))]
    (U : W^{1,(p : ℝ≥0∞)}(ℝ^n)) :
    ‖subcriticalEmbeddingCLM hp hn (by simpa using hsub) U‖ ≤
      firstOrderGraphConstant n p * ‖U‖ := by
  let I := subcriticalEmbeddingCLM (k := 1) hp hn (by simpa using hsub)
  have hcore (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (hcs : HasCompactSupport f) :
      ‖I (mkWkpSpaceOnOfContDiff f hf hcs)‖ ≤
        firstOrderGraphConstant n p * ‖mkWkpSpaceOnOfContDiff
          (k := 1) (p := (p : ℝ≥0∞)) (Ω := Set.univ) f hf hcs‖ := by
    let V : W^{1,(p : ℝ≥0∞)}(ℝ^n) := mkWkpSpaceOnOfContDiff f hf hcs
    have hbase : (I V : ℝ^n → ℝ) =ᵐ[volume] f := by
      refine (memLp_higherOrderExponent hp hn (by simpa using hsub) V).coeFn_toLp.trans ?_
      simpa [globalBaseFunction, V, domainMeasure, iteratedPartialDeriv] using
        mkWkpSpaceOnOfContDiff_apply_ae (p := (p : ℝ≥0∞)) (Ω := Set.univ)
          f hf hcs (baseIndex n 1)
    have hcoord (i : Fin n) :
        (eLpNorm (∂[i] f) (p : ℝ≥0∞) volume).toReal ≤ ‖V‖ := by
      have h := norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal
        (p := (p : ℝ≥0∞)) (Ω := Set.univ) f hf hcs (firstDerivIndex n 1 (by decide) i)
      have hb := PiLp.norm_apply_le V.val (firstDerivIndex n 1 (by decide) i)
      rw [h] at hb
      simpa [domainMeasure, iteratedPartialDeriv] using hb
    have hfinite (i : Fin n) :
        eLpNorm (∂[i] f) (p : ℝ≥0∞) volume ≠ ∞ :=
      ((PDE.contDiff_top_iteratedPartialDeriv hf [i]).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_iteratedPartialDeriv hcs [i])).ne_top
    have hgns := eLpNorm_le_sum_eLpNorm_partialDeriv_of_eq
      (hf.of_le (by simp)) hcs hp hn
      (by
        simpa using inv_higherOrderExponent_eq (k := 1) (p := p)
          (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)) (by simpa using hsub))
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr fun i _ ↦ hfinite i)) hgns
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ ↦ hfinite i)] at hreal
    calc
      ‖I V‖ = (eLpNorm f (higherOrderExponent n 1 p : ℝ≥0∞) volume).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae hbase]
      _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) (p : ℝ) : ℝ) *
          ∑ i : Fin n, (eLpNorm (∂[i] f) (p : ℝ≥0∞) volume).toReal := by
        simpa using hreal
      _ ≤ firstOrderGraphConstant n p * ‖V‖ := by
        have hsum := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) ↦ hcoord i)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
        exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (mul_assoc _ _ _).symm
  obtain ⟨f, hf, hcs, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier n) ENNReal.coe_ne_top 1 U
  have hlim' := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  exact le_of_tendsto_of_tendsto ((I.continuous.tendsto U).comp hlim').norm
    (hlim'.norm.const_mul (firstOrderGraphConstant n p))
    (Filter.Eventually.of_forall fun m ↦ hcore (f m) (hf m) (hcs m))

/-- An explicit bound for the operator norm of the completed first-order inclusion. -/
theorem opNorm_subcriticalEmbeddingCLM_firstOrder_le
    (hp : 1 ≤ p) (hn : 0 < n) (hsub : (p : ℝ) < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n 1 p : ℝ≥0∞))] :
    ‖subcriticalEmbeddingCLM (k := 1) hp hn (by simpa using hsub)‖ ≤
      firstOrderGraphConstant n p :=
  ContinuousLinearMap.opNorm_le_bound _ firstOrderGraphConstant_nonneg
    (norm_subcriticalEmbeddingCLM_firstOrder_le hp hn hsub)

/-- Restriction after extension gives a domain estimate with the GNS constant
and the norm of the chosen first-order extension. The domain need not be bounded. -/
theorem eLpNorm_firstOrder_le_of_extension
    {Ω : Set (ℝ^n)} (hp : 1 ≤ p) (hn : 0 < n) (hsub : (p : ℝ) < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (E : Extension.GraphSpace.Operator n 1 (p : ℝ≥0∞) Ω)
    (U : W^{1,(p : ℝ≥0∞)}(Ω)) :
    eLpNorm (baseRepresentative U) (higherOrderExponent n 1 p : ℝ≥0∞)
        (domainMeasure n Ω) ≤
      ENNReal.ofReal (firstOrderGraphConstant n p * ‖E.toContinuousLinearMap‖ * ‖U‖) := by
  have : Fact (1 ≤ (higherOrderExponent n 1 p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_higherOrderExponent hp (by simpa using hsub)⟩
  let V := E.toContinuousLinearMap U
  let I := subcriticalEmbeddingCLM (k := 1) hp hn (by simpa using hsub)
  have hnorm :
      eLpNorm (globalBaseFunction V) (higherOrderExponent n 1 p : ℝ≥0∞) volume =
        ENNReal.ofReal ‖I V‖ := by
    have hmem := memLp_higherOrderExponent hp hn (by simpa using hsub) V
    have hcoe : (I V : ℝ^n → ℝ) =ᵐ[volume] globalBaseFunction V := hmem.coeFn_toLp
    rw [Lp.norm_def, eLpNorm_congr_ae hcoe, ENNReal.ofReal_toReal hmem.ne_top]
  calc
    eLpNorm (baseRepresentative U) _ (domainMeasure n Ω) =
        eLpNorm (globalBaseFunction V) _ (domainMeasure n Ω) :=
      eLpNorm_congr_ae (show globalBaseFunction V =ᵐ[domainMeasure n Ω]
        baseRepresentative U from E.agree_ae U).symm
    _ ≤ eLpNorm (globalBaseFunction V) _ volume := by
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = ENNReal.ofReal ‖I V‖ := hnorm
    _ ≤ ENNReal.ofReal
        (firstOrderGraphConstant n p * ‖E.toContinuousLinearMap‖ * ‖U‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact (norm_subcriticalEmbeddingCLM_firstOrder_le hp hn hsub V).trans
        ((mul_le_mul_of_nonneg_left (E.toContinuousLinearMap.le_opNorm U)
          firstOrderGraphConstant_nonneg).trans_eq (mul_assoc _ _ _).symm)

/-- The one-step domain constant depends only on dimension, exponent, and
the operational first-order extension, independently of the retained order. -/
def firstOrderDomainConstant {Ω : Set (ℝ^n)}
    [Fact (0 < n)] [Fact (1 ≤ (p : ℝ≥0∞))] [Boundary.C1ExtensionAtlas n Ω] : ℝ :=
  firstOrderGraphConstant n p *
    ‖(Extension.C1.operator (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)).toContinuousLinearMap‖

/-- The operational domain constant is nonnegative. -/
theorem firstOrderDomainConstant_nonneg {Ω : Set (ℝ^n)}
    [Fact (0 < n)] [Fact (1 ≤ (p : ℝ≥0∞))] [Boundary.C1ExtensionAtlas n Ω] :
    0 ≤ firstOrderDomainConstant (p := p) (Ω := Ω) := by
  unfold firstOrderDomainConstant
  exact mul_nonneg firstOrderGraphConstant_nonneg (by positivity)

end SobolevSpace.Inequalities

namespace SobolevSpace.GraphSpace.Embedding

open MeasureTheory Inequalities
open scoped ENNReal Sobolev

variable {n k : ℕ} {p : NNReal} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Fact (1 ≤ (p : ℝ≥0∞))] [Boundary.C1ExtensionAtlas n Ω]

/-- Each retained coordinate after one Sobolev step is bounded by applying the
quantitative first-order domain estimate to its contractive derivative slice. -/
theorem norm_firstOrderStep_coordinate_le
    (hp : 1 ≤ p) (hsub : (p : ℝ) < n)
    (U : W^{k + 1,(p : ℝ≥0∞)}(Ω)) (a : DerivIndex n k) :
    ‖(firstOrderStep hp hsub U).val a‖ ≤
      firstOrderDomainConstant (p := p) (Ω := Ω) * ‖U‖ := by
  let V := derivativeWordCLM (n := n) (m := k + 1) (r := 1) (p := (p : ℝ≥0∞))
    (Ω := Ω) a.toList (Nat.add_le_add_right a.toList_length_le 1) U
  have hbound := eLpNorm_firstOrder_le_of_extension hp Fact.out hsub
    (Extension.C1.operator (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)) V
  rw [Lp.norm_def, eLpNorm_congr_ae (firstOrderStep_apply_ae hp hsub U a)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  change (eLpNorm (baseRepresentative V) _ _).toReal ≤
    (ENNReal.ofReal (firstOrderDomainConstant (p := p) (Ω := Ω) * ‖V‖)).toReal at hreal
  rw [ENNReal.toReal_ofReal (show
    0 ≤ firstOrderDomainConstant (p := p) (Ω := Ω) * ‖V‖ from
      mul_nonneg firstOrderDomainConstant_nonneg (norm_nonneg V))] at hreal
  have hcoord :
      baseRepresentative V = ((U.val (a.castOrder (Nat.le_succ k))) : ℝ^n → ℝ) := by
    simp [V, baseRepresentative]
  rw [hcoord] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_left (norm_derivativeWordCLM_apply_le _ _ U)
    firstOrderDomainConstant_nonneg)

/-- Quantitative higher-order domain step `W^{k+1,p} → W^{k,p*}`.
Summing the retained coordinate bounds introduces only their finite cardinality. -/
theorem norm_firstOrderStep_le
    (hp : 1 ≤ p) (hsub : (p : ℝ) < n)
    [Fact (1 ≤ (higherOrderExponent n 1 p : ℝ≥0∞))]
    (U : W^{k + 1,(p : ℝ≥0∞)}(Ω)) :
    ‖firstOrderStep hp hsub U‖ ≤
      (Fintype.card (DerivIndex n k) : ℝ) *
        firstOrderDomainConstant (p := p) (Ω := Ω) * ‖U‖ := by
  apply (PiLp.norm_le_sum_norm (firstOrderStep hp hsub U).val).trans
  calc
    ∑ a : DerivIndex n k, ‖(firstOrderStep hp hsub U).val a‖ ≤
        ∑ _a : DerivIndex n k, firstOrderDomainConstant (p := p) (Ω := Ω) * ‖U‖ :=
      Finset.sum_le_sum fun a _ ↦ norm_firstOrderStep_coordinate_le hp hsub U a
    _ = _ := by simp [mul_assoc]

end SobolevSpace.GraphSpace.Embedding
