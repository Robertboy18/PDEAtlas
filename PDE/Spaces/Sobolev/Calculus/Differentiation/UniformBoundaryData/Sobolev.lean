/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Algebra
public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Sobolev realizations of classical closure data

The classical-to-Sobolev construction commutes with restriction, differentiation,
linear operations, and multiplication. Equality follows from the classical
base representative and uniqueness of the weak derivative graph on an open set.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open MeasureTheory Set GraphSpace
open scoped ENNReal

variable {n k : ℕ} {Ω : Set (ℝ^n)} {f g : ℝ^n → ℝ}

/-- Restriction of the constructed Sobolev graph is the lower-order construction. -/
theorem lowerOrder_toWkpSpaceOn (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {r : ℕ} (hr : r ≤ k) :
    lowerOrderCLM hr (hf.toWkpSpaceOn hopen hbounded p) =
      (hf.of_le hr).toWkpSpaceOn hopen hbounded p := by
  apply WkpSpaceOn.ext_of_base_ae hopen
  change baseRepresentative (lowerOrderCLM hr (hf.toWkpSpaceOn hopen hbounded p)) =ᵐ[_]
    baseRepresentative ((hf.of_le hr).toWkpSpaceOn hopen hbounded p)
  have heq : baseRepresentative (lowerOrderCLM hr (hf.toWkpSpaceOn hopen hbounded p)) =
      baseRepresentative (hf.toWkpSpaceOn hopen hbounded p) := by
    funext x
    simp only [baseRepresentative, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  rw [heq]
  exact (hf.toWkpSpaceOn_base_ae hopen hbounded p).trans
    ((hf.of_le hr).toWkpSpaceOn_base_ae hopen hbounded p).symm

/-- Classical addition agrees with addition in the weak derivative graph. -/
theorem toWkpSpaceOn_add (hf : ContDiffUpToBoundary k f Ω)
    (hg : ContDiffUpToBoundary k g Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (hf.add hg hopen).toWkpSpaceOn hopen hbounded p =
      hf.toWkpSpaceOn hopen hbounded p + hg.toWkpSpaceOn hopen hbounded p := by
  apply WkpSpaceOn.ext_of_base_ae hopen
  filter_upwards [(hf.add hg hopen).toWkpSpaceOn_base_ae hopen hbounded p,
    baseRepresentative_add_ae (hf.toWkpSpaceOn hopen hbounded p)
      (hg.toWkpSpaceOn hopen hbounded p),
    hf.toWkpSpaceOn_base_ae hopen hbounded p,
    hg.toWkpSpaceOn_base_ae hopen hbounded p] with x hsum hadd hfx hgx
  exact hsum.trans (hadd.trans (congrArg₂ (· + ·) hfx hgx)).symm

/-- Classical negation agrees with negation in the weak derivative graph. -/
theorem toWkpSpaceOn_neg (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (hf.neg hopen).toWkpSpaceOn hopen hbounded p = -hf.toWkpSpaceOn hopen hbounded p := by
  apply WkpSpaceOn.ext_of_base_ae hopen
  filter_upwards [(hf.neg hopen).toWkpSpaceOn_base_ae hopen hbounded p,
    baseRepresentative_neg_ae (hf.toWkpSpaceOn hopen hbounded p),
    hf.toWkpSpaceOn_base_ae hopen hbounded p] with x hneg hbase hfx
  exact hneg.trans (hbase.trans (congrArg Neg.neg hfx)).symm

/-- Finite classical sums agree with finite sums in the Sobolev graph. -/
theorem toWkpSpaceOn_sum {ι : Type*} [Fintype ι]
    {F : ι → ℝ^n → ℝ} (hF : ∀ i, ContDiffUpToBoundary k (F i) Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (sum Finset.univ (fun i _ ↦ hF i) hopen).toWkpSpaceOn hopen hbounded p =
      ∑ i, (hF i).toWkpSpaceOn hopen hbounded p := by
  apply WkpSpaceOn.ext_of_base_ae hopen
  filter_upwards [(sum Finset.univ (fun i _ ↦ hF i) hopen).toWkpSpaceOn_base_ae
      hopen hbounded p,
    baseRepresentative_sum_ae (fun i ↦ (hF i).toWkpSpaceOn hopen hbounded p),
    ae_all_iff.mpr (fun i ↦ (hF i).toWkpSpaceOn_base_ae hopen hbounded p)] with
      x hsum hbase hFx
  exact hsum.trans (hbase.trans (Finset.sum_congr rfl (fun i _ ↦ hFx i))).symm

/-- The weak first derivative of classical data is its classical partial derivative. -/
theorem derivativeWord_toWkpSpaceOn (hf : ContDiffUpToBoundary (k + 1) f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin n) :
    derivativeWordCLM [i] (show [i].length + k ≤ k + 1 from (Nat.add_comm 1 k).le)
        (hf.toWkpSpaceOn hopen hbounded p) =
      (hf.partialDeriv_of_succ hopen i).toWkpSpaceOn hopen hbounded p := by
  apply WkpSpaceOn.ext_of_base_ae hopen
  have hderiv : baseRepresentative
      (derivativeWordCLM [i] (show [i].length + k ≤ k + 1 from (Nat.add_comm 1 k).le)
        (hf.toWkpSpaceOn hopen hbounded p)) =ᵐ[domainMeasure n Ω] ∂[i] f := by
    simpa only [baseRepresentative, derivativeWordCLM_apply,
      derivativeWordIndex_singleton_baseIndex, firstDerivIndex_toList,
      iteratedPartialDeriv] using hf.toWkpSpaceOn_apply_ae hopen hbounded p
        (firstDerivIndex n (k + 1) (Nat.succ_pos k) i)
  exact hderiv.trans ((hf.partialDeriv_of_succ hopen i).toWkpSpaceOn_base_ae
    hopen hbounded p).symm

/-- The bounded Sobolev multiplier agrees with multiplication of classical functions. -/
theorem wkTopMultiplier_toWkpSpaceOn (hk : 0 < k)
    (hf : ContDiffUpToBoundary k f Ω) (hg : ContDiffUpToBoundary k g Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    wkTopMultiplierCLM hk hopen (hf.toWkpSpaceOn hopen hbounded ∞)
        (hg.toWkpSpaceOn hopen hbounded 2) =
      (hf.mul hg hopen hbounded).toWkpSpaceOn hopen hbounded 2 := by
  rw [wkTopMultiplierCLM_apply]
  apply WkpSpaceOn.ext_of_base_ae hopen
  filter_upwards [wkTopProduct_base_ae hk hopen (hf.toWkpSpaceOn hopen hbounded ∞)
      (hg.toWkpSpaceOn hopen hbounded 2),
    hf.toWkpSpaceOn_base_ae hopen hbounded ∞,
    hg.toWkpSpaceOn_base_ae hopen hbounded 2,
    (hf.mul hg hopen hbounded).toWkpSpaceOn_base_ae hopen hbounded 2] with
      x hmul hfx hgx hfgx
  exact (hmul.trans (congrArg₂ (· * ·) hfx hgx)).trans hfgx.symm

end SobolevSpace.ContDiffUpToBoundary
