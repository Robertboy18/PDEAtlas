/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.Endpoint.Embedding
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Embedding

/-!
# Full Morrey embedding for all supercritical exponents

The finite-exponent embedding and the bounded weak-gradient endpoint together give
the full bounded Hölder norm for every `n < p ≤ ∞`. The constant depends only on the
dimension and exponent. For a C¹ function, continuity identifies the representative
everywhere, so no compact-support hypothesis is needed.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace

/-- The exponent `1 - n / p`, including the Lipschitz exponent at infinity. -/
def morreyHolderExponent (n : ℕ) (p : ℝ≥0∞)
    (hn : 0 < n) (hp : (n : ℝ≥0∞) < p) : HolderSpace.Exponent :=
  ⟨(morreyExponent n p).toNNReal, Real.toNNReal_pos.mpr (morreyExponent_pos hn hp),
    Real.toNNReal_le_one.mpr <|
      sub_le_self 1 (div_nonneg (Nat.cast_nonneg n) ENNReal.toReal_nonneg)⟩

/-- The bundled Morrey exponent has the usual real value. -/
@[simp] theorem morreyHolderExponent_coe_real
    (n : ℕ) (p : ℝ≥0∞) (hn : 0 < n) (hp : (n : ℝ≥0∞) < p) :
    ((morreyHolderExponent n p hn hp : ℝ≥0) : ℝ) = morreyExponent n p :=
  Real.coe_toNNReal _ (morreyExponent_pos hn hp).le

/-- The infinite-exponent case is the bounded Lipschitz space. -/
@[simp] theorem morreyHolderExponent_top (n : ℕ) (hn : 0 < n)
    (hp : (n : ℝ≥0∞) < ∞) :
    morreyHolderExponent n ∞ hn hp = 1 := by
  apply Subtype.ext
  simp [morreyHolderExponent]

/-- At a finite exponent, the finite Morrey bundle is recovered. -/
theorem morreyHolderExponent_ofReal
    (n : ℕ) (p : ℝ) (hn : 0 < n) (hp : (n : ℝ) < p)
    (hp' : (n : ℝ≥0∞) < ENNReal.ofReal p) :
    morreyHolderExponent n (ENNReal.ofReal p) hn hp' =
      finiteMorreyHolderExponent n p hn hp := rfl

/-- The full Morrey bound on whole-space Sobolev elements, including `p = ∞`.
The constant is independent of the function. -/
theorem exists_morreyEmbeddingBound
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hn : 0 < n) (hp : (n : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : W^{1,p}(ℝ^n),
      ∃ F : HolderSpace.C0GammaOn (ℝ^n) (morreyHolderExponent n p hn hp),
        (fun x ↦ F x) =ᵐ[volume] GraphSpace.baseRepresentative U ∧
        ‖F‖ ≤ C * ‖U‖ := by
  by_cases htop : p = ∞
  · subst p
    refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
    intro U
    rw [morreyHolderExponent_top]
    exact U.exists_holder_one_representative
  · obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ ENNReal.ofReal r = p :=
      ⟨p.toReal, ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop⟩
    have hpReal : (n : ℝ) < r := by
      simpa only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hr] using
        ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hp
    have hp1 : 1 < r :=
      (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans_lt hpReal
    have hconj := Real.HolderConjugate.conjExponent hp1
    refine ⟨finiteMorreyEmbeddingConstant n r (Real.conjExponent r),
      finiteMorreyEmbeddingConstant_nonneg _ _ _, ?_⟩
    intro U
    rw [morreyHolderExponent_ofReal n r hn hpReal]
    exact
      exists_morreyHolderRepresentative hn hpReal hconj U

/-- A C¹ function with its classical derivatives in `Lᵖ` satisfies the full Morrey
bound. The representative equals the original function at every point; compact
support is not required. The norm on the right is the usual Sobolev graph norm. -/
theorem exists_morreyBound_of_contDiff
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hn : 0 < n) (hp : (n : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ^n → ℝ) (hf : ContDiff ℝ 1 f)
      (hmem : ∀ a : GraphSpace.DerivIndex n 1,
        MemLp (iteratedPartialDeriv a.toList f) p (domainMeasure n univ)),
      ∃ F : HolderSpace.C0GammaOn (ℝ^n) (morreyHolderExponent n p hn hp),
        (∀ x, F x = f x) ∧
        ‖F‖ ≤ C * ‖GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite f hf hmem‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_morreyEmbeddingBound hn hp
  refine ⟨C, hC, fun f hf hmem ↦ ?_⟩
  let U := GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite f hf hmem
  obtain ⟨F, heq, hnorm⟩ := hbound U
  have hbase : GraphSpace.baseRepresentative U =ᵐ[volume] f := by
    simpa only [GraphSpace.baseRepresentative, domainMeasure, Measure.restrict_univ,
      GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      GraphSpace.mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
        f hf hmem (GraphSpace.baseIndex n 1)
  have hF : (fun x ↦ F x) = f :=
    Measure.eq_of_ae_eq (heq.trans hbase) F.continuous hf.continuous
  exact ⟨F, congrFun hF, hnorm⟩

end SobolevSpace
