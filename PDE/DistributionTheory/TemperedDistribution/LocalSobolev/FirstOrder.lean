/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Sobolev
public import PDE.DistributionTheory.TemperedDistribution.Leibniz

/-!
# First-order interior regularity from divergence data

A locally L² distribution gains one Sobolev order when its Laplacian is locally
H⁻¹. In particular, a divergence of locally L² fields is admissible forcing.
The proof differentiates products with compact cutoffs; it never assumes an L²
first derivative of the state. This is the first step in interior regularity for
systems whose differentiated equations have divergence-form right-hand sides.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv Laplacian

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiating a Schwartz cutoff does not enlarge its compact support. -/
theorem hasCompactSupport_lineDerivOp {a : 𝓢(E, ℂ)}
    (ha : HasCompactSupport a) (v : E) : HasCompactSupport (∂_{v} a : 𝓢(E, ℂ)) :=
  ha.of_isClosed_subset (isClosed_tsupport (∂_{v} a : 𝓢(E, ℂ)))
    (tsupport_lineDerivOp_subset v a)

end SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F]

section Normed

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- A Schwartz multiplier preserves order-zero Sobolev membership, including Lp
endpoints, by the L∞-Lp product estimate. -/
theorem MemSobolev.zero_smulLeftCLM {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {T : 𝓢'(E, F)} (hT : MemSobolev 0 p T) (a : 𝓢(E, ℂ)) :
    MemSobolev 0 p (smulLeftCLM F a T) := by
  obtain ⟨u, rfl⟩ := memSobolev_zero_iff.mp hT
  apply memSobolev_zero_iff.mpr
  refine ⟨(a.memLp_top volume).toLp a • u, ?_⟩
  exact (Lp.toTemperedDistribution_smul_eq (p := ⊤) (q := p) (r := p)
    a.hasTemperateGrowth (a.memLp_top volume) u).symm

end Normed

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A finite sum of H^s distributions remains in H^s. This combines the coordinate
terms in the cutoff Laplacian. -/
theorem MemSobolev.sum {ι : Type*} (s : ℝ) (t : Finset ι)
    (g : ι → 𝓢'(E, F)) (hg : ∀ i ∈ t, MemSobolev s 2 (g i)) :
    MemSobolev s 2 (∑ i ∈ t, g i) := by
  classical
  revert hg
  induction t using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert i t hit ih =>
    intro hg
    rw [Finset.sum_insert hit]
    exact (hg i (Finset.mem_insert_self i t)).add
      (ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj)))

/-- A locally L² distribution with locally H⁻¹ Laplacian belongs to H¹ after every
compact cutoff. The divergence-form commutator is H⁻¹ using only the L² state,
so no first derivative or L² Laplacian is assumed. -/
theorem memSobolev_one_smulLeftCLM_of_local_laplacian
    {Ω : Set E} {T : 𝓢'(E, F)}
    (hT : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a T))
    (hΔ : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev (-1) 2 (smulLeftCLM F a (Δ T)))
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) :
    MemSobolev 1 2 (smulLeftCLM F a T) := by
  let b := stdOrthonormalBasis ℝ E
  have hfirst (v : E) : MemSobolev 0 2 (smulLeftCLM F (∂_{v} a : 𝓢(E, ℂ)) T) :=
    hT _ (SchwartzMap.hasCompactSupport_lineDerivOp ha v)
      ((SchwartzMap.tsupport_lineDerivOp_subset v a).trans haΩ)
  have hsecond (v : E) : MemSobolev 0 2 (smulLeftCLM F (∂_{v} (∂_{v} a : 𝓢(E, ℂ)) : 𝓢(E, ℂ)) T) :=
    hT _ (SchwartzMap.hasCompactSupport_lineDerivOp
      (SchwartzMap.hasCompactSupport_lineDerivOp ha v) v)
      (((SchwartzMap.tsupport_lineDerivOp_subset v (∂_{v} a : 𝓢(E, ℂ))).trans
        (SchwartzMap.tsupport_lineDerivOp_subset v a)).trans haΩ)
  have hcutΔ : MemSobolev (-1) 2 (Δ (smulLeftCLM F a T)) := by
    rw [laplacian_smulLeftCLM_divergence b]
    apply (hΔ a ha haΩ).add
    apply MemSobolev.sum
    intro i _
    have hd : MemSobolev (-1) 2 (∂_{b i} (smulLeftCLM F (∂_{b i} a : 𝓢(E, ℂ)) T)) := by
      simpa using (hfirst (b i)).lineDerivOp (m := b i)
    exact (hd.smul 2).sub (MemSobolev.mono (by norm_num) (hsecond (b i)))
  have hu : MemSobolev (-1) 2 (smulLeftCLM F a T) :=
    MemSobolev.mono (by norm_num) (hT a ha haΩ)
  convert hu.add_two_of_laplacian hcutΔ using 1
  norm_num

/-- Localizing a derivative of locally L² data gives an H⁻¹ distribution.
The product rule transfers the derivative to the globally L² cutoff product. -/
theorem memSobolev_neg_one_smulLeftCLM_lineDeriv
    {Ω : Set E} {G : 𝓢'(E, F)}
    (hG : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a G))
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) (v : E) :
    MemSobolev (-1) 2 (smulLeftCLM F a (∂_{v} G)) := by
  have heq : smulLeftCLM F a (∂_{v} G) =
      ∂_{v} (smulLeftCLM F a G) - smulLeftCLM F (∂_{v} a : 𝓢(E, ℂ)) G := by
    rw [lineDerivOp_smulLeftCLM, add_sub_cancel_left]
  rw [heq]
  have hd : MemSobolev (-1) 2 (∂_{v} (smulLeftCLM F a G)) := by
    simpa using (hG a ha haΩ).lineDerivOp (m := v)
  exact hd.sub (MemSobolev.mono (by norm_num)
    (hG _ (SchwartzMap.hasCompactSupport_lineDerivOp ha v)
      ((SchwartzMap.tsupport_lineDerivOp_subset v a).trans haΩ)))

/-- A locally L² state whose Laplacian is a divergence of locally L² fields has
H¹ compact localizations. The equation is an equality of localized
distributions, and the finitely many directions need not form a basis. -/
theorem memSobolev_one_smulLeftCLM_of_local_divergence
    {ι : Type*} [Fintype ι] {Ω : Set E} {T : 𝓢'(E, F)} (G : ι → 𝓢'(E, F)) (v : ι → E)
    (hT : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a T))
    (hG : ∀ i, ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      MemSobolev 0 2 (smulLeftCLM F a (G i)))
    (hΔ : ∀ a : 𝓢(E, ℂ), HasCompactSupport a → tsupport a ⊆ Ω →
      smulLeftCLM F a (Δ T) = ∑ i, smulLeftCLM F a (∂_{v i} (G i)))
    (a : 𝓢(E, ℂ)) (ha : HasCompactSupport a) (haΩ : tsupport a ⊆ Ω) :
    MemSobolev 1 2 (smulLeftCLM F a T) := by
  apply memSobolev_one_smulLeftCLM_of_local_laplacian hT _ a ha haΩ
  intro χ hχ hχΩ
  rw [hΔ χ hχ hχΩ]
  apply MemSobolev.sum
  intro i _
  exact memSobolev_neg_one_smulLeftCLM_lineDeriv (hG i) χ hχ hχΩ (v i)

end TemperedDistribution
