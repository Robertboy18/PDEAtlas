/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
import PDE.Analysis.Calculus.UniformClosure
import PDE.FDeriv.Calculus

/-!
# Sobolev coefficients from classical regularity up to the boundary

Here `C^k` up to the boundary means interior `C^k` regularity and uniform continuity on the domain
of the classical derivatives through order `k`. Evans (App. A.3, p. 702) asks for uniform
continuity on bounded subsets; the two conditions agree on bounded domains. No values or
derivatives outside the domain, and no differentiable extension across its boundary, are assumed.

On a bounded open set these hypotheses give `W^{k,p}` elements for every exponent,
including infinity. Their rows are the classical derivatives, and a common pointwise bound
controls the `W^{k,∞}` norm. The derivative bounds and integrability are derived here.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. A.3, p. 702, for `C^k(Ū)`: functions whose derivatives
  of order at most `k` are uniformly continuous on bounded subsets of `U`, and so extend
  continuously to `Ū`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- Interior classical regularity with uniformly continuous derivatives up to the indicated
order. On an open set the derivative words represent the usual commutative multi-indices. -/
structure ContDiffUpToBoundary (k : ℕ) (f : ℝ^n → ℝ) (Ω : Set (ℝ^n)) : Prop where
  /-- Classical differentiability is required only in the domain. -/
  contDiffOn : ContDiffOn ℝ k f Ω
  /-- Each classical derivative, including the function, is uniformly continuous there. -/
  uniformContinuousOn : ∀ α : List (Fin n), α.length ≤ k →
    UniformContinuousOn (iteratedPartialDeriv α f) Ω

/-- On an open domain, the closure regularity condition can equivalently be checked
on the finite family of commutative multi-indices. -/
theorem contDiffUpToBoundary_iff (hopen : IsOpen Ω) :
    ContDiffUpToBoundary k f Ω ↔ ContDiffOn ℝ k f Ω ∧
      ∀ a : GraphSpace.DerivIndex n k,
        UniformContinuousOn (iteratedPartialDeriv a.toList f) Ω := by
  constructor
  · intro hf
    exact ⟨hf.contDiffOn, fun a ↦ hf.uniformContinuousOn a.toList a.toList_length_le⟩
  · rintro ⟨hf, hu⟩
    refine ⟨hf, fun α hα ↦ ?_⟩
    exact (hu (GraphSpace.derivIndexOfList α hα)).congr
      (iteratedPartialDeriv_congr_perm_of_contDiffOn hopen hf
        (GraphSpace.derivIndexOfList α hα).toList_length_le
        (GraphSpace.derivIndexOfList_toList_perm α hα))

namespace ContDiffUpToBoundary

/-- Constants have classical regularity of every finite order up to any boundary. -/
theorem const (c : ℝ) : ContDiffUpToBoundary k (fun _ : ℝ^n ↦ c) Ω := by
  refine ⟨contDiffOn_const, fun α hα ↦ ?_⟩
  clear hα
  have hconst : ∃ d : ℝ, iteratedPartialDeriv α (fun _ : ℝ^n ↦ c) = fun _ ↦ d := by
    induction α with
    | nil => exact ⟨c, rfl⟩
    | cons i α ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨0, funext fun x ↦ ?_⟩
      change (∂[i] (iteratedPartialDeriv α (fun _ : ℝ^n ↦ c))) x = 0
      rw [hd]
      exact PDE.partialDeriv_const d
  obtain ⟨d, hd⟩ := hconst
  rw [hd]
  exact uniformContinuous_const.uniformContinuousOn

/-- Lowering the regularity order preserves classical regularity up to the boundary. -/
theorem of_le (hf : ContDiffUpToBoundary k f Ω) {j : ℕ} (hj : j ≤ k) :
    ContDiffUpToBoundary j f Ω :=
  ⟨hf.contDiffOn.of_le (by exact_mod_cast hj),
    fun α hα ↦ hf.uniformContinuousOn α (hα.trans hj)⟩

/-- Taking one coordinate derivative lowers the order of closure regularity by one. -/
theorem partialDeriv_of_succ (hf : ContDiffUpToBoundary (k + 1) f Ω)
    (hopen : IsOpen Ω) (i : Fin n) :
    ContDiffUpToBoundary k (∂[i] f) Ω := by
  refine ⟨fun x hx ↦
    (PDE.contDiffAt_partialDeriv k (hf.contDiffOn.contDiffAt (hopen.mem_nhds hx))
      i).contDiffWithinAt,
    fun α hα ↦ ?_⟩
  have hlen : (α ++ [i]).length ≤ k + 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  have heq : iteratedPartialDeriv (α ++ [i]) f =
      iteratedPartialDeriv α (∂[i] f) :=
    funext (PDE.iteratedPartialDeriv_append_single α i f)
  rw [← heq]
  exact hf.uniformContinuousOn (α ++ [i]) hlen

/-- Classical closure regularity depends only on the function's values in the open domain. -/
theorem congr (hf : ContDiffUpToBoundary k f Ω) (hopen : IsOpen Ω)
    {g : ℝ^n → ℝ} (hgf : EqOn g f Ω) :
    ContDiffUpToBoundary k g Ω := by
  refine ⟨hf.contDiffOn.congr hgf, fun α hα ↦ ?_⟩
  apply (hf.uniformContinuousOn α hα).congr
  intro x hx
  exact ((hgf.eventuallyEq_of_mem (hopen.mem_nhds hx)).iteratedPartialDeriv α).eq_of_nhds.symm

/-- The values admit a continuous ambient representative, obtained by completion and Tietze. -/
theorem exists_continuous_eqOn (hf : ContDiffUpToBoundary k f Ω) :
    ∃ g : ℝ^n → ℝ, Continuous g ∧ EqOn g f Ω :=
  (hf.uniformContinuousOn [] (Nat.zero_le k)).exists_continuous_eqOn

/-- Every classical derivative through order `k` is bounded on a bounded domain. -/
theorem exists_derivative_bound (hf : ContDiffUpToBoundary k f Ω)
    (hbounded : Bornology.IsBounded Ω) (α : List (Fin n)) (hα : α.length ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Ω, ‖iteratedPartialDeriv α f x‖ ≤ C :=
  (hf.uniformContinuousOn α hα).exists_pos_bound hbounded

/-- The classical derivatives belong to every `L^p` on a bounded open domain. -/
theorem memLp_iteratedPartialDeriv (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) (α : List (Fin n)) (hα : α.length ≤ k) :
    MemLp (iteratedPartialDeriv α f) p (domainMeasure n Ω) := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  obtain ⟨C, _, hC⟩ := hf.exists_derivative_bound hbounded α hα
  apply MemLp.of_bound
    ((hf.uniformContinuousOn α hα).continuousOn.aestronglyMeasurable hopen.measurableSet) C
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  exact hC x hx

/-- The `L^p` class of classical boundary data on a bounded open domain. -/
def toLp (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (p : ℝ≥0∞) :
    Lp ℝ p (domainMeasure n Ω) :=
  (hf.memLp_iteratedPartialDeriv hopen hbounded p [] (Nat.zero_le k)).toLp f

/-- The constructed `L^p` class agrees almost everywhere with the original values. -/
theorem toLp_coeFn (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (p : ℝ≥0∞) :
    (hf.toLp hopen hbounded p : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f :=
  (hf.memLp_iteratedPartialDeriv hopen hbounded p [] (Nat.zero_le k)).coeFn_toLp

open GraphSpace

/-- The Sobolev graph of classical data up to the boundary. Its weak-derivative constraints
follow from interior integration by parts; its integrability follows from uniform continuity. -/
def toWkpSpaceOn (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (p : ℝ≥0∞) :
    W^{k,p}(Ω) :=
  mkWkpSpaceOnOfWeakDerivatives f (fun a ↦ iteratedPartialDeriv a.toList f)
    (by simp [iteratedPartialDeriv])
    (fun a ↦ hf.memLp_iteratedPartialDeriv hopen hbounded p a.toList a.toList_length_le)
    (fun a ↦ hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn
      hopen hf.contDiffOn a.toList a.toList_length_le)

/-- Every row of the constructed Sobolev element is the corresponding classical derivative. -/
theorem toWkpSpaceOn_apply_ae (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (p : ℝ≥0∞)
    (a : DerivIndex n k) :
    ((hf.toWkpSpaceOn hopen hbounded p : WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] iteratedPartialDeriv a.toList f :=
  mkWkpSpaceOnOfWeakDerivatives_apply_ae _ _ _ _ _ a

/-- The base coordinate of the constructed graph represents the original function. -/
theorem toWkpSpaceOn_base_ae (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (wkpBaseCoordinateCLM (hf.toWkpSpaceOn hopen hbounded p) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] f := by
  simpa only [wkpBaseCoordinateCLM_apply, baseIndex_toList, iteratedPartialDeriv] using
    hf.toWkpSpaceOn_apply_ae hopen hbounded p (baseIndex n k)

/-- The Sobolev construction and the direct `L^p` construction have the same base class. -/
theorem toWkpSpaceOn_base_eq_toLp (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    wkpBaseCoordinateCLM (hf.toWkpSpaceOn hopen hbounded p) = hf.toLp hopen hbounded p :=
  Lp.ext ((hf.toWkpSpaceOn_base_ae hopen hbounded p).trans
    (hf.toLp_coeFn hopen hbounded p).symm)

/-- A common classical derivative bound controls the maximum Sobolev graph norm. -/
theorem norm_toWkpSpaceOn_top_le (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a : DerivIndex n k, ∀ x ∈ Ω, ‖iteratedPartialDeriv a.toList f x‖ ≤ C) :
    ‖hf.toWkpSpaceOn hopen hbounded ∞‖ ≤ C := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have : Nonempty (DerivIndex n k) := ⟨baseIndex n k⟩
  change ‖(hf.toWkpSpaceOn hopen hbounded ∞ : WkpAmbientOn n k ∞ Ω)‖ ≤ C
  rw [PiLp.norm_eq_ciSup]
  apply ciSup_le
  intro a
  have hrow : ∀ᵐ x ∂domainMeasure n Ω,
      ‖((hf.toWkpSpaceOn hopen hbounded ∞ : WkpAmbientOn n k ∞ Ω) a :
        ℝ^n → ℝ) x‖ ≤ C := by
    filter_upwards [hf.toWkpSpaceOn_apply_ae hopen hbounded ∞ a,
      ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    rw [hx]
    exact hbound a x hxΩ
  simpa using Lp.norm_le_of_ae_bound hC hrow

/-- Uniform continuity supplies one finite positive bound for all Sobolev coordinates. -/
theorem exists_norm_bound (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧
      (∀ a : DerivIndex n k, ∀ x ∈ Ω, ‖iteratedPartialDeriv a.toList f x‖ ≤ C) ∧
      ‖hf.toWkpSpaceOn hopen hbounded ∞‖ ≤ C := by
  classical
  choose C hC hbound using fun a : DerivIndex n k ↦
    hf.exists_derivative_bound hbounded a.toList a.toList_length_le
  let M := 1 + ∑ a, C a
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun a _ ↦ (hC a).le)
  have hb (a : DerivIndex n k) (x : ℝ^n) (hx : x ∈ Ω) :
      ‖iteratedPartialDeriv a.toList f x‖ ≤ M :=
    (hbound a x hx).trans
      ((Finset.single_le_sum (fun b _ ↦ (hC b).le) (Finset.mem_univ a)).trans
        (le_add_of_nonneg_left zero_le_one))
  exact ⟨M, hM, hb, hf.norm_toWkpSpaceOn_top_le hopen hbounded hM.le hb⟩

/-- Uniform continuity of the first partial derivatives supplies continuous ambient value
and derivative fields agreeing with the classical first jet in the open domain. -/
theorem exists_continuous_firstJet (hf : ContDiffUpToBoundary 1 f Ω)
    (hopen : IsOpen Ω) :
    ∃ F : ℝ^n → ℝ, ∃ F' : ℝ^n → (ℝ^n →L[ℝ] ℝ),
      Continuous F ∧ Continuous F' ∧ EqOn F f Ω ∧
        ∀ x ∈ Ω, HasFDerivAt F (F' x) x := by
  classical
  obtain ⟨F, hF, hFf⟩ := hf.exists_continuous_eqOn
  have hi (i : Fin n) : ∃ g : ℝ^n → ℝ,
      Continuous g ∧ EqOn g (∂[i] f) Ω := by
    simpa only [iteratedPartialDeriv] using
      (hf.uniformContinuousOn [i] (by simp)).exists_continuous_eqOn
  choose g hg hgf using hi
  let F' : ℝ^n → (ℝ^n →L[ℝ] ℝ) :=
    fun x ↦ ∑ i, g i x • EuclideanSpace.proj i
  refine ⟨F, F', hF, ?_, hFf, ?_⟩
  · exact continuous_finsetSum _ fun i _ ↦
      (hg i).smul (continuous_const (y := EuclideanSpace.proj i))
  · intro x hx
    have hfd : F' x = fderiv ℝ f x := by
      ext v
      simp only [F', sum_apply, smul_apply, smul_eq_mul,
        PDE.fderiv_apply_eq_sum_partialDeriv_mul]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (· * v i) (hgf i hx)
    rw [hfd]
    apply (hf.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt
      (by norm_num) |>.hasFDerivAt.congr_of_eventuallyEq
    exact hFf.eventuallyEq_of_mem (hopen.mem_nhds hx)

end ContDiffUpToBoundary

end SobolevSpace
