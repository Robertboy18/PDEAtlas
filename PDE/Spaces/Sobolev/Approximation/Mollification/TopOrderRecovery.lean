/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakRecovery
public import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
public import PDE.Spaces.Sobolev.Calculus.Slicing.TopOrderAssembly
import PDE.Analysis.Integration.ConvolutionDerivative
import PDE.Analysis.MeasureTheory.Lp.Products
import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Spaces.Sobolev.Approximation.Mollification.L2Operator
import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator
import PDE.Analysis.Integration.ConvolutionL2

/-!
# From bounded derivatives of mollifications to the next Sobolev order

Let `f` be in the class of a member of `Hᵏ(ℝⁿ)`, and suppose that the derivatives of order
`k + 1` of its mollifications `ρ_ε ∗ f` are bounded in `L²` uniformly in `ε ∈ (0, 1)`. Then `f`
is in `H^{k+1}(ℝⁿ)` (`exists_wkpSpace_succ_of_bounded_convolution`). Hou, Wang and Yang end each
step of their regularity induction this way, "by the theory of mollifiers". The module also
proves, for single functions, the facts about mollifiers that such an induction uses: the weak
derivatives of a member of `Hᵏ(ℝⁿ)` as square integrable functions, the `L²` contraction and
convergence of mollification, and the bound for a product of two `L⁴` functions.
`exists_higherOrder_Lp_of_bounded_mollifications` is the form for Bochner classes, with the bound
in the full graph norm.

## Main results

* `exists_hasWeakDerivativeOn_of_ae_eq`, `exists_hasWeakDerivativeOn_pair_of_ae_eq`: for `f` in
  the class of `V ∈ Hᵏ(ℝⁿ)`, the weak derivatives of `f` of order at most `k` as functions,
  square integrable with `∫ (∂^α f)² ≤ ‖V‖²`.
* `integral_sq_convolution_scaled_le`, `tendsto_integral_sq_convolution_scaled`: for `f ∈ L²` and
  every mollifier, `∫ (f ∗ ρ_ε)² ≤ ∫ f²`, and `∫ (f ∗ ρ_ε)² → ∫ f²` as `ε → 0`.
* `integral_sq_convolution_mul_scaled_le`: for `f, g ∈ L⁴` and `ε > 0`,
  `∫ ((f g) ∗ ρ_ε)² ≤ (‖f‖_{L⁴} ‖g‖_{L⁴})²`, the first inequality of (2.12) of Hou, Wang and
  Yang.
* `integral_sq_convolution_iteratedPartialDeriv_scaled_le`: `∫ (f ∗ ∂^α ρ_ε)² ≤ ‖V‖²`, so
  mollification does not increase the `L²` norm of a derivative, (2.11) of Hou, Wang and Yang.
* `exists_wkpSpace_succ_of_bounded_convolution`: if `∫ (∂ⱼ(f ∗ ∂^α ρ_ε))² ≤ C²` for every word
  `α` of length `k`, every `j` and every `ε ∈ (0, 1)`, then `f` is in the class of a member of
  `H^{k+1}(ℝⁿ)`.

## How it works

For a word `α` of length `k` the weak derivative `∂^α f` is in `L²`, and
`∂ⱼ∂^α(ρ_ε ∗ f) = (∂ⱼρ_ε) ∗ ∂^α f`. Along `ε = 1/(m + 2)` these functions are bounded in `L²`, so
they have a weak limit along an ultrafilter, and the limit is the weak derivative `∂ⱼ∂^α f`
(`exists_L2_weakDerivativeOn_of_bounded_mollifierDerivativeRowCLM`). The graph of order `k` and
the new derivatives of order `k + 1` assemble to a graph of order `k + 1`
(`exists_succ_order_of_top_derivatives`).

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2, the estimates (2.11)
  and (2.12) and the conclusion of each step of the regularity induction.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open ContinuousLinearMap (mul)
open PDE (iteratedPartialDeriv)
open PDE.Analysis SobolevSpace.GraphSpace
open scoped Convolution ENNReal Sobolev Topology

namespace SobolevSpace.Approximation

variable {n k : ℕ}

/-- A function in the class of a member of `Hᵏ(ℝⁿ)` is square integrable. -/
theorem memLp_two_of_baseRepresentative_ae_eq (V : W^{k,2}(ℝ^n)) {f : ℝ^n → ℝ}
    (hf : baseRepresentative V =ᵐ[volume] f) : MemLp f 2 volume := by
  have h := Lp.memLp ((V : WkpAmbientOn n k 2 univ) (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h.ae_eq hf

/-- **The weak derivatives of a member of `Hᵏ(ℝⁿ)`, as functions.** If `f` is in the class of
`V ∈ Hᵏ(ℝⁿ)` and `α` is a word of length at most `k`, then `f` has a weak derivative `∂^α f`
that is square integrable, with `∫ (∂^α f)² ≤ ‖V‖²`. -/
theorem exists_hasWeakDerivativeOn_of_ae_eq (V : W^{k,2}(ℝ^n)) {f : ℝ^n → ℝ}
    (hf : baseRepresentative V =ᵐ[volume] f) (α : List (Fin n)) (hα : α.length ≤ k) :
    ∃ g : ℝ^n → ℝ, HasWeakDerivativeOn univ α f g ∧ MemLp g 2 volume ∧
      ∫ x, g x ^ 2 ≤ ‖V‖ ^ 2 := by
  set c : DerivLp n 2 univ := (V : WkpAmbientOn n k 2 univ) (derivIndexOfList α hα) with hc
  have hmem : MemLp (c : ℝ^n → ℝ) 2 volume := by
    have h := Lp.memLp c
    simpa only [domainMeasure, Measure.restrict_univ] using h
  have hnorm : ∫ x, (c x) ^ 2 = ‖c‖ ^ 2 := by
    have h := Lp.norm_sq_eq_integral_sq c
    simpa only [domainMeasure, Measure.restrict_univ] using h.symm
  have hf' : baseRepresentative V =ᵐ[domainMeasure n univ] f := by
    simpa only [domainMeasure, Measure.restrict_univ] using hf
  refine ⟨(c : ℝ^n → ℝ), ?_, hmem, ?_⟩
  · exact (V.property.hasWeakDerivativeOn_list α hα).congr_ae hf' Filter.EventuallyEq.rfl
  · rw [hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (V : WkpAmbientOn n k 2 univ) _) 2

/-- **A weak derivative of a member of `Hᵏ(ℝⁿ)` with its first weak derivatives.** If `f` is in
the class of `V ∈ Hᵏ(ℝⁿ)` and `β` is a word of length less than `k`, then `f` has a weak
derivative `g = ∂^β f`, and `g` has weak derivatives `h j = ∂ⱼ g` that are square integrable,
with `∫ (h j)² ≤ ‖V‖²`. -/
theorem exists_hasWeakDerivativeOn_pair_of_ae_eq (V : W^{k,2}(ℝ^n)) {f : ℝ^n → ℝ}
    (hf : baseRepresentative V =ᵐ[volume] f) (β : List (Fin n)) (hβ : β.length + 1 ≤ k) :
    ∃ (g : ℝ^n → ℝ) (h : Fin n → ℝ^n → ℝ), HasWeakDerivativeOn univ β f g ∧
      (∀ j, HasWeakDerivativeOn univ [j] g (h j)) ∧ (∀ j, MemLp (h j) 2 volume) ∧
      ∀ j, ∫ x, h j x ^ 2 ≤ ‖V‖ ^ 2 := by
  have hβk : β.length ≤ k := by omega
  have hβj : ∀ j : Fin n, (β ++ [j]).length ≤ k := fun j ↦ by
    simpa only [List.length_append, List.length_singleton] using hβ
  set c : Fin n → DerivLp n 2 univ := fun j ↦
    (V : WkpAmbientOn n k 2 univ) (derivIndexOfList (β ++ [j]) (hβj j)) with hc
  have hmem : ∀ j, MemLp (c j : ℝ^n → ℝ) 2 volume := fun j ↦ by
    have h := Lp.memLp (c j)
    simpa only [domainMeasure, Measure.restrict_univ] using h
  have hnorm : ∀ j, ∫ x, (c j x) ^ 2 = ‖c j‖ ^ 2 := fun j ↦ by
    have h := Lp.norm_sq_eq_integral_sq (c j)
    simpa only [domainMeasure, Measure.restrict_univ] using h.symm
  have hf' : baseRepresentative V =ᵐ[domainMeasure n univ] f := by
    simpa only [domainMeasure, Measure.restrict_univ] using hf
  refine ⟨((V : WkpAmbientOn n k 2 univ) (derivIndexOfList β hβk) : ℝ^n → ℝ),
    fun j ↦ (c j : ℝ^n → ℝ), ?_, fun j ↦ ?_, hmem, fun j ↦ ?_⟩
  · exact (V.property.hasWeakDerivativeOn_list β hβk).congr_ae hf' Filter.EventuallyEq.rfl
  · exact V.property.hasWeakDerivativeOn_from_coordinate β [j]
      (by simpa only [List.length_singleton] using hβ)
  · rw [hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (V : WkpAmbientOn n k 2 univ) _) 2

/-- Mollification does not increase the `L²` norm: for `f ∈ L²`, `ρ_ε ∗ f` is square
integrable and `∫ (f ∗ ρ_ε)² ≤ ∫ f²`. -/
theorem integral_sq_convolution_scaled_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ^n → ℝ} (hf : MemLp f 2 volume) :
    MemLp (f ⋆[mul ℝ ℝ, volume] scaled μ ε) 2 volume ∧
      ∫ x, (f ⋆[mul ℝ ℝ, volume] scaled μ ε) x ^ 2 ≤ ∫ x, f x ^ 2 := by
  have hY := integral_sq_convolution_le hf (integrable_scaled μ hε)
  have h1 : ∫ y, ‖scaled μ ε y‖ = 1 := by
    rw [← scaled_integral_one μ hε]
    exact integral_congr_ae (.of_forall fun y ↦ Real.norm_of_nonneg (scaled_nonneg μ hε y))
  refine ⟨hY.1, hY.2.trans_eq ?_⟩
  rw [h1, one_pow, one_mul]

/-- The derivative `∂^α` of a mollification is the mollification of the weak derivative:
`f ∗ ∂^α ρ_ε = (∂^α f) ∗ ρ_ε`. -/
theorem convolution_iteratedPartialDeriv_scaled_eq {α : List (Fin n)} {f g : ℝ^n → ℝ}
    (hw : HasWeakDerivativeOn univ α f g) (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    (f ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (scaled μ ε)) =
      (g ⋆[mul ℝ ℝ, volume] scaled μ ε) := funext fun x ↦ by
  have h := convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn hw (scaled_contDiff μ)
    (scaled_hasCompactSupport μ hε) x (subset_univ _)
  rw [indicator_univ, indicator_univ] at h
  exact h

/-- **Mollification of a product of two `L⁴` functions**, in squares:
`‖ρ_ε ∗ (f g)‖_{L²} ≤ ‖f‖_{L⁴} ‖g‖_{L⁴}`. Young's inequality for the mollifier
(`integral_sq_convolution_scaled_le`) and Hölder's inequality for the product
(`MeasureTheory.lpNorm_mul_le`). -/
theorem integral_sq_convolution_mul_scaled_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {f g : ℝ^n → ℝ} (hf : MemLp f 4 volume) (hg : MemLp g 4 volume) :
    ∫ x, ((fun y ↦ f y * g y) ⋆[mul ℝ ℝ, volume] scaled μ ε) x ^ 2 ≤
      (lpNorm f 4 volume * lpNorm g 4 volume) ^ 2 := by
  have hfg : MemLp (fun y ↦ f y * g y) 2 volume := hf.fun_mul (r := 2) hg
  refine (integral_sq_convolution_scaled_le μ hε hfg).2.trans ?_
  rw [hfg.integral_sq_eq_lpNorm_sq]
  exact pow_le_pow_left₀ lpNorm_nonneg (lpNorm_mul_le hf hg) 2

/-- **Mollifications converge in `L²`**, as integrals of squares: for `f ∈ L²` and scales
`ε_k → 0`, `∫ (f ∗ ρ_{ε_k})² → ∫ f²`. -/
theorem tendsto_integral_sq_convolution_scaled (μ : Mollifier n) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) {f : ℝ^n → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun k ↦ ∫ x, (f ⋆[mul ℝ ℝ, volume] scaled μ (ε k)) x ^ 2) atTop
      (𝓝 (∫ x, f x ^ 2)) := by
  have hf' : MemLp f 2 (domainMeasure n univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using hf
  set u : DerivLp n 2 univ := hf'.toLp f with hu
  have hu_ae : (u : ℝ^n → ℝ) =ᵐ[volume] f := by
    have h := hf'.coeFn_toLp
    simpa only [domainMeasure, Measure.restrict_univ] using h
  have hnorm : Tendsto (fun k ↦ ‖mollifierRowCLM μ (hε k) u‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) :=
    (tendsto_mollifierRowCLM μ ε hε hε0 u).norm.pow 2
  have e1 : ‖u‖ ^ 2 = ∫ x, f x ^ 2 := by
    have h := Lp.norm_sq_eq_integral_sq u
    simp only [domainMeasure, Measure.restrict_univ] at h
    rw [h]
    exact integral_congr_ae (hu_ae.mono fun x hx ↦ congrArg (· ^ 2) hx)
  have e2 : ∀ k, ‖mollifierRowCLM μ (hε k) u‖ ^ 2 =
      ∫ x, (f ⋆[mul ℝ ℝ, volume] scaled μ (ε k)) x ^ 2 := fun k ↦ by
    have h := Lp.norm_sq_eq_integral_sq (mollifierRowCLM μ (hε k) u)
    simp only [domainMeasure, Measure.restrict_univ] at h
    rw [h]
    have h1 := (wholeSpaceL2Equiv_ae (mollifierRowCLM μ (hε k) u)).symm
    rw [wholeSpaceL2Equiv_mollifierRowCLM] at h1
    have h2 := convolutionL2CLM_ae_eq (scaled μ (ε k)) (integrable_scaled μ (hε k))
      (wholeSpaceL2Equiv u)
    have h3 : (scaled μ (ε k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (wholeSpaceL2Equiv u : ℝ^n → ℝ)) = (f ⋆[mul ℝ ℝ, volume] scaled μ (ε k)) := by
      rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl
        ((wholeSpaceL2Equiv_ae u).trans hu_ae)]
      exact convolution_lsmul_eq_convolution_mul _ _
    exact integral_congr_ae ((h1.trans (h2.trans (.of_forall fun x ↦ congrFun h3 x))).mono
      fun x hx ↦ congrArg (· ^ 2) hx)
  rw [← e1]
  exact hnorm.congr e2

/-- **Mollification does not increase the `L²` norm of a derivative** ((2.11) of Hou, Wang and
Yang). If `f` is in the class of `V ∈ Hᵏ(ℝⁿ)` and `α` is a word of length at most `k`, then
`f ∗ ∂^α ρ_ε`, which is `∂^α(ρ_ε ∗ f) = ρ_ε ∗ ∂^α f`, is square integrable with
`∫ (f ∗ ∂^α ρ_ε)² ≤ ‖V‖²`. -/
theorem integral_sq_convolution_iteratedPartialDeriv_scaled_le (V : W^{k,2}(ℝ^n))
    {f : ℝ^n → ℝ} (hf : baseRepresentative V =ᵐ[volume] f) (α : List (Fin n))
    (hα : α.length ≤ k) (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    MemLp (f ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (scaled μ ε)) 2 volume ∧
      ∫ x, (f ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (scaled μ ε)) x ^ 2 ≤ ‖V‖ ^ 2 := by
  obtain ⟨g, hg, hg2, hgV⟩ := exists_hasWeakDerivativeOn_of_ae_eq V hf α hα
  have hY := integral_sq_convolution_scaled_le μ hε hg2
  rw [convolution_iteratedPartialDeriv_scaled_eq hg μ hε]
  exact ⟨hY.1, hY.2.trans hgV⟩

/-- **From bounded derivatives of mollifications to the next Sobolev order.** Let `f` be in the
class of `V ∈ Hᵏ(ℝⁿ)` and let `μ` be a mollifier. If for every word `α` of length `k`, every
direction `j` and every `ε ∈ (0, 1)`

`∫ (∂ⱼ(f ∗ ∂^α ρ_ε))² ≤ C²`,

then `f` is in the class of a member of `H^{k+1}(ℝⁿ)`. The function `f ∗ ∂^α ρ_ε` is the
derivative `∂^α` of the mollification `ρ_ε ∗ f`. -/
theorem exists_wkpSpace_succ_of_bounded_convolution (V : W^{k,2}(ℝ^n)) {f : ℝ^n → ℝ}
    (hf : baseRepresentative V =ᵐ[volume] f) (μ : Mollifier n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ α : List (Fin n), α.length = k → ∀ j : Fin n, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∫ x, (∂[j] (f ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (scaled μ ε)) x) ^ 2 ≤ C ^ 2) :
    ∃ U : W^{k + 1,2}(ℝ^n), baseRepresentative U =ᵐ[volume] f := by
  have hf' : baseRepresentative V =ᵐ[domainMeasure n univ] f := by
    simpa only [domainMeasure, Measure.restrict_univ] using hf
  suffices htop : ∀ α' : List (Fin n), α'.length = k + 1 → ∃ v : DerivLp n 2 univ,
      ‖v‖ ≤ C ∧ HasWeakDerivativeOn univ α' (baseRepresentative V) v by
    obtain ⟨U, hU, -⟩ := exists_succ_order_of_top_derivatives V hC htop
    have hU' : baseRepresentative U =ᵐ[volume] baseRepresentative V := by
      simpa only [domainMeasure, Measure.restrict_univ] using hU
    exact ⟨U, hU'.trans hf⟩
  intro α' hα'
  -- Split the word into a word of length `k` and one more direction.
  have hne : α' ≠ [] := fun h ↦ by simp [h] at hα'
  have hsplit : α'.dropLast ++ [α'.getLast hne] = α' := List.dropLast_append_getLast hne
  have hαlen : α'.dropLast.length = k := by rw [List.length_dropLast, hα']; rfl
  have hαk : α'.dropLast.length ≤ k := hαlen.le
  set α := α'.dropLast with hαdef
  set j := α'.getLast hne with hjdef
  set c : DerivLp n 2 univ := (V : WkpAmbientOn n k 2 univ) (derivIndexOfList α hαk) with hc
  have hcV : HasWeakDerivativeOn univ α (baseRepresentative V) c :=
    V.property.hasWeakDerivativeOn_list α hαk
  have hcf : HasWeakDerivativeOn univ α f c := hcV.congr_ae hf' Filter.EventuallyEq.rfl
  have hcmem : MemLp (c : ℝ^n → ℝ) 2 volume := by
    have h := Lp.memLp c
    simpa only [domainMeasure, Measure.restrict_univ] using h
  have hcloc : LocallyIntegrable (c : ℝ^n → ℝ) volume := hcmem.locallyIntegrable one_le_two
  -- A sequence of scales in `(0, 1)` that tends to zero.
  let ε : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 2)
  have hε : ∀ m, 0 < ε m := fun m ↦ by positivity
  have hε1 : ∀ m, ε m < 1 := fun m ↦ by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [div_lt_one (by positivity)]
    linarith
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  -- The constant one, as a bounded multiplier.
  let b : DerivLp n ∞ univ := (memLp_top_const (1 : ℝ)).toLp _
  have hb1 : (b : ℝ^n → ℝ) =ᵐ[domainMeasure n univ] fun _ ↦ (1 : ℝ) := MemLp.coeFn_toLp _
  have hb : ∀ᵐ x ∂domainMeasure n univ, x ∈ univ → b x = 1 := hb1.mono fun x hx _ ↦ hx
  suffices hrow : ∀ m, ‖b • mollifierDerivativeRowCLM μ (hε m) j c‖ ≤ C by
    obtain ⟨v, hvC, hv⟩ := exists_L2_weakDerivativeOn_of_bounded_mollifierDerivativeRowCLM μ ε
      hε hε0 j c b univ hb C hrow
    refine ⟨v, hvC, ?_⟩
    rw [← hsplit]
    exact hcV.append_single j hv
  intro m
  -- The uniform bound, from the hypothesis on the convolutions.
  have hρ : ContDiff ℝ (⊤ : ℕ∞) (scaled μ (ε m)) := scaled_contDiff μ
  have hρc : HasCompactSupport (scaled μ (ε m)) := scaled_hasCompactSupport μ (hε m)
  set w : DerivLp n 2 univ := mollifierDerivativeRowCLM μ (hε m) j c with hw
  -- The row is `∂ⱼ(c ∗ ρ_ε)` almost everywhere.
  have hw1 : (w : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ∂[j] ((c : ℝ^n → ℝ) ⋆[mul ℝ ℝ, volume] scaled μ (ε m)) x := by
    have h1 := (wholeSpaceL2Equiv_ae w).symm
    rw [wholeSpaceL2Equiv_mollifierDerivativeRowCLM] at h1
    have h2 := convolutionL2CLM_ae_eq (∂[j] (scaled μ (ε m)))
      (integrable_fderiv_scaled_apply μ (hε m) j) (wholeSpaceL2Equiv c)
    have h3 : (∂[j] (scaled μ (ε m)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (wholeSpaceL2Equiv c : ℝ^n → ℝ)) =
        ((c : ℝ^n → ℝ) ⋆[mul ℝ ℝ, volume] ∂[j] (scaled μ (ε m))) := by
      rw [convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl
        (wholeSpaceL2Equiv_ae c)]
      exact convolution_lsmul_eq_convolution_mul _ _
    refine h1.trans (h2.trans (.of_forall fun x ↦ ?_))
    rw [h3]
    exact (convolution_partialDeriv_right (c : ℝ^n → ℝ) (scaled μ (ε m)) hcloc hρc
      (hρ.of_le (by simp)) j x).symm
  -- Move the weak derivative to the kernel.
  have hfun : ((c : ℝ^n → ℝ) ⋆[mul ℝ ℝ, volume] scaled μ (ε m)) =
      (f ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (scaled μ (ε m))) := funext fun x ↦ by
    have h := convolution_iteratedPartialDeriv_eq_of_hasWeakDerivativeOn hcf hρ hρc x
      (subset_univ _)
    rw [indicator_univ, indicator_univ] at h
    exact h.symm
  rw [hfun] at hw1
  have hbw : ((b • w : DerivLp n 2 univ) : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ∂[j] (f ⋆[mul ℝ ℝ, volume] iteratedPartialDeriv α (scaled μ (ε m))) x := by
    have h1 := Lp.coeFn_lpSMul (r := 2) b w
    simp only [domainMeasure, Measure.restrict_univ] at h1 hb1
    filter_upwards [h1, hb1, hw1] with x hx1 hx2 hx3
    rw [hx1]
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [hx2, one_mul, hx3]
  have hsq : ‖b • w‖ ^ 2 ≤ C ^ 2 := by
    have h := Lp.norm_sq_eq_integral_sq (b • w : DerivLp n 2 univ)
    simp only [domainMeasure, Measure.restrict_univ] at h
    rw [h, integral_congr_ae (hbw.mono fun x hx ↦ congrArg (· ^ 2) hx)]
    exact hbound α hαlen j (ε m) (hε m) (hε1 m)
  exact (sq_le_sq₀ (norm_nonneg _) hC).mp hsq

end SobolevSpace.Approximation
