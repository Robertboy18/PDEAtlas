/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Mollification.FiniteJets
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure

/-!
# Finite regularity multipliers for chart iteration

A compactly supported `C^k` coefficient multiplies `W^{k,p}` into itself, including the
endpoints `p = 1` and `p = ∞`. Mollification converges uniformly in every available classical
derivative. Hölder multiplication therefore makes each weak Leibniz row converge in `L^p`,
and closedness of weak differentiation supplies the product.

On a bounded set, a smooth cutoff first makes any global `C^k` coefficient compactly
supported without changing its value on the set. This is the multiplier needed for the
derivative entries of a `C^k` chart; no additional derivative of the chart is required.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology

namespace SobolevSpace.Extension.HigherOrder

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

omit [Fact (1 ≤ p)] in
/-- A finite list sum of `Lᵖ` functions belongs to `Lᵖ`. -/
theorem memLp_list_sum {ι : Type*} (l : List ι) (f : ι → ℝ^n → ℝ)
    (hf : ∀ i ∈ l, MemLp (f i) p (domainMeasure n Ω)) :
    MemLp (fun x ↦ (l.map fun i ↦ f i x).sum) p (domainMeasure n Ω) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    exact (hf i (by simp)).add (ih fun j hj ↦ hf j (by simp [hj]))

/-- Convergence in `Lᵖ` is preserved by a fixed finite list sum. -/
theorem tendsto_toLp_list_sum {ι : Type*} (l : List ι)
    (f : ℕ → ι → ℝ^n → ℝ) (g : ι → ℝ^n → ℝ)
    (hf : ∀ j i, i ∈ l → MemLp (f j i) p (domainMeasure n Ω))
    (hg : ∀ i ∈ l, MemLp (g i) p (domainMeasure n Ω))
    (hfg : ∀ i (hi : i ∈ l), Tendsto (fun j ↦ (hf j i hi).toLp (f j i))
      atTop (𝓝 ((hg i hi).toLp (g i)))) :
    Tendsto
      (fun j ↦ (memLp_list_sum l (f j) (hf j)).toLp
        (fun x ↦ (l.map fun i ↦ f j i x).sum))
      atTop (𝓝 ((memLp_list_sum l g hg).toLp (fun x ↦ (l.map fun i ↦ g i x).sum))) := by
  induction l with
  | nil => simpa using tendsto_const_nhds
  | cons i l ih =>
    have ht := (hfg i (by simp)).add
      (ih (fun j a ha ↦ hf j a (by simp [ha]))
        (fun a ha ↦ hg a (by simp [ha])) (fun a ha ↦ hfg a (by simp [ha])))
    exact ht

/-- Uniform convergence of essentially bounded functions gives convergence in `L∞`. -/
theorem tendsto_toLp_top_of_uniform {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j, MemLp (f j) ∞ (domainMeasure n Ω))
    (hg : MemLp g ∞ (domainMeasure n Ω)) (hfg : TendstoUniformly f g atTop) :
    Tendsto (fun j ↦ (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hf _ hg).2
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by simp : (1 : ℝ≥0∞) ≠ ∞) hε.ne'
  filter_upwards [Metric.tendstoUniformly_iff.mp hfg δ hδ] with j hj
  rw [eLpNorm_exponent_top ((hf j).sub hg).aestronglyMeasurable]
  apply (eLpNormEssSup_le_of_ae_bound (C := (δ : ℝ)) ?_).trans
    (by simpa using hδε.le)
  exact Eventually.of_forall fun x ↦ by
    simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (hj x).le

/-- Pointwise multiplication of representatives agrees with the bounded Hölder product. -/
theorem toLp_mul_eq_holder {a f : ℝ^n → ℝ}
    (ha : MemLp a ∞ (domainMeasure n Ω)) (hf : MemLp f p (domainMeasure n Ω)) :
    (ha.fun_mul hf).toLp (fun x ↦ a x * f x) =
      (ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure n Ω) ∞ p p
        (ha.toLp a) (hf.toLp f) := by
  apply Lp.ext
  filter_upwards [(ha.fun_mul (r := p) hf).coeFn_toLp, ha.coeFn_toLp, hf.coeFn_toLp,
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p) (ha.toLp a) (hf.toLp f)]
    with x hx ha hf hh
  change _ = ContinuousLinearMap.holder p (ContinuousLinearMap.mul ℝ ℝ) _ _ x
  rw [hx, hh, ha, hf]
  rfl

omit [Fact (1 ≤ p)] in
/-- Bounded classical coefficient derivatives make every weak Leibniz row belong to `Lᵖ`. -/
theorem weakLeibnizExpansion_memLp (U : W^{k,p}(Ω)) (a : ℝ^n → ℝ)
    (ha : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β a) ∞ (domainMeasure n Ω))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    MemLp (weakLeibnizExpansion a (wkpWordRepresentative U) α) p
      (domainMeasure n Ω) := by
  apply memLp_list_sum (derivativeSplits α)
    (fun q x ↦ iteratedPartialDeriv q.1 a x * wkpWordRepresentative U q.2 x)
  intro q hq
  have hlen := derivativeSplits_length hq
  exact (ha q.1 (by omega)).fun_mul (wkpWordRepresentative_memLp U q.2 (by omega))

/-- Uniform convergence of coefficient derivatives gives `Lᵖ` convergence of each weak
Leibniz row, with the Sobolev factor fixed. -/
theorem tendsto_toLp_weakLeibnizExpansion_of_uniform (U : W^{k,p}(Ω))
    (a : ℕ → ℝ^n → ℝ) (b : ℝ^n → ℝ)
    (ha : ∀ j β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β (a j)) ∞ (domainMeasure n Ω))
    (hb : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β b) ∞ (domainMeasure n Ω))
    (hab : ∀ β, β.length ≤ k →
      TendstoUniformly (fun j ↦ iteratedPartialDeriv β (a j))
        (iteratedPartialDeriv β b) atTop)
    (α : List (Fin n)) (hα : α.length ≤ k) :
    Tendsto (fun j ↦
      (weakLeibnizExpansion_memLp U (a j) (ha j) α hα).toLp
        (weakLeibnizExpansion (a j) (wkpWordRepresentative U) α))
      atTop (𝓝 ((weakLeibnizExpansion_memLp U b hb α hα).toLp
        (weakLeibnizExpansion b (wkpWordRepresentative U) α))) := by
  let f := fun j (q : List (Fin n) × List (Fin n)) x ↦
    iteratedPartialDeriv q.1 (a j) x * wkpWordRepresentative U q.2 x
  let g := fun (q : List (Fin n) × List (Fin n)) x ↦
    iteratedPartialDeriv q.1 b x * wkpWordRepresentative U q.2 x
  have hmem j q (hq : q ∈ derivativeSplits α) :
      MemLp (f j q) p (domainMeasure n Ω) := by
    have hlen := derivativeSplits_length hq
    exact (ha j q.1 (by omega)).fun_mul (wkpWordRepresentative_memLp U q.2 (by omega))
  have hg q (hq : q ∈ derivativeSplits α) :
      MemLp (g q) p (domainMeasure n Ω) := by
    have hlen := derivativeSplits_length hq
    exact (hb q.1 (by omega)).fun_mul (wkpWordRepresentative_memLp U q.2 (by omega))
  apply tendsto_toLp_list_sum (derivativeSplits α) f g hmem hg
  intro q hq
  have hlen := derivativeSplits_length hq
  have hq₁ : q.1.length ≤ k := by omega
  have hq₂ : q.2.length ≤ k := by omega
  let d := (wkpWordRepresentative_memLp U q.2 hq₂).toLp (wkpWordRepresentative U q.2)
  have ht := (((ContinuousLinearMap.mul ℝ ℝ).holderL
    (domainMeasure n Ω) ∞ p p).flip d).continuous.tendsto
      ((hb q.1 hq₁).toLp (iteratedPartialDeriv q.1 b))
  convert ht.comp (tendsto_toLp_top_of_uniform (fun j ↦ ha j q.1 hq₁)
    (hb q.1 hq₁) (hab q.1 hq₁)) using 1
  · funext j
    exact toLp_mul_eq_holder (ha j q.1 hq₁) (wkpWordRepresentative_memLp U q.2 hq₂)
  · congr 1
    exact toLp_mul_eq_holder (hb q.1 hq₁) (wkpWordRepresentative_memLp U q.2 hq₂)

/-- Multiplication by a compactly supported `C^k` function preserves every `W^{k,p}`,
with the exact weak Leibniz rows. The exponent may equal either endpoint. -/
theorem exists_mul_contDiff_compact (a : ℝ^n → ℝ) (ha : ContDiff ℝ k a)
    (hac : HasCompactSupport a) (U : W^{k,p}(Ω)) :
    ∃ W : W^{k,p}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] (fun x ↦ a x * baseRepresentative U x) ∧
      ∀ α : DerivIndex n k,
        ((W : WkpAmbientOn n k p Ω) α : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          weakLeibnizExpansion a (wkpWordRepresentative U) α.toList.reverse := by
  let ε := fun j : ℕ ↦ 1 / ((j : ℝ) + 1)
  have hε j : 0 < ε j := by dsimp [ε]; positivity
  have hεle j : ε j ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).2 (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let μ := Approximation.standardMollifier n
  let as := fun j ↦ Approximation.mollify μ (ε j) a
  have has j : ContDiff ℝ (⊤ : ℕ∞) (as j) :=
    Approximation.mollify_contDiff_of_pos μ (hε j) a ha.continuous.locallyIntegrable
  obtain ⟨K, hK, _, hKs⟩ :=
    Approximation.exists_common_compact_mollify_support μ hac ε hε hεle
  have hasc j : HasCompactSupport (as j) :=
    HasCompactSupport.of_support_subset_isCompact hK ((subset_tsupport _).trans (hKs j))
  have ham β (hβ : β.length ≤ k) :
      MemLp (iteratedPartialDeriv β a) ∞ (domainMeasure n Ω) :=
    (PDE.contDiff_iteratedPartialDeriv_of_le ha β hβ).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv hac β) _
  have hasm j β (_hβ : β.length ≤ k) :
      MemLp (iteratedPartialDeriv β (as j)) ∞ (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv (has j) β).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv (hasc j) β) _
  have hconv β (hβ : β.length ≤ k) :
      TendstoUniformly (fun j ↦ iteratedPartialDeriv β (as j))
        (iteratedPartialDeriv β a) atTop :=
    Approximation.iteratedPartialDeriv_mollify_tendstoUniformly μ ha hac ε hε hεle hε0 β hβ
  let rows := fun α : DerivIndex n k ↦
    weakLeibnizExpansion a (wkpWordRepresentative U) α.toList.reverse
  let base := fun x ↦ a x * baseRepresentative U x
  have hbase : rows (baseIndex n k) = base := by
    simp [rows, base, baseRepresentative]
  have hmem α : MemLp (rows α) p (domainMeasure n Ω) :=
    weakLeibnizExpansion_memLp U a ham α.toList.reverse (by simpa using α.toList_length_le)
  have hweak α : HasWeakDerivativeOn Ω α.toList base (rows α) := by
    have hlen : α.toList.reverse.length ≤ k := by simpa using α.toList_length_le
    have ht β hβ := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
      (fun j ↦ weakLeibnizExpansion_memLp U (as j) (hasm j) β hβ) _
      (weakLeibnizExpansion_memLp U a ham β hβ)).1
        (tendsto_toLp_weakLeibnizExpansion_of_uniform U as a hasm ham hconv β hβ)
    have hw := WeakChangeOfVariables.hasWeakDerivativeOn_of_tendsto_eLpNorm
      (fun j ↦ weakLeibnizExpansion_memLp U (as j) (hasm j) [] (by simp))
      (fun j ↦ weakLeibnizExpansion_memLp U (as j) (hasm j) α.toList.reverse hlen)
      (weakLeibnizExpansion_memLp U a ham [] (by simp)) (hmem α)
      (fun j ↦ by
        simpa only [weakLeibnizExpansion_nil, wkpWordRepresentative_nil] using
          U.hasWeakDerivativeOn_mul_smooth (as j) (has j) (hasm j)
            α.toList α.toList_length_le)
      (ht [] (by simp)) (ht α.toList.reverse hlen)
    simpa only [weakLeibnizExpansion_nil, wkpWordRepresentative_nil, base,
      baseRepresentative, rows] using hw
  refine ⟨mkWkpSpaceOnOfWeakDerivatives base rows hbase hmem hweak, ?_, ?_⟩
  · simpa only [baseRepresentative, hbase, base] using
      mkWkpSpaceOnOfWeakDerivatives_apply_ae base rows hbase hmem hweak (baseIndex n k)
  · exact mkWkpSpaceOnOfWeakDerivatives_apply_ae base rows hbase hmem hweak

/-- A global `C^k` coefficient multiplies `W^{k,p}` on any bounded measurable set.
Compactification supplies all coefficient bounds; none are assumed as Sobolev data. -/
theorem exists_mul_contDiff_on_bounded (hΩ : MeasurableSet Ω)
    (hbounded : Bornology.IsBounded Ω) (a : ℝ^n → ℝ) (ha : ContDiff ℝ k a)
    (U : W^{k,p}(Ω)) :
    ∃ W : W^{k,p}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] fun x ↦ a x * baseRepresentative U x := by
  obtain ⟨ψ, _, hψ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ hbounded.isCompact_closure (subset_univ _)
  obtain ⟨W, hW, _⟩ := exists_mul_contDiff_compact
    (fun x ↦ ψ.toFun x * a x) ((ψ.contDiff.of_le (by simp)).mul ha)
    ψ.hasCompactSupport.mul_right U
  refine ⟨W, ?_⟩
  filter_upwards [hW, ae_restrict_mem hΩ] with x hx hxΩ
  simpa only [hψ x (subset_closure hxΩ), one_mul] using hx

end SobolevSpace.Extension.HigherOrder
