/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Global
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Supercritical Sobolev fields from compactly supported square-integrable jets

A common finite-measure support allows every derivative coordinate to be placed in a
lower `Lᵖ` space. For `r = n / 2` (integer division), choosing `p = 2n / (2r + 1)`
lets the global Sobolev inequality spend `r` derivatives and reach exponent `2n`.
Thus a compactly supported `W^{k+1+r,2}` field supplies a global `W^{k+1,2n}` field
with the same base representative.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set

variable {n k r : ℕ}

/-- The global higher-order Sobolev inequality applies to all retained derivative
coordinates simultaneously, preserving their weak derivative identities. -/
theorem exists_global_sobolev_of_inv_eq
    {p q : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hsub : (r : ℝ) * p < n)
    (hq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (r : ℝ) * (n : ℝ)⁻¹)
    (U : W^{k + r,(p : ℝ≥0∞)}(ℝ^n)) :
    ∃ V : W^{k,(q : ℝ≥0∞)}(ℝ^n), ∀ a : DerivIndex n k,
      (((V : WkpAmbientOn n k (q : ℝ≥0∞) univ) a :
        DerivLp n (q : ℝ≥0∞) univ) : ℝ^n → ℝ) =ᵐ[volume]
      (((U : WkpAmbientOn n (k + r) (p : ℝ≥0∞) univ)
        (a.castOrder (Nat.le_add_right k r)) :
        DerivLp n (p : ℝ≥0∞) univ) : ℝ^n → ℝ) := by
  have hp : 1 ≤ p := ENNReal.one_le_coe_iff.mp Fact.out
  have hn : 0 < n := by
    have h0 : (0 : ℝ) ≤ (r : ℝ) * p := by positivity
    exact_mod_cast h0.trans_lt hsub
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
    ((U : WkpAmbientOn n (k + r) (p : ℝ≥0∞) univ)
      (a.castOrder (Nat.le_add_right k r)) : DerivLp n (p : ℝ≥0∞) univ)
  have hmem (a : DerivIndex n k) :
      MemLp (d a) (q : ℝ≥0∞) (domainMeasure n univ) := by
    simpa [d, domainMeasure] using
      Inequalities.memLp_derivativeWord_of_inv_eq hp hn hsub hq
        a.toList (Nat.add_le_add_right a.toList_length_le r) U
  have hweak (a : DerivIndex n k) :
      HasWeakDerivativeOn (n := n) univ a.toList (d (baseIndex n k)) (d a) := by
    simpa [d] using
      (lowerOrderCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := univ)
        (Nat.le_add_right k r) U).property a
  refine ⟨mkWkpSpaceOnOfWeakDerivatives
    (d (baseIndex n k)) d rfl hmem hweak, ?_⟩
  intro a
  simpa only [domainMeasure, Measure.restrict_univ] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (d (baseIndex n k)) d rfl hmem hweak a

/-- Every row of a cutoff extension vanishes almost everywhere outside the support
of the cutoff, including rows of arbitrary positive order. -/
theorem extendByCutoff_hasCoordinateSupportIn
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {V Ω : Set (ℝ^n)}
    (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (U : W^{k,p}(V)) :
    HasCoordinateSupportIn (tsupport ψ.toFun)
      (CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff hV hVΩ ψ hψ U) := by
  intro a
  filter_upwards
    [CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_coordinate_ae
      hV hVΩ ψ hψ U a] with x hx
  by_cases hxs : x ∈ tsupport ψ.toFun
  · simp only [Set.indicator_of_mem hxs]
  · rw [Set.indicator_of_notMem hxs, hx]
    exact (Function.notMem_support.mp fun h ↦
      hxs (CompactSupportLocalization.HigherOrderLocalizedCutoff.weakLeibnizExpansion_support
        U ψ a.toList.reverse h)).symm

/-- A compactly supported square-integrable jet of order `k + 1 + n / 2` has a global
representative in `W^{k+1,q}` for some finite `q > n`. The construction uses `q = 2n`
and preserves the base almost everywhere; it assumes no boundary atlas. -/
theorem exists_global_supercritical_of_finiteMeasureSupport
    (hn : 0 < n)
    (s : Set (ℝ^n)) (hs : volume s ≠ ∞)
    (U : W^{k + 1 + n / 2,2}(ℝ^n)) (hsupp : HasCoordinateSupportIn s U) :
    ∃ q : NNReal, 1 ≤ q ∧ (n : ℝ) < q ∧
      ∃ V : W^{k + 1,(q : ℝ≥0∞)}(ℝ^n),
        baseRepresentative V =ᵐ[volume] baseRepresentative U := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hhalfLo : 2 * ((n / 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (show 2 * (n / 2) ≤ n by omega)
  have hhalfHi : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
  have hden : 0 < 2 * ((n / 2 : ℕ) : ℝ) + 1 := by positivity
  let p : NNReal := ⟨2 * n / (2 * ((n / 2 : ℕ) : ℝ) + 1), by positivity⟩
  let q : NNReal := 2 * n
  have hpR : (p : ℝ) = 2 * n / (2 * ((n / 2 : ℕ) : ℝ) + 1) := rfl
  have hqR : (q : ℝ) = 2 * n := by simp [q]
  have hp1 : (1 : NNReal) ≤ p := by
    change (1 : ℝ) ≤ 2 * n / (2 * ((n / 2 : ℕ) : ℝ) + 1)
    exact (le_div_iff₀ hden).2 (by linarith)
  have hp2 : p ≤ (2 : NNReal) := by
    change 2 * (n : ℝ) / (2 * ((n / 2 : ℕ) : ℝ) + 1) ≤ 2
    exact (div_le_iff₀ hden).2 (by linarith)
  have hq1 : (1 : NNReal) ≤ q := by
    change (1 : ℝ) ≤ (q : ℝ)
    rw [hqR]
    linarith
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp1⟩
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
  have hsub : ((n / 2 : ℕ) : ℝ) * p < n := by
    rw [hpR, ← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hinv : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - ((n / 2 : ℕ) : ℝ) * (n : ℝ)⁻¹ := by
    rw [hqR, hpR]
    field_simp [show (n : ℝ) ≠ 0 by linarith, hden.ne']
    ring
  have hs' : domainMeasure n univ s ≠ ∞ := by
    simpa only [domainMeasure, Measure.restrict_univ] using hs
  let W : W^{k + 1 + n / 2,(p : ℝ≥0∞)}(ℝ^n) :=
    lowerExponentOfFiniteMeasureSupport (q := (p : ℝ≥0∞))
      (by exact_mod_cast hp2) s hs' U hsupp
  have hW : baseRepresentative W =ᵐ[volume] baseRepresentative U := by
    simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using
      lowerExponentOfFiniteMeasureSupport_apply_ae
        (q := (p : ℝ≥0∞)) (by exact_mod_cast hp2) s hs' U hsupp
        (baseIndex n (k + 1 + n / 2))
  obtain ⟨V, hV⟩ := exists_global_sobolev_of_inv_eq (k := k + 1) (r := n / 2)
     hsub hinv W
  refine ⟨q, hq1, ?_, V, ?_⟩
  · rw [hqR]
    linarith
  · apply Filter.EventuallyEq.trans _ hW
    simpa only [baseRepresentative, DerivIndex.castOrder_baseIndex] using hV (baseIndex n (k + 1))

/-- A smooth compactly supported localization of a `W^{k+1+n/2,2}` field on an arbitrary
open set has a global `W^{k+1,q}` representative for some finite `q > n`. Its base
agrees with the cutoff times the original base on all of Euclidean space. -/
theorem exists_global_supercritical_cutoff
    (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ Ω)
    (U : W^{k + 1 + n / 2,2}(Ω)) :
    ∃ q : NNReal, 1 ≤ q ∧ (n : ℝ) < q ∧
      ∃ V : W^{k + 1,(q : ℝ≥0∞)}(ℝ^n),
        baseRepresentative V =ᵐ[volume] fun x ↦ ψ.toFun x * baseRepresentative U x := by
  let W : W^{k + 1 + n / 2,2}(ℝ^n) :=
    CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff
      hΩ (subset_univ Ω) ψ hψ U
  obtain ⟨q, hq, hqn, V, hV⟩ := exists_global_supercritical_of_finiteMeasureSupport
    hn (tsupport ψ.toFun) ψ.hasCompactSupport.isCompact.measure_ne_top W
    (extendByCutoff_hasCoordinateSupportIn hΩ (subset_univ Ω) ψ hψ U)
  refine ⟨q, hq, hqn, V, hV.trans ?_⟩
  simpa only [domainMeasure, Measure.restrict_univ] using
    CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
      hΩ (subset_univ Ω) ψ hψ U

/-- Near every point of an open domain, a square-integrable Sobolev field of order
at least `k + 1 + n / 2` agrees almost everywhere with a global `W^{k+1,q}` field
for some finite `q > n`. The neighborhood and cutoff are constructed from openness. -/
theorem exists_global_supercritical_on_nhds
    {m : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (U : W^{m,2}(Ω)) (hm : k + 1 + n / 2 ≤ m)
    {x : ℝ^n} (hx : x ∈ Ω) :
    ∃ N : Set (ℝ^n), IsOpen N ∧ x ∈ N ∧ N ⊆ Ω ∧
      ∃ q : NNReal, 1 ≤ q ∧ (n : ℝ) < q ∧
        ∃ V : W^{k + 1,(q : ℝ≥0∞)}(ℝ^n),
          baseRepresentative V =ᵐ[domainMeasure n N] baseRepresentative U := by
  obtain ⟨ψ, hψ, _, hψnhds, _⟩ := TestFunction.exists_eq_one_on_compact
    hΩ (isCompact_singleton (x := x)) (by simpa using hx)
  obtain ⟨N, hN, hNopen, hxN⟩ := mem_nhds_iff.mp (hψnhds x (by simp))
  obtain ⟨q, hq, hqn, V, hV⟩ := exists_global_supercritical_cutoff hn hΩ ψ hψ
    (lowerOrderCLM (n := n) (p := 2) (Ω := Ω) hm U)
  have hbase : baseRepresentative V =ᵐ[volume]
      fun y ↦ ψ.toFun y * baseRepresentative U y := by
    simpa [baseRepresentative] using hV
  refine ⟨N ∩ Ω, hNopen.inter hΩ, ⟨hxN, hx⟩, inter_subset_right, q, hq, hqn, V, ?_⟩
  filter_upwards [ae_restrict_of_ae hbase,
    ae_restrict_mem (hNopen.inter hΩ).measurableSet] with y hy hyN
  rw [hy, show ψ.toFun y = 1 from hN hyN.1, one_mul]

end SobolevSpace.GraphSpace
