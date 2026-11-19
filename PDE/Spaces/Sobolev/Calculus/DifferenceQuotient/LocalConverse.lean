/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalVector
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.LocalPairing
import PDE.Analysis.MeasureTheory.Lp.EuclideanReflexivity
import PDE.Analysis.WeakCompactness

/-!
# Local Sobolev regularity from bounded difference quotients

The weak limit is taken in Euclidean-valued Lp, so the resulting full gradient has
the same norm bound as the vector of difference quotients. Compactly supported tests
identify its coordinates without any extension or integrability assumption outside
the open test domain.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set Rellich NormedSpace PDE.Analysis
open scoped Distributions ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform vector quotient bounds along any nonzero sequence tending to zero construct
a Sobolev function with the prescribed base representative and the same gradient bound. -/
theorem exists_sobolev_of_vectorDifference_sequence
    (hp : 1 < p) (hp_top : p ≠ ∞) {V : Set (ℝ^n)} (hV : IsOpen V)
    {u : ℝ^n → ℝ} (hu : MemLp u p (domainMeasure n V))
    (h : ℕ → ℝ) (hzero : Tendsto h atTop (𝓝 0)) (hne : ∀ m, h m ≠ 0)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ m, eLpNorm (vectorDifference (h m) u) p (domainMeasure n V) ≤
      ENNReal.ofReal C) :
    ∃ U : W^{1,p}(V),
      baseRepresentative U =ᵐ[domainMeasure n V] u ∧ ‖∇ U‖ ≤ C := by
  let q := ENNReal.conjExponent p
  have : ENNReal.HolderConjugate p q := inferInstance
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp).ne
  have hs_mem (m : ℕ) : MemLp (vectorDifference (h m) u) p (domainMeasure n V) :=
    (hbound m).trans_lt ENNReal.ofReal_lt_top
  let s (m : ℕ) : Lp (ℝ^n) p (domainMeasure n V) :=
    (hs_mem m).toLp (vectorDifference (h m) u)
  have hs_bound (m : ℕ) : ‖s m‖ ≤ C := by
    rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound m)).trans_eq
      (ENNReal.toReal_ofReal hC)
  have hs_bounded : Bornology.IsBounded (range s) :=
    isBounded_iff_forall_norm_le.2 ⟨C, forall_mem_range.2 hs_bound⟩
  obtain ⟨gw, F, hF, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter_of_reflexive
      (Lp.surjective_inclusionInDoubleDual_euclidean hp hp_top) atTop s hs_bounded
  let g : Lp (ℝ^n) p (domainMeasure n V) :=
    (toWeakSpace ℝ (Lp (ℝ^n) p (domainMeasure n V))).symm gw
  have hg_bound : ‖g‖ ≤ C :=
    WeakCompactness.norm_le_of_tendsto_of_norm_le hweak
      (Eventually.of_forall hs_bound)
  let P (i : Fin n) : ℝ^n →L[ℝ] ℝ := EuclideanSpace.proj i
  let gi (i : Fin n) : DerivLp n p V := (P i).compLpL p (domainMeasure n V) g
  have hgi (i : Fin n) : HasWeakDerivativeOn V [i] u (gi i) := by
    refine ⟨memLp_locallyIntegrableOn_domain hu (Fact.out : 1 ≤ p),
      memLp_locallyIntegrableOn_domain (Lp.memLp (gi i)) (Fact.out : 1 ≤ p), ?_⟩
    intro φ hφ
    let si (m : ℕ) : DerivLp n p V := (P i).compLpL p (domainMeasure n V) (s m)
    have hsi (m : ℕ) :
        (si m : ℝ^n → ℝ) =ᵐ[domainMeasure n V] forwardDifference i (h m) u := by
      filter_upwards [(P i).coeFn_compLpL (s m), (hs_mem m).coeFn_toLp] with x hx hy
      exact hx.trans (congrArg (fun z : ℝ^n ↦ z i) hy)
    let φV : DerivLp n q V := restrictDerivLp (subset_univ V) (testFunctionLp q φ)
    have hφV : (φV : ℝ^n → ℝ) =ᵐ[domainMeasure n V] φ.toFun :=
      (restrictDerivLp_apply_ae (subset_univ V) (testFunctionLp q φ)).trans
        ((testFunctionLp_apply_ae q φ).filter_mono (ae_mono Measure.restrict_le_self))
    let ell : StrongDual ℝ (Lp (ℝ^n) p (domainMeasure n V)) :=
      (((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n V) p q).flip φV
        ).comp ((P i).compLpL p (domainMeasure n V))
    have heval := WeakCompactness.tendsto_evaluation hweak ell
    have hpair (v : DerivLp n p V) :
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n V) p q v φV =
          ∫ x, v x * φ.toFun x ∂domainMeasure n V := by
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      exact integral_congr_ae <| hφV.mono fun x hx ↦ by
        simp only [ContinuousLinearMap.mul_apply', hx]
    change Tendsto (fun m ↦
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n V) p q (si m) φV)
      (F : Filter ℕ)
      (𝓝 ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n V) p q (gi i) φV))
      at heval
    simp only [hpair] at heval
    have hdist := (tendsto_integral_local_quotient hV hq hu i h hzero hne si hsi φ hφ
      ).mono_left hF
    have heq := tendsto_nhds_unique heval hdist
    simp only [iteratedPartialDeriv, List.length_cons, List.length_nil, Nat.zero_add,
      pow_one, neg_mul, one_mul]
    change (∫ x, u x * (∂[i] φ.toFun) x ∂domainMeasure n V) =
      -(∫ x, gi i x * φ.toFun x ∂domainMeasure n V)
    linarith
  let d : DerivIndex n 1 → ℝ^n → ℝ := firstOrderRows u (fun i ↦ (gi i : ℝ^n → ℝ))
  have hd_base : d (baseIndex n 1) = u := firstOrderRows_baseIndex _ _
  have hd_mem (a : DerivIndex n 1) : MemLp (d a) p (domainMeasure n V) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, firstOrderRows_baseIndex] using hu
    · simpa only [d, firstOrderRows_singleDerivIndex] using Lp.memLp (gi i)
  have hd_weak (a : DerivIndex n 1) : HasWeakDerivativeOn V a.toList u (d a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, firstOrderRows_baseIndex, baseIndex_toList] using
        hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hu (Fact.out : 1 ≤ p))
    · simpa only [d, firstOrderRows_singleDerivIndex, singleDerivIndex_toList] using hgi i
  let U := mkWkpSpaceOnOfWeakDerivatives u d hd_base hd_mem hd_weak
  have hU (a : DerivIndex n 1) :
      (U.val a : ℝ^n → ℝ) =ᵐ[domainMeasure n V] d a :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae u d hd_base hd_mem hd_weak a
  refine ⟨U, ?_, ?_⟩
  · simpa only [baseRepresentative, hd_base] using hU (baseIndex n 1)
  have hgrad : ∇ U = g := by
    apply Lp.ext
    have hrows : ∀ᵐ x ∂domainMeasure n V, ∀ i : Fin n,
        U.val (singleDerivIndex n i) x = gi i x := ae_all_iff.mpr fun i ↦
      (hU (singleDerivIndex n i)).mono fun x hx ↦ by
        simpa only [d, firstOrderRows_singleDerivIndex] using hx
    have hcoords : ∀ᵐ x ∂domainMeasure n V, ∀ i : Fin n, gi i x = g x i :=
      ae_all_iff.mpr fun i ↦ (P i).coeFn_compLpL g
    filter_upwards [wkpGradientCLM_apply_ae U, hrows, hcoords] with x hx hy hz
    exact PiLp.ext fun i ↦ (hx i).trans ((hy i).trans (hz i))
  exact hgrad ▸ hg_bound

/-- Uniformly bounded difference quotients at all sufficiently small nonzero steps imply
local Sobolev regularity, with the exact bound for the full gradient. -/
theorem exists_sobolev_of_bounded_vectorDifference
    (hp : 1 < p) (hp_top : p ≠ ∞) {V : Set (ℝ^n)} (hV : IsOpen V)
    {u : ℝ^n → ℝ} (hu : MemLp u p (domainMeasure n V))
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (vectorDifference h u) p (domainMeasure n V) ≤ ENNReal.ofReal C) :
    ∃ U : W^{1,p}(V),
      baseRepresentative U =ᵐ[domainMeasure n V] u ∧ ‖∇ U‖ ≤ C := by
  let h (m : ℕ) : ℝ := (δ / 2) * (1 / ((m : ℝ) + 1))
  have hzero : Tendsto h atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ / 2)
  have hpos (m : ℕ) : 0 < h m := by
    dsimp [h]
    positivity
  apply exists_sobolev_of_vectorDifference_sequence hp hp_top hV hu h hzero
    (fun m ↦ (hpos m).ne') hC
  intro m
  apply hbound (h m) (hpos m).ne'
  rw [abs_of_pos (hpos m)]
  have hinv : 1 / ((m : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  exact ((mul_le_mul_of_nonneg_left hinv (by positivity)).trans_lt
    (by simpa using (half_lt_self hδ)))

/-- Small-step bounds for the scalar coordinate quotients of an
`Lp` field construct its interior first weak derivatives. The base
coordinate is exactly its original restriction. -/
theorem exists_sobolev_of_restricted_differenceQuotient_bounds
    (hp : 1 < p) (hp_top : p ≠ ∞) {Ω V : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hshift : ∀ (i : Fin n) (h : ℝ), |h| < ρ →
      MapsTo (fun x ↦ x + coordinateStep i h) V Ω)
    (f : DerivLp n p Ω)
    (hbound : ∀ (i : Fin n) (h : ℝ), h ≠ 0 → |h| < ρ →
      ‖restrictDerivLp (subset_univ V)
        (differenceQuotientLp p i h (SobolevSpace.Extension.Lp.zeroExtendLp hΩ f))‖ ≤ C) :
    ∃ U : W^{1,p}(V),
      U.val (baseIndex n 1) = restrictDerivLp hVΩ f ∧
      ‖∇ U‖ ≤ (n : ℝ) * C := by
  have hmem : MemLp (f : ℝ^n → ℝ) p (domainMeasure n V) :=
    (Lp.memLp f).mono_measure (domainMeasure_le hVΩ)
  have hb (h : ℝ) (hh : h ≠ 0) (hhρ : |h| < ρ) :
      eLpNorm (vectorDifference h (f : ℝ^n → ℝ)) p (domainMeasure n V) ≤
        ENNReal.ofReal ((n : ℝ) * C) :=
    eLpNorm_vectorDifference_le_of_restricted_bounds hΩ hVΩ f
      Filter.EventuallyEq.rfl h (fun i ↦ hshift i h hhρ)
      (fun i ↦ hbound i h hh hhρ)
  obtain ⟨U, hU, hnorm⟩ := exists_sobolev_of_bounded_vectorDifference hp hp_top hV hmem hρ
    (mul_nonneg (Nat.cast_nonneg n) hC) hb
  refine ⟨U, Lp.ext ?_, hnorm⟩
  exact hU.trans (restrictDerivLp_apply_ae hVΩ f).symm

end SobolevSpace.GraphSpace.DifferenceQuotient
