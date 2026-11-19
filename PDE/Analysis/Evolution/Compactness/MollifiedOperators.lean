/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Compactness.Lp.Basic
public import PDE.Analysis.Evolution.Compactness.Lp.Ultrafilter
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.WeakCompactness

/-!
# Weak limits of mollified first-order operators

Self-adjoint contractions that converge strongly to the identity preserve weak
limits through a bounded coefficient multiplier. Applied on Bochner L², this
passes the principal term while keeping spatial derivatives on the H¹ state.
Coefficient derivative measurability is not needed.

The compactness theorem constructs a common ultrafilter weak limit and proves
the unmollified operator equation. It does not invoke spatial compact embedding.
The spatial coefficient multiplier below is built by applying Hölder twice:
first in space, then in time.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Analysis.Evolution

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} {l : Filter ι}

/-- Strongly convergent contractions also converge on strongly varying inputs. -/
theorem tendsto_contraction_apply_of_tendsto
    (Q : ι → E →L[ℝ] E) (hQbound : ∀ i x, ‖Q i x‖ ≤ ‖x‖)
    (hQ : ∀ x, Tendsto (fun i ↦ Q i x) l (𝓝 x))
    {x : ι → E} {xLimit : E} (hx : Tendsto x l (𝓝 xLimit)) :
    Tendsto (fun i ↦ Q i (x i)) l (𝓝 xLimit) := by
  have hsmall : Tendsto (fun i ↦ Q i (x i - xLimit)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun i ↦ norm_nonneg _) (fun i ↦ hQbound i _)
      (tendsto_iff_norm_sub_tendsto_zero.mp hx)
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add (hQ xLimit)

/-- The two mollifiers surrounding a fixed bounded coefficient operator disappear
strongly on each fixed test vector. -/
theorem tendsto_contraction_sandwich
    (Q : ι → E →L[ℝ] E) (hQbound : ∀ i x, ‖Q i x‖ ≤ ‖x‖)
    (hQ : ∀ x, Tendsto (fun i ↦ Q i x) l (𝓝 x))
    (M : E →L[ℝ] E) (x : E) :
    Tendsto (fun i ↦ Q i (M (Q i x))) l (𝓝 (M x)) :=
  tendsto_contraction_apply_of_tendsto Q hQbound hQ
    (M.continuous.continuousAt.tendsto.comp (hQ x))

end Operators

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {ι : Type*} {l : Filter ι}

/-- Moving both self-adjoint mollifiers onto the test vector passes a variable
weakly convergent input through the coefficient term. The coefficient operator
itself need not be self-adjoint. -/
theorem tendsto_inner_contraction_sandwich_of_tendsto_weak
    (Q : ι → E →L[ℝ] E) (hQbound : ∀ i x, ‖Q i x‖ ≤ ‖x‖)
    (hQ : ∀ x, Tendsto (fun i ↦ Q i x) l (𝓝 x))
    (hQself : ∀ i x y, ⟪Q i x, y⟫_ℝ = ⟪x, Q i y⟫_ℝ)
    (M : E →L[ℝ] E) {u : ι → E} {uLimit : E}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l
      (𝓝 (toWeakSpace ℝ E uLimit)))
    (R : ℝ) (hR : ∀ i, ‖u i‖ ≤ R) (φ : E) :
    Tendsto (fun i ↦ ⟪φ, Q i (M (Q i (u i)))⟫_ℝ) l
      (𝓝 (⟪φ, M uLimit⟫_ℝ)) := by
  have htest := tendsto_contraction_sandwich Q hQbound hQ M.adjoint φ
  have hpair := tendsto_inner_of_tendsto_weak_of_tendsto_strong hu htest R hR
  simpa only [hQself, ContinuousLinearMap.adjoint_inner_left] using hpair

omit [CompleteSpace E] in
/-- Pointwise contraction lifts to Bochner L² without an operator-norm conversion. -/
theorem norm_compLpL_apply_le_of_contraction
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (Q : E →L[ℝ] E) (hQ : ∀ x, ‖Q x‖ ≤ ‖x‖) (u : Lp E 2 ν) :
    ‖Q.compLpL 2 ν u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Q.coeFn_compLpL u] with t ht
  simpa only [ht] using hQ (u t)

omit [CompleteSpace E] in
/-- A self-adjoint spatial map remains self-adjoint on Bochner L². -/
theorem inner_compLpL_left_of_self_adjoint
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (Q : E →L[ℝ] E) (hQ : ∀ x y, ⟪Q x, y⟫_ℝ = ⟪x, Q y⟫_ℝ)
    (u v : Lp E 2 ν) :
    ⟪Q.compLpL 2 ν u, v⟫_ℝ = ⟪u, Q.compLpL 2 ν v⟫_ℝ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Q.coeFn_compLpL u, Q.coeFn_compLpL v] with t hut hvt
  simp only [hut, hvt, hQ]

end Hilbert

section Coefficients

variable {α X : Type*} [MeasurableSpace α] [MeasurableSpace X]
  (ν : Measure α) (μ : Measure X)

/-- A bounded, strongly measurable L-infinity coefficient family acts on
Bochner L²(L²). Hölder in space and time constructs the multiplier. -/
def bochnerScalarMultiplier
    (a : Lp (Lp ℝ ∞ μ) ∞ ν) : Lp (Lp ℝ 2 μ) 2 ν →L[ℝ] Lp (Lp ℝ 2 μ) 2 ν :=
  (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).holderL μ ∞ 2 2).holderL
    ν ∞ 2 2) a

/-- The constructed Bochner multiplier agrees with spatial multiplication
for almost every time. -/
theorem bochnerScalarMultiplier_apply_ae
    (a : Lp (Lp ℝ ∞ μ) ∞ ν) (u : Lp (Lp ℝ 2 μ) 2 ν) :
    (bochnerScalarMultiplier ν μ a u : α → Lp ℝ 2 μ) =ᵐ[ν]
      fun t ↦ a t • u t := by
  let B : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).holderL μ ∞ 2 2
  have hB (c : Lp ℝ ∞ μ) (v : Lp ℝ 2 μ) : B c v = c • v := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ).coeFn_holder (r := 2) c v,
      Lp.coeFn_lpSMul (r := 2) c v] with x hl hr
    exact hl.trans hr.symm
  filter_upwards [B.coeFn_holder (r := 2) a u] with t ht
  exact ht.trans (hB (a t) (u t))

/-- The mollified Bochner coefficient term has the expected pointwise
representative. `P` may be a weak derivative coordinate of an H¹ state. -/
theorem bochner_mollified_coefficient_apply_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] Lp ℝ 2 μ) (J : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (a : Lp (Lp ℝ ∞ μ) ∞ ν) (u : Lp E 2 ν) :
    (J.compLpL 2 ν
      (bochnerScalarMultiplier ν μ a (J.compLpL 2 ν (P.compLpL 2 ν u))) :
        α → Lp ℝ 2 μ) =ᵐ[ν] fun t ↦ J (a t • J (P (u t))) := by
  filter_upwards
    [J.coeFn_compLpL
      (bochnerScalarMultiplier ν μ a (J.compLpL 2 ν (P.compLpL 2 ν u))),
      bochnerScalarMultiplier_apply_ae ν μ a (J.compLpL 2 ν (P.compLpL 2 ν u)),
      J.coeFn_compLpL (P.compLpL 2 ν u), P.coeFn_compLpL u]
    with t houter hmult hinner hP
  rw [houter, hmult, hinner, hP]

end Coefficients

section Compactness

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Weak compactness passes a finite sum of mollified first-order terms
to its unmollified equation. `D` records bounded derivative projections from the
energy state, and `M` the coefficient multipliers on the output space.

For evolution, use Bochner H¹ for `V` and Bochner L² for `H`. The conclusion
constructs weak limits; no compact embedding or preselected solution is assumed. -/
theorem exists_weak_limit_mollified_operator_equation
    {κ σ : Type*} [Fintype κ] [Finite σ]
    (Q : ℕ → H →L[ℝ] H) (hQbound : ∀ k x, ‖Q k x‖ ≤ ‖x‖)
    (hQ : ∀ x, Tendsto (fun k ↦ Q k x) atTop (𝓝 x))
    (hQself : ∀ k x y, ⟪Q k x, y⟫_ℝ = ⟪x, Q k y⟫_ℝ)
    (D : κ → V →L[ℝ] H) (M : σ → κ → H →L[ℝ] H)
    (u : ℕ → V) (g : σ → ℕ → H) (f : σ → H)
    (hu : Bornology.IsBounded (range u)) (hg : ∀ p, Bornology.IsBounded (range (g p)))
    (heq : ∀ p k, g p k = f p - ∑ r, Q k (M p r (Q k (D r (u k))))) :
    ∃ (uLimit : V) (gLimit : σ → H) (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun k ↦ toWeakSpace ℝ V (u k)) U (𝓝 (toWeakSpace ℝ V uLimit)) ∧
      (∀ p, Tendsto (fun k ↦ toWeakSpace ℝ H (g p k)) U
        (𝓝 (toWeakSpace ℝ H (gLimit p)))) ∧
      ∀ p, gLimit p = f p - ∑ r, M p r (D r uLimit) := by
  classical
  obtain ⟨uLimit, U₁, hU₁, hu₁⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter atTop u hu
  obtain ⟨gLimit, U, hU, hgweak⟩ :=
    exists_ultrafilter_weak_limits_finite (U₁ : Filter ℕ) g hg
  have huweak := hu₁.mono_left hU
  have hUtop := hU.trans hU₁
  obtain ⟨R, hR⟩ := hu.exists_norm_le
  refine ⟨uLimit, gLimit, U, hUtop, huweak, hgweak, ?_⟩
  intro p
  apply ext_inner_left ℝ
  intro φ
  have hterms (r : κ) :
      Tendsto (fun k ↦ ⟪φ, Q k (M p r (Q k (D r (u k))))⟫_ℝ) U
        (𝓝 (⟪φ, M p r (D r uLimit)⟫_ℝ)) := by
    have hDweak :
        Tendsto (fun k ↦ toWeakSpace ℝ H (D r (u k))) U
          (𝓝 (toWeakSpace ℝ H (D r uLimit))) := by
      exact (WeakSpace.map (D r)).continuous.continuousAt.tendsto.comp huweak
    apply tendsto_inner_contraction_sandwich_of_tendsto_weak Q hQbound
      (fun x ↦ (hQ x).mono_left hUtop) hQself (M p r) hDweak (‖D r‖ * R)
    intro k
    exact ((D r).le_opNorm (u k)).trans
      (mul_le_mul_of_nonneg_left (hR (u k) (mem_range_self k)) (norm_nonneg _))
  have hrhs :
      Tendsto (fun k ↦ ⟪φ, f p - ∑ r, Q k (M p r (Q k (D r (u k))))⟫_ℝ) U
        (𝓝 (⟪φ, f p - ∑ r, M p r (D r uLimit)⟫_ℝ)) := by
    simp only [inner_sub_right, inner_sum]
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun r _ ↦ hterms r)
  have hgpair :
      Tendsto (fun k ↦ ⟪φ, g p k⟫_ℝ) U (𝓝 (⟪φ, gLimit p⟫_ℝ)) := by
    simpa only [LinearEquiv.symm_apply_apply, innerSL_apply_apply] using
      WeakCompactness.tendsto_evaluation (hgweak p) (innerSL ℝ φ)
  have hrhs' :
      Tendsto (fun k ↦ ⟪φ, g p k⟫_ℝ) U
        (𝓝 (⟪φ, f p - ∑ r, M p r (D r uLimit)⟫_ℝ)) := by
    simpa only [← heq] using hrhs
  exact tendsto_nhds_unique hgpair hrhs'

end Compactness

end PDE.Analysis.Evolution
