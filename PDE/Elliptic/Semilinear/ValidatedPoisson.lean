/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.ValidatedQuadratic
import PDE.FDeriv.Laplacian.Congruence
import PDE.Spaces.Sobolev.Boundary.Atlas.Interval.Graph
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
import CAS.CEGA
import PDE.Symbolic.PDEDerivatives
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Certified quadratic Dirichlet solutions on an interval and a cube

On the unit interval, the linear Poisson solution `p(x) = x(1-x)/2` is a candidate
for `-u'' + u² = 1`. Its range, Sobolev bound and Dirichlet coercivity validate a
weak solution within `1/16` in the full `H¹` norm.

On the three-dimensional unit cube, the product `P(x) = ∏ᵢ xᵢ(1-xᵢ)` is the
linear Poisson candidate for the fixed forcing `f = -ΔP`. Clamping extends it
across the corners as a compact Lipschitz function and constructs its `H¹₀` class.
Its residual is `-P²`. The range bound `0 ≤ P ≤ 1/64`, the bound `12` on the
`H¹₀ → L⁴` embedding, coordinate-slab coercivity `1/2` and the scalar radius budget
give a weak solution within `1/512` of this candidate.

Both applications discharge the analytic hypotheses of the general validation
theorem. CAS checks the derivatives and CEGA checks the scalar inequalities.
The cube problem illustrates Hou–Wang–Yang, arXiv:2509.25116, §3.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev Topology InnerProductSpace

namespace SobolevSpace.GraphSpace

local notation "Ω₁" => Set.preimage (EuclideanSpace.proj (0 : Fin 1)) (Ioo (0 : ℝ) 1)
local notation "e" => PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)

/-- The `H¹` inner product on `H¹₀` of the unit interval. -/
local instance innerProductSpaceH10UnitInterval : InnerProductSpace ℝ H¹₀(Ω₁) := inferInstance

private theorem unit_interval_geometry :
    IsOpen Ω₁ ∧ Bornology.IsBounded Ω₁ ∧ volume Ω₁ = 1 := by
  have heq : Ω₁ = (e) ⁻¹' Ioo (0 : ℝ) 1 := by
    ext x
    rfl
  have hopen : IsOpen Ω₁ := by
    rw [heq]
    exact isOpen_Ioo.preimage (e).continuous
  have hb : Bornology.IsBounded ((e).symm '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image (e).symm.continuous).isBounded
  have hbounded : Bornology.IsBounded Ω₁ := hb.subset fun x hx ↦
    ⟨(e) x, ⟨hx.1.le, hx.2.le⟩, (e).symm_apply_apply x⟩
  have hmp := (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((volume_preserving_funUnique (Fin 1) ℝ).symm _)
  have hmp' : MeasurePreserving (e) (volume : Measure (ℝ^1)) (volume : Measure ℝ) :=
    hmp.symm (e).symm.toHomeomorph.toMeasurableEquiv
  have hvol : volume Ω₁ = 1 := by
    calc
      _ = volume ((e) ⁻¹' Ioo (0 : ℝ) 1) := congrArg volume heq
      _ = volume (Ioo (0 : ℝ) 1) := hmp'.measure_preimage measurableSet_Ioo.nullMeasurableSet
      _ = 1 := by norm_num
  exact ⟨hopen, hbounded, hvol⟩

/-- The equation `-u'' + u² = 1` on `(0,1)` has a weak zero-boundary solution
within `1/16` of the linear Poisson candidate in the full `H¹` norm. Both
the candidate and the fixed forcing retain their literal representatives. -/
theorem exists_quadratic_dirichlet_solution_unit_interval :
    ∃ (p u : H¹₀(Ω₁)) (f : DerivLp 1 2 Ω₁),
      (baseCoordCLM p : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω₁]
        (fun x ↦ x 0 * (1 - x 0) / 2) ∧
      (f : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω₁] (fun _ ↦ 1) ∧
      ‖u - p‖ ≤ (1 : ℝ) / 16 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ z ^ 2) f u := by
  obtain ⟨hopen, hbounded, hvol⟩ := unit_interval_geometry
  have : IsFiniteMeasure (domainMeasure 1 Ω₁) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have : Fact (0 < (1 : ℕ)) := ⟨by decide⟩
  let P : ℝ^1 → ℝ := fun x ↦ x 0 * (1 - x 0) / 2
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := by
    dsimp only [P]
    cas
  have hgraph := (Boundary.Atlas.Interval.hasContDiffGraphBoundary_Ioo
    (by norm_num : (0 : ℝ) < 1) 1).hasC1GraphBoundary le_rfl
  obtain ⟨p, hp, hd⟩ := (ContDiffUpToBoundary.of_contDiff
    (hP.of_le (by simp)) hbounded).exists_H10_of_eq_zero_on_frontier
      hopen hbounded hgraph hP.continuous.continuousOn (fun x hx ↦ by
        obtain hx | hx := Boundary.Atlas.Interval.eq_endpoint_of_mem_frontier_Ioo hx
        · simp only [P, hx, zero_mul, zero_div]
        · simp only [P, hx, sub_self, mul_zero, zero_div])
  have hdP (x : ℝ^1) : (∂[0] P) x = 1 / 2 - x 0 := by
    change (∂[0] (fun x : ℝ^1 ↦ x 0 * (1 - x 0) / 2)) x = 1 / 2 - x 0
    cas
  have hd' : (derivCoordCLM 0 p : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω₁]
      (fun x ↦ 1 / 2 - x 0) := (hd 0).trans (Filter.Eventually.of_forall hdP)
  let f : DerivLp 1 2 Ω₁ := (memLp_const (1 : ℝ)).toLp (fun _ ↦ 1)
  have hf : (f : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 Ω₁] (fun _ ↦ 1) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  have hweak : HasWeakDerivativeOn Ω₁ [0] (derivCoordCLM 0 p : ℝ^1 → ℝ)
      ((-f : DerivLp 1 2 Ω₁) : ℝ^1 → ℝ) := by
    have hw := hasWeakDerivativeOn_of_contDiffAt_one hopen
      (f := fun x : ℝ^1 ↦ 1 / 2 - x 0) (fun _ _ ↦ by
        have hs : ContDiff ℝ 1 (fun x : ℝ^1 ↦ 1 / 2 - x 0) := by cas
        exact hs.contDiffAt) 0
    apply hw.congr_ae hd'.symm
    filter_upwards [hf, Lp.coeFn_neg f] with x hx hneg
    rw [hneg]
    change (∂[0] (fun x : ℝ^1 ↦ 1 / 2 - x 0)) x = -f x
    rw [hx]
    cas
  have hlinear : dirichletForm p = loadFunctional f := by
    ext v
    rw [dirichletForm_apply, Fin.sum_univ_one,
      weakDerivative_integrationByParts_H10 0 _ _ hweak v, loadFunctional_apply,
      inner_neg_left, neg_neg]
  have hnonneg : ∀ᵐ x ∂domainMeasure 1 Ω₁, 0 ≤ baseCoordCLM p x := by
    filter_upwards [hp, ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    rw [hx]
    exact div_nonneg (mul_nonneg hxΩ.1.le (sub_nonneg.mpr hxΩ.2.le)) (by norm_num)
  have hbound : ∀ᵐ x ∂domainMeasure 1 Ω₁,
      ‖baseCoordCLM p x‖ ≤ (1 : ℝ) / 8 := by
    filter_upwards [hp, hnonneg, ae_restrict_mem hopen.measurableSet] with x hx hx0 hxΩ
    rw [Real.norm_eq_abs, abs_of_nonneg hx0, hx]
    change x 0 * (1 - x 0) / 2 ≤ (1 : ℝ) / 8
    have h0 : (0 : ℝ) ≤ x 0 := hxΩ.1.le
    have h1 : x 0 ≤ (1 : ℝ) := hxΩ.2.le
    have hquadratic : x 0 * (1 - x 0) ≤ (1 : ℝ) / 4 := by cega
    linarith
  have hcoercive (v : H¹₀(Ω₁)) : (1 / 2 : ℝ) * ‖v‖ * ‖v‖ ≤ dirichletForm v v := by
    have h := dirichletForm_coercive_bound_one hbounded v
    simp only [hvol, ENNReal.toReal_one, one_pow, one_add_one_eq_two] at h
    linarith
  have hembedding : ‖dirichletL4Embedding (by omega) (by omega) hopen hbounded‖ ≤
      (1 : NNReal) := by
    have h := norm_h10LpEmbedding_le_one hopen.measurableSet (q := 4) (by norm_num)
    simpa only [dirichletL4Embedding, hvol, ENNReal.toReal_one, Real.one_rpow,
      NNReal.coe_one] using h
  obtain ⟨u, hu, hsol⟩ := exists_dirichlet_quadratic_weak_solution_near_poisson
    (by omega) (by omega) hopen hbounded p f hlinear hnonneg
    (M := 1 / 8) (c := 1 / 2) (r := 1 / 16) (by norm_num) (by norm_num)
    (by norm_num) hbound hcoercive (s := 1) hembedding (by
      rw [hvol, ENNReal.toReal_one, Real.one_rpow]
      simp only [NNReal.coe_one, one_mul]
      cega)
  exact ⟨p, u, f, hp, hf, hu, hsol⟩

end SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace.UnitCube

private def clampUnit (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem clampUnit_mem (t : ℝ) : clampUnit t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨le_max_left _ _, ?_⟩
  exact max_le (by norm_num) (min_le_left _ _)

private theorem clampUnit_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    clampUnit t = t := by
  simp only [clampUnit, min_eq_right ht.2, max_eq_right ht.1]

private def unitQuadratic (t : ℝ) : ℝ := clampUnit t * (1 - clampUnit t)

private theorem unitQuadratic_bounds (t : ℝ) :
    0 ≤ unitQuadratic t ∧ unitQuadratic t ≤ (1 : ℝ) / 4 := by
  obtain ⟨h0, h1⟩ := clampUnit_mem t
  refine ⟨mul_nonneg h0 (sub_nonneg.mpr h1), ?_⟩
  dsimp only [unitQuadratic]
  nlinarith [sq_nonneg (clampUnit t - 1 / 2)]

private theorem unitQuadratic_zero {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) :
    unitQuadratic t = 0 := by
  by_cases h0 : t ≤ 0
  · have hc : clampUnit t = 0 := max_eq_left ((min_le_right _ _).trans h0)
    simp only [unitQuadratic, hc, zero_mul]
  · have h1 : 1 ≤ t := by
      by_contra h1
      exact ht ⟨lt_of_not_ge h0, lt_of_not_ge h1⟩
    have hc : clampUnit t = 1 := by
      simp only [clampUnit, min_eq_left h1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [unitQuadratic, hc, sub_self, mul_zero]

private theorem lipschitz_mul_of_abs_le_one
    {X : Type*} [PseudoEMetricSpace X] {f g : X → ℝ} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfb : ∀ x, |f x| ≤ 1) (hgb : ∀ x, |g x| ≤ 1) :
    LipschitzWith (K + L) (fun x ↦ f x * g x) := by
  intro x y
  have h : |f x * g x - f y * g y| ≤ |f x - f y| + |g x - g y| := by
    calc
      |f x * g x - f y * g y| =
          |(f x - f y) * g x + f y * (g x - g y)| := by congr 1; ring
      _ ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
      _ ≤ |f x - f y| + |g x - g y| := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (hgb x))
          (mul_le_of_le_one_left (abs_nonneg _) (hfb y))
  calc
    edist (f x * g x) (f y * g y) =
        ENNReal.ofReal |f x * g x - f y * g y| := by rw [edist_dist, Real.dist_eq]
    _ ≤ ENNReal.ofReal |f x - f y| + ENNReal.ofReal |g x - g y| :=
      (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le
    _ = edist (f x) (f y) + edist (g x) (g y) := by rw [edist_dist, edist_dist,
      Real.dist_eq, Real.dist_eq]
    _ ≤ (K : ℝ≥0∞) * edist x y + (L : ℝ≥0∞) * edist x y := add_le_add (hf x y) (hg x y)
    _ = ((K + L : ℝ≥0) : ℝ≥0∞) * edist x y := by rw [ENNReal.coe_add, add_mul]

private theorem lipschitz_unitQuadratic : LipschitzWith 2 unitQuadratic := by
  change LipschitzWith 2 (fun t : ℝ ↦ clampUnit t * (1 - clampUnit t))
  have hc : LipschitzWith 1 clampUnit :=
    (LipschitzWith.id.const_min 1).const_max 0
  have hd : LipschitzWith 1 (fun t : ℝ ↦ 1 - clampUnit t) := by
    simpa using (LipschitzWith.const (1 : ℝ)).sub hc
  simpa only [one_add_one_eq_two] using
    lipschitz_mul_of_abs_le_one hc hd
      (fun t ↦ by rw [abs_of_nonneg (clampUnit_mem t).1]; exact (clampUnit_mem t).2)
      (fun t ↦ by
        rw [abs_of_nonneg (sub_nonneg.mpr (clampUnit_mem t).2)]
        linarith [(clampUnit_mem t).1])

private theorem lipschitz_prod_of_abs_le_one
    {X ι : Type*} [PseudoEMetricSpace X]
    (s : Finset ι) (f : ι → X → ℝ) (K : ι → ℝ≥0)
    (hf : ∀ i, LipschitzWith (K i) (f i)) (hb : ∀ i x, |f i x| ≤ 1) :
    LipschitzWith (∑ i ∈ s, K i) (fun x ↦ ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using
      lipschitz_mul_of_abs_le_one (hf i) ih (hb i) (fun x ↦ by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun j _ ↦ abs_nonneg _) (fun j _ ↦ hb j x))

/-- Open cube, with no boundary smoothness assumption. -/
def unitCube (n : ℕ) : Set (ℝ^n) := {x | ∀ i, x i ∈ Ioo (0 : ℝ) 1}

/-- Global clamped extension of the product of coordinate quadratics. -/
def candidate (n : ℕ) (x : ℝ^n) : ℝ :=
  ∏ i, max 0 (min 1 (x i)) * (1 - max 0 (min 1 (x i)))

/-- The polynomial used to define the fixed linear Poisson forcing. -/
def polynomial (n : ℕ) (x : ℝ^n) : ℝ := ∏ i, x i * (1 - x i)

theorem isOpen_unitCube (n : ℕ) : IsOpen (unitCube n) := by
  have heq : unitCube n = ⋂ i : Fin n,
      (EuclideanSpace.proj i) ⁻¹' Ioo (0 : ℝ) 1 := by
    ext x
    simp only [unitCube, mem_ofPred_eq, mem_iInter, mem_preimage,
      EuclideanSpace.coe_proj]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous

theorem candidate_eq_polynomial {n : ℕ} {x : ℝ^n} (hx : x ∈ unitCube n) :
    candidate n x = polynomial n x := by
  apply Finset.prod_congr rfl
  intro i _
  change clampUnit (x i) * (1 - clampUnit (x i)) = x i * (1 - x i)
  rw [clampUnit_eq ⟨(hx i).1.le, (hx i).2.le⟩]

theorem candidate_zero_outside {n : ℕ} {x : ℝ^n} (hx : x ∉ unitCube n) :
    candidate n x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ∉ Ioo (0 : ℝ) 1 := by
    simpa only [unitCube, mem_ofPred_eq, not_forall] using hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (unitQuadratic_zero hi)

theorem candidate_bounds (n : ℕ) (x : ℝ^n) :
    0 ≤ candidate n x ∧ candidate n x ≤ ((1 : ℝ) / 4) ^ n := by
  refine ⟨Finset.prod_nonneg (fun i _ ↦ (unitQuadratic_bounds (x i)).1), ?_⟩
  calc
    candidate n x ≤ ∏ _i : Fin n, ((1 : ℝ) / 4) :=
      Finset.prod_le_prod₀ (fun i _ ↦ (unitQuadratic_bounds (x i)).1)
        (fun i _ ↦ (unitQuadratic_bounds (x i)).2)
    _ = ((1 : ℝ) / 4) ^ n := by simp

theorem lipschitzWith_candidate (n : ℕ) :
    LipschitzWith (2 * n) (candidate n) := by
  change LipschitzWith (2 * n) (fun x : ℝ^n ↦ ∏ i, unitQuadratic (x i))
  have hproj (i : Fin n) : LipschitzWith 1 (fun x : ℝ^n ↦ x i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using PiLp.dist_apply_le x y i
  have hi (i : Fin n) : LipschitzWith 2 (fun x : ℝ^n ↦ unitQuadratic (x i)) := by
    simpa only [mul_one, Function.comp_def] using lipschitz_unitQuadratic.comp (hproj i)
  have hb (i : Fin n) (x : ℝ^n) : |unitQuadratic (x i)| ≤ 1 := by
    rw [abs_of_nonneg (unitQuadratic_bounds (x i)).1]
    exact ((unitQuadratic_bounds (x i)).2).trans (by norm_num)
  have h := lipschitz_prod_of_abs_le_one Finset.univ
    (fun i : Fin n ↦ fun x : ℝ^n ↦ unitQuadratic (x i)) (fun _ ↦ (2 : ℝ≥0)) hi hb
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_comm] using h

private def closedCube (n : ℕ) : Set (ℝ^n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm ''
    {x : Fin n → ℝ | ∀ i, x i ∈ Icc (0 : ℝ) 1}

private theorem isCompact_closedCube (n : ℕ) : IsCompact (closedCube n) :=
  (isCompact_pi_infinite fun _ ↦ isCompact_Icc).image
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous

private theorem unitCube_subset_closedCube (n : ℕ) : unitCube n ⊆ closedCube n := by
  intro x hx
  refine ⟨(EuclideanSpace.equiv (Fin n) ℝ) x,
    fun i ↦ ⟨(hx i).1.le, (hx i).2.le⟩, ?_⟩
  exact (EuclideanSpace.equiv (Fin n) ℝ).symm_apply_apply x

theorem isBounded_unitCube (n : ℕ) : Bornology.IsBounded (unitCube n) :=
  (isCompact_closedCube n).isBounded.subset (unitCube_subset_closedCube n)

/-- Euclidean volume of the open unit cube, obtained from the product measure. -/
theorem volume_unitCube (n : ℕ) : volume (unitCube n) = 1 := by
  have hpre : (WithLp.toLp 2 : (Fin n → ℝ) → ℝ^n) ⁻¹' unitCube n =
      Set.pi Set.univ (fun _ : Fin n ↦ Ioo (0 : ℝ) 1) := by
    ext x
    simp [unitCube, Set.mem_pi]
  calc
    volume (unitCube n) =
        volume ((WithLp.toLp 2 : (Fin n → ℝ) → ℝ^n) ⁻¹' unitCube n) :=
      ((PiLp.volume_preserving_toLp (Fin n)).measure_preimage
        (isOpen_unitCube n).measurableSet.nullMeasurableSet).symm
    _ = volume (Set.pi Set.univ (fun _ : Fin n ↦ Ioo (0 : ℝ) 1)) := congrArg volume hpre
    _ = 1 := by rw [Real.volume_pi_Ioo]; norm_num

theorem hasCompactSupport_candidate (n : ℕ) : HasCompactSupport (candidate n) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedCube n)
  intro x hx
  apply unitCube_subset_closedCube n
  by_contra h
  exact hx (candidate_zero_outside h)

/-- The candidate is nonzero: its value at the cube midpoint is its maximum. -/
theorem candidate_midpoint (n : ℕ) :
    candidate n ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ ↦ (1 : ℝ) / 2)) =
      ((1 : ℝ) / 4) ^ n := by
  change (∏ _i : Fin n, unitQuadratic ((1 : ℝ) / 2)) = ((1 : ℝ) / 4) ^ n
  have hq : unitQuadratic ((1 : ℝ) / 2) = (1 : ℝ) / 4 := by
    norm_num [unitQuadratic, clampUnit]
  simp only [hq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem exists_H10_candidate (n : ℕ) :
    ∃ p : H¹₀(unitCube n),
      (baseCoordCLM p : ℝ^n → ℝ) =ᵐ[domainMeasure n (unitCube n)] candidate n ∧
      ∀ i, (derivCoordCLM i p : ℝ^n → ℝ) =ᵐ[domainMeasure n (unitCube n)]
        ∂[i] (candidate n) :=
  exists_H10_of_lipschitzWith_zero_outside (isOpen_unitCube n)
    (lipschitzWith_candidate n) (hasCompactSupport_candidate n)
    (fun _ hx ↦ candidate_zero_outside hx)

/-- The global extension and polynomial have the same germ at every interior point. -/
theorem candidate_eventuallyEq_polynomial {n : ℕ} {x : ℝ^n}
    (hx : x ∈ unitCube n) : candidate n =ᶠ[𝓝 x] polynomial n := by
  filter_upwards [(isOpen_unitCube n).mem_nhds hx] with y hy
  exact candidate_eq_polynomial hy

/-- The corner-compatible Sobolev candidate retains the polynomial's interior derivatives. -/
theorem exists_H10_polynomial_candidate (n : ℕ) :
    ∃ p : H¹₀(unitCube n),
      (baseCoordCLM p : ℝ^n → ℝ) =ᵐ[domainMeasure n (unitCube n)] polynomial n ∧
      ∀ i, (derivCoordCLM i p : ℝ^n → ℝ) =ᵐ[domainMeasure n (unitCube n)]
        ∂[i] (polynomial n) := by
  obtain ⟨p, hp, hd⟩ := exists_H10_candidate n
  refine ⟨p, ?_, fun i ↦ ?_⟩
  · filter_upwards [hp, ae_restrict_mem (isOpen_unitCube n).measurableSet] with x hpx hx
    exact hpx.trans (candidate_eq_polynomial hx)
  · filter_upwards [hd i, ae_restrict_mem (isOpen_unitCube n).measurableSet] with x hdx hx
    exact hdx.trans (PDE.partialDeriv_congr_nhds i (candidate_eventuallyEq_polynomial hx))

/-- The interior polynomial is smooth in every dimension. -/
theorem contDiff_polynomial (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (polynomial n) := by
  unfold polynomial
  apply contDiff_prod
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul
    (contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

private theorem polynomial_three : polynomial 3 = fun x : ℝ^3 ↦
    (x 0 * (1 - x 0)) * (x 1 * (1 - x 1)) * (x 2 * (1 - x 2)) := by
  funext x
  simp [polynomial, Fin.prod_univ_three]

/-- Each diagonal second partial removes one coordinate quadratic and supplies a factor -2. -/
private theorem polynomial_second_partial (i : Fin 3) (x : ℝ^3) :
    (∂[i] (∂[i] (polynomial 3))) x =
      ![-2 * (x 1 * (1 - x 1)) * (x 2 * (1 - x 2)),
        -2 * (x 0 * (1 - x 0)) * (x 2 * (1 - x 2)),
        -2 * (x 0 * (1 - x 0)) * (x 1 * (1 - x 1))] i := by
  rw [polynomial_three]
  change (∂[i] (fun y : ℝ^3 ↦ (∂[i] (fun z : ℝ^3 ↦
    (z 0 * (1 - z 0)) * (z 1 * (1 - z 1)) * (z 2 * (1 - z 2)))) y)) x = _
  fin_cases i <;> dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] <;> cas

/-- Fixed forcing obtained from the linear Poisson equation. -/
def forcing (x : ℝ^3) : ℝ :=
  2 * ((x 0 * (1 - x 0)) * (x 1 * (1 - x 1)) +
    (x 0 * (1 - x 0)) * (x 2 * (1 - x 2)) +
    (x 1 * (1 - x 1)) * (x 2 * (1 - x 2)))

/-- The polynomial solves the linear Poisson equation for the fixed forcing. -/
theorem neg_laplacian_polynomial (x : ℝ^3) :
    -PDE.laplacian (polynomial 3) x = forcing x := by
  simp only [PDE.laplacian, polynomial_second_partial, Fin.sum_univ_three]
  change -(-2 * (x 1 * (1 - x 1)) * (x 2 * (1 - x 2)) +
    -2 * (x 0 * (1 - x 0)) * (x 2 * (1 - x 2)) +
    -2 * (x 0 * (1 - x 0)) * (x 1 * (1 - x 1))) = forcing x
  unfold forcing
  ring

/-- Locality identifies the clamped candidate's interior Laplacian with the polynomial's. -/
theorem neg_laplacian_candidate {x : ℝ^3} (hx : x ∈ unitCube 3) :
    -PDE.laplacian (candidate 3) x = forcing x := by
  rw [EuclideanLaplacian.laplacian_congr_nhds (candidate_eventuallyEq_polynomial hx)]
  exact neg_laplacian_polynomial x

/-- The nonlinear residual is genuine: forcing minus the candidate operator is -p². -/
theorem candidate_quadratic_residual {x : ℝ^3} (hx : x ∈ unitCube 3) :
    forcing x - (-PDE.laplacian (candidate 3) x + (candidate 3 x) ^ 2) =
      -(polynomial 3 x) ^ 2 := by
  rw [neg_laplacian_candidate hx, candidate_eq_polynomial hx]
  ring

/-- The clamped cube candidate solves the weak linear Poisson problem with the fixed forcing.
No smoothness of the cube boundary is needed: the derivatives are identified in the interior,
and zero-boundary integration by parts follows from the closure definition of H¹₀. -/
theorem exists_weak_poisson_candidate :
    ∃ (p : H¹₀(unitCube 3)) (f : DerivLp 3 2 (unitCube 3)),
      (baseCoordCLM p : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (unitCube 3)] polynomial 3 ∧
      (f : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (unitCube 3)] forcing ∧
      dirichletForm p = loadFunctional f := by
  let Ω := unitCube 3
  have hopen : IsOpen Ω := isOpen_unitCube 3
  have hbounded : Bornology.IsBounded Ω := isBounded_unitCube 3
  have hP : ContDiff ℝ (⊤ : ℕ∞) (polynomial 3) := contDiff_polynomial 3
  have hF : ContDiff ℝ 1 forcing := by
    unfold forcing
    cas
  let Fdata := ContDiffUpToBoundary.of_contDiff hF hbounded
  let f : DerivLp 3 2 Ω := Fdata.toLp hopen hbounded 2
  have hf : (f : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 Ω] forcing :=
    Fdata.toLp_coeFn hopen hbounded 2
  obtain ⟨p, hp, hd⟩ := exists_H10_polynomial_candidate 3
  have hsecond (i : Fin 3) : ContDiff ℝ 1 (∂[i] (∂[i] (polynomial 3))) :=
    ((PDE.contDiff_top_partialDeriv (i := i) (PDE.contDiff_top_partialDeriv (i := i) hP)).of_le
      (by simp))
  let Sdata (i : Fin 3) := ContDiffUpToBoundary.of_contDiff (hsecond i) hbounded
  let S (i : Fin 3) : DerivLp 3 2 Ω := (Sdata i).toLp hopen hbounded 2
  have hS (i : Fin 3) : (S i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 Ω]
      ∂[i] (∂[i] (polynomial 3)) := (Sdata i).toLp_coeFn hopen hbounded 2
  have hweak (i : Fin 3) : HasWeakDerivativeOn Ω [i]
      (derivCoordCLM i p : ℝ^3 → ℝ) (S i : ℝ^3 → ℝ) := by
    have hfirst : ContDiff ℝ 1 (∂[i] (polynomial 3)) :=
      (PDE.contDiff_top_partialDeriv (i := i) hP).of_le (by simp)
    exact (hasWeakDerivativeOn_of_contDiffAt_one hopen
      (fun _ _ ↦ hfirst.contDiffAt) i).congr_ae (hd i).symm (hS i).symm
  have hsum : (∑ i, S i) = -f := by
    apply Lp.ext
    have hSall : ∀ᵐ x ∂domainMeasure 3 Ω, ∀ i, S i x =
        (∂[i] (∂[i] (polynomial 3))) x := (ae_all_iff).2 hS
    filter_upwards [hSall, hf, Lp.coeFn_fun_finsetSum Finset.univ S, Lp.coeFn_neg f]
      with x hx hfx hs hn
    rw [hs, hn, Pi.neg_apply, hfx]
    simp only [hx]
    exact neg_eq_iff_eq_neg.mp (neg_laplacian_polynomial x)
  refine ⟨p, f, hp, hf, ?_⟩
  ext v
  rw [dirichletForm_apply, loadFunctional_apply, Finset.sum_congr rfl fun i _ ↦
    weakDerivative_integrationByParts_H10 i _ _ (hweak i) v, Finset.sum_neg_distrib,
    ← sum_inner, hsum, inner_neg_left, neg_neg]

/-- The fixed-forcing quadratic equation has a genuine weak solution near the cube polynomial. -/
theorem exists_quadratic_dirichlet_solution :
    ∃ (p u : H¹₀(unitCube 3)) (f : DerivLp 3 2 (unitCube 3)),
      (baseCoordCLM p : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (unitCube 3)] polynomial 3 ∧
      (f : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (unitCube 3)] forcing ∧
      ‖u - p‖ ≤ (1 : ℝ) / 512 ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ z ^ 2) f u := by
  let Ω := unitCube 3
  have hopen : IsOpen Ω := isOpen_unitCube 3
  have hbounded : Bornology.IsBounded Ω := isBounded_unitCube 3
  have hvol : volume Ω = 1 := volume_unitCube 3
  have : IsFiniteMeasure (domainMeasure 3 Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  obtain ⟨p, f, hp, hf, hlinear⟩ := exists_weak_poisson_candidate
  have hnonneg : ∀ᵐ x ∂domainMeasure 3 Ω, 0 ≤ baseCoordCLM p x := by
    filter_upwards [hp, ae_restrict_mem hopen.measurableSet] with x hpx hx
    rw [hpx, ← candidate_eq_polynomial hx]
    exact (candidate_bounds 3 x).1
  have hbound : ∀ᵐ x ∂domainMeasure 3 Ω,
      ‖baseCoordCLM p x‖ ≤ (1 : ℝ) / 64 := by
    filter_upwards [hp, hnonneg, ae_restrict_mem hopen.measurableSet] with x hpx h0 hx
    rw [Real.norm_eq_abs, abs_of_nonneg h0, hpx, ← candidate_eq_polynomial hx]
    have h := (candidate_bounds 3 x).2
    norm_num at h
    exact h
  have hcoercive (v : H¹₀(Ω)) :
      (1 / 2 : ℝ) * ‖v‖ * ‖v‖ ≤ dirichletForm v v := by
    have hs : Ω ⊆ {x | x (0 : Fin 3) ∈ Icc (0 : ℝ) 1} :=
      fun _ hx ↦ ⟨(hx 0).1.le, (hx 0).2.le⟩
    have h := dirichletForm_coercive_bound_of_slab (n := 2) 0 hs v
    norm_num [Real.volume_Icc] at h
    exact (by ring : (1 / 2 : ℝ) * ‖v‖ * ‖v‖ = ‖v‖ ^ 2 / 2).trans_le h
  have hembedding :
      ‖dirichletL4Embedding (by omega) (by omega) hopen hbounded‖ ≤ (12 : NNReal) := by
    have : Fact (1 ≤ ENNReal.ofReal (4 : ℝ)) := ⟨by norm_num⟩
    have : Fact (1 ≤ ENNReal.ofReal (6 : ℝ)) := ⟨by norm_num⟩
    have h46 := norm_h10LpEmbedding_le_of_le (by norm_num : 0 < 3)
      hopen.measurableSet (q := 4) (r := 6) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have h6 : ‖h10LpEmbedding (by norm_num) hopen.measurableSet (q := 6)
        (by norm_num) (by norm_num)‖ ≤ (12 : ℝ) := by
      apply norm_h10LpEmbedding_le_of_testFunction_bound (by norm_num)
        hopen.measurableSet (by norm_num) (by norm_num) (12 : ℝ≥0)
      intro φ
      have h := Inequalities.eLpNorm_le_explicit_mul_eLpNorm_fderiv_pStar
        (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport
        (p := 2) (by norm_num) (by norm_num) (by norm_num)
      norm_num [Inequalities.pStar] at h ⊢
      exact h
    simp only [hvol, ENNReal.toReal_one, Real.one_rpow, one_mul] at h46
    simpa only [dirichletL4Embedding, NNReal.coe_ofNat] using h46.trans h6
  obtain ⟨u, hu, hsol⟩ := exists_dirichlet_quadratic_weak_solution_near_poisson
    (by omega) (by omega) hopen hbounded p f hlinear hnonneg
    (M := 1 / 64) (c := 1 / 2) (r := 1 / 512)
    (by norm_num) (by norm_num) (by norm_num) hbound hcoercive
    (s := 12) hembedding (by
      rw [hvol, ENNReal.toReal_one, Real.one_rpow]
      simp only [one_mul, NNReal.coe_ofNat]
      cega)
  exact ⟨p, u, f, hp, hf, hu, hsol⟩

end SobolevSpace.GraphSpace.UnitCube
