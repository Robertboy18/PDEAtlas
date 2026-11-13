/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedH1
public import PDE.Analysis.Evolution.Compactness.InitialTrace
import PDE.Analysis.Evolution.Compactness.MollifiedOperators
import PDE.Analysis.Evolution.Compactness.Lp.PointwiseBounds
import PDE.Spaces.Sobolev.Approximation.Mollification.BochnerConsistency

/-!
# Symmetric first-order Cauchy systems with an H¹ energy bound

For a finite interval `a < b`, symmetric W¹,∞ coefficient matrices on the whole
space, H¹ initial data, and L²-in-time H¹ forcing, mollified trajectories yield
an original-system solution in L∞-in-time H¹. Each component has an L² time
velocity and a continuous L² representative taking the prescribed initial value.

The base coefficient rows are continuous on `[a,b]` with values in L∞. Uniform bounds on the
divergence and full spatial gradient rows control the H¹ energy. A common weak Bochner limit passes
the equation and the initial identity. Weak closedness retains the pointwise exponential energy
envelope, with exponent `C + 2 * L + 1`.

The construction uses no spatial compact embedding. The traces are continuous
in L², not in the H¹ norm.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

section H1SystemInstances

open scoped SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

variable {n m : ℕ}

local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "D" => DerivLp n 2 univ

/-- The base-row operator is bounded from H¹ to L² independently of the mollifier
scale. The constant is the sum of the L-infinity norms in this coefficient row. -/
theorem norm_mollifiedH1SystemOperator_base_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U : V) (p : Fin m) :
    ‖wkpCoordinateCLM (baseIndex n 1) (mollifiedH1SystemOperator μ hε A U p)‖ ≤
      (∑ j, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖) * ‖U‖ := by
  classical
  rw [mollifiedH1SystemOperator_base, norm_neg]
  simp_rw [mollifierDerivativeRowCLM_base]
  calc
    _ ≤ ∑ j, ∑ q, ‖mollifierRowCLM μ hε (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierRowCLM μ hε (wkpCoordinateCLM (singleDerivIndex n j) (U q)))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ norm_sum_le _ _)
    _ ≤ ∑ j, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖ * ‖U‖ :=
      Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun q _ ↦
        (norm_mollifierRowCLM_apply_le μ hε _).trans <| (Lp.norm_smul_le _ _).trans <|
          mul_le_mul_of_nonneg_left ((norm_mollifierRowCLM_apply_le μ hε _).trans
            ((wkpCoordinateCLM_norm_le _ _).trans (PiLp.norm_apply_le U q))) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

/-- Adding the forcing gives a velocity envelope with no epsilon dependence.
No coefficient derivative appears in this estimate. -/
theorem norm_mollifiedH1SystemOperator_base_add_forcing_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U F : V) (p : Fin m) {M R : ℝ}
    (hM : (∑ j, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖) ≤ M) (hMnonneg : 0 ≤ M)
    (hU : ‖U‖ ≤ R) :
    ‖wkpCoordinateCLM (baseIndex n 1) (mollifiedH1SystemOperator μ hε A U p) +
      wkpCoordinateCLM (baseIndex n 1) (F p)‖ ≤ M * R + ‖F‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ((wkpCoordinateCLM_norm_le _ _).trans
    (PiLp.norm_apply_le F p)))
  exact (norm_mollifiedH1SystemOperator_base_le μ hε A U p).trans
    (mul_le_mul hM hU (norm_nonneg U) hMnonneg)

/-- The base velocity belongs to Bochner L². Continuity of the coefficient
base rows and of the Picard trajectory on `[a,b]` handles the principal term; the forcing
needs only Bochner L² regularity. -/
theorem memLp_mollified_h1_cauchy_base_velocity (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ}
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b) {F : ℝ → V} {U₀ : V} (hF : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : AffineCaratheodorySolutionOn (E := V)
      (fun t : ℝ ↦ mollifiedH1SystemOperator (n := n) (m := m) μ hε (A t)) F a b U₀)
    (p : Fin m) :
    MemLp (fun t ↦ wkpCoordinateCLM (baseIndex n 1)
        (mollifiedH1SystemOperator μ hε (A t) (U.trajectory t) p) +
      wkpCoordinateCLM (baseIndex n 1) (F t p)) 2 (volume.restrict (Ioc a b)) := by
  let P : V →L[ℝ] DerivLp n 2 univ :=
    (wkpCoordinateCLM (baseIndex n 1)).comp (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)
  have hUcont : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  exact (memLp_restrict_Ioc_of_continuousOn (P.continuous.comp_continuousOn
    ((continuousOn_mollifiedH1SystemOperator μ hε A hA).clm_apply hUcont))).add
      (P.lipschitzWith.comp_memLp (map_zero P) hF)

/-- A uniformly H¹-bounded family of the constructed trajectories has bounded
Bochner L² velocities in every component, with the time derivative and
principal-term formula identified. This is the compactness bound for epsilon
tending to zero, not the fixed-epsilon Picard operator bound. -/
theorem exists_bounded_mollified_h1_base_velocities (μ : Mollifier n) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ}
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b) {F : ℝ → V} {U₀ : V} (hF : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : ∀ k, AffineCaratheodorySolutionOn (E := V)
      (fun t : ℝ ↦ mollifiedH1SystemOperator (n := n) (m := m) μ (hε k) (A t)) F a b U₀)
    (M R : ℝ) (hMnonneg : 0 ≤ M)
    (hM : ∀ t ∈ Icc a b, ∀ p,
      (∑ j, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖) ≤ M)
    (hU : ∀ k t, t ∈ Icc a b → ‖(U k).trajectory t‖ ≤ R) :
    ∃ g : Fin m → ℕ → Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)),
      (∀ p, Bornology.IsBounded (range (g p))) ∧
      (∀ p k, ∀ᵐ t ∂volume.restrict (Ioc a b),
        HasDerivAt (fun s ↦ wkpCoordinateCLM (baseIndex n 1) ((U k).trajectory s p))
          (g p k t) t) ∧
      (∀ p k, (g p k : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc a b)]
        fun t ↦ wkpCoordinateCLM (baseIndex n 1)
          (mollifiedH1SystemOperator μ (hε k) (A t) ((U k).trajectory t) p) +
          wkpCoordinateCLM (baseIndex n 1) (F t p)) := by
  let rhs := fun p k t ↦ wkpCoordinateCLM (baseIndex n 1)
    (mollifiedH1SystemOperator μ (hε k) (A t) ((U k).trajectory t) p) +
    wkpCoordinateCLM (baseIndex n 1) (F t p)
  have hmem (p : Fin m) (k : ℕ) : MemLp (rhs p k) 2 (volume.restrict (Ioc a b)) :=
    memLp_mollified_h1_cauchy_base_velocity μ (hε k) A hA hab hF (U k) p
  refine ⟨fun p k ↦ (hmem p k).toLp (rhs p k), fun p ↦ ?_, fun p k ↦ ?_,
    fun p k ↦ (hmem p k).coeFn_toLp⟩
  · refine isBounded_range_toLp_of_memLp_envelope (rhs p) (hmem p) _
      ((memLp_const (M * R)).add hF.norm) fun k ↦ ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (norm_mollifiedH1SystemOperator_base_add_forcing_le μ (hε k) (A t) ((U k).trajectory t)
      (F t) p (hM t (Ioc_subset_Icc_self ht) p) hMnonneg
        (hU k t (Ioc_subset_Icc_self ht))).trans (le_abs_self _)
  · filter_upwards [(U k).hasDerivAt_comp_ae ((wkpCoordinateCLM (baseIndex n 1)).comp
      (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)), (hmem p k).coeFn_toLp] with t ht hgt
    exact hgt ▸ ht

/-- Uniformly H¹-bounded mollified trajectories admit a
componentwise solution of the unmollified system. The velocity is in Bochner L²,
and each base row has a continuous L² representative with the given initial
value. The spatial derivatives in the equation are the H¹ weak derivatives.

The compactness is weak Bochner compactness. Only base coefficient rows occur in the time-dependent
multiplier. The prescribed energy envelope is retained by weak closedness of the almost-everywhere
squared-norm constraint. -/
theorem exists_unmollified_cauchy_with_energy_of_mollified_trajectories
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ}
    (hA : ∀ j p q, ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
      (Icc a b))
    (hab : a < b) (F : ℝ → V) (hF : MemLp F 2 (volume.restrict (Ioc a b))) (U₀ : V)
    (U : ∀ k, AffineCaratheodorySolutionOn (E := V) (fun t : ℝ ↦
      mollifiedH1SystemOperator (n := n) (m := m) (standardMollifier n) (hε k) (A t)) F a b U₀)
    (M R : ℝ) (hMnonneg : 0 ≤ M)
    (hM : ∀ t ∈ Icc a b, ∀ p,
      (∑ j, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖) ≤ M)
    (hU : ∀ k t, t ∈ Icc a b → ‖(U k).trajectory t‖ ≤ R) (energy : ℝ → ℝ)
    (henergy : ∀ k t, t ∈ Icc a b → ‖(U k).trajectory t‖ ^ 2 ≤ energy t) :
    ∃ (u : Lp V 2 (volume.restrict (Ioc a b))) (g : Fin m → Lp D 2 (volume.restrict (Ioc a b))),
      (∀ᵐ t ∂volume.restrict (Ioc a b), ‖u t‖ ^ 2 ≤ energy t) ∧
      (∀ p, ∀ᵐ t ∂volume.restrict (Ioc a b),
        g p t = -(∑ j, ∑ q, ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
            wkpCoordinateCLM (singleDerivIndex n j) (u t q)) +
          wkpCoordinateCLM (baseIndex n 1) (F t p)) ∧
      ∀ p, ∃ E : ContinuousPivotEvolutionOn (GelfandTriple.identity D)
          (fun t ↦ ((wkpCoordinateCLM (baseIndex n 1)).comp
            (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)).compLpL 2 (volume.restrict (Ioc a b)) u t)
          (fun t ↦ (GelfandTriple.identity D).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
            (g p) t) a b,
        E.representative a = wkpCoordinateCLM (baseIndex n 1) (U₀ p) := by
  classical
  let : MeasurableSpace D := borel D
  let : BorelSpace D := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ D) := borel (StrongDual ℝ D)
  let : BorelSpace (StrongDual ℝ D) := ⟨rfl⟩
  let ν := volume.restrict (Ioc a b)
  let base (p : Fin m) : V →L[ℝ] D :=
    (wkpCoordinateCLM (baseIndex n 1)).comp (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)
  let deriv (r : Fin n × Fin m) : V →L[ℝ] D :=
    (wkpCoordinateCLM (singleDerivIndex n r.1)).comp (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) r.2)
  let coeff := fun j p q t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  have hcoeff (j p q) : MemLp (coeff j p q) ∞ ν := by
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA j p q)
    refine memLp_top_of_bound (((hA j p q).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc) K ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hK t (Ioc_subset_Icc_self ht)
  let c := fun j p q ↦ (hcoeff j p q).toLp (coeff j p q)
  have hc (j p q) : (c j p q : ℝ → DerivLp n ∞ univ) =ᵐ[ν] coeff j p q := (hcoeff j p q).coeFn_toLp
  have htraj (k : ℕ) : MemLp (U k).trajectory 2 ν := memLp_restrict_Ioc_of_continuousOn <| by
    simpa only [uIcc_of_le hab.le] using (U k).absolutely_continuous.continuousOn
  let u := fun k ↦ (htraj k).toLp (U k).trajectory
  have hu (k : ℕ) : (u k : ℝ → V) =ᵐ[ν] (U k).trajectory := (htraj k).coeFn_toLp
  have hubounded : Bornology.IsBounded (range u) :=
    isBounded_range_toLp_of_memLp_envelope _ htraj (fun _ ↦ R) (memLp_const R) fun k ↦ by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hU k t (Ioc_subset_Icc_self ht)).trans (le_abs_self R)
  obtain ⟨g, hgbounded, hgderiv, hgae⟩ := exists_bounded_mollified_h1_base_velocities
    (standardMollifier n) ε hε A hA hab.le hF U M R hMnonneg hM hU
  let J := fun k ↦ mollifierRowCLM (standardMollifier n) (hε k)
  let Q := fun k ↦ (J k).compLpL 2 ν
  let B := fun p (r : Fin n × Fin m) ↦
    bochnerScalarMultiplier ν (domainMeasure n univ) (c r.1 p r.2)
  let f := fun p ↦ (base p).compLpL 2 ν (hF.toLp F)
  have hf (p : Fin m) : (f p : ℝ → D) =ᵐ[ν] fun t ↦ base p (F t) := by
    filter_upwards [(base p).coeFn_compLpL (hF.toLp F), hF.coeFn_toLp] with t ht hFt
    rw [ht, hFt]
  have hterm (p : Fin m) (r : Fin n × Fin m) (k : ℕ) :
      (Q k (B p r (Q k ((deriv r).compLpL 2 ν (u k)))) : ℝ → D) =ᵐ[ν]
        fun t ↦ J k (coeff r.1 p r.2 t • J k (deriv r ((U k).trajectory t))) := by
    filter_upwards [bochner_mollified_coefficient_apply_ae ν (domainMeasure n univ) (deriv r) (J k)
      (c r.1 p r.2) (u k), hc r.1 p r.2, hu k] with t ht hct hut
    simpa only [hct, hut] using ht
  have heq (p : Fin m) (k : ℕ) :
      g p k = f p - ∑ r, Q k (B p r (Q k ((deriv r).compLpL 2 ν (u k)))) := by
    apply Lp.ext
    filter_upwards [hgae p k, hf p,
      Lp.coeFn_sub (f p) (∑ r, Q k (B p r (Q k ((deriv r).compLpL 2 ν (u k))))),
      Lp.coeFn_finsetSum Finset.univ (fun r ↦ Q k (B p r (Q k ((deriv r).compLpL 2 ν (u k))))),
      ae_all_iff.2 (fun r ↦ hterm p r k)] with t hgt hft hsub hsum hterms
    rw [hgt, hsub, Pi.sub_apply, hft, hsum]
    simp only [Finset.sum_apply, hterms, Fintype.sum_prod_type, mollifiedH1SystemOperator_base,
      mollifierDerivativeRowCLM_base, base, deriv, coeff, J, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply]
    abel
  obtain ⟨uLimit, gLimit, W, _, huweak, hgweak, hlimit⟩ :=
    exists_weak_limit_mollified_operator_equation Q
      (fun k ↦ norm_compLpL_apply_le_of_contraction ν _
        (norm_mollifierRowCLM_apply_le (standardMollifier n) (hε k)))
      (tendsto_mollifierRowCLM_compLpL ν (standardMollifier n) ε hε hε0)
      (fun k ↦ inner_compLpL_left_of_self_adjoint ν _ (inner_standardMollifierRowCLM_left (hε k)))
      (fun r ↦ (deriv r).compLpL 2 ν) B u g f hubounded hgbounded heq
  refine ⟨uLimit, gLimit, ?_, ?_, ?_⟩
  · refine ae_norm_sq_le_of_tendsto_weak_Lp (p := 2) energy huweak (.of_forall fun k ↦ ?_)
    filter_upwards [hu k, ae_restrict_mem measurableSet_Ioc] with t hut ht
    exact hut ▸ henergy k t (Ioc_subset_Icc_self ht)
  · intro p
    have hlimitTerm (r : Fin n × Fin m) : (B p r ((deriv r).compLpL 2 ν uLimit) : ℝ → D) =ᵐ[ν]
          fun t ↦ coeff r.1 p r.2 t • deriv r (uLimit t) := by
      filter_upwards [bochnerScalarMultiplier_apply_ae ν (domainMeasure n univ) (c r.1 p r.2)
        ((deriv r).compLpL 2 ν uLimit), (deriv r).coeFn_compLpL uLimit, hc r.1 p r.2]
        with t ht hdt hct
      simpa only [hdt, hct] using ht
    filter_upwards [hf p, Lp.coeFn_sub (f p) (∑ r, B p r ((deriv r).compLpL 2 ν uLimit)),
      Lp.coeFn_finsetSum Finset.univ (fun r ↦ B p r ((deriv r).compLpL 2 ν uLimit)),
      ae_all_iff.2 hlimitTerm] with t hft hsub hsum hterms
    rw [hlimit p, hsub, Pi.sub_apply, hft, hsum]
    simp only [Finset.sum_apply, hterms, Fintype.sum_prod_type,
      base, deriv, coeff, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    abel
  · intro p
    have hzu (k : ℕ) : (fun t ↦ base p ((U k).trajectory t)) =ᵐ[ν]
        ((base p).compLpL 2 ν (u k) : ℝ → D) := by
      filter_upwards [(base p).coeFn_compLpL (u k), hu k] with t ht hut
      rw [ht, hut]
    obtain ⟨E, _, hE⟩ :=
      exists_continuousPivotEvolutionOn_of_weak_projected_trajectories hab (base p)
        u (g p) uLimit (gLimit p) (base p U₀) huweak (hgweak p) _
        (fun k ↦ (base p).lipschitzWith.comp_absolutelyContinuousOnInterval
          (U k).absolutely_continuous) hzu (hgderiv p)
        (fun k ↦ congrArg (base p) (U k).initial_value)
    exact ⟨E, hE⟩

/-- Symmetric W¹-infinity coefficients with uniformly bounded spatial derivative
rows, H¹ initial data, and L²-in-time H¹ forcing give an original-system solution
in L-infinity-in-time H¹, with L² time velocity and continuous L² initial traces.

Only the base coefficient rows are assumed continuous on `[a,b]`. The proof constructs mollified H¹
trajectories, uses the epsilon-independent exponent `C + 2 * L + 1`, and passes to the original
equation by weak Bochner compactness. Weak closedness of the pointwise energy constraint retains the
full time-dependent envelope and gives an explicit L-infinity-in-time H¹ bound. -/
theorem exists_symmetric_cauchy_with_h1_energy
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ}
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (F : ℝ → V)
    (hF : MemLp F 2 (volume.restrict (Icc a b))) (U₀ : V) :
    ∃ (u : Lp V 2 (volume.restrict (Ioc a b))) (g : Fin m → Lp D 2 (volume.restrict (Ioc a b))),
      (∀ p, ∀ᵐ t ∂volume.restrict (Ioc a b),
        g p t = -(∑ j, ∑ q, ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
            wkpCoordinateCLM (singleDerivIndex n j) (u t q)) +
          wkpCoordinateCLM (baseIndex n 1) (F t p)) ∧
      (∀ p, ∃ E : ContinuousPivotEvolutionOn (GelfandTriple.identity D)
          (fun t ↦ ((wkpCoordinateCLM (baseIndex n 1)).comp
            (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)).compLpL 2 (volume.restrict (Ioc a b)) u t)
          (fun t ↦ (GelfandTriple.identity D).pivotToDual.compLpL 2 (volume.restrict (Ioc a b))
            (g p) t) a b,
        E.representative a = wkpCoordinateCLM (baseIndex n 1) (U₀ p)) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        ‖u t‖ ^ 2 ≤ (‖U₀‖ ^ 2 + ∫ s in a..b, ‖F s‖ ^ 2) * Real.exp ((C + 2 * L + 1) * (t - a))) ∧
      MemLp (u : ℝ → V) ∞ (volume.restrict (Ioc a b)) ∧
      eLpNorm (u : ℝ → V) ∞ (volume.restrict (Ioc a b)) ≤
        ENNReal.ofReal (Real.sqrt ((‖U₀‖ ^ 2 + ∫ s in a..b, ‖F s‖ ^ 2) *
          Real.exp ((C + 2 * L + 1) * (b - a)))) := by
  classical
  let ε := fun k : ℕ ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose U henergy using fun k ↦ exists_mollified_h1_cauchy_with_uniform_energy A hA hab.le hsym
      hC hL hdiv hgrad F hF U₀ (hε k)
  let energy := fun t ↦ (‖U₀‖ ^ 2 + ∫ s in a..b, ‖F s‖ ^ 2) * Real.exp ((C + 2 * L + 1) * (t - a))
  have henergyCont : Continuous energy := by fun_prop
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn henergyCont.continuousOn
  have hUbound (k : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ‖(U k).trajectory t‖ ≤ Real.sqrt K :=
    Real.le_sqrt_of_sq_le ((henergy k t ht).trans ((le_abs_self (energy t)).trans (hK t ht)))
  let total := fun t ↦ ∑ p, ∑ j, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖
  have htotal : ContinuousOn total (Icc a b) :=
    continuousOn_finsetSum _ fun p _ ↦ continuousOn_finsetSum _ fun j _ ↦
      continuousOn_finsetSum _ fun q _ ↦ (hA j p q).norm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn htotal
  have hMnonneg : 0 ≤ M := (norm_nonneg (total a)).trans (hM a ⟨le_rfl, hab.le⟩)
  have hrow (t : ℝ) (ht : t ∈ Icc a b) (p : Fin m) :
      (∑ j, ∑ q, ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖) ≤ M :=
    (Finset.single_le_sum (f := fun r ↦ ∑ j, ∑ q,
      ‖(A t j r q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)‖) (fun r _ ↦ by positivity)
        (Finset.mem_univ p)).trans ((le_abs_self (total t)).trans (hM t ht))
  have hFoc : MemLp F 2 (volume.restrict (Ioc a b)) :=
    hF.mono_measure (volume.restrict_mono_set Ioc_subset_Icc_self)
  obtain ⟨u, g, huEnergy, heq, htrace⟩ :=
    exists_unmollified_cauchy_with_energy_of_mollified_trajectories
      ε hε hε0 A hA hab F hFoc U₀ U M (Real.sqrt K) hMnonneg hrow hUbound energy henergy
  have hKnonneg : 0 ≤ ‖U₀‖ ^ 2 + ∫ s in a..b, ‖F s‖ ^ 2 :=
    add_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg hab.le fun s _ ↦ sq_nonneg _)
  have hc : 0 ≤ C + 2 * L + 1 := by positivity
  obtain ⟨huTop, huNorm⟩ := memLp_top_and_eLpNorm_le_of_ae_norm_sq_le_exp u hKnonneg hc huEnergy
  exact ⟨u, g, heq, htrace, huEnergy, huTop, huNorm⟩

end PDE.Hyperbolic.FirstOrder

end H1SystemInstances
