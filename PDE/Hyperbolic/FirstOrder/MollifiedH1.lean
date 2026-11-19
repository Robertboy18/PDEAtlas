/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedEnergy
public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Constructed mollified H¹ trajectories and uniform H¹ energy

For a finite first-order system on ℝⁿ, the spatial operator is constructed
from two mollifiers and the W¹,∞ coefficient entries. Affine Picard existence then gives
an H¹-valued trajectory on each finite interval, with its initial value and
differentiated equation. The fixed outer mollifier maps L² boundedly to H¹, so time
continuity of the base coefficient rows in L∞ on the time interval supplies operator
continuity there.

For symmetric base coefficient matrices and the standard mollifier, the H¹ energy estimate
is independent of the positive scale. Its exponent is `C + 2L + 1`, where `C` bounds the
coefficient divergence rows and `L` bounds all first spatial coefficient derivatives.
Initial data lie in the finite Hilbert product of H¹ spaces; forcing is Bochner L² in time
with values in that product. No time continuity of the weak coefficient derivatives is required.

Evans, §7.3.2, regularizes by the viscous problems (11) instead; the scale-independent `H¹` bound
plays the role of his estimates (21) and (23).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, equation (11) and proof of Theorem 2, steps 1-3,
  equations (18)-(23).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

variable {n m : ℕ}

/-- On an H1 vector field, the regularized principal operator is bounded in L2
by the coefficient norms and the first derivatives, uniformly in epsilon.
This is the spatial estimate needed to bound the time derivative of its Cauchy trajectory. -/
theorem norm_mollifiedPrincipalOperator_le_of_H1 (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (B : Fin n → Lp (ℝ^m →L[ℝ] ℝ^m) ∞ (volume : Measure (ℝ^n))) (U : Fin m → H¹(ℝ^n))
    (u : Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) (g : Fin n → Lp (ℝ^m) 2 (volume : Measure (ℝ^n)))
    (hu : ∀ p, ((U p : WkpAmbientOn n 1 2 univ) (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ u x p)
    (hg : ∀ j p, ((U p : WkpAmbientOn n 1 2 univ) (singleDerivIndex n j) : ℝ^n → ℝ) =ᵐ[volume] fun
      x ↦ g j x p) :
    ‖mollifiedPrincipalOperator μ hε B u‖ ≤ ∑ j, ‖B j‖ * ‖g j‖ := by
  classical
  let J : Lp (ℝ^m) 2 (volume : Measure (ℝ^n)) →L[ℝ]
      Lp (ℝ^m) 2 (volume : Measure (ℝ^n)) := mollifierL2CLM μ hε
  have hcontract (v : Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) : ‖J v‖ ≤ ‖v‖ := by
    simpa using J.le_of_opNorm_le (norm_mollifierL2CLM_le (E := ℝ^m) μ hε) v
  have hcomm (j : Fin n) : mollifierDerivativeL2CLM μ hε j u = J (g j) :=
    mollifierDerivativeL2CLM_eq_of_H1_coordinates μ hε j U u (g j) hu (hg j)
  rw [mollifiedPrincipalOperator_apply, norm_neg]
  simp only [hcomm]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ (hcontract _).trans
    ((norm_multiplicationL2CLM_apply_le (B j) (J (g j))).trans
      (mul_le_mul_of_nonneg_left (hcontract (g j)) (norm_nonneg _))))

end PDE.Hyperbolic.FirstOrder

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

variable {n m : ℕ}

/-- The entrywise bound for all first spatial derivatives of the principal matrices.
The product-index ordering matches the commutator pairing; the quantity contains no scale. -/
def coefficientGradientBound
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) : ℝ :=
  ∑ l, ∑ p, ∑ j, ∑ q,
    ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖

/-- The full coefficient gradient bound is nonnegative. -/
theorem coefficientGradientBound_nonneg (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) :
    0 ≤ coefficientGradientBound A := by
  unfold coefficientGradientBound
  positivity

/-- The coefficient derivative term in mollified H1 energy has a bound independent of
scale. Moving the outer standard mollifier to the test field leaves a finite matrix
pairing, and contraction bounds the energy of all mollified gradient components. -/
theorem abs_sum_inner_mollified_coefficientDerivative_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (D : Fin n → Fin n → Lp (ℝ^m →L[ℝ] ℝ^m) ∞ (volume : Measure (ℝ^n)))
    (hD : ∀ l j p q, (fun x ↦ D l j x (EuclideanSpace.single q 1) p) =ᵐ[volume]
      ((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l) : ℝ^n → ℝ))
    {ε : ℝ} (hε : 0 < ε) (g : Fin n → Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) :
    |∑ l, ∑ j, ⟪mollifierL2CLM (standardMollifier n) hε
        (multiplicationL2CLM (D l j) (mollifierL2CLM (standardMollifier n) hε (g j))),
      g l⟫_ℝ| ≤ coefficientGradientBound A * (∑ l, ‖g l‖ ^ 2) := by
  classical
  let J : Lp (ℝ^m) 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp (ℝ^m) 2 (volume : Measure (ℝ^n)) :=
    mollifierL2CLM (standardMollifier n) hε
  have hex (l : Fin n) : ∃ U : Fin m → H¹(ℝ^n),
      ∀ p, ((U p : WkpAmbientOn n 1 2 univ) (baseIndex n 1) : ℝ^n → ℝ)
        =ᵐ[volume] fun x ↦ J (g l) x p :=
    (exists_H1_coordinates_mollifierL2CLM (standardMollifier n) hε (g l)).imp fun _ h ↦ h.1
  choose U hbase using hex
  let v := fun a : Fin n × Fin m ↦ (U a.1 a.2 : WkpAmbientOn n 1 2 univ) (baseIndex n 1)
  let d := fun a b : Fin n × Fin m ↦
    (A b.1 a.2 b.2 : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n a.1)
  have hpair (l j : Fin n) : ⟪multiplicationL2CLM (D l j) (J (g j)), J (g l)⟫_ℝ =
        ∑ p, ∑ q, ⟪d (l, p) (j, q) • v (j, q), v (l, p)⟫_ℝ :=
    inner_multiplicationL2CLM_eq_sum_of_ae_coordinates (D l j)
      (fun p q ↦ d (l, p) (j, q)) (fun q ↦ v (j, q)) (fun p ↦ v (l, p))
      (J (g j)) (J (g l)) (hD l j) (hbase j) (hbase l)
  have htotal : (∑ l, ∑ j, ⟪J (multiplicationL2CLM (D l j) (J (g j))), g l⟫_ℝ) =
        ∑ a, ∑ b, ⟪d a b • v b, v a⟫_ℝ := by
    simp only [J, inner_standardMollifierL2CLM_left, hpair, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_comm
  have henergy : (∑ a, ‖v a‖ ^ 2) ≤ ∑ l, ‖g l‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun l _ ↦ ?_
    rw [sum_norm_sq_eq_of_ae_coordinates _ _ (hbase l)]
    gcongr
    simpa using J.le_of_opNorm_le (norm_mollifierL2CLM_le (E := ℝ^m) (standardMollifier n) hε) (g l)
  have hcoefficient : (∑ a, ∑ b, ‖d a b‖) = coefficientGradientBound A := by
    simp only [d, Fintype.sum_prod_type, coefficientGradientBound]
  change |∑ l, ∑ j, ⟪J (multiplicationL2CLM (D l j) (J (g j))), g l⟫_ℝ| ≤ _
  rw [htotal]
  refine (MeasureTheory.Lp.abs_sum_inner_lpSMul_le d v).trans ?_
  rw [hcoefficient]
  exact mul_le_mul_of_nonneg_left henergy (coefficientGradientBound_nonneg A)

end PDE.Hyperbolic.FirstOrder

section H1SystemInstances

open scoped SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

variable {n m : ℕ}

local notation "L2" => DerivLp n 2 univ
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))

/-- The mollified matrix operator on the finite product of the H1 spaces.
Only the base L-infinity coefficient rows enter its definition. -/
def mollifiedH1SystemOperator (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) : V →L[ℝ] V :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ H¹(ℝ^n))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun p ↦
      -∑ j, ∑ q, (mollifierH1CLM μ hε).comp
        ((mulLpLeft ((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))).comp
          ((mollifierDerivativeRowCLM μ hε j).comp
            ((wkpCoordinateCLM (baseIndex n 1)).comp
              (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) q)))))

/-- The component formula for the constructed H1 operator. -/
theorem mollifiedH1SystemOperator_apply (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U : V) (p : Fin m) :
    mollifiedH1SystemOperator μ hε A U p = -∑ j, ∑ q, mollifierH1CLM μ hε
      (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
      mollifierDerivativeRowCLM μ hε j (wkpCoordinateCLM (baseIndex n 1) (U q))) := by
  simp only [mollifiedH1SystemOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply, ContinuousLinearMap.pi_apply, neg_apply, sum_apply,
    mulLpLeft_apply, PiLp.proj_apply]

/-- The base row solves the mollified matrix equation, component by component. -/
theorem mollifiedH1SystemOperator_base (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U : V) (p : Fin m) :
    wkpCoordinateCLM (baseIndex n 1) (mollifiedH1SystemOperator μ hε A U p) =
      -∑ j, ∑ q, mollifierRowCLM μ hε
        (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierDerivativeRowCLM μ hε j (wkpCoordinateCLM (baseIndex n 1) (U q))) := by
  rw [mollifiedH1SystemOperator_apply]
  simp only [map_neg, map_sum, mollifierH1CLM_base]

/-- Each weak derivative of the operator has the principal differentiated term
and the coefficient commutator. -/
theorem mollifiedH1SystemOperator_derivative (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (U : V) (p : Fin m) (l : Fin n) :
    wkpCoordinateCLM (singleDerivIndex n l) (mollifiedH1SystemOperator μ hε A U p) =
      (-∑ j, ∑ q, mollifierRowCLM μ hε
        (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          mollifierDerivativeRowCLM μ hε j
            (wkpCoordinateCLM (singleDerivIndex n l) (U q)))) -
      ∑ j, ∑ q, mollifierRowCLM μ hε
        (((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)) •
          mollifierRowCLM μ hε (wkpCoordinateCLM (singleDerivIndex n j) (U q))) := by
  rw [mollifiedH1SystemOperator_apply]
  simp only [map_neg, map_sum, mollifierH1CLM_derivative,
    derivative_mollifier_coefficient_term, Finset.sum_add_distrib, neg_add_rev, sub_eq_add_neg]
  abel

/-- Continuity of the base coefficient rows in L-infinity on a parameter set gives
continuity of the H1 operator on that set. The fixed outer mollifier is bounded from L2 to H1. -/
theorem continuousOn_mollifiedH1SystemOperator {X : Type*} [TopologicalSpace X] (μ : Mollifier n)
    {ε : ℝ} (hε : 0 < ε) (A : X → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {s : Set X}
    (hA : ∀ j p q, ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) s) :
    ContinuousOn (fun t ↦ mollifiedH1SystemOperator μ hε (A t)) s := by
  unfold mollifiedH1SystemOperator
  refine continuousOn_const.clm_comp
    ((ContinuousLinearMap.piEquivL ℝ V (fun _ : Fin m ↦ H¹(ℝ^n))).continuous.comp_continuousOn
      (continuousOn_pi.2 fun p ↦ (continuousOn_finsetSum _ fun j _ ↦
        continuousOn_finsetSum _ fun q _ ↦ ?_).neg))
  have hmult : ContinuousOn (fun t ↦ mulLpLeft
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) :
        X → L2 →L[ℝ] L2) s := by
    let T := (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ).holderL (domainMeasure n univ) ∞ 2 2
    have heq (a : DerivLp n ∞ univ) : T a = mulLpLeft a := by
      refine ContinuousLinearMap.ext fun u ↦ ?_
      apply Lp.ext
      filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).coeFn_holder (r := 2) a u,
        Lp.coeFn_lpSMul (r := 2) a u] with x hleft hright
      exact hleft.trans hright.symm
    simpa only [Function.comp_def, heq] using T.continuous.comp_continuousOn (hA j p q)
  exact continuousOn_const.clm_comp (hmult.clm_comp continuousOn_const)

/-- H1 initial data and Bochner L2-in-time H1 forcing construct a fixed-epsilon H1
trajectory. Only the base coefficient rows are assumed continuous in L-infinity on `[a,b]`.
The bounded outer mollifier supplies H1 output. This existence step alone gives no
epsilon-independent H1 bound. -/
theorem exists_mollified_h1_cauchy (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ}
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b) (F : ℝ → V) (hF : MemLp F 2 (volume.restrict (Icc a b))) (U₀ : V) :
    Nonempty (AffineCaratheodorySolutionOn (E := V)
      (fun t : ℝ ↦ mollifiedH1SystemOperator (n := n) (m := m) μ hε (A t)) F a b U₀) := by
  have hOp : ContinuousOn (fun t : ℝ ↦
      mollifiedH1SystemOperator (n := n) (m := m) μ hε (A t)) (Icc a b) :=
    continuousOn_mollifiedH1SystemOperator μ hε A hA
  obtain ⟨M, hMnorm⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
      (f := fun t : ℝ ↦ ‖mollifiedH1SystemOperator (n := n) (m := m) μ hε (A t)‖) hOp.norm
  have hM : ∀ t ∈ Icc a b, ‖mollifiedH1SystemOperator μ hε (A t)‖ ≤ M := fun t ht ↦ by
    simpa only [norm_norm] using hMnorm t ht
  have hMnonneg : 0 ≤ M :=
    (norm_nonneg (mollifiedH1SystemOperator μ hε (A a))).trans (hM a ⟨le_rfl, hab⟩)
  let : SecondCountableTopologyEither ℝ (V →L[ℝ] V) := ⟨Or.inl inferInstance⟩
  exact AffineCaratheodorySolutionOn.exists hab _ F (hOp.aestronglyMeasurable measurableSet_Icc)
    (hF.integrable (by norm_num)) ⟨M, hMnonneg⟩ hM U₀

/-- The base rows of the H1 trajectory satisfy the constructed mollified Cauchy equation
almost everywhere, with the base rows of the supplied forcing. -/
theorem mollified_h1_cauchy_base_equation_ae (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ} {F : ℝ → V} {U₀ : V}
    (U : AffineCaratheodorySolutionOn (E := V)
      (fun t : ℝ ↦ mollifiedH1SystemOperator (n := n) (m := m) μ hε (A t)) F a b U₀)
    (p : Fin m) :
    ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt
        (fun s ↦ wkpCoordinateCLM (baseIndex n 1) (U.trajectory s p))
        ((-∑ j, ∑ q, mollifierRowCLM μ hε
          (((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
            mollifierDerivativeRowCLM μ hε j
              (wkpCoordinateCLM (baseIndex n 1) (U.trajectory t q)))) +
          wkpCoordinateCLM (baseIndex n 1) (F t p)) t := by
  have h := U.hasDerivAt_comp_ae
    ((wkpCoordinateCLM (baseIndex n 1)).comp (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p))
  simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    mollifiedH1SystemOperator_base] using h

/-- The H1 trajectory's weak derivative rows satisfy the differentiated equation
with the weak coefficient derivatives and the derivative rows of the supplied forcing. -/
theorem mollified_h1_cauchy_derivative_equation_ae (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ} {F : ℝ → V} {U₀ : V}
    (U : AffineCaratheodorySolutionOn (E := V)
      (fun t : ℝ ↦ mollifiedH1SystemOperator (n := n) (m := m) μ hε (A t)) F a b U₀)
    (p : Fin m) (l : Fin n) :
    ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt
        (fun s ↦ wkpCoordinateCLM (singleDerivIndex n l) (U.trajectory s p))
        ((-∑ j, ∑ q, mollifierRowCLM μ hε
          (((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
            mollifierDerivativeRowCLM μ hε j
              (wkpCoordinateCLM (singleDerivIndex n l) (U.trajectory t q)))) -
          (∑ j, ∑ q, mollifierRowCLM μ hε
            (((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)) •
              mollifierRowCLM μ hε
                (wkpCoordinateCLM (singleDerivIndex n j) (U.trajectory t q)))) +
          wkpCoordinateCLM (singleDerivIndex n l) (F t p)) t := by
  have h := U.hasDerivAt_comp_ae
    ((wkpCoordinateCLM (singleDerivIndex n l)).comp (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p))
  simpa only [ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    mollifiedH1SystemOperator_derivative] using h

end PDE.Hyperbolic.FirstOrder

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

variable {n m : ℕ}

local notation "L2" => DerivLp n 2 univ
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))

/-- The principal quadratic bound applies to arbitrary scalar L2 component rows.
The H1 witnesses used in integration by parts are supplied by the mollifier lift. -/
theorem mollified_row_system_quadratic_le (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, (A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {ε : ℝ} (hε : 0 < ε) (u : Fin m → L2) :
    2 * (∑ p, ⟪-∑ j, ∑ q, mollifierRowCLM (standardMollifier n) hε
      (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
        mollifierDerivativeRowCLM (standardMollifier n) hε j (u q)), u p⟫_ℝ) ≤
      coefficientDerivativeBound A * (∑ p, ‖u p‖ ^ 2) := by
  classical
  let J := mollifierRowCLM (standardMollifier n) hε
  let K := mollifierDerivativeRowCLM (standardMollifier n) hε
  let c := fun j ↦ ∑ p, ∑ q, ‖(A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖
  have hc (j : Fin n) : 0 ≤ c j :=
    Finset.sum_nonneg fun p _ ↦ Finset.sum_nonneg fun q _ ↦ norm_nonneg _
  have henergy : (∑ p, ‖J (u p)‖ ^ 2) ≤ ∑ p, ‖u p‖ ^ 2 := Finset.sum_le_sum fun p _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (norm_mollifierRowCLM_apply_le _ hε (u p)) 2
  have hrow (j : Fin n) : -(∑ p, ∑ q, ⟪((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
        K j (u q), J (u p)⟫_ℝ) ≤
      (1 / 2 : ℝ) * c j * (∑ p, ‖u p‖ ^ 2) := by
    have h := symmetric_matrix_transport_energy_le (A j) (hA j) j
      (fun p ↦ mollifierH1CLM (standardMollifier n) hε (u p))
    simp only [← wkpCoordinateCLM_apply, mollifierH1CLM_base, mollifierH1CLM_derivative] at h
    exact h.trans (mul_le_mul_of_nonneg_left henergy
      (mul_nonneg (by norm_num) (hc j)))
  calc
    _ = 2 * ∑ j, -(∑ p, ∑ q, ⟪((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) •
          K j (u q), J (u p)⟫_ℝ) := by
      simp only [inner_neg_left, sum_inner, inner_standardMollifierRowCLM_left,
        Finset.sum_neg_distrib, J, K]
      rw [Finset.sum_comm]
    _ ≤ 2 * ∑ j, (1 / 2 : ℝ) * c j * (∑ p, ‖u p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hrow j) (by norm_num)
    _ = coefficientDerivativeBound A * (∑ p, ‖u p‖ ^ 2) := by
      simp only [coefficientDerivativeBound, ← Finset.sum_mul, ← Finset.mul_sum, c]
      ring

/-- The smoothed coefficient commutator has an epsilon-independent bound on scalar
gradient rows. The coefficient entries are W1-infinity weak derivative rows. -/
theorem abs_sum_inner_mollified_row_commutator_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    {ε : ℝ} (hε : 0 < ε) (g : Fin n → Fin m → L2) :
    |∑ l, ∑ p, ⟪∑ j, ∑ q, mollifierRowCLM (standardMollifier n) hε
      (((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)) •
        mollifierRowCLM (standardMollifier n) hε (g j q)), g l p⟫_ℝ| ≤
      coefficientGradientBound A * (∑ l, ∑ p, ‖g l p‖ ^ 2) := by
  classical
  let J := mollifierRowCLM (standardMollifier n) hε
  have h := abs_sum_inner_w1TopMultiplier_derivative_commutator_le A
    (fun l p ↦ mollifierH1CLM (standardMollifier n) hε (g l p))
  simp only [w1TopMultiplierCLM_apply_coe, w1TopMultiplierAmbient_singleDeriv,
    add_sub_cancel_left] at h
  simp only [← wkpCoordinateCLM_apply, mollifierH1CLM_base] at h
  have henergy : (∑ l, ∑ p, ‖J (g l p)‖ ^ 2) ≤ ∑ l, ∑ p, ‖g l p‖ ^ 2 :=
    Finset.sum_le_sum fun l _ ↦ Finset.sum_le_sum fun p _ ↦
      pow_le_pow_left₀ (norm_nonneg _) (norm_mollifierRowCLM_apply_le _ hε (g l p)) 2
  simpa only [sum_inner, inner_standardMollifierRowCLM_left, wkpCoordinateCLM_apply,
    coefficientGradientBound] using
    h.trans (mul_le_mul_of_nonneg_left henergy (coefficientGradientBound_nonneg A))

/-- The H1 matrix operator has quadratic bound Cdiv + 2 Cgrad. The proof uses its differentiated
coefficient formula. -/
theorem mollifiedH1SystemOperator_quadratic_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, (A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {ε : ℝ} (hε : 0 < ε) (U : V) :
    2 * ⟪mollifiedH1SystemOperator (standardMollifier n) hε A U, U⟫_ℝ ≤
      (coefficientDerivativeBound A + 2 * coefficientGradientBound A) * ‖U‖ ^ 2 := by
  classical
  let J := mollifierRowCLM (standardMollifier n) hε
  let K := mollifierDerivativeRowCLM (standardMollifier n) hε
  let u := fun p ↦ wkpCoordinateCLM (baseIndex n 1) (U p)
  let g := fun l p ↦ wkpCoordinateCLM (singleDerivIndex n l) (U p)
  let P := fun (v : Fin m → L2) p ↦
    -∑ j, ∑ q, J (((A j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • K j (v q))
  let R := fun l p ↦ ∑ j, ∑ q, J (((A j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)) •
      J (g j q))
  let T := mollifiedH1SystemOperator (standardMollifier n) hε A
  have hinner (p : Fin m) : ⟪T U p, U p⟫_ℝ = ⟪P u p, u p⟫_ℝ +
        ∑ l, (⟪P (g l) p, g l p⟫_ℝ - ⟪R l p, g l p⟫_ℝ) := by
    change ⟪(T U p : WkpAmbientOn n 1 2 univ), (U p : WkpAmbientOn n 1 2 univ)⟫_ℝ = _
    rw [ambient_inner_eq_base_add_sum_deriv]
    change ⟪wkpCoordinateCLM (baseIndex n 1) (T U p), u p⟫_ℝ +
      (∑ l, ⟪wkpCoordinateCLM (singleDerivIndex n l) (T U p), g l p⟫_ℝ) = _
    simp only [T, mollifiedH1SystemOperator_base, mollifiedH1SystemOperator_derivative,
      inner_sub_left, P, R, u, g, J, K]
  have hpair : ⟪T U, U⟫_ℝ = (∑ p, ⟪P u p, u p⟫_ℝ) + (∑ l, ∑ p, ⟪P (g l) p, g l p⟫_ℝ) -
        (∑ l, ∑ p, ⟪R l p, g l p⟫_ℝ) := by
    rw [PiLp.inner_apply]
    simp only [hinner, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
    ring
  have hnorm : ‖U‖ ^ 2 = (∑ p, ‖u p‖ ^ 2) + ∑ l, ∑ p, ‖g l p‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hcomponent (p : Fin m) : ‖U p‖ ^ 2 = ‖u p‖ ^ 2 + ∑ l, ‖g l p‖ ^ 2 :=
      ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (U p : WkpAmbientOn n 1 2 univ)
    simp only [hcomponent, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  have hbase := mollified_row_system_quadratic_le A hA hε u
  have hgrad : 2 * (∑ l, ∑ p, ⟪P (g l) p, g l p⟫_ℝ) ≤
        coefficientDerivativeBound A * (∑ l, ∑ p, ‖g l p‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ ↦ mollified_row_system_quadratic_le A hA hε (g l)
  have hcommLower := (neg_le_abs _).trans (abs_sum_inner_mollified_row_commutator_le A hε g)
  have hcross : 0 ≤ coefficientGradientBound A * (∑ p, ‖u p‖ ^ 2) :=
    mul_nonneg (coefficientGradientBound_nonneg A) (by positivity)
  change 2 * ⟪T U, U⟫_ℝ ≤ _
  rw [hpair, hnorm]
  change 2 * (∑ p, ⟪P u p, u p⟫_ℝ) ≤ _ at hbase
  linarith only [hbase, hgrad, hcommLower, hcross]

/-- H1 data and L2-in-time H1 forcing give a constructed mollified trajectory with an
epsilon-independent H1 estimate. The coefficients are symmetric in their base rows and
their base rows are continuous in L-infinity on `[a,b]`. C bounds the divergence rows and L
bounds all first coefficient derivatives. The fixed outer mollifier supplies operator continuity,
and the weak derivative rows enter the energy estimate pointwise in time.

The solution's weak spatial derivative rows satisfy
`mollified_h1_cauchy_derivative_equation_ae`. The original-system epsilon limit is separate. -/
theorem exists_mollified_h1_cauchy_with_uniform_energy
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) {a b : ℝ}
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a ≤ b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (F : ℝ → V)
    (hF : MemLp F 2 (volume.restrict (Icc a b))) (U₀ : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : AffineCaratheodorySolutionOn (E := V)
      (fun t : ℝ ↦ mollifiedH1SystemOperator (n := n) (m := m)
        (standardMollifier n) hε (A t)) F a b U₀,
      ∀ t ∈ Icc a b,
        ‖U.trajectory t‖ ^ 2 ≤
          (‖U₀‖ ^ 2 + ∫ s in a..b, ‖F s‖ ^ 2) *
            Real.exp ((C + 2 * L + 1) * (t - a)) := by
  obtain ⟨U⟩ := exists_mollified_h1_cauchy (standardMollifier n) hε A hA hab F hF U₀
  refine ⟨U, U.norm_sq_le_mul_exp_of_quadratic_bound (C := C + 2 * L)
    hab hF (by positivity) fun t ht v ↦
      (mollifiedH1SystemOperator_quadratic_le (A t) (hsym t ht) hε v).trans ?_⟩
  gcongr
  exacts [hdiv t ht, hgrad t ht]

end PDE.Hyperbolic.FirstOrder

end H1SystemInstances
