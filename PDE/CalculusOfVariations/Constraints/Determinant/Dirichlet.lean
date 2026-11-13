/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Classical
public import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.Fibers

/-!
# Affine Sobolev minimization with determinant one

The determinant constraint is weakly sequentially closed at every finite real
exponent above the positive dimension. The common constrained direct method
then applies to a C¹ density convex in the gradient matrix. The energy shift
is finite on bounded domains, so the minimizer also minimizes the original
signed extended energy, including when every admissible energy is infinite.

This is the affine-class form of Evans, §8.4.4(b), Theorem 7, which is stated there for maps
of three variables and `q > 3`. Here the dimension `n` is any positive integer, `q > n`, the
boundary condition is `u - g ∈ W₀^{1,q}`, and the density may also depend on the value of the
map. All matrix coercivity norms are Frobenius norms.

## Main results

* `exists_minimizer_matrixWkpIntegral_prescribed_boundary_det_eq_one`: a minimizer among
  determinant-one maps in the affine class of a determinant-one map `g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.4(b), Theorem 7.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Topology Matrix.Norms.Elementwise Sobolev

namespace PDE.CalculusOfVariations

/-- A C¹ convex matrix density with Frobenius power coercivity attains its
signed extended minimum among determinant-one maps in an affine zero-trace
class. The prescribed map supplies admissibility, not finite energy. -/
theorem exists_minimizer_matrixWkpIntegral_prescribed_boundary_det_eq_one
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : (n : ℝ) < q)
    {L : (ℝ^n × ℝ^n) × Matrix (Fin n) (Fin n) ℝ → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ))
    (hconvex : ∀ x ∈ Ω, ∀ s : ℝ^n,
      ConvexOn ℝ univ (fun P : Matrix (Fin n) (Fin n) ℝ ↦ L ((x, s), P)))
    {α β : ℝ} (hα : 0 < α)
    (hcoercive : ∀ x ∈ Ω, ∀ (s : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ),
      α * ‖Matrix.euclideanEquiv P‖ ^ q - β ≤ L ((x, s), P))
    (g : Fin n → W^{1,ENNReal.ofReal q}(Ω))
    (hg : ∀ᵐ x ∂domainMeasure n Ω,
      (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex n j) (g i) x).det = 1) :
    ∃ u : Fin n → W^{1,ENNReal.ofReal q}(Ω),
      (∀ᵐ x ∂domainMeasure n Ω,
        (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex n j) (u i) x).det = 1) ∧
      (∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω)) ∧
      ∀ v : Fin n → W^{1,ENNReal.ofReal q}(Ω),
        (∀ᵐ x ∂domainMeasure n Ω,
          (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex n j) (v i) x).det = 1) →
        (∀ i, v i - g i ∈ wkp0SubmoduleOn
          (n := n) (k := 1) (p := ENNReal.ofReal q) (Ω := Ω)) →
        vectorWkpIntegral (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) u ≤
          vectorWkpIntegral (fun x z ↦ L ((x, z.1), Matrix.euclideanEquiv.symm z.2)) v := by
  have hn : 0 < n := Fact.out
  have hq1 : 1 < q :=
    (show (1 : ℝ) ≤ n by exact_mod_cast Nat.succ_le_iff.mpr hn).trans_lt hq
  have hq0 : 0 ≤ q := zero_le_one.trans hq1.le
  have hp : 1 < q.toNNReal := by
    exact_mod_cast (show (1 : ℝ) < (q.toNNReal : ℝ) by
      simpa only [Real.coe_toNNReal q hq0] using hq1)
  let : Fact (1 ≤ (q.toNNReal : ℝ≥0∞)) := ⟨by exact_mod_cast hp.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) :=
    ⟨(ENNReal.one_lt_ofReal_div_nat hn hq).le⟩
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let A := {u : Fin n → W^{1,ENNReal.ofReal q}(Ω) |
    ∀ᵐ x ∂domainMeasure n Ω,
      (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex n j) (u i) x).det = 1}
  have hclosed : IsSeqClosed (toWeakSpace ℝ
      (Fin n → W^{1,ENNReal.ofReal q}(Ω)) '' A) :=
    isSeqClosed_weak_setOf_jacobianDet_eq_ae (Ω := ⟨Ω, hopen⟩)
      hbounded hgraph hq (fun _ ↦ 1) (memLp_const 1)
  have hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ L ((x, s), P) := by
    intro x hx s P
    have h := hcoercive x hx s P
    have hnonneg := mul_nonneg hα.le
      (Real.rpow_nonneg (norm_nonneg (Matrix.euclideanEquiv P)) q)
    linarith
  have hlow : ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^n) (z : ℝ^(n * n)),
      α * ‖z‖ ^ (q.toNNReal : ℝ) - β ≤ L ((x, s), Matrix.euclideanEquiv.symm z) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
    intro s z
    simpa only [ContinuousLinearEquiv.apply_symm_apply, Real.coe_toNNReal q hq0] using
      hcoercive x hx s (Matrix.euclideanEquiv.symm z)
  have hL' : ContDiffOn ℝ 1
      (fun t : (ℝ^n × ℝ^n) × ℝ^(n * n) ↦ L (t.1, Matrix.euclideanEquiv.symm t.2))
      ((Ω ×ˢ univ) ×ˢ univ) :=
    hL.comp (contDiff_fst.prodMk
      (Matrix.euclideanEquiv.symm.contDiff.comp contDiff_snd)).contDiffOn
      (fun _ ht ↦ ⟨ht.1, mem_univ _⟩)
  have hconv' : ∀ x ∈ Ω, ∀ s : ℝ^n, ConvexOn ℝ univ
      (fun z : ℝ^(n * n) ↦ L ((x, s), Matrix.euclideanEquiv.symm z)) := by
    intro x hx s
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ t r ht hr htr
    change L ((x, s), Matrix.euclideanEquiv.symm (t • a + r • b)) ≤
      t • L ((x, s), Matrix.euclideanEquiv.symm a) +
        r • L ((x, s), Matrix.euclideanEquiv.symm b)
    rw [map_add, map_smul, map_smul]
    exact (hconvex x hx s).2 (mem_univ _) (mem_univ _) ht hr htr
  obtain ⟨u, huA, hu, hmin⟩ :=
    exists_minimizer_vectorWkpLIntegral_prescribed_boundary_of_weak_lsc
      hbounded hp hα hlow
      (fun h ↦ vectorWkpLIntegral_le_liminf_of_contDiffOn_convex
        hopen hbounded hgraph hp hL' hconv'
        (fun x hx s z ↦ hlower x hx s (Matrix.euclideanEquiv.symm z)) h) hclosed g hg
  refine ⟨u, huA, hu, fun v hvA hv ↦ ?_⟩
  calc
    _ = _ := vectorWkpIntegral_eq_lIntegral_sub_of_continuousOn
      hopen.measurableSet hL.continuousOn hlower u
    _ ≤ _ := add_le_add
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (hmin v hvA hv)) le_rfl
    _ = _ := (vectorWkpIntegral_eq_lIntegral_sub_of_continuousOn
      hopen.measurableSet hL.continuousOn hlower v).symm

end PDE.CalculusOfVariations
