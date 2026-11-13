/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Ellipticity-preserving coefficient extension

Let `Ω ⊆ ℝⁿ` have a `C¹` extension atlas, so that `Ω` is bounded, and let `a` be a `C¹` matrix field
on `ℝⁿ` that is uniformly elliptic on `Ω` with constant `α`. Then `a` agrees on `Ω` with a bounded,
globally Lipschitz field that is uniformly elliptic on `ℝⁿ` with constant `α/2`
(`exists_global_ellipticCoefficientExtension`). The whole-space difference-quotient theorem applies
to such coefficients.

Evans's §6.3.2, Theorem 4, assumes `aⁱʲ ∈ C¹(Ū)`, his (38);
`exists_global_ellipticCoefficientExtension` assumes that `a` is `C¹` on all of `ℝⁿ`.

## How it works

An entrywise perturbation of size `δ` changes the quadratic form by at most `n δ |ξ|²`
(`abs_principalEnergy_sub_le_of_entrywise`). By continuity, `a` is elliptic with constant `α` on the
closure of `Ω` and with constant `α/2` on an open neighborhood of it
(`exists_open_uniformlyElliptic_neighborhood`). With a smooth cutoff `η` with values in `[0, 1]`
that equals one on the compact closure and has support in that neighborhood, `η a + (1 - η)(α/2) I`
is at each point a convex combination of matrices with constant `α/2`. It differs from `(α/2) I` by
a compactly supported `C¹` field, so it is globally Lipschitz and bounded. The argument uses only
the quadratic form, not eigenvalues.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), (38)-(42),
  p. 334.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

/-- Entrywise perturbations control the associated quadratic form. -/
theorem abs_principalEnergy_sub_le_of_entrywise
    (A B : Fin n → Fin n → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hAB : ∀ i j, |A i j - B i j| ≤ delta) (xi : Fin n → ℝ) :
    |principalEnergy A xi - principalEnergy B xi| ≤
      (n : ℝ) * delta * (xi ⬝ᵥ xi) := by
  classical
  have hrewrite : principalEnergy A xi - principalEnergy B xi =
      ∑ i, ∑ j, (A i j - B i j) * xi i * xi j := by
    simp only [principalEnergy, ← Finset.sum_sub_distrib, sub_mul]
  rw [hrewrite]
  calc
    _ ≤ ∑ i, ∑ j, |(A i j - B i j) * xi i * xi j| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (delta / 2) * (xi i ^ 2 + xi j ^ 2) := by
      gcongr with i _ j _
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hAB i j)
        (abs_nonneg (xi i))) (abs_nonneg (xi j)), sq_nonneg (|xi i| - |xi j|), sq_abs (xi i),
        sq_abs (xi j), abs_nonneg (xi i), abs_nonneg (xi j)]
    _ = (n : ℝ) * delta * (xi ⬝ᵥ xi) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, dotProduct]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- A sufficiently small entrywise perturbation preserves half of a positive
ellipticity constant. -/
theorem matrixEllipticLowerBound_of_entrywise_close
    (A B : Fin n → Fin n → ℝ) {alpha delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hsmall : (n : ℝ) * delta ≤ alpha / 2)
    (hA : MatrixEllipticLowerBound A alpha)
    (hAB : ∀ i j, |B i j - A i j| ≤ delta) :
    MatrixEllipticLowerBound B (alpha / 2) := by
  intro xi
  have hperturb := abs_principalEnergy_sub_le_of_entrywise B A delta hdelta hAB xi
  have hnorm : 0 ≤ xi ⬝ᵥ xi := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (xi i)
  linarith [hA xi, neg_abs_le (principalEnergy B xi - principalEnergy A xi),
    mul_le_mul_of_nonneg_right hsmall hnorm]

variable [Fact (0 < n)]

/-- Uniform ellipticity of a continuous field on a set persists, with half the constant, on
an open neighborhood of the closure of the set. -/
theorem exists_open_uniformlyElliptic_neighborhood
    {Omega : Set (ℝ^n)}
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, Continuous (fun x ↦ a x i j))
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    ∃ U : Set (ℝ^n), IsOpen U ∧ closure Omega ⊆ U ∧
      ∀ x ∈ U, MatrixEllipticLowerBound (a x) (alpha / 2) := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast (Fact.out : 0 < n)
  let delta : ℝ := alpha / (4 * n)
  have hdelta : 0 < delta := by positivity
  have hsmall : (n : ℝ) * delta ≤ alpha / 2 := by
    rw [mul_div_assoc', mul_comm (4 : ℝ), mul_div_mul_left _ _ hn.ne']
    linarith
  have hEllipticClosure (x : ℝ^n) (hx : x ∈ closure Omega) :
      MatrixEllipticLowerBound (a x) alpha := fun xi ↦
    closure_minimal (t := {y | alpha * (xi ⬝ᵥ xi) ≤ principalEnergy (a y) xi})
      (fun y hy ↦ hElliptic y hy xi)
      (isClosed_le continuous_const (by unfold principalEnergy; fun_prop)) hx
  refine ⟨⋃ x0 : closure Omega, {x | ∀ i j, |a x i j - a x0 i j| < delta},
    isOpen_iUnion fun x0 ↦ ?_,
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, fun i j ↦ by simpa using hdelta⟩, fun x hx ↦ ?_⟩
  · simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_lt ((ha i j).sub continuous_const).abs continuous_const
  · obtain ⟨x0, hx⟩ := mem_iUnion.1 hx
    exact matrixEllipticLowerBound_of_entrywise_close (a x0) (a x) hdelta.le hsmall
      (hEllipticClosure x0 x0.2) fun i j ↦ (hx i j).le

/-- A `C¹` coefficient field which is uniformly elliptic on a bounded domain
admits a globally Lipschitz, globally bounded, uniformly elliptic extension
which agrees with it on the domain.

The extension is uniformly elliptic with constant `alpha / 2`. It turns coefficient
assumptions on the domain into the whole-space coefficients used by the
difference-quotient proof. -/
theorem exists_global_ellipticCoefficientExtension
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    ∃ (extension : ℝ^n → Fin n → Fin n → ℝ)
        (lipschitzConstant : Fin n → Fin n → NNReal)
        (coefficient : Fin n → Fin n → DerivLp n ∞ Set.univ),
      Set.EqOn extension a Omega ∧
      (∀ i j,
        LipschitzWith (lipschitzConstant i j) (fun x ↦ extension x i j)) ∧
      (∀ i j,
        (coefficient i j : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ extension x i j) ∧
      AEUniformlyElliptic (n := n) (Ω := Set.univ) coefficient (alpha / 2) := by
  classical
  obtain ⟨U, hUopen, hclosureU, hEllipticU⟩ :=
    exists_open_uniformlyElliptic_neighborhood a (fun i j ↦ (ha i j).continuous) halpha hElliptic
  obtain ⟨eta, hetaU, hetaOne, -, hetaRange⟩ :=
    TestFunction.exists_eq_one_on_compact hUopen hOmega.bounded.isCompact_closure hclosureU
  let beta := alpha / 2
  let aext : ℝ^n → Fin n → Fin n → ℝ := glueCoefficientField (n := n) eta.toFun beta a
  let deviation (i j : Fin n) (x : ℝ^n) : ℝ := aext x i j - scalarIdentityMatrix (n := n) beta i j
  have hdeviation (i j : Fin n) : deviation i j =
      fun x ↦ eta.toFun x * (a x i j - scalarIdentityMatrix (n := n) beta i j) := by
    funext x
    simp only [deviation, aext, glueCoefficientField, glueToScalarIdentity]
    ring
  have hdeviationCompact (i j : Fin n) : HasCompactSupport (deviation i j) := by
    rw [hdeviation]
    exact eta.hasCompactSupport.mul_right
  have hdeviationC1 (i j : Fin n) : ContDiff ℝ 1 (deviation i j) := by
    rw [hdeviation]
    exact (eta.contDiff.of_le (by simp)).mul ((ha i j).sub contDiff_const)
  choose C hC using fun i j ↦ ContDiff.lipschitzWith_of_hasCompactSupport
    (hdeviationCompact i j) (hdeviationC1 i j) (by norm_num)
  have hLip (i j : Fin n) : LipschitzWith (C i j) (fun x ↦ aext x i j) := by
    simpa [deviation] using
      (hC i j).add (LipschitzWith.const (scalarIdentityMatrix (n := n) beta i j))
  have hmem (i j : Fin n) : MemLp (fun x ↦ aext x i j) ∞ (domainMeasure n Set.univ) := by
    simpa only [Pi.add_def, deviation, sub_add_cancel] using
      ((hdeviationC1 i j).continuous.memLp_top_of_hasCompactSupport
        (hdeviationCompact i j) _).add (memLp_top_const (scalarIdentityMatrix (n := n) beta i j))
  let Aext : Fin n → Fin n → DerivLp n ∞ Set.univ := fun i j ↦
    (hmem i j).toLp (fun x ↦ aext x i j)
  have hrepAll : ∀ᵐ x ∂domainMeasure n Set.univ, ∀ i j, (Aext i j : ℝ^n → ℝ) x = aext x i j :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ (hmem i j).coeFn_toLp
  refine ⟨aext, C, Aext, fun x hx ↦ glueCoefficientField_eq_of_cutoff_eq_one _ _ _
    (hetaOne x (subset_closure hx)), hLip,
    fun i j ↦ by simpa [domainMeasure] using (hmem i j).coeFn_toLp, half_pos halpha, ?_⟩
  filter_upwards [hrepAll] with x hx xi
  have hpoint : MatrixEllipticLowerBound (aext x) beta :=
    matrixEllipticLowerBound_glueCoefficientField eta.toFun beta beta a x
    (hetaRange x).1 (hetaRange x).2 le_rfl fun heta0 ↦
      hEllipticU x (hetaU (subset_tsupport _ heta0))
  simpa [beta, MatrixEllipticLowerBound, dotProduct, principalEnergy, pow_two, hx, mul_comm,
    mul_left_comm, mul_assoc] using hpoint xi

end SobolevSpace.GraphSpace.BoundaryRegularity
