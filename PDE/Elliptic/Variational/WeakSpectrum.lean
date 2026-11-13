/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fredholm.WeakForm.Reduction
public import PDE.Analysis.Variational.Spectral
public import PDE.Elliptic.Variational.FredholmAlternative
public import PDE.Elliptic.Variational.ShiftedDivergenceForm
import PDE.Analysis.Fredholm.Nullity
import PDE.Analysis.Fredholm.WeakForm.Alternative
import PDE.Analysis.Spectral.Enumeration

/-!
# Weak elliptic spectrum

We prove Evans's §6.2.3, Theorem 5 (Third Existence Theorem for weak solutions) for a form pencil
`B - λM`: the real weak spectrum is countable, unique weak solvability for every forcing holds
exactly off the spectrum, and an infinite spectrum has an exhaustive increasing enumeration tending
to infinity. We also prove that weak eigenspaces are finite-dimensional, which is Theorem 4(ii) for
`L - λ`, and that distinct eigenvalues have no finite accumulation point. For the full divergence
form we prove Theorem 6 (Boundedness of the inverse): off the spectrum, `‖u‖_{L²} ≤ C ‖f‖_{L²}` with
one constant `C` for all forcings.

The public definitions use ordinary weak forms. An eigenvalue `lambda` is a real number for which
`B[u,v] = lambda M[u,v]` has a nonzero weak solution.

Nonnegative mass and shifted coercivity bound the weak spectrum from below. Compactness then makes
every sublevel finite. Enumerating the subtype of all weak eigenvalues gives each distinct value
exactly once. `fullDivergenceForm.weakSpectrum_properties_of_aeElliptic` discharges these
assumptions for bounded open domains and bounded measurable coefficients with almost-everywhere
uniform ellipticity. It requires neither symmetry nor boundary regularity.

For a symmetric form coercive after a mass shift, a compact map with dense range into a pivot
Hilbert space gives a Hilbert basis of weak eigenfunctions in that space. This uses the self-adjoint
pivot solution operator, rather than assuming symmetry of the solution operator on the energy space.
The ordered enumeration for Dirichlet forms is `OrderedDirichletSpectrum`.

## Main definitions

* `pencilForm`: the pencil `B - λM` of a form `B` and a mass form `M`.
* `IsWeakEigenfunction`, `weakSpectrum`, `weakEigenspace`: nonzero weak solutions of
  `B[u,v] = λ M[u,v]`, the real weak spectrum, and the eigenspace at `λ`.
* `spectralSolutionOperator`: the shifted solution operator `L_γ⁻¹ M`.

## Main results

* `weakSpectrum_countable`, `finiteDimensional_weakEigenspace`,
  `weakSpectrum_has_no_finite_injective_limit`: countability, finite multiplicity, and no finite
  accumulation.
* `unique_pencil_solution_iff_notMem_weakSpectrum`: unique solvability exactly off the spectrum,
  Evans's Theorem 5(i).
* `exists_strictMono_enumeration_weakSpectrum`: the increasing enumeration of an infinite spectrum,
  Theorem 5(ii).
* `fullDivergenceForm.weakSpectrum_properties_of_aeElliptic` and
  `fullDivergenceForm.exists_l2_bound_of_notMem_weakSpectrum`: Theorems 5 and 6 for `L∞`
  coefficients on a bounded open set.
* `exists_hilbertBasis_weakEigenfunctions_of_coercive_shift`: a Hilbert basis of weak eigenfunctions
  for a symmetric form.

## How it works

Evans assumes `λ > -γ`, (25), where `γ` is the constant of the energy estimates, and writes the
eigen-equation as (27), `u = ((γ + λ)/γ) K u` with `K = γ L_γ⁻¹` compact on `L²(U)`. Then `λ` is an
eigenvalue exactly when `γ/(γ + λ)` is an eigenvalue of `K`, (28), and §D.5, Theorem 6 describes
those eigenvalues. We work on the energy space with `spectralSolutionOperator`, the composition
`L_γ⁻¹ M` of the Lax-Milgram inverse with a compact mass operator `M`, whose eigenvalue for `λ` is
`(γ + λ)⁻¹` (`isWeakEigenfunction_iff_hasEigenvector_spectralSolutionOperator`). Coercivity excludes
`γ + λ = 0` (`add_ne_zero_of_isWeakEigenfunction`), so the substitution is valid for every
eigenvalue; with nonnegative mass every eigenvalue is greater than `-γ`
(`neg_shift_lt_of_isWeakEigenfunction`), which gives the finite sublevels behind the enumeration.
For Theorem 6 Evans argues by contradiction with a subsequence converging weakly in `H¹₀` and
strongly in `L²`, (30); we apply the open mapping theorem of Mathlib,
`ContinuousLinearMap.exists_preimage_norm_le`, to the surjective pencil operator.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.3, Theorem 4 (Second Existence Theorem for weak
  solutions) and its proof, (10)-(23), pp. 321-323; Theorem 5 (Third Existence Theorem for weak
  solutions), Theorem 6 (Boundedness of the inverse) and their proofs, (24)-(30), pp. 323-325; §D.5,
  Theorem 6 (Spectrum of a compact operator), p. 727.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

universe v

namespace SobolevSpace.Weak

open Set Function Filter
open PDE.Analysis.Variational
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The weak operator pencil `B - lambda M`. -/
def pencilForm
    (form massForm : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ) :
    V →L[ℝ] StrongDual ℝ V :=
  form - lambda • massForm

omit [CompleteSpace V] in
/-- Evaluating the pencil: `(B - lambda M)[u,v] = B[u,v] - lambda * M[u,v]`. -/
@[simp]
theorem pencilForm_apply
    (form massForm : V →L[ℝ] StrongDual ℝ V)
    (lambda : ℝ) (u v : V) :
    pencilForm form massForm lambda u v =
      form u v - lambda * massForm u v := by
  simp [pencilForm]

/-- A nonzero weak eigenfunction for `B[u,v] = lambda M[u,v]`. -/
def IsWeakEigenfunction
    (form massForm : V →L[ℝ] StrongDual ℝ V)
    (lambda : ℝ) (u : V) : Prop :=
  u ≠ 0 ∧ ∀ v : V, form u v = lambda * massForm u v

/-- The real weak spectrum of the form pencil `(form, massForm)`. -/
def weakSpectrum
    (form massForm : V →L[ℝ] StrongDual ℝ V) : Set ℝ :=
  {lambda | ∃ u : V, IsWeakEigenfunction form massForm lambda u}

/-- The weak eigenspace at `lambda`, defined as the kernel of the ordinary
form pencil `B - lambda M`. -/
def weakEigenspace
    (form massForm : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ) : Submodule ℝ V :=
  (pencilForm form massForm lambda).ker

omit [CompleteSpace V] in
/-- Membership in the weak eigenspace at `lambda` is the weak eigen-equation
`B[u,v] = lambda * M[u,v]` for every test vector `v`. Unlike `IsWeakEigenfunction`, the zero
vector is allowed, so the eigenspace is a submodule. -/
@[simp]
theorem mem_weakEigenspace_iff
    (form massForm : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ) (u : V) :
    u ∈ weakEigenspace form massForm lambda ↔
      ∀ v : V, form u v = lambda * massForm u v := by
  rw [weakEigenspace, LinearMap.mem_ker]
  constructor
  · intro hu v
    have heval := congrArg (fun ell : StrongDual ℝ V ↦ ell v) hu
    change pencilForm form massForm lambda u v = 0 at heval
    rw [pencilForm_apply] at heval
    linarith
  · intro hu
    ext v
    simp [pencilForm_apply, hu v]

/-- Weak eigenspaces have finite dimension under shifted coercivity and
compactness of the mass form, as in Evans's §6.2.3, Theorem 4(ii), for
`L - λ`. The proof applies the finite-dimensional kernel theorem to the pencil
`B - lambda M`. -/
theorem finiteDimensional_weakEigenspace
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    FiniteDimensional ℝ (weakEigenspace form massForm lambda) := by
  apply PDE.Analysis.finiteDimensional_ker_form
    (pencilForm form massForm lambda) shiftedForm massForm coercive (gamma + lambda)
  · intro u v
    rw [hshift u v, pencilForm_apply]
    ring
  · exact hcompactMass

omit [CompleteSpace V] in
/-- A weak eigenfunction at `lambda` is the same as a nonzero weak solution of the homogeneous
pencil problem `(B - lambda M)[u, ·] = 0`. -/
theorem isWeakEigenfunction_iff_homogeneous_pencil
    (form massForm : V →L[ℝ] StrongDual ℝ V)
    (lambda : ℝ) (u : V) :
    IsWeakEigenfunction form massForm lambda u ↔
      u ≠ 0 ∧ IsWeakSolution (pencilForm form massForm lambda) 0 u := by
  constructor
  · rintro ⟨hu, heig⟩
    refine ⟨hu, fun v ↦ ?_⟩
    simp [pencilForm_apply, heig v]
  · rintro ⟨hu, hweak⟩
    refine ⟨hu, fun v ↦ ?_⟩
    have hv := hweak v
    simp only [pencilForm_apply, zero_apply] at hv
    linarith

omit [CompleteSpace V] in
/-- `lambda` lies in the weak spectrum exactly when the homogeneous pencil problem at `lambda`
has a nonzero weak solution. -/
theorem mem_weakSpectrum_iff_nonzero_homogeneous_pencil
    (form massForm : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ) :
    lambda ∈ weakSpectrum form massForm ↔
      ∃ u : V, u ≠ 0 ∧ IsWeakSolution (pencilForm form massForm lambda) 0 u := by
  exact exists_congr fun u ↦ isWeakEigenfunction_iff_homogeneous_pencil
    form massForm lambda u

/-- The shifted solution operator `L_gamma⁻¹ M`, compact when `M` is. It takes
the place of the operator `K = γ L_γ⁻¹` of (18) in the proof of Evans's §6.2.3,
Theorem 4. -/
def spectralSolutionOperator
    (shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) : V →L[ℝ] V :=
  (solveCLM shiftedForm coercive).comp massForm

/-- The shifted solution operator `L_gamma⁻¹ M` is compact whenever the mass operator `M` is:
composing a compact operator with the bounded Lax-Milgram inverse preserves compactness. -/
theorem isCompactOperator_spectralSolutionOperator
    (shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm)
    (hcompactMass : IsCompactOperator massForm) :
    IsCompactOperator (spectralSolutionOperator shiftedForm massForm coercive) :=
  hcompactMass.clm_comp (solveCLM shiftedForm coercive)

/-- The spectral substitution `(gamma + lambda)⁻¹`: weak eigenfunctions of the
form pencil are exactly the eigenvectors of the shifted solution operator for
the eigenvalue `(gamma + lambda)⁻¹`. This is our form of (26)-(28) in the proof
of Evans's §6.2.3, Theorem 5, where the eigenvalue of `K = γ L_γ⁻¹` is
`γ/(γ + λ)`. -/
theorem isWeakEigenfunction_iff_hasEigenvector_spectralSolutionOperator
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hgamma : gamma + lambda ≠ 0) (u : V) :
    IsWeakEigenfunction form massForm lambda u ↔
      Module.End.HasEigenvector
        (spectralSolutionOperator shiftedForm massForm coercive : Module.End ℝ V)
        (gamma + lambda)⁻¹ u := by
  let a := gamma + lambda
  let R := spectralSolutionOperator shiftedForm massForm coercive
  have ha : a ≠ 0 := hgamma
  constructor
  · rintro ⟨hu, heigen⟩
    have huShifted : IsWeakSolution shiftedForm (a • massForm u) u := fun v ↦ by
      simp only [hshift u v, heigen v, a, FunLike.coe_smul, Pi.smul_apply,
        smul_eq_mul]
      ring
    have huEq : u = a • R u := (IsWeakSolution.unique shiftedForm coercive _ huShifted
      (solveCLM.isWeakSolution shiftedForm coercive _)).trans (map_smul _ _ _)
    exact ⟨Module.End.mem_eigenspace_iff.mpr ((eq_inv_smul_iff₀ ha).mpr huEq.symm), hu⟩
  · intro heigen
    have hRu : R u = a⁻¹ • u := Module.End.mem_eigenspace_iff.mp heigen.1
    have hscaledSolve : solveCLM shiftedForm coercive (a • massForm u) = u := by
      rw [map_smul]
      change a • R u = u
      rw [hRu, smul_inv_smul₀ ha]
    have huShifted := solveCLM.isWeakSolution shiftedForm coercive (a • massForm u)
    rw [hscaledSolve] at huShifted
    refine ⟨heigen.2, fun v ↦ ?_⟩
    have hv := huShifted v
    simp only [hshift u v, a, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] at hv
    linarith

omit [CompleteSpace V] in
/-- Coercivity of the shifted form excludes the singular spectral parameter
`gamma + lambda = 0`. This justifies the reciprocal substitution for every
eigenvalue; Evans assumes `λ > -γ`, (25), in the proof of §6.2.3, Theorem 5. -/
theorem add_ne_zero_of_isWeakEigenfunction
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    {u : V} (hu : IsWeakEigenfunction form massForm lambda u) :
    gamma + lambda ≠ 0 := by
  intro hzero
  rcases coercive with ⟨C, hC, hcoer⟩
  have hshiftZero : shiftedForm u u = 0 := by
    rw [hshift u u, hu.2 u]
    have : lambda + gamma = 0 := by linarith
    rw [← add_mul, this, zero_mul]
  have hbound := hcoer u
  rw [hshiftZero] at hbound
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu.1
  have hpositive : 0 < C * ‖u‖ * ‖u‖ := mul_pos (mul_pos hC hnorm) hnorm
  exact (not_le_of_gt hpositive) hbound

omit [CompleteSpace V] in
/-- For nonnegative mass, a coercive shift bounds every real weak eigenvalue
strictly above the negative shift. -/
theorem neg_shift_lt_of_isWeakEigenfunction
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hmass : ∀ u, 0 ≤ massForm u u)
    {u : V} (hu : IsWeakEigenfunction form massForm lambda u) :
    -gamma < lambda := by
  obtain ⟨C, hC, hcoer⟩ := coercive
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu.1
  have hpos : 0 < shiftedForm u u :=
    (mul_pos (mul_pos hC hnorm) hnorm).trans_le (hcoer u)
  rw [hshift u u, hu.2 u, ← add_mul] at hpos
  have hadd : 0 < lambda + gamma := pos_of_mul_pos_left hpos (hmass u)
  linarith

/-- The weak spectrum is countable. As in step 3 of Evans's proof of §6.2.3,
Theorem 5, `lambda` maps injectively to the nonzero eigenvalue
`(gamma + lambda)⁻¹` of a compact operator, and those eigenvalues are
countable, as in §D.5, Theorem 6(iii). -/
theorem weakSpectrum_countable
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    (weakSpectrum form massForm).Countable := by
  let R := spectralSolutionOperator shiftedForm massForm coercive
  let f : ℝ → ℝ := fun lambda ↦ (gamma + lambda)⁻¹
  have hRcompact : IsCompactOperator R :=
    isCompactOperator_spectralSolutionOperator shiftedForm massForm coercive hcompactMass
  have htarget :
      {μ : ℝ | μ ≠ 0 ∧ Module.End.HasEigenvalue (R : Module.End ℝ V) μ}.Countable :=
    PDE.Analysis.countable_nonzero_eigenvalues R hRcompact
  have hfinj : Injective f := inv_injective.comp (add_right_injective gamma)
  apply Set.Countable.mono _ (htarget.preimage hfinj)
  intro lambda hlambda
  obtain ⟨u, hu⟩ := hlambda
  have hgamma := add_ne_zero_of_isWeakEigenfunction
    form shiftedForm massForm coercive gamma lambda hshift hu
  have heigen :=
    (isWeakEigenfunction_iff_hasEigenvector_spectralSolutionOperator
      form shiftedForm massForm coercive gamma lambda hshift hgamma u).1 hu
  exact ⟨inv_ne_zero hgamma, Module.End.hasEigenvalue_of_hasEigenvector heigen⟩

/-- Distinct weak eigenvalues have no finite accumulation point. This is the
sequential form of `λ_k → +∞` in Evans's §6.2.3, Theorem 5(ii). The proof also
treats the apparent singular limit
`lambda → -gamma`: the corresponding compact eigenvalues would violate the
operator-norm bound before the reciprocal-limit argument is applied. -/
theorem weakSpectrum_has_no_finite_injective_limit
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm)
    (lambda : ℕ → ℝ) (hlambdaInj : Injective lambda)
    (hlambdaSpec : ∀ n, lambda n ∈ weakSpectrum form massForm)
    {eta : ℝ} (hlambda : Tendsto lambda atTop (nhds eta)) : False := by
  let R := spectralSolutionOperator shiftedForm massForm coercive
  have hRcompact : IsCompactOperator R :=
    isCompactOperator_spectralSolutionOperator shiftedForm massForm coercive hcompactMass
  choose u hu using hlambdaSpec
  have hgamma (n : ℕ) : gamma + lambda n ≠ 0 :=
    add_ne_zero_of_isWeakEigenfunction
      form shiftedForm massForm coercive gamma (lambda n) hshift (hu n)
  have heigen (n : ℕ) :
      Module.End.HasEigenvalue (R : Module.End ℝ V) (gamma + lambda n)⁻¹ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ((isWeakEigenfunction_iff_hasEigenvector_spectralSolutionOperator
        form shiftedForm massForm coercive gamma (lambda n) hshift (hgamma n) (u n)).1 (hu n))
  have haway (n : ℕ) : 1 ≤ |gamma + lambda n| * ‖R‖ := by
    have hbound : |(gamma + lambda n)⁻¹| ≤ ‖R‖ := by
      simpa only [Real.norm_eq_abs] using PDE.Analysis.norm_eigenvalue_le_norm R (heigen n)
    rwa [abs_inv, inv_le_iff_one_le_mul₀' (abs_pos.mpr (hgamma n))] at hbound
  have hadd : Tendsto (fun n ↦ gamma + lambda n) atTop (nhds (gamma + eta)) :=
    tendsto_const_nhds.add hlambda
  have hawayLimit : 1 ≤ |gamma + eta| * ‖R‖ :=
    ge_of_tendsto' (hadd.abs.mul tendsto_const_nhds) haway
  have hgammaEta : gamma + eta ≠ 0 := fun hzero ↦ by
    rw [hzero, abs_zero, zero_mul] at hawayLimit
    norm_num at hawayLimit
  exact inv_ne_zero hgammaEta (PDE.Analysis.distinct_eigenvalues_tendsto_zero R hRcompact
    (fun n ↦ (gamma + lambda n)⁻¹) (inv_injective.comp ((add_right_injective gamma).comp
      hlambdaInj)) (fun n ↦ inv_ne_zero (hgamma n)) heigen (hadd.inv₀ hgammaEta))

/-- Any strictly increasing enumeration of weak eigenvalues tends to
`+∞`. This is the ordered-sequence formulation of Evans's §6.2.3,
Theorem 5(ii): bounded monotone eigenvalues would converge to a finite
limit, contradicting `weakSpectrum_has_no_finite_injective_limit`. -/
theorem strictMono_weakEigenvalues_tendsto_atTop
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm)
    (lambda : ℕ → ℝ) (hlambdaMono : StrictMono lambda)
    (hlambdaSpec : ∀ n, lambda n ∈ weakSpectrum form massForm) :
    Tendsto lambda atTop atTop := by
  apply hlambdaMono.monotone.tendsto_atTop_atTop
  intro b
  by_contra hcofinal
  push Not at hcofinal
  have hbdd : BddAbove (lambda '' Set.Ici 0) := by
    refine ⟨b, ?_⟩
    rintro y ⟨n, _hn, rfl⟩
    exact (hcofinal n).le
  have hconv := Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici
    (f := lambda) (k := 0) (hlambdaMono.monotone.monotoneOn (Set.Ici 0)) hbdd
  exact weakSpectrum_has_no_finite_injective_limit
    form shiftedForm massForm coercive gamma hshift hcompactMass
    lambda hlambdaMono.injective hlambdaSpec hconv

/-- With nonnegative mass, only finitely many weak eigenvalues lie below any
real bound. Otherwise the lower bound from coercivity would give a convergent
subsequence of distinct eigenvalues in a compact interval. -/
theorem weakSpectrum_inter_Iic_finite
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm)
    (hmass : ∀ u, 0 ≤ massForm u u) (r : ℝ) :
    (weakSpectrum form massForm ∩ Iic r).Finite := by
  by_contra hinfinite
  let e := Set.Infinite.natEmbedding _ hinfinite
  let lambda : ℕ → ℝ := fun n ↦ e n
  have hmem (n : ℕ) : lambda n ∈ weakSpectrum form massForm := (e n).property.1
  have hinterval (n : ℕ) : lambda n ∈ Icc (-gamma) r := by
    obtain ⟨u, hu⟩ := hmem n
    exact ⟨(neg_shift_lt_of_isWeakEigenfunction
      form shiftedForm massForm coercive gamma (lambda n) hshift hmass hu).le,
      (e n).property.2⟩
  obtain ⟨eta, _, phi, hphi, hlimit⟩ := isCompact_Icc.tendsto_subseq hinterval
  exact weakSpectrum_has_no_finite_injective_limit
    form shiftedForm massForm coercive gamma hshift hcompactMass
    (lambda ∘ phi) ((Subtype.val_injective.comp e.injective).comp hphi.injective)
    (fun n ↦ hmem (phi n)) hlimit

/-- An infinite real weak spectrum with nonnegative compact mass and a coercive
shift has an exhaustive strictly increasing enumeration tending to infinity.
The enumeration lists each value once; the sequence in Evans's §6.2.3,
Theorem 5(ii), is nondecreasing. -/
theorem exists_strictMono_enumeration_weakSpectrum
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm)
    (hmass : ∀ u, 0 ≤ massForm u u)
    (hinfinite : (weakSpectrum form massForm).Infinite) :
    ∃ lambda : ℕ → ℝ, StrictMono lambda ∧
      range lambda = weakSpectrum form massForm ∧ Tendsto lambda atTop atTop := by
  let : Infinite (weakSpectrum form massForm) := hinfinite.to_subtype
  have hfinite (r : ℝ) :
      {x : weakSpectrum form massForm | (x : ℝ) ≤ r}.Finite := by
    exact Set.Finite.of_injOn (f := fun x : weakSpectrum form massForm ↦ (x : ℝ))
      (t := weakSpectrum form massForm ∩ Iic r)
      (fun x hx ↦ ⟨x.property, hx⟩) Subtype.val_injective.injOn
      (weakSpectrum_inter_Iic_finite
        form shiftedForm massForm coercive gamma hshift hcompactMass hmass r)
  obtain ⟨e, hmono, hlimit⟩ :=
    PDE.Analysis.Spectral.exists_equiv_nat_monotone_of_finite_sublevel
      (fun x : weakSpectrum form massForm ↦ (x : ℝ)) hfinite
  refine ⟨fun n ↦ (e n : ℝ),
    hmono.strictMono_of_injective (Subtype.val_injective.comp e.injective), ?_, hlimit⟩
  exact (e.surjective.range_comp Subtype.val).trans Subtype.range_coe_subtype

/-- The shifted Fredholm operator for spectral parameter `lambda` is
`(gamma + lambda)` times the single compact spectral solution operator. -/
theorem fredholmOperator_pencil_eq_smul_spectralSolutionOperator
    (shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ) :
    PDE.Analysis.fredholmOperator shiftedForm massForm coercive (gamma + lambda) =
      (gamma + lambda) • spectralSolutionOperator shiftedForm massForm coercive := by
  rfl

/-- Evans's §6.2.3, Theorem 4(i), applied to the pencil `L - λ`:
at every real parameter, either there is a nonzero homogeneous eigenfunction,
or every continuous forcing has a unique weak solution. -/
theorem pencilForm.fredholmAlternative
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    Xor
      (∃ u : V, IsWeakEigenfunction form massForm lambda u)
      (∀ ell : StrongDual ℝ V,
        ∃! u : V, IsWeakSolution (pencilForm form massForm lambda) ell u) := by
  have hpencilShift : ∀ u v,
      shiftedForm u v =
        pencilForm form massForm lambda u v + (gamma + lambda) * massForm u v := by
    intro u v
    rw [hshift u v, pencilForm_apply]
    ring
  rcases PDE.Analysis.fredholmAlternative_weak_solution_exactlyOne
      (pencilForm form massForm lambda) shiftedForm massForm coercive
      (gamma + lambda) hpencilShift hcompactMass with
    ⟨hhom, hnotUnique⟩ | ⟨hunique, hnoHom⟩
  · left
    obtain ⟨u, hu, hweak⟩ := hhom
    refine ⟨⟨u, (isWeakEigenfunction_iff_homogeneous_pencil
      form massForm lambda u).2 ⟨hu, hweak⟩⟩, hnotUnique⟩
  · right
    refine ⟨hunique, ?_⟩
    rintro ⟨u, hu⟩
    have hpencil :=
      (isWeakEigenfunction_iff_homogeneous_pencil
        form massForm lambda u).1 hu
    exact hnoHom ⟨u, hpencil.1, hpencil.2⟩

/-- Outside the weak spectrum, every forcing has a unique weak solution. -/
theorem pencilForm.unique_solution_of_notMem_weakSpectrum
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm)
    (hlambda : lambda ∉ weakSpectrum form massForm) :
    ∀ ell : StrongDual ℝ V,
      ∃! u : V, IsWeakSolution (pencilForm form massForm lambda) ell u := by
  rcases pencilForm.fredholmAlternative form shiftedForm massForm coercive
      gamma lambda hshift hcompactMass with
    ⟨hhom, _⟩ | ⟨hunique, _⟩
  · exact False.elim (hlambda hhom)
  · exact hunique

omit [CompleteSpace V] in
/-- If every forcing has a unique weak solution at `lambda`, then `lambda`
is not an eigenvalue. -/
theorem pencilForm.notMem_weakSpectrum_of_unique_solution
    (form massForm : V →L[ℝ] StrongDual ℝ V) (lambda : ℝ)
    (hunique : ∀ ell : StrongDual ℝ V,
      ∃! u : V, IsWeakSolution (pencilForm form massForm lambda) ell u) :
    lambda ∉ weakSpectrum form massForm := by
  intro hlambda
  obtain ⟨u, hu, hweak⟩ :=
    (mem_weakSpectrum_iff_nonzero_homogeneous_pencil
      form massForm lambda).1 hlambda
  obtain ⟨u0, hu0, huniq⟩ := hunique 0
  have hzero : IsWeakSolution (pencilForm form massForm lambda) 0 0 := by
    intro v
    simp
  have huEqZero := huniq 0 hzero
  have huEqU := huniq u hweak
  exact hu (huEqU.trans huEqZero.symm)

/-- Evans's §6.2.3, Theorem 5(i): every forcing has a unique weak solution exactly
off the weak spectrum. -/
theorem unique_pencil_solution_iff_notMem_weakSpectrum
    (form shiftedForm massForm : V →L[ℝ] StrongDual ℝ V)
    (coercive : IsCoercive shiftedForm) (gamma lambda : ℝ)
    (hshift : ∀ u v, shiftedForm u v = form u v + gamma * massForm u v)
    (hcompactMass : IsCompactOperator massForm) :
    (∀ ell : StrongDual ℝ V,
      ∃! u : V, IsWeakSolution (pencilForm form massForm lambda) ell u) ↔
      lambda ∉ weakSpectrum form massForm := by
  constructor
  · exact pencilForm.notMem_weakSpectrum_of_unique_solution form massForm lambda
  · exact pencilForm.unique_solution_of_notMem_weakSpectrum
      form shiftedForm massForm coercive gamma lambda hshift hcompactMass

/-- A symmetric form coercive after adding `gamma` times the pivot mass form has weak
eigenfunctions whose images form a Hilbert basis of the pivot space. Their eigenvalues
are greater than `-gamma`. Compactness and density concern the map into the pivot space;
no injectivity of that map or preselected eigenvectors are assumed. -/
theorem exists_hilbertBasis_weakEigenfunctions_of_coercive_shift
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (form : V →L[ℝ] StrongDual ℝ V) (gamma : ℝ) (j : V →L[ℝ] H)
    (coercive : IsCoercive (form + gamma • PDE.Analysis.innerPullbackOperator j))
    (hsymm : ∀ u v, form u v = form v u)
    (hcompact : IsCompactOperator j) (hdense : DenseRange j) :
    ∃ (ι : Type v) (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (u : ι → V),
      ∀ i, -gamma < lambda i ∧ j (u i) = b i ∧
        IsWeakEigenfunction form (PDE.Analysis.innerPullbackOperator j) (lambda i) (u i) := by
  have hsymmShift : ∀ u v,
      (form + gamma • PDE.Analysis.innerPullbackOperator j) u v =
        (form + gamma • PDE.Analysis.innerPullbackOperator j) v u := by
    intro u v
    simp only [add_apply, smul_apply, smul_eq_mul, PDE.Analysis.innerPullbackOperator_apply]
    rw [hsymm u v, real_inner_comm (j u) (j v)]
  obtain ⟨ι, b, μ, u, h⟩ :=
    PDE.Analysis.Variational.exists_hilbertBasis_weakEigenfunctions
      (form + gamma • PDE.Analysis.innerPullbackOperator j) coercive hsymmShift
      j hcompact hdense
  refine ⟨ι, b, fun i ↦ μ i - gamma, u, fun i ↦ ⟨?_, (h i).2.1, ?_, ?_⟩⟩
  · linarith [(h i).1]
  · intro hzero
    have := (h i).2.1
    rw [hzero, map_zero] at this
    exact b.orthonormal.ne_zero i this.symm
  · intro v
    have hweak := (h i).2.2 v
    simp only [add_apply, smul_apply, smul_eq_mul,
      PDE.Analysis.innerPullbackOperator_apply, (h i).2.1] at hweak ⊢
    rw [sub_mul]
    exact (eq_sub_iff_add_eq).2 hweak

end SobolevSpace.Weak

namespace SobolevSpace.GraphSpace

open Set Filter ENNReal
open PDE.Analysis.Variational

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Evans's §6.2.3, Theorem 5, for the full form with operator coefficients.
The exceptional set is at most countable and is exactly where unique solvability
for all `L²` loads fails. If infinite, it admits an exhaustive strictly increasing
enumeration tending to infinity. Boundedness supplies Rellich compactness, and
the Gårding estimate supplies a coercive shift. -/
theorem fullDivergenceForm.weakSpectrum_properties_of_bounded
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω)
    (A : Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))
    (b : Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))
    (c : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma) :
    let B := fullDivergenceForm (n := n) (Ω := Ω) A b c
    let M := massFormCLM (n := n) (Ω := Ω)
    let spectrum := Weak.weakSpectrum (V := H¹₀(Ω)) B M
    spectrum.Countable ∧
      (∀ lambda : ℝ,
        (∀ f : DerivLp n 2 Ω, ∃! u : H¹₀(Ω),
          IsWeakSolution (Weak.pencilForm (V := H¹₀(Ω)) B M lambda)
            (loadFunctional (n := n) (Ω := Ω) f) u) ↔
        lambda ∉ spectrum) ∧
      (spectrum.Infinite → ∃ lambda : ℕ → ℝ,
        StrictMono lambda ∧ range lambda = spectrum ∧ Tendsto lambda atTop atTop) := by
  intro B M spectrum
  let shift := coerciveShift (n := n) alpha beta gamma
  let shifted : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    shiftedDivergenceForm (n := n) (Ω := Ω) A b c shift
  have hcoer : IsCoercive shifted :=
    shiftedDivergenceForm_isCoercive (n := n) (Ω := Ω) A b c hA hbc
  have hshift (u v : H¹₀(Ω)) :
      shifted u v = B u v + shift * M u v := by
    simpa only [shifted, B, M, massFormCLM_apply] using
      shiftedDivergenceForm_apply (n := n) (Ω := Ω) A b c shift u v
  have hcompact : IsCompactOperator M :=
    isCompactOperator_massFormCLM_of_bounded (n := n) (Ω := Ω) hΩmeas hΩbounded
  have hmass (u : H¹₀(Ω)) : 0 ≤ M u u := by
    rw [massFormCLM_apply]
    exact real_inner_self_nonneg
  constructor
  · exact @Weak.weakSpectrum_countable (H¹₀(Ω))
      inferInstance inferInstance inferInstance B shifted M hcoer shift hshift hcompact
  constructor
  · intro lambda
    constructor
    · intro hsolv
      rintro ⟨u, hu⟩
      have hhom := (@Weak.isWeakEigenfunction_iff_homogeneous_pencil
        (H¹₀(Ω)) inferInstance inferInstance B M lambda u).mp hu
      have huniq := hsolv 0
      rw [loadFunctional_zero] at huniq
      exact hhom.1 (huniq.unique hhom.2 (IsWeakSolution.zero _))
    · intro hlambda f
      exact @Weak.pencilForm.unique_solution_of_notMem_weakSpectrum (H¹₀(Ω))
        inferInstance inferInstance inferInstance B shifted M hcoer shift lambda hshift
        hcompact hlambda (loadFunctional (n := n) (Ω := Ω) f)
  · exact @Weak.exists_strictMono_enumeration_weakSpectrum (H¹₀(Ω))
      inferInstance inferInstance inferInstance B shifted M hcoer shift hshift hcompact hmass

/-- Evans's §6.2.3, Theorem 5, on a bounded open set for `L∞` principal, first-order,
and zeroth-order coefficients with almost-everywhere uniform ellipticity.
The real exceptional spectrum is characterized by weak solvability for every
`L²` forcing. When infinite, its distinct values are enumerated in strictly
increasing order and tend to `+∞`. No symmetry or boundary regularity is assumed. -/
theorem fullDivergenceForm.weakSpectrum_properties_of_aeElliptic
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha) :
    let B := fullDivergenceForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
      (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
    let M := massFormCLM (n := n) (Ω := Ω)
    let spectrum := Weak.weakSpectrum (V := H¹₀(Ω)) B M
    spectrum.Countable ∧
      (∀ lambda : ℝ,
        (∀ f : DerivLp n 2 Ω, ∃! u : H¹₀(Ω),
          IsWeakSolution (Weak.pencilForm (V := H¹₀(Ω)) B M lambda)
            (loadFunctional (n := n) (Ω := Ω) f) u) ↔
        lambda ∉ spectrum) ∧
      (spectrum.Infinite → ∃ lambda : ℕ → ℝ,
        StrictMono lambda ∧ range lambda = spectrum ∧ Tendsto lambda atTop atTop) :=
  fullDivergenceForm.weakSpectrum_properties_of_bounded
    (n := n) (Ω := Ω) hΩopen.measurableSet hΩbounded
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
    (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
    (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
    (integratedElliptic_multiplication_of_ae (n := n) (Ω := Ω) a ha)
    (lowerOrderBounds_multiplication (n := n) (Ω := Ω) b c (norm_nonneg b) (norm_nonneg c)
      (norm_le_pi_norm b) le_rfl)

/-- Evans's §6.2.3, Theorem 6: away from the weak spectrum, the Dirichlet solution has
an `L²` bound uniform over all forcing data. The constant depends on the fixed
domain, coefficients and spectral parameter. Bounded measurable coefficients and
almost-everywhere uniform ellipticity suffice; no boundary regularity is required. -/
theorem fullDivergenceForm.exists_l2_bound_of_notMem_weakSpectrum
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha) :
    let B := fullDivergenceForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (multiplicationFirstOrderOperator (n := n) (Ω := Ω) b)
      (multiplicationZeroOrderOperator (n := n) (Ω := Ω) c)
    let M := massFormCLM (n := n) (Ω := Ω)
    ∀ lambda : ℝ, lambda ∉ Weak.weakSpectrum (V := H¹₀(Ω)) B M →
      ∃ C > 0, ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
        IsWeakSolution (Weak.pencilForm (V := H¹₀(Ω)) B M lambda)
          (loadFunctional (n := n) (Ω := Ω) f) u →
        ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≤ C * ‖f‖ := by
  intro B M lambda hlambda
  let A := multiplicationCoefficientOperator (n := n) (Ω := Ω) a
  let bOp := multiplicationFirstOrderOperator (n := n) (Ω := Ω) b
  let cOp := multiplicationZeroOrderOperator (n := n) (Ω := Ω) c
  let shift := coerciveShift (n := n) alpha ‖b‖ ‖c‖
  let shifted : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    shiftedDivergenceForm (n := n) (Ω := Ω) A bOp cOp shift
  have hcoer : IsCoercive shifted :=
    shiftedDivergenceForm_isCoercive (n := n) (Ω := Ω) A bOp cOp
      (integratedElliptic_multiplication_of_ae (n := n) (Ω := Ω) a ha)
      (lowerOrderBounds_multiplication (n := n) (Ω := Ω) b c
        (norm_nonneg b) (norm_nonneg c) (norm_le_pi_norm b) le_rfl)
  have hshift (u v : H¹₀(Ω)) :
      shifted u v = B u v + shift * M u v := by
    simpa only [shifted, B, A, bOp, cOp, M, massFormCLM_apply] using
      shiftedDivergenceForm_apply (n := n) (Ω := Ω) A bOp cOp shift u v
  have hcompact : IsCompactOperator M :=
    isCompactOperator_massFormCLM_of_bounded
      (n := n) (Ω := Ω) hΩopen.measurableSet hΩbounded
  let P := Weak.pencilForm (V := H¹₀(Ω)) B M lambda
  have hunique : ∀ ell : StrongDual ℝ (H¹₀(Ω)),
      ∃! u : H¹₀(Ω), IsWeakSolution P ell u :=
    @Weak.pencilForm.unique_solution_of_notMem_weakSpectrum (H¹₀(Ω))
      inferInstance inferInstance inferInstance B shifted M hcoer shift lambda hshift
      hcompact hlambda
  have hsurj : Function.Surjective P := fun ell ↦
    (hunique ell).exists.imp fun _ hu ↦ ContinuousLinearMap.ext hu
  obtain ⟨C, hC, hbound⟩ := P.exists_preimage_norm_le hsurj
  refine ⟨C, hC, fun f u hu ↦ ?_⟩
  obtain ⟨v, hv, hvnorm⟩ := hbound (loadFunctional (n := n) (Ω := Ω) f)
  have hvweak : IsWeakSolution P (loadFunctional (n := n) (Ω := Ω) f) v :=
    fun w ↦ congrArg (fun ell : StrongDual ℝ (H¹₀(Ω)) ↦ ell w) hv
  have huv : u = v := (hunique (loadFunctional (n := n) (Ω := Ω) f)).unique hu hvweak
  calc
    ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≤ ‖u‖ := baseCoordCLM_norm_le u
    _ = ‖v‖ := congrArg norm huv
    _ ≤ C * ‖loadFunctional (n := n) (Ω := Ω) f‖ := hvnorm
    _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_left (norm_loadFunctional_le f) hC.le

end SobolevSpace.GraphSpace
