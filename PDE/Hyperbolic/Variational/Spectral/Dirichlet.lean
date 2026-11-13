/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.Spectral.IntegratedEquations
public import PDE.Hyperbolic.WeakWave.IntegratedTrajectory
public import PDE.Hyperbolic.WeakWave.EvansCoefficientIntegrability
public import PDE.Elliptic.Variational.OrderedDirichletSpectrum
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# Spectral Dirichlet waves with continuous forcing

On a nonempty bounded open domain in positive dimension, autonomous, essentially
bounded, measurable, symmetric, uniformly elliptic coefficients give a strongly
continuous wave semigroup on `H₀¹ × L²`. The homogeneous semigroup conserves energy
and has uniformly bounded operator norms for nonnegative times.

For every globally continuous `L²`-valued force, its Duhamel trajectory satisfies
both integrated equations and determines a Bochner weak wave on `(0, b]`, for `b > 0`.
No boundary smoothness or spatial `H²` regularity is required. Energy conservation
is proved for the homogeneous semigroup.

Conversely, a weak wave with the same initial data and force agrees almost everywhere
with this Duhamel trajectory. Uniqueness follows from symmetry and coercivity of the autonomous
form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology InnerProductSpace Interval BigOperators ENNReal

namespace SobolevSpace.GraphSpace

open Hyperbolic.Variational

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- Time-independent, essentially bounded, measurable symmetric coefficients with
uniform ellipticity on a nonempty bounded open domain construct a strongly continuous
Dirichlet wave semigroup. The homogeneous semigroup conserves energy and has uniformly
bounded operator norms. Its orbits and the Duhamel curves for continuous forces
`f : ℝ → L²` satisfy both integrated weak equations. -/
theorem exists_dirichlet_waveSemigroup (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ S : PDE.Analysis.Evolution.StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ (t : NNReal) (x : H¹₀(Ω) × L2),
        autonomousWaveEnergy
          (variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)) (S t x) =
        autonomousWaveEnergy
          (variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)) x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      (∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
        (∫ s in (0 : ℝ)..t, (S s.toNNReal x).2) =
            baseCoordCLM (n := n) (Ω := Ω) (S t.toNNReal x).1 - baseCoordCLM (n := n) (Ω := Ω) x.1 ∧
          (∫ s in (0 : ℝ)..t,
              -(variableCoeffForm (n := n) (Ω := Ω)
                (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) (S s.toNNReal x).1)) =
            loadFunctionalCLM (n := n) (Ω := Ω) (S t.toNNReal x).2 -
              loadFunctionalCLM (n := n) (Ω := Ω) x.2) ∧
      ∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
        let u := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : H¹₀(Ω)), f r)) s
        (∫ s in (0 : ℝ)..t, (u s).2) =
            baseCoordCLM (n := n) (Ω := Ω) (u t).1 - baseCoordCLM (n := n) (Ω := Ω) x.1 ∧
          (∫ s in (0 : ℝ)..t,
              loadFunctionalCLM (n := n) (Ω := Ω) (f s) -
                variableCoeffForm (n := n) (Ω := Ω)
                  (multiplicationCoefficientOperator (n := n) (Ω := Ω) a) (u s).1) =
            loadFunctionalCLM (n := n) (Ω := Ω) (u t).2 -
              loadFunctionalCLM (n := n) (Ω := Ω) x.2 := by
  let A : Fin n → Fin n → L2 →L[ℝ] L2 := multiplicationCoefficientOperator (n := n) (Ω := Ω) a
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω) A
  let J : H¹₀(Ω) →L[ℝ] L2 := baseCoordCLM (n := n) (Ω := Ω)
  let K : L2 →L[ℝ] StrongDual ℝ H¹₀(Ω) := loadFunctionalCLM (n := n) (Ω := Ω)
  have hJ : Function.Injective J := baseCoordCLM_injective hΩopen
  have hK (p : L2) (w : H¹₀(Ω)) : K p w = ⟪p, J w⟫_ℝ := loadFunctional_apply p w
  have hA := integratedElliptic_multiplication_of_ae a ha
  have hAsymm := symmetricCoefficientOperator_multiplication_of_ae a hsymm
  have hBsymm (v w : H¹₀(Ω)) : B v w = B w v := variableCoeffForm_symm hAsymm v w
  obtain ⟨basis, lambda, e, _, _, heigen, _⟩ :=
    exists_ordered_hilbertBasis_variableCoeff_eigenfunctions hn hΩopen hΩbounded hΩne A hA hAsymm
  obtain ⟨c, hc, hcoercive⟩ := variableCoeffForm_isCoercive hn hΩbounded A hA
  have hcoercive' (v : H¹₀(Ω)) : c * ‖v‖ ^ 2 ≤ B v v := by
    simpa only [B, pow_two, mul_assoc] using hcoercive v
  have he (i : ℕ) : J (e i) = basis i := (heigen i).2.1
  have hweak (i : ℕ) (w : H¹₀(Ω)) : B (e i) w = lambda i * ⟪basis i, J w⟫_ℝ := by
    have h := (heigen i).2.2.2 w
    rwa [massFormCLM_apply, (heigen i).2.1] at h
  obtain ⟨S, henergy, hcoordinate, hbound⟩ :=
    exists_waveSemigroup_of_weakEigenbasis (V := H¹₀(Ω)) (H := L2) B hBsymm hc hcoercive' J hJ
      basis lambda (fun i ↦ (heigen i).1.le) e he hweak
  exact ⟨S, henergy, hbound, fun x t ht ↦ waveSemigroup_integral_equations (V := H¹₀(Ω))
      (H := L2) B hBsymm hc hcoercive' J hJ K hK basis lambda (fun i ↦ (heigen i).1.le) e he
      hweak S hcoordinate x ht,
    fun f hf x t ht ↦ forced_waveSemigroup_integral_equations (V := H¹₀(Ω)) (H := L2) B hBsymm
      J K hK basis lambda e he hweak (PDE.Analysis.Variational.hasSum_weakEigenfunction_expansion
        (V := H¹₀(Ω)) (H := L2) B hBsymm hc hcoercive' J hJ basis lambda
        (fun i ↦ (heigen i).1.le) e he hweak) S hcoordinate hf x ht⟩

end SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace

open Hyperbolic.Variational PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- The spectral Dirichlet wave semigroup produces Bochner weak solutions for every
force `f : ℝ → L²` continuous on the real line and every energy initial state. The
displacement and velocity classes are represented by the Duhamel trajectory; the
acceleration is its continuous `H⁻¹` residual. The coefficients are time-independent,
essentially bounded, measurable, symmetric, and uniformly elliptic. The same semigroup also retains
the integrated displacement equation for every continuous force, so its velocity is identified with
the time derivative of displacement in the pivot space. -/
theorem exists_forced_dirichlet_weakWave (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ S : StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ (t : NNReal) (x : H¹₀(Ω) × L2),
        autonomousWaveEnergy
            (variableCoeffForm (n := n) (Ω := Ω)
              (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)) (S t x) =
          autonomousWaveEnergy
            (variableCoeffForm (n := n) (Ω := Ω)
              (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)) x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      (∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (t : ℝ), 0 ≤ t →
        let u := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : H¹₀(Ω)), f r)) s
        (∫ s in (0 : ℝ)..t, (u s).2) =
          baseCoordCLM (n := n) (Ω := Ω) (u t).1 - baseCoordCLM (n := n) (Ω := Ω) x.1) ∧
      ∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (b : ℝ), 0 < b →
        let u := fun t ↦ S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) t
        let B := variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
        let T := h10L2GelfandTriple hΩopen
        ∃ (ellLp : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 b)))
          (qLp : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 b)))
          (pLp : Lp L2 2 (volume.restrict (Ioc 0 b)))
          (accLp : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 b))),
          (ellLp : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 b)]
            (fun t ↦ T.pivotToDual (f t)) ∧
          (qLp : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).1) ∧
          (pLp : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).2) ∧
          (accLp : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 b)]
            (fun t ↦ T.pivotToDual (f t) - B (u t).1) ∧
          IsGelfandWeakWaveSolution T (fun _ ↦ B) ellLp qLp pLp accLp x.1 x.2 := by
  obtain ⟨S, henergy, hbound, _, hforced⟩ :=
    exists_dirichlet_waveSemigroup hn hΩopen hΩbounded hΩne a ha hsymm
  refine ⟨S, henergy, hbound, fun f hf x t ht ↦ (hforced f hf x t ht).1, fun f hf x b hb ↦ ?_⟩
  let u := fun t ↦ S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) t
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  let T := h10L2GelfandTriple hΩopen
  have hK : T.pivotToDual = loadFunctionalCLM (n := n) (Ω := Ω) := by
    ext p w
    exact (loadFunctional_apply p w).symm
  exact exists_weakWave_of_continuous_integral_equations (V := H¹₀(Ω)) (H := L2) T B
    (T.pivotToDual.continuous.comp hf) (((S.continuous_orbit x).comp continuous_real_toNNReal).add
      (S.continuous_duhamel (continuous_const.prodMk hf))) x hb
    (fun t ht ↦ (hforced f hf x t ht.1).1) (fun t ht ↦ hK ▸ (hforced f hf x t ht.1).2)

end SobolevSpace.GraphSpace

namespace SobolevSpace.GraphSpace

open Hyperbolic.Variational PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- Every weak Dirichlet wave driven by a force `f : ℝ → L²` continuous on the
real line agrees almost everywhere with the constructed Duhamel trajectory. This gives a
displacement representative continuous in `H¹₀`, a velocity representative continuous in
`L²`, and an acceleration representative continuous in `H⁻¹`. Values assigned to an
arbitrary Bochner representative at individual times are immaterial.

The coefficients are autonomous, essentially bounded, symmetric, and uniformly
elliptic on a nonempty bounded open set. Symmetry and coercivity give uniqueness through
`IsGelfandWeakWaveSolution.eq_of_autonomous_symmetric_coercive`, our form of Evans, §7.2.2,
Theorem 4. -/
theorem exists_dirichlet_waveSemigroup_weak_identification (hn : 0 < n) (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (hΩne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    {alpha : ℝ} (ha : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ S : StronglyContinuousSemigroup (H¹₀(Ω) × L2),
      (∀ (t : NNReal) (x : H¹₀(Ω) × L2),
        autonomousWaveEnergy
            (variableCoeffForm (n := n) (Ω := Ω)
              (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)) (S t x) =
          autonomousWaveEnergy
            (variableCoeffForm (n := n) (Ω := Ω)
              (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)) x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t : NNReal, ‖S t‖ ≤ C) ∧
      ∀ (f : ℝ → L2), Continuous f → ∀ (x : H¹₀(Ω) × L2) (b : ℝ), 0 < b →
        let u : ℝ → H¹₀(Ω) × L2 := fun t ↦
          S t.toNNReal x + S.duhamel (fun s ↦ ((0 : H¹₀(Ω)), f s)) t
        let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
        let T : GelfandTriple (V := H¹₀(Ω)) (H := L2) := h10L2GelfandTriple hΩopen
        ∀ (ell : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 b)))
          (q : Lp H¹₀(Ω) 2 (volume.restrict (Ioc 0 b))) (p : Lp L2 2 (volume.restrict (Ioc 0 b)))
          (acc : Lp (StrongDual ℝ H¹₀(Ω)) 2 (volume.restrict (Ioc 0 b))),
          (ell : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 b)]
            (fun t ↦ T.pivotToDual (f t)) →
          IsGelfandWeakWaveSolution T (fun _ ↦ B) ell q p acc x.1 x.2 →
          (q : ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).1) ∧
          (p : ℝ → L2) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).2) ∧
          (acc : ℝ → StrongDual ℝ H¹₀(Ω)) =ᵐ[volume.restrict (Ioc 0 b)]
            (fun t ↦ T.pivotToDual (f t) - B (u t).1) := by
  obtain ⟨S, henergy, hbound, _, hforced⟩ :=
    exists_forced_dirichlet_weakWave hn hΩopen hΩbounded hΩne a ha hsymm
  refine ⟨S, henergy, hbound, fun f hf x b hb ↦ ?_⟩
  dsimp only
  intro ell q p acc hell hweak
  let A : Fin n → Fin n → L2 →L[ℝ] L2 := multiplicationCoefficientOperator (n := n) (Ω := Ω) a
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω) := variableCoeffForm (n := n) (Ω := Ω) A
  have hA := integratedElliptic_multiplication_of_ae a ha
  have hAsymm := symmetricCoefficientOperator_multiplication_of_ae a hsymm
  obtain ⟨c, hc, hcoercive⟩ := variableCoeffForm_isCoercive hn hΩbounded A hA
  have hcoercive' (v : H¹₀(Ω)) : c * ‖v‖ ^ 2 ≤ B v v := by
    simpa only [B, pow_two, mul_assoc] using hcoercive v
  obtain ⟨ell', q', p', acc', hell', hq', hp', hacc', hweak'⟩ := hforced f hf x b hb
  obtain rfl : ell' = ell := Lp.ext (hell'.trans hell.symm)
  obtain ⟨rfl, rfl, rfl⟩ := hweak.eq_of_autonomous_symmetric_coercive hweak'
    (fun v w ↦ variableCoeffForm_symm hAsymm v w) hc hcoercive'
  exact ⟨hq', hp', hacc'⟩

end SobolevSpace.GraphSpace
