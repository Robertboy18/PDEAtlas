/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.CoefficientLocalization
public import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.EnergyEstimate
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.ScalarEstimates
import PDE.Elliptic.Regularity.Localization.CutoffEquation.WeakEquation
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative
import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives

/-!
# Interior `H²` regularity: the compactness conclusion

Let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aᵢⱼ ∂ⱼ u) = f` with uniformly
elliptic coefficients having globally Lipschitz representatives and `f ∈ L²`.
The energy estimates of `DifferenceQuotientEnergy` bound `‖η Dₖʰ ∂ⱼ u‖_{L²}`
independently of `h`. Bounded sequences in `L²` have weakly convergent
subsequences, and the weak limit of `Dₖʰ v` as `h → 0` is the weak derivative
`∂ₖ v` wherever the cutoff is one. We carry out that passage,
assemble the second weak derivatives into an `H²` representative of `u` on
any region where `η = 1`, and finally remove the zero-trace assumption with
a second cutoff. The result is the conclusion `u ∈ H²_loc` of Evans's interior
regularity theorem (§6.3.1, Theorem 1) for equations without lower-order terms,
with locally Lipschitz coefficients in place of `C¹` ones.

## Main results

* `exists_local_secondDerivative_of_weighted_energy_bound_with_norm`:
  from a uniform weighted bound on `η Dₖʰ ∂ⱼ u` to all second weak
  derivatives `∂ₖ ∂ⱼ u` on `{η = 1}`, with the weak-compactness norm bound.
  This step does not use the equation.
* `exists_local_h2_with_bounds_of_weighted_energy_bounds`: the
  coordinatewise conclusions assembled into an `H²(V)` element.
* `exists_zeroTrace_local_h2_with_bounds_of_absorption`,
  `exists_zeroTrace_local_h2`: the full difference-quotient argument
  for `u ∈ H¹₀(Ω)`, with an explicit bound and in qualitative form.
* `exists_zeroTrace_local_h2_open_neighborhood_of_compact`,
  `exists_local_h2_open_neighborhood_of_compact`: every compact
  `K ⊆ Ω` has an open neighbourhood on which the solution has an `H²`
  representative, first for zero-trace solutions and then for arbitrary
  `H¹(Ω)` weak solutions by an outer cutoff.
* `exists_local_h2_of_locallyLipschitzOn`: the same interior conclusion with
  Lipschitz regularity and ellipticity assumed only on `Ω`. The global coefficient
  extension is constructed by a compact cutoff blend.

## Implementation notes

The quantitative statements keep the Young absorption parameter as an
explicit argument; the qualitative versions choose it internally. Second
derivatives are produced on `ℝ^n` for the zero extension and restricted to
the region `V` where the cutoff is one.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1 (interior `H²`-regularity) and step 6
  of its proof, which applies §5.8.2, Theorem 3(ii).
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity),
  pp. 177-218.
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Compactness conclusion of Evans's interior difference-quotient argument.
A uniform positive weighted bound for the cutoff-localized quotients of every
first derivative produces all coordinate weak second derivatives on any
region where the cutoff is one.

This theorem is independent of the elliptic equation: the estimates in
`Interior.DifferenceQuotientEnergy.EnergyEstimate` establish `henergy`. This result
performs the weak compactness and discrete-integration-by-parts passage to the limit. -/
theorem exists_local_secondDerivative_of_weighted_energy_bound_with_norm
    (k : Fin n) (h : ℕ → ℝ)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (d0u : Fin n → DerivLp n 2 Set.univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (V : Set (ℝ^n))
    (hηone : ∀ x ∈ V, η.toFun x = 1)
    {weight bound : ℝ} (hweight : 0 < weight)
    (henergy : ∀ m,
      weight * ∑ j : Fin n,
        ‖testFunctionLpTop (n := n) (Ω := Set.univ) η •
          differenceQuotientLp 2 k (h m) (d0u j)‖ ^ 2 ≤ bound) :
    ∀ i : Fin n, ∃ g : DerivLp n 2 Set.univ,
      ‖g‖ ≤ Real.sqrt (bound / weight) ∧
      HasWeakDerivativeOn (n := n) V [k]
        (d0u i : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  exact fun i ↦ exists_L2_weakDerivativeOn_of_bounded_localizedDifferenceQuotients_with_norm
    k h hzero hne (d0u i) (testFunctionLpTop (n := n) (Ω := Set.univ) η) V
    (Real.sqrt (bound / weight))
    (fun m ↦ norm_component_le_sqrt_of_weighted_energy (fun j : Fin n ↦
      testFunctionLpTop (n := n) (Ω := Set.univ) η • differenceQuotientLp 2 k (h m) (d0u j)) i
        hweight (henergy m))
    fun φ hφV ↦ testFunctionLpTop_smul_testFunctionL2_eq_of_eq_one η φ V hηone hφV

/-- Qualitative corollary of the quantitative local second-derivative
estimate. -/
theorem exists_local_secondDerivative_of_weighted_energy_bound
    (k : Fin n) (h : ℕ → ℝ)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0))
    (hne : ∀ m, h m ≠ 0)
    (d0u : Fin n → DerivLp n 2 Set.univ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (V : Set (ℝ^n))
    (hηone : ∀ x ∈ V, η.toFun x = 1)
    {weight bound : ℝ} (hweight : 0 < weight)
    (henergy : ∀ m,
      weight * ∑ j : Fin n,
        ‖testFunctionLpTop (n := n) (Ω := Set.univ) η •
          differenceQuotientLp 2 k (h m) (d0u j)‖ ^ 2 ≤ bound) :
    ∀ i : Fin n, ∃ g : DerivLp n 2 Set.univ,
      HasWeakDerivativeOn (n := n) V [k]
        (d0u i : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  intro i
  obtain ⟨g, _hgNorm, hg⟩ :=
    exists_local_secondDerivative_of_weighted_energy_bound_with_norm
      k h hzero hne d0u η V hηone hweight henergy i
  exact ⟨g, hg⟩

/-- Quantitatively assemble the localized compactness conclusions in every
coordinate into an `H²(V)` representative.  Each second-derivative
coordinate retains the weak-compactness norm bound from its corresponding
difference-quotient direction. -/
theorem exists_local_h2_with_bounds_of_weighted_energy_bounds
    (U : H¹((Set.univ : Set (ℝ^n))))
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (V : Set (ℝ^n)) (hVmeas : MeasurableSet V)
    (hηone : ∀ x ∈ V, η.toFun x = 1)
    (h : Fin n → ℕ → ℝ)
    (hzero : ∀ k, Filter.Tendsto (h k) Filter.atTop (nhds 0))
    (hne : ∀ k m, h k m ≠ 0)
    (weight bound : Fin n → ℝ)
    (hweight : ∀ k, 0 < weight k)
    (henergy : ∀ k m,
      weight k * ∑ i : Fin n,
        ‖testFunctionLpTop (n := n) (Ω := Set.univ) η •
          differenceQuotientLp 2 k (h k m)
            ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))‖ ^ 2
        ≤ bound k) :
    ∃ W : W^{2,2}(V),
      baseRepresentative W =ᵐ[domainMeasure n V]
        (fun x ↦
          ⇑((U : WkpAmbientOn n 1 2 Set.univ)
            (baseIndex n 1) : DerivLp n 2 Set.univ) x) ∧
      (∀ i,
        ⇑((W : WkpAmbientOn n 2 2 V)
            (firstDerivIndex n 2 (by norm_num) i) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑((U : WkpAmbientOn n 1 2 Set.univ)
              (singleDerivIndex n i) : DerivLp n 2 Set.univ)) ∧
      ∀ a : DerivIndex n 2, ∀ i k : Fin n, a.toList = [i, k] →
        ‖((W : WkpAmbientOn n 2 2 V) a :
            DerivLp n 2 V)‖ ≤ Real.sqrt (bound k / weight k) := by
  choose g hgNorm hg using fun k i ↦
    exists_local_secondDerivative_of_weighted_energy_bound_with_norm k (h k) (hzero k) (hne k)
      (fun i ↦ (U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)) η V hηone (hweight k)
      (henergy k) i
  let UV : H¹(V) := restrictCLM (n := n) (k := 1) (p := 2) hVmeas (subset_univ V) U
  have hUV := restrictCLM_apply_ae (n := n) (k := 1) (p := 2) hVmeas (subset_univ V) U
  obtain ⟨W, hWbase, hWfirst, hWsecond, -⟩ := exists_H2_of_firstDerivatives_haveWeakDerivatives UV
    (fun i k ↦ (restrictDerivLp (n := n) (p := 2) (subset_univ V) (g k i) : ℝ^n → ℝ))
    (fun i k ↦ Lp.memLp _) fun i k ↦ (hg k i).congr_ae (hUV (singleDerivIndex n i)).symm
      (restrictDerivLp_apply_ae (subset_univ V) (g k i)).symm
  refine ⟨W, hWbase.trans (hUV (baseIndex n 1)), fun i ↦ (hWfirst i).trans (hUV _),
    fun a i k ha ↦ ?_⟩
  rw [Lp.ext (hWsecond a i k ha)]
  exact (norm_restrictDerivLp_le (subset_univ V) (g k i)).trans (hgNorm k i)

/-- Qualitative form of the localized `H²` assembly theorem. -/
theorem exists_local_h2_of_weighted_energy_bounds
    (U : H¹((Set.univ : Set (ℝ^n))))
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (V : Set (ℝ^n)) (hVmeas : MeasurableSet V)
    (hηone : ∀ x ∈ V, η.toFun x = 1)
    (h : Fin n → ℕ → ℝ)
    (hzero : ∀ k, Filter.Tendsto (h k) Filter.atTop (nhds 0))
    (hne : ∀ k m, h k m ≠ 0)
    (weight bound : Fin n → ℝ)
    (hweight : ∀ k, 0 < weight k)
    (henergy : ∀ k m,
      weight k * ∑ i : Fin n,
        ‖testFunctionLpTop (n := n) (Ω := Set.univ) η •
          differenceQuotientLp 2 k (h k m)
            ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))‖ ^ 2
        ≤ bound k) :
    ∃ W : W^{2,2}(V),
      ((((W : WkpAmbientOn n 2 2 V) (baseIndex n 2) : DerivLp n 2 V) :
          ℝ^n → ℝ) =ᵐ[domainMeasure n V]
        (((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)) ∧
      ∀ i,
        ((((W : WkpAmbientOn n 2 2 V)
            (firstDerivIndex n 2 (by norm_num) i) :
              DerivLp n 2 V) : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
          (((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)) := by
  obtain ⟨W, hW, hfirst, _⟩ :=
    exists_local_h2_with_bounds_of_weighted_energy_bounds
      U η V hVmeas hηone h hzero hne weight bound hweight henergy
  exact ⟨W, hW, hfirst⟩

/-- Zero-trace specialization of Evans §6.3.1, with a prescribed cutoff.

Let `u ∈ H¹₀(Ω)` solve the uniformly elliptic divergence-form equation with
globally Lipschitz coefficients and `L²` forcing.  On every measurable region
`V` where a compactly supported smooth cutoff `η` equals one, the zero
extension of `u` has an `H²(V)` representative.  Every coordinate second
derivative satisfies the explicit localized difference-quotient estimate
produced by the coercivity argument.

The proof contains the complete difference-quotient argument: a uniform
support collar, explicit nonzero steps tending to zero, the coercive energy
estimate with all lower-order terms independent of the step, weak
compactness, discrete integration by parts, and assembly of the second weak
derivatives. This quantitative zero-trace theorem is the analytic core used
by both the global Dirichlet pipeline and the general local `H¹` theorem
below. -/
theorem exists_zeroTrace_local_h2_with_bounds_of_absorption
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (V : Set (ℝ^n)) (hVmeas : MeasurableSet V)
    (hηone : ∀ x ∈ V, η.toFun x = 1)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (habsorb : gamma *
      ‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖ ^ 2 < alpha) :
    ∃ W : W^{2,2}(V),
      baseRepresentative W =ᵐ[domainMeasure n V]
        baseRepresentative (ZeroTrace.zeroExtendH10 hΩopen.measurableSet u) ∧
      (∀ i,
        ⇑((W : WkpAmbientOn n 2 2 V)
            (firstDerivIndex n 2 (by norm_num) i) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑(zeroExtendedGradient hΩopen.measurableSet u i)) ∧
      ∀ a : DerivIndex n 2, ∀ i k : Fin n, a.toList = [i, k] →
        ‖((W : WkpAmbientOn n 2 2 V) a : DerivLp n 2 V)‖ ≤
          Real.sqrt (localizedDifferenceBound A C η
            (zeroExtendedGradient hΩopen.measurableSet u) ‖f‖ alpha gamma ‖u‖ /
            localizedDifferenceWeight η alpha gamma) := by
  dsimp only [zeroExtendedGradient, localizedDifferenceWeight]
  choose ρ hρ hcollar using fun k : Fin n ↦ exists_uniform_shiftedSupport_collar hΩopen η hηΩ k
  have hfixed (k : Fin n) (m : ℕ) := localizedDifference_uniform_fixed_energy_le hΩopen A a C ha
    hrep halpha hA f u hu η hηΩ k (collarStep_ne_zero (hρ k) m) (hρ k)
    (hcollar k _ (by simpa using abs_collarStep_le (hρ k) m)) hgamma habsorb
  exact exists_local_h2_with_bounds_of_weighted_energy_bounds _ η V hVmeas hηone
    (fun k ↦ collarStep (ρ k)) (fun k ↦ tendsto_collarStep_zero (ρ k))
    (fun k m ↦ collarStep_ne_zero (hρ k) m) _ _ (fun k ↦ (hfixed k 0).1) fun k m ↦ (hfixed k m).2

/-- Zero-trace specialization of Evans §6.3.1, interior `H²` regularity.

A weak `H¹₀(Ω)` solution of a uniformly elliptic divergence-form equation
with globally Lipschitz coefficients and `L²` forcing belongs to `H²` on
every region cut out by an interior smooth cutoff.  The absorption parameter
used in Young's inequality is chosen internally. The general local theorem
below removes the zero-trace assumption by an outer cutoff. -/
theorem exists_zeroTrace_local_h2
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (V : Set (ℝ^n)) (hVmeas : MeasurableSet V)
    (hηone : ∀ x ∈ V, η.toFun x = 1) :
    ∃ W : W^{2,2}(V),
      baseRepresentative W =ᵐ[domainMeasure n V]
        baseRepresentative (ZeroTrace.zeroExtendH10 hΩopen.measurableSet u) ∧
      ∀ i,
        ⇑((W : WkpAmbientOn n 2 2 V)
            (firstDerivIndex n 2 (by norm_num) i) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V] ⇑(zeroExtendedGradient hΩopen.measurableSet u i) := by
  obtain ⟨gamma, hgamma, habsorb⟩ := exists_positive_absorption_parameter halpha
    ‖testFunctionLpTop (n := n) (Ω := Set.univ) η‖
  obtain ⟨W, hW, hfirst, -⟩ := exists_zeroTrace_local_h2_with_bounds_of_absorption hΩopen A a C ha
    hrep halpha hA f u hu η hηΩ V hVmeas hηone hgamma habsorb
  exact ⟨W, hW, hfirst⟩

/-- A cutoff that equals one near the compact set `K ⊆ U` equals one on an open neighborhood
`V ⊆ U` of `K`. -/
private theorem exists_cutoff_eq_one_on_open_nhds {U K : Set (ℝ^n)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport η.toFun ⊆ U ∧
      ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ ∀ x ∈ V, η.toFun x = 1 := by
  obtain ⟨η, hηU, -, hηnhds, -⟩ := TestFunction.exists_eq_one_on_compact hU hK hKU
  have hone (x : ℝ^n) (hx : x ∈ interior {y | η.toFun y = 1}) : η.toFun x = 1 :=
    interior_subset (s := {y | η.toFun y = 1}) hx
  exact ⟨η, hηU, interior {y | η.toFun y = 1}, isOpen_interior,
    fun x hx ↦ mem_interior_iff_mem_nhds.2 (hηnhds x hx), fun x hx ↦ hηU (subset_tsupport _
      (Function.mem_support.2 (by rw [hone x hx]; exact one_ne_zero))), hone⟩

/-- Zero-trace compact-set specialization of Evans §6.3.1.  Every compact
subset of the domain is contained in an open set on which the `H¹₀(Ω)` weak
solution has an `H²` representative.  Both the cutoff and the open
neighborhood are constructed inside the proof. This specialization remains
useful in the global Dirichlet assembly; the following theorem treats
arbitrary local `H¹(Ω)` weak solutions. -/
theorem exists_zeroTrace_local_h2_open_neighborhood_of_compact
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := Ω)
        (multiplicationCoefficientOperator (n := n) (Ω := Ω)
          (fun i j ↦ restrictDerivLp
            (n := n) (p := ∞) (subset_univ Ω) (A i j))))
      (loadFunctional (n := n) (Ω := Ω) f) u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKΩ : K ⊆ Ω) :
    let U : H¹((Set.univ : Set (ℝ^n))) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet u
    ∃ V : Set (ℝ^n), ∃ _hVopen : IsOpen V,
      K ⊆ V ∧ V ⊆ Ω ∧ ∃ W : W^{2,2}(V),
        ((((W : WkpAmbientOn n 2 2 V) (baseIndex n 2) : DerivLp n 2 V) :
            ℝ^n → ℝ) =ᵐ[domainMeasure n V]
          (((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)) ∧
        ∀ i,
          ((((W : WkpAmbientOn n 2 2 V)
              (firstDerivIndex n 2 (by norm_num) i) :
                DerivLp n 2 V) : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
            (((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i) :
              DerivLp n 2 Set.univ) : ℝ^n → ℝ)) := by
  obtain ⟨η, hηΩ, V, hVopen, hKV, hVΩ, hηone⟩ :=
    exists_cutoff_eq_one_on_open_nhds hΩopen hKcompact hKΩ
  obtain ⟨W, hWbase, hWfirst⟩ := exists_zeroTrace_local_h2 hΩopen A a C ha hrep halpha hA f u hu
    η hηΩ V hVopen.measurableSet hηone
  exact ⟨V, hVopen, hKV, hVΩ, W, hWbase, hWfirst⟩

/-- Evans §6.3.1, interior `H²` regularity for general weak solutions.

Let `u ∈ H¹(Ω)` solve a uniformly elliptic divergence-form equation weakly,
without any boundary condition. Every compact subset `K ⊆ Ω` has an open
neighborhood `V ⊆ Ω` on which `u` has an `H²(V)` representative.

The proof uses two nested cutoffs. The outer cutoff turns `u` into an
`H¹₀(Ω)` solution with an `L²` commutator forcing. The inner cutoff lies
where the outer cutoff equals one, so the zero-trace
difference-quotient theorem produces an `H²` representative of the original
field near `K`. -/
theorem exists_local_h2_open_neighborhood_of_compact
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[MeasureTheory.volume] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hA : AEUniformlyElliptic (n := n) (Ω := Set.univ) A alpha)
    (f : DerivLp n 2 Ω)
    (u : H¹(Ω))
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦ restrictDerivLp
        (n := n) (p := ∞) (subset_univ Ω) (A i j)) f u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ W : W^{2,2}(V),
        ⇑((W : WkpAmbientOn n 2 2 V)
            (baseIndex n 2) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑((u : WkpAmbientOn n 1 2 Ω)
              (baseIndex n 1) : DerivLp n 2 Ω) := by
  let Alocal : Fin n → Fin n → DerivLp n ∞ Ω := fun i j ↦
    restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A i j)
  have hAlocalRep (i j : Fin n) : (Alocal i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j :=
    (restrictDerivLp_apply_ae (subset_univ Ω) (A i j)).trans (ae_restrict_of_ae (hrep i j))
  let A1 : Fin n → Fin n → W^{1,∞}(Ω) := fun i j ↦ w1TopOfLipschitzRepresentative
    hΩopen.measurableSet (Alocal i j) (a i j) (C i j) (ha i j) (hAlocalRep i j)
  have hcoeff : (fun i j ↦ ((A1 i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) : DerivLp n ∞ Ω)) =
      Alocal := funext₂ fun i j ↦ Lp.ext (w1TopOfLipschitzRepresentative_base_ae
        hΩopen.measurableSet (Alocal i j) (a i j) (C i j) (ha i j) (hAlocalRep i j))
  obtain ⟨ρ, hρΩ, N, hNopen, hKN, hNΩ, hρone⟩ :=
    exists_cutoff_eq_one_on_open_nhds hΩopen hKcompact hKΩ
  obtain ⟨w, hwbase, g, -, -, hgw⟩ := exists_localized_interiorWeakDivergenceSolution A1 u
    f (by simpa only [hcoeff] using hu) ρ hρΩ
  obtain ⟨η, hηN, V, hVopen, hKV, hVN, hηone⟩ :=
    exists_cutoff_eq_one_on_open_nhds hNopen hKcompact hKN
  have hVΩ : V ⊆ Ω := hVN.trans hNΩ
  obtain ⟨W, hWbase, -⟩ := exists_zeroTrace_local_h2 hΩopen A a C ha hrep halpha hA g w
    ((isWeakSolution_iff_isWeakDivergenceSolution hΩopen Alocal g w).2
      (by simpa only [hcoeff] using hgw)) η (hηN.trans hNΩ) V hVopen.measurableSet hηone
  refine ⟨V, hVopen, hKV, hVΩ, W, hWbase.trans ?_⟩
  filter_upwards [ae_restrict_of_ae (ZeroTrace.zeroExtendH10_coordinate_apply_ae
    hΩopen.measurableSet w (baseIndex n 1)), hwbase.filter_mono (ae_mono (domainMeasure_le hVΩ)),
    ae_restrict_mem hVopen.measurableSet] with x hzero hw hxV
  change _ = ρ.toFun x * _ at hw
  rw [baseRepresentative, hzero, Set.indicator_of_mem (hVΩ hxV)]
  rw [hρone x (hVN hxV), one_mul] at hw
  simpa only [wkpBaseCoordinateCLM_apply, baseCoordCLM_apply] using hw

/-- Interior `H²` regularity for coefficients that are only locally Lipschitz on the domain.

The global bounded Lipschitz elliptic matrix used by the difference-quotient estimates is
constructed near `K`; no extension is assumed. -/
theorem exists_local_h2_of_locallyLipschitzOn
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, LocallyLipschitzOn Ω (a i j))
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    (f : DerivLp n 2 Ω) (u : H¹(Ω))
    (hu : IsInteriorWeakDivergenceSolution A f u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      ∃ W : W^{2,2}(V),
        ⇑((W : WkpAmbientOn n 2 2 V) (baseIndex n 2) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : DerivLp n 2 Ω) := by
  have hlocal : ∀ᵐ x ∂domainMeasure n Ω,
      BoundaryRegularity.MatrixEllipticLowerBound (fun i j ↦ a i j x) alpha := by
    filter_upwards [hA.2, ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hrep i)] with x hx hax ξ
    simpa only [dotProduct, BoundaryRegularity.principalEnergy, mul_right_comm, hax] using hx ξ
  obtain ⟨N, hNopen, hKN, hNΩ, B, b, C, hb, hBrep, hB, hba⟩ :=
    BoundaryRegularity.exists_global_elliptic_extension_of_compact
      hΩopen a ha hA.1 hlocal K hKcompact hKΩ
  have hcoeff (i j : Fin n) : restrictDerivLp (n := n) (p := ∞) hNΩ (A i j) =
      restrictDerivLp (n := n) (p := ∞) (subset_univ N) (B i j) := by
    apply Lp.ext
    filter_upwards [restrictDerivLp_apply_ae hNΩ (A i j),
      restrictDerivLp_apply_ae (subset_univ N) (B i j), ae_mono (domainMeasure_le hNΩ) (hrep i j),
      ae_restrict_of_ae (s := N) (hBrep i j), ae_restrict_mem hNopen.measurableSet]
      with x hxA hxB hxa hxb hxN
    exact hxA.trans (hxa.trans ((hba i j hxN).symm.trans (hxb.symm.trans hxB.symm)))
  obtain ⟨V, hVopen, hKV, hVN, W, hW⟩ :=
    exists_local_h2_open_neighborhood_of_compact hNopen B b C hb hBrep hB.1 hB
      (restrictDerivLp (n := n) (p := 2) hNΩ f) (restrictCLM hNopen.measurableSet hNΩ u)
      (by simpa only [hcoeff] using hu.restrict hNopen hNΩ) K hKcompact hKN
  exact ⟨V, hVopen, hKV, hVN.trans hNΩ, W, hW.trans ((ae_mono (domainMeasure_le hVN))
    (restrictCLM_apply_ae (n := n) (k := 1) (p := 2) hNopen.measurableSet hNΩ u (baseIndex n 1)))⟩

end SobolevSpace.GraphSpace
