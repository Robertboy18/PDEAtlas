/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.Variational.Energy
public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.ZeroBoundary
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import CAS.ExactTactic

/-!
# Dirichlet's principle in the classical affine boundary class

The boundary class `classicalDirichletClass Ω g` consists of the functions that are `C²` in `Ω`
with derivatives through order two uniformly continuous there, continuous on the closure, and
equal to `g` on the frontier. For a bounded open set with `C¹` graph boundary and forcing `f`
continuous in `Ω` with `f u` integrable, `poisson_iff_isMinOn_classicalEnergy` shows that a member
`u` of the class solves `-Δu = f` in `Ω` if and only if it minimizes the energy over the class,
without a `C²` extension of either the domain or the functions. This is Evans's §2.2.5(b),
Theorem 17 (Dirichlet's principle), with the energy read as a real number. The Bochner integral of
a nonintegrable density is zero, so the converse compares `u` only with competitors whose energy
density `½|∇v|² - f v` is integrable on `Ω`. For that converse, continuity of the forcing in the
open domain suffices.

## How it works

Evans integrates by parts once and bounds `Du · Dw` by the Cauchy inequality to get `I[u] ≤ I[w]`,
his (48); for the converse, he differentiates `τ ↦ I[u + τv]` at `τ = 0`. We integrate the first
variation by parts with LeanPDE's zero-boundary identity
`integral_sum_partialDeriv_mul_eq_neg_laplacian` (`integral_firstVariation_eq_residual`), which
needs zero boundary values but not compact support. In `classicalEnergy_le_of_poisson`, the exact
expansion `classicalEnergy_add_mul` at `t = 1`, whose quadratic term is nonnegative, takes the
place of the Cauchy inequality. The converse `poisson_of_isMinOn_finiteClassicalEnergy`
differentiates along `u + tφ` for smooth `φ` with compact support in `Ω` and concludes with
Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` and continuity of the residual.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.5(b), the energy functional and the admissible set,
  Theorem 17 (Dirichlet's principle) and its proof, (47)-(48), pp. 42-43.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PoissonEquation

open MeasureTheory Set SobolevSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {f u v : ℝ^n → ℝ}

/-- The classical affine boundary class: `C²` functions on `Ω` whose derivatives through
order two are uniformly continuous there, continuous on `closure Ω` and equal to `g` on
`frontier Ω`. -/
def classicalDirichletClass (Ω : Set (ℝ^n)) (g : ℝ^n → ℝ) : Set (ℝ^n → ℝ) :=
  {u | ContDiffUpToBoundary 2 u Ω ∧ ContinuousOn u (closure Ω) ∧
    EqOn u g (frontier Ω)}

/-- The members of the classical boundary class whose energy density `½|∇u|² - f u`
is integrable on `Ω`, so that `classicalEnergy Ω f u` is a genuine integral. -/
def finiteClassicalDirichletClass (Ω : Set (ℝ^n)) (f g : ℝ^n → ℝ) :
    Set (ℝ^n → ℝ) :=
  {u ∈ classicalDirichletClass Ω g |
    IntegrableOn
      (fun x ↦ (1 / 2 : ℝ) * (∑ i, ((∂[i] u) x) ^ 2) - f x * u x) Ω}

omit [Fact (0 < n)] in
/-- A function `C²` up to the boundary of a bounded open set has `Δu ∈ L²(Ω)`, so the
forcing of `-Δu = f` lies in `L²(Ω)`. -/
theorem memLp_two_of_poisson
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 2 u Ω) (hpde : ∀ x ∈ Ω, -laplacian u x = f x) :
    MemLp f 2 (volume.restrict Ω) := by
  have hl : MemLp (laplacian u) 2 (volume.restrict Ω) :=
    memLp_finsetSum Finset.univ fun i _ ↦
      hu.memLp_iteratedPartialDeriv hΩ hb 2 [i, i] (by simp)
  apply MemLp.ae_eq (hf_Lp := hl.neg)
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  exact hpde x hx

/-- The first variation pairs the Poisson residual with the variation.
The boundary condition is used only to remove the boundary term. -/
theorem integral_firstVariation_eq_residual
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u Ω) (hv : ContDiffUpToBoundary 1 v Ω)
    (hc : ContinuousOn v (closure Ω)) (hz : ∀ x ∈ frontier Ω, v x = 0)
    (hfv : IntegrableOn (fun x ↦ f x * v x) Ω) :
    (∫ x in Ω, (∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x) =
      ∫ x in Ω, (-laplacian u x - f x) * v x := by
  have hp : IntegrableOn
      (fun x ↦ ∑ i, (∂[i] u) x * (∂[i] v) x) Ω :=
    integrable_finsetSum _ fun i _ ↦
      (hu.memLp_iteratedPartialDeriv hΩ hb 2 [i] (by simp)).integrable_mul
        (hv.memLp_iteratedPartialDeriv hΩ hb 2 [i] (by simp))
  have hl : IntegrableOn (fun x ↦ laplacian u x * v x) Ω := by
    have hi (i : Fin n) : IntegrableOn
        (fun x ↦ (∂[i] (∂[i] u)) x * v x) Ω :=
      (hu.memLp_iteratedPartialDeriv hΩ hb 2 [i, i] (by simp)).integrable_mul
        (hv.memLp_iteratedPartialDeriv hΩ hb 2 [] (by simp))
    exact (integrable_finsetSum Finset.univ fun i _ ↦ hi i).congr
      (Filter.Eventually.of_forall fun x ↦ by simp only [laplacian, Finset.sum_mul])
  rw [integral_sub hp hfv,
    integral_sum_partialDeriv_mul_eq_neg_laplacian hΩ hb hg hu hv hc hz]
  symm
  calc
    _ = ∫ x in Ω, -(laplacian u x * v x) - f x * v x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = _ := by
      have hneg : IntegrableOn (fun x ↦ -(laplacian u x * v x)) Ω := hl.neg
      rw [integral_sub hneg hfv, integral_neg]

/-- A classical solution of `-Δu = f` has energy at most that of every classical
function with the same boundary values. The equation gives `f = -Δu ∈ L²(Ω)`, so
no integrability hypothesis on `f` is needed. -/
theorem classicalEnergy_le_of_poisson
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u Ω) (huc : ContinuousOn u (closure Ω))
    (hpde : ∀ x ∈ Ω, -laplacian u x = f x)
    (hv : ContDiffUpToBoundary 2 v Ω) (hvc : ContinuousOn v (closure Ω))
    (hbd : EqOn v u (frontier Ω)) :
    classicalEnergy Ω f u ≤ classicalEnergy Ω f v := by
  have hf := memLp_two_of_poisson hΩ hb hu hpde
  let w : ℝ^n → ℝ := fun x ↦ v x - u x
  have hw : ContDiffUpToBoundary 1 w Ω :=
    (hv.sub hu hΩ).of_le (by omega)
  have hwc : ContinuousOn w (closure Ω) := hvc.sub huc
  have hwz : ∀ x ∈ frontier Ω, w x = 0 := fun x hx ↦ sub_eq_zero.mpr (hbd hx)
  have hfu := hf.integrable_mul (hu.memLp_iteratedPartialDeriv hΩ hb 2 [] (by simp))
  have hfw := hf.integrable_mul (hw.memLp_iteratedPartialDeriv hΩ hb 2 [] (by simp))
  have hzero : (∫ x in Ω,
      (∑ i, (∂[i] u) x * (∂[i] w) x) - f x * w x) = 0 := by
    rw [integral_firstVariation_eq_residual hΩ hb hg hu hw hwc hwz hfw]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [hpde x hx, sub_self, zero_mul]
  have heq := classicalEnergy_add_mul hΩ hb (hu.of_le (by omega)) hw hfu hfw 1
  have hfunction : (fun x ↦ u x + 1 * w x) = v := by
    funext x
    simp [w]
  rw [hfunction, hzero] at heq
  have hn : 0 ≤ ∫ x in Ω, ∑ i, ((∂[i] w) x) ^ 2 :=
    integral_nonneg fun x ↦ Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  nlinarith

/-- A minimizer of the energy over the finite-energy boundary class solves `-Δu = f`
in `Ω`. Continuity of `f` in `Ω` suffices: for every smooth `φ` with compact support
in `Ω`, each variation `u + tφ` stays in the finite-energy class. -/
theorem poisson_of_isMinOn_finiteClassicalEnergy
    {g : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : u ∈ finiteClassicalDirichletClass Ω f g) (hf : ContinuousOn f Ω)
    (hmin : IsMinOn (classicalEnergy Ω f) (finiteClassicalDirichletClass Ω f g) u) :
    ∀ x ∈ Ω, -laplacian u x = f x := by
  have hub := hu.1.1
  have huc := hu.1.2.1
  have hfu := (integrable_classicalEnergy_iff hΩ hb (hub.of_le (by omega))).mp hu.2
  have hrc : ContinuousOn (fun x ↦ -laplacian u x - f x) Ω :=
    (continuousOn_finsetSum Finset.univ fun i _ ↦
      (hub.uniformContinuousOn [i, i] (by simp)).continuousOn).neg.sub hf
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (hrc.locallyIntegrableOn hΩ.measurableSet) ?_
  · exact fun x hx ↦ sub_eq_zero.mp (Measure.eqOn_open_of_ae_eq
      ((ae_restrict_iff' hΩ.measurableSet).mpr hae) hΩ hrc continuousOn_const hx)
  intro φ hφ hφc hφΩ
  have hφb : ContDiffUpToBoundary 2 φ Ω :=
    contDiffUpToBoundary_of_contDiffOn isOpen_univ
      (hφ.of_le (by simp)).contDiffOn hb.isCompact_closure (subset_univ _)
  have hφz (x : ℝ^n) (hx : x ∉ Ω) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφΩ h)
  have hφfront : ∀ x ∈ frontier Ω, φ x = 0 := fun x hx ↦
    hφz x (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ) hx)
  have hfp : IntegrableOn (fun x ↦ f x * φ x) Ω := by
    have hs : Function.support (fun x ↦ f x * φ x) ⊆ tsupport φ :=
      (Function.support_mul_subset_right _ _).trans (subset_tsupport φ)
    exact ((integrableOn_iff_integrable_of_support_subset hs).mp
      (((hf.mono hφΩ).mul hφ.continuous.continuousOn).integrableOn_compact hφc)).integrableOn
  have hd := hasDerivAt_classicalEnergy_add_mul hΩ hb (hub.of_le (by omega))
    (hφb.of_le (by omega)) hfu hfp
  have hlocal : IsLocalMin
      (fun t ↦ classicalEnergy Ω f (fun x ↦ u x + t * φ x)) 0 := .of_forall fun t ↦ by
    have hut := hub.add ((ContDiffUpToBoundary.const t).mul hφb hΩ hb) hΩ
    have hft : IntegrableOn (fun x ↦ f x * (u x + t * φ x)) Ω := by
      convert hfu.add (hfp.const_mul t) using 1
      funext x
      cas
    have hmem : (fun x ↦ u x + t * φ x) ∈ finiteClassicalDirichletClass Ω f g :=
      ⟨⟨hut, huc.add (continuousOn_const.mul hφ.continuous.continuousOn),
        fun x hx ↦ by simp [hφfront x hx, hu.1.2.2 hx]⟩,
        integrable_classicalEnergy hΩ hb (hut.of_le (by omega)) hft⟩
    simpa only [zero_mul, add_zero] using
      (show classicalEnergy Ω f u ≤ classicalEnergy Ω f (fun x ↦ u x + t * φ x) from
        hmin hmem)
  have hz := hlocal.hasDerivAt_eq_zero hd
  rw [integral_firstVariation_eq_residual hΩ hb hg hub
    (hφb.of_le (by omega)) hφ.continuous.continuousOn hφfront hfp] at hz
  rw [← hz, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by rw [hφz x hx, mul_zero])]
  simp only [smul_eq_mul, mul_comm]

/-- Dirichlet's principle for an integrable load `f u`: a member of the classical
boundary class solves `-Δu = f` in `Ω` if and only if it minimizes the energy over
that class. -/
theorem poisson_iff_isMinOn_classicalEnergy
    {g : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : u ∈ classicalDirichletClass Ω g)
    (hf : ContinuousOn f Ω) (hfu : IntegrableOn (fun x ↦ f x * u x) Ω) :
    (∀ x ∈ Ω, -laplacian u x = f x) ↔
      IsMinOn (classicalEnergy Ω f) (classicalDirichletClass Ω g) u := by
  constructor
  · intro hpde v hv
    exact classicalEnergy_le_of_poisson hΩ hb hg hu.1 hu.2.1 hpde hv.1 hv.2.1
      (fun x hx ↦ (hv.2.2 hx).trans (hu.2.2 hx).symm)
  · intro hmin
    exact poisson_of_isMinOn_finiteClassicalEnergy hΩ hb hg
      ⟨hu, integrable_classicalEnergy hΩ hb (hu.1.of_le (by omega)) hfu⟩ hf
      (fun _ hv ↦ hmin hv.1)

/-- For forcing continuous on the compact closure every member of the classical
boundary class has finite energy, and Dirichlet's principle needs no integrability
hypothesis. -/
theorem poisson_iff_isMinOn_classicalEnergy_of_continuousOn_closure
    {g : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hg : Boundary.HasC1GraphBoundary Ω)
    (hu : u ∈ classicalDirichletClass Ω g)
    (hf : ContinuousOn f (closure Ω)) :
    (∀ x ∈ Ω, -laplacian u x = f x) ↔
      IsMinOn (classicalEnergy Ω f) (classicalDirichletClass Ω g) u := by
  apply poisson_iff_isMinOn_classicalEnergy hΩ hb hg hu (hf.mono subset_closure)
  exact (hf.mul hu.2.1).integrableOn_of_subset_isCompact hb.isCompact_closure
    hΩ.measurableSet subset_closure hb.measure_lt_top.ne

end PoissonEquation
