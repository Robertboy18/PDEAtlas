/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Variational.DivergenceForm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
import PDE.Analysis.MeasureTheory.LocalRepresentative
import PDE.Elliptic.Regularity.Global.HigherOrder
import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding

/-!
# Smooth elliptic regularity up to the boundary

For the homogeneous Dirichlet problem `-∂ᵢ(aᵢⱼ ∂ⱼu) = f` in `Ω`, `u = 0` on `∂Ω`, with smooth
boundary charts, smooth uniformly elliptic coefficients and forcing in every `W^{k,2}`, the weak
solution has one representative that is `C∞` on `closure Ω` and agrees almost everywhere with it
(`exists_smoothRepresentativeOnClosure_of_isWeakDivergenceSolution`). This is Evans's §6.3.2,
Theorem 6 (Infinite differentiability up to the boundary), for an operator without lower-order
terms.

## Main definitions

* `AllOrderPrincipalData`: coefficient and forcing Sobolev bundles at every order that represent
  fixed functions.
* `weakSolutionBase`: the chosen order-zero representative of the weak solution.

## Main results

* `exists_allOrderSobolevRepresentatives_of_isWeakDivergenceSolution`: `W^{k,2}` representatives of
  the same weak solution at every order.
* `exists_interior_smoothRepresentative_of_isWeakDivergenceSolution`: a representative that is `C∞`
  on `Ω`.
* `exists_smoothRepresentativeOnClosure_of_isWeakDivergenceSolution`: a representative that is `C∞`
  on `closure Ω`.

## How it works

Evans obtains `u ∈ H^m(U)` for every `m` from Theorem 5, and then `u ∈ C^k(Ū)` for every `k` from
the general Sobolev inequalities of §5.6.3, Theorem 6. We follow the same route, with
`exists_global_higherOrder_of_isWeakDivergenceSolution` at each finite order. Two coherence issues
arise before those representatives determine a single smooth function. The coefficient and forcing
bundles at different orders must represent the same functions, which `AllOrderPrincipalData`
records, and the continuous representatives obtained at different orders must agree pointwise.
Continuous functions that agree almost everywhere agree on the open domain and therefore on its
closure, so one representative has every finite `ContDiffOn` order, without a boundary
reconstruction hypothesis.

## Implementation notes

The operational Sobolev iteration raises each finite-order bundle to the supercritical space
`W^{m+1,2n}`, through `W^{m+n+1,2}(Ω) → W^{m+1,2n}(Ω)`; the surplus `n + 1` is not optimal.
Higher-order Morrey embedding gives continuous representatives of the weak derivatives, and interior
weak-to-classical reconstruction identifies adjacent representatives as Fréchet derivatives on `Ω`.
At the boundary, the operational charts flatten `closure Ω` to a closed upper half-space, and
Mathlib's derivative-extension theorem on a convex half-ball identifies the same continuous
derivative field as the derivative within `closure Ω`. Induction then gives a `C^m` representative
on the closure, which proves the completed-space Sobolev embedding
`W^{m+n+1,2}(Ω) → C^m(closure Ω)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6 (General Sobolev inequalities),
  pp. 284-286; §6.3.2, Theorem 5 (Higher boundary regularity), pp. 340-343, and Theorem 6 (Infinite
  differentiability up to the boundary) and its proof, p. 343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

/-- The supercritical exponent `2n` used for Morrey reconstruction satisfies `1 ≤ 2n` in every
positive dimension. -/
local instance doubleDimensionNNRealExponentFact [Fact (0 < n)] :
    Fact (1 ≤ (((2 * n : ℕ) : NNReal) : ℝ≥0∞)) :=
  ⟨by
    have hn : 0 < n := Fact.out
    exact_mod_cast (by omega : 1 ≤ 2 * n)⟩

/-- The exponent `2n` written as `ENNReal.ofReal` of a real number, matching the form produced
by the Sobolev embedding iteration. -/
local instance doubleDimensionOfRealExponentFact [Fact (0 < n)] :
    Fact (1 ≤ ENNReal.ofReal ((2 * n : ℕ) : ℝ)) := by
  simpa only [ENNReal.ofReal_natCast, ENNReal.coe_natCast] using
    doubleDimensionNNRealExponentFact (n := n)

private def castWkpSpaceOnExponent
    {k : ℕ} {p q : ℝ≥0∞} {Omega : Set (ℝ^n)}
    (hpq : p = q) (W : W^{k,p}(Omega)) :
    W^{k,q}(Omega) := by
  subst q
  exact W

private theorem baseRepresentative_castWkpSpaceOnExponent
    {k : ℕ} {p q : ℝ≥0∞} {Omega : Set (ℝ^n)}
    (hpq : p = q) (W : W^{k,p}(Omega)) :
    baseRepresentative (castWkpSpaceOnExponent hpq W) =
      baseRepresentative W := by
  subst q
  rfl

/--
Compatible coefficient and forcing data at every Sobolev order.

The fixed functions `coefficient` and `forcing` prevent an invalid
quantifier swap: every Sobolev bundle in the family represents the same
analytic datum.  Global smoothness of the coefficient representative
supplies the finite `C^{k+1}` hypotheses in the higher-order elliptic
bootstrap. The all-order Sobolev assumption on `forcing` is the exact
property used by that bootstrap. For a forcing that is `C^k` up to the
boundary for every `k`, `ContDiffUpToBoundary.toWkpSpaceOn` supplies such
a family.
-/
structure AllOrderPrincipalData
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega) where
  /-- Every forward boundary chart is smooth. -/
  chart_smooth : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x)
  /-- Every inverse boundary chart is smooth. -/
  chart_symm_smooth : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y)
  /-- A fixed pointwise coefficient matrix. -/
  coefficient : ℝ^n → Fin n → Fin n → ℝ
  /-- The fixed coefficient representative is globally smooth. -/
  coefficient_smooth : ∀ i j,
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ coefficient x i j)
  /-- Coefficient bundles at every order required by the bootstrap. -/
  coefficientSobolev :
    ∀ k, Fin n → Fin n → W^{k + 1,∞}(Omega)
  /-- Every coefficient bundle represents the fixed coefficient field. -/
  coefficient_ae : ∀ k i j,
    baseRepresentative (coefficientSobolev k i j)
      =ᵐ[domainMeasure n Omega] fun x ↦ coefficient x i j
  /-- A fixed pointwise forcing representative. -/
  forcing : ℝ^n → ℝ
  /-- Forcing bundles at every finite Sobolev order. -/
  forcingSobolev : ∀ k, W^{k,2}(Omega)
  /-- Every forcing bundle represents the fixed forcing. -/
  forcing_ae : ∀ k,
    baseRepresentative (forcingSobolev k)
      =ᵐ[domainMeasure n Omega] forcing

/-- The coefficient `L∞` value used by the weak equation at order `k`. -/
def AllOrderPrincipalData.coefficientBase
    {Omega : Set (ℝ^n)} [Fact (0 < n)]
    {hOmega : SobolevSpace.C2BoundaryAtlas n Omega}
    (data : AllOrderPrincipalData hOmega) (k : ℕ) (i j : Fin n) :
    DerivLp n ∞ Omega :=
  ((data.coefficientSobolev k i j :
    WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega)

/-- The forcing `L²` value used by the weak equation at order `k`. -/
def AllOrderPrincipalData.forcingBase
    {Omega : Set (ℝ^n)} [Fact (0 < n)]
    {hOmega : SobolevSpace.C2BoundaryAtlas n Omega}
    (data : AllOrderPrincipalData hOmega) (k : ℕ) :
    DerivLp n 2 Omega :=
  ((data.forcingSobolev k :
    WkpAmbientOn n k 2 Omega) (baseIndex n k) :
      DerivLp n 2 Omega)

/-- Coefficient base coordinates from any two Sobolev orders are equal in `L∞`. -/
theorem AllOrderPrincipalData.coefficientBase_eq
    {Omega : Set (ℝ^n)} [Fact (0 < n)]
    {hOmega : SobolevSpace.C2BoundaryAtlas n Omega}
    (data : AllOrderPrincipalData hOmega) (k l : ℕ) :
    data.coefficientBase k = data.coefficientBase l := by
  funext i j
  apply MeasureTheory.Lp.ext
  exact (data.coefficient_ae k i j).trans
    (data.coefficient_ae l i j).symm

/-- Forcing base coordinates from any two Sobolev orders are equal in `L²`. -/
theorem AllOrderPrincipalData.forcingBase_eq
    {Omega : Set (ℝ^n)} [Fact (0 < n)]
    {hOmega : SobolevSpace.C2BoundaryAtlas n Omega}
    (data : AllOrderPrincipalData hOmega) (k l : ℕ) :
    data.forcingBase k = data.forcingBase l := by
  apply MeasureTheory.Lp.ext
  exact (data.forcing_ae k).trans (data.forcing_ae l).symm

/-- The weak solution's chosen order-zero representative. -/
def weakSolutionBase
    {Omega : Set (ℝ^n)}
    (u : H¹₀(Omega)) :
    ℝ^n → ℝ :=
  baseRepresentative (u : H¹(Omega))

/--
The all-orders Sobolev step of the proof of Evans's §6.3.2, Theorem 6.

For each requested order `k`, the result is a `W^{k,2}` bundle whose base
coordinate represents the *same* weak solution. This is stronger than
separate existence statements at each order: the fixed function
`weakSolutionBase u` records compatibility across all orders.
-/
theorem exists_allOrderSobolevRepresentatives_of_isWeakDivergenceSolution
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (data : AllOrderPrincipalData hOmega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (data.coefficientBase 0)
      (data.forcingBase 0)
      u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (data.coefficient x) alpha) :
    ∀ k, ∃ W : W^{k,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        weakSolutionBase u := by
  intro k
  obtain ⟨regularityW, hregularityW⟩ := exists_global_higherOrder_of_isWeakDivergenceSolution
    k hOmega (fun i ↦ (data.chart_smooth i).of_le (by simp))
    (fun i ↦ (data.chart_symm_smooth i).of_le (by simp)) (data.coefficientSobolev k)
    data.coefficient (data.coefficient_ae k)
    (fun i j ↦ (data.coefficient_smooth i j).of_le (by simp)) (data.forcingSobolev k) u
    (show IsWeakDivergenceSolution (data.coefficientBase k) (data.forcingBase k) u by
      simpa only [data.coefficientBase_eq k 0, data.forcingBase_eq k 0] using hu)
    alpha halpha hElliptic
  exact ⟨lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega : k ≤ k + 2) regularityW,
    hregularityW⟩

/--
Operational reduction from the surplus Sobolev order used in this file to
a supercritical first-order jet:

`W^{m+n+1,2}(Omega) -> W^{m+1,2n}(Omega)`.

In dimension one, this is only a restriction from order `m + 2` to
`m + 1`, since `2 > 1` is already supercritical. In higher dimensions,
the proof lowers the exponent to one, performs `n - 1` subcritical
Sobolev steps to reach exponent `n`, and then applies the critical
embedding once with target exponent `2n`.
-/
theorem exists_supercriticalSobolevJet
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (m : ℕ) (W : W^{m + n + 1,2}(Omega)) :
    ∃ V : W^{m + 1,(((2 * n : ℕ) : NNReal) : ℝ≥0∞)}(Omega),
      baseRepresentative V =ᵐ[domainMeasure n Omega]
        baseRepresentative W := by
  by_cases hn1 : n = 1
  · subst n
    exact ⟨lowerOrderCLM (n := 1) (p := (((2 * 1 : ℕ) : NNReal) : ℝ≥0∞)) (Ω := Omega)
      (by omega : m + 1 ≤ m + 1 + 1) W, .of_forall fun _ ↦ rfl⟩
  · have hn2 : 2 ≤ n := by have : 0 < n := Fact.out; omega
    let : Boundary.C1ExtensionAtlas n Omega := hOmega.toC1ExtensionAtlas
    have := isFiniteMeasure_domainMeasure_of_isBounded hOmega.toC1ExtensionAtlas.bounded
    let : Fact (1 ≤ ((1 : NNReal) : ℝ≥0∞)) := ⟨by norm_num⟩
    let : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ n)⟩
    let Wrestricted : W^{(m + 2) + (n - 1),2}(Omega) := lowerOrderCLM (n := n) (p := 2)
      (Ω := Omega) (by omega : (m + 2) + (n - 1) ≤ m + n + 1) W
    let Wone : W^{(m + 2) + (n - 1),(1 : ℝ≥0∞)}(Omega) :=
      SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasure (n := n) (k := (m + 2) + (n - 1))
        (Ω := Omega) (p := 2) (q := 1) (by norm_num) Wrestricted
    let Wdimension : W^{m + 2,(n : ℝ≥0∞)}(Omega) :=
      SobolevSpace.GraphSpace.Embedding.toDimensionExponent (n := n) (k := m + 2) (Ω := Omega) Wone
    exact ⟨SobolevSpace.GraphSpace.Embedding.criticalStep (n := n) (k := m + 1) (Ω := Omega)
      (q := (2 * n : ℕ)) (by exact_mod_cast (by omega : 1 ≤ 2 * n)) Wdimension,
      (SobolevSpace.GraphSpace.Embedding.criticalStep_apply_ae (n := n) (k := m + 1)
        (Ω := Omega) (q := (2 * n : ℕ)) (by exact_mod_cast (by omega : 1 ≤ 2 * n)) Wdimension
          (baseIndex n (m + 1))).trans
      ((SobolevSpace.GraphSpace.Embedding.toDimensionExponent_apply_ae (n := n) (k := m + 2)
        (Ω := Omega) Wone (baseIndex n (m + 2))).trans
      (SobolevSpace.GraphSpace.lowerExponentOfFiniteMeasure_apply_ae (n := n)
        (k := (m + 2) + (n - 1)) (Ω := Omega) (p := 2) (q := 1) (by norm_num) Wrestricted
          (baseIndex n ((m + 2) + (n - 1)))))⟩

/--
A supercritical Sobolev jet has a classical representative on the domain
closure.

For exponent `2n > n`, higher-order Morrey embedding supplies continuous
representatives of all weak derivatives through order `m`. The
weak-to-classical reconstruction theorem identifies the adjacent
representatives as ordinary derivatives in `Omega`. Boundary charts and
the derivative-extension theorem identify the same continuous fields as
derivatives within `closure Omega`.
-/
theorem exists_supercriticalSobolevJet_classical_on_closure
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (m : ℕ)
    (W : W^{m + 1,(((2 * n : ℕ) : NNReal) : ℝ≥0∞)}(Omega)) :
    ∃ v : ℝ^n → ℝ,
      ContDiffOn ℝ m v (closure Omega) ∧
        v =ᵐ[domainMeasure n Omega] baseRepresentative W := by
  let : Boundary.C1ExtensionAtlas n Omega := hOmega.toC1ExtensionAtlas
  have hn : 0 < n := Fact.out
  have hp : (n : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : n < 2 * n)
  have hpq := Real.HolderConjugate.conjExponent
    (show (1 : ℝ) < ((2 * n : ℕ) : ℝ) by exact_mod_cast (by omega : 1 < 2 * n))
  have hexponent : (((2 * n : ℕ) : NNReal) : ℝ≥0∞) = ENNReal.ofReal ((2 * n : ℕ) : ℝ) := by
    norm_num
  let W' := castWkpSpaceOnExponent hexponent W
  refine ⟨_, finiteMorreyDerivativeRepresentativeOn_contDiffOn_closure hp hpq m [] (by simp) W',
    ?_⟩
  have hvW' : finiteMorreyDerivativeRepresentativeOn hp hpq [] (by simp) W'
      =ᵐ[domainMeasure n Omega] baseRepresentative W' := by
    change _ =ᵐ[domainMeasure n Omega] fun x ↦ (((W' : WkpAmbientOn n (m + 1)
      (ENNReal.ofReal ((2 * n : ℕ) : ℝ)) Omega) (baseIndex n (m + 1)) :
        DerivLp n (ENNReal.ofReal ((2 * n : ℕ) : ℝ)) Omega) : ℝ^n → ℝ) x
    simpa using finiteMorreyDerivativeRepresentativeOn_ae hp hpq [] (by simp) W'
  simpa only [W', baseRepresentative_castWkpSpaceOnExponent] using hvW'

/--
A supercritical Sobolev jet also has a classical representative in the open
domain.

This is the interior restriction of
`exists_supercriticalSobolevJet_classical_on_closure`.
-/
theorem exists_supercriticalSobolevJet_classical
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (m : ℕ)
    (W : W^{m + 1,(((2 * n : ℕ) : NNReal) : ℝ≥0∞)}(Omega)) :
    ∃ v : ℝ^n → ℝ,
      ContDiffOn ℝ m v Omega ∧
        v =ᵐ[domainMeasure n Omega] baseRepresentative W := by
  obtain ⟨v, hvRegular, hvAE⟩ :=
    exists_supercriticalSobolevJet_classical_on_closure hOmega m W
  exact ⟨v, hvRegular.mono subset_closure, hvAE⟩

/--
Every finite Sobolev order has a classical representative on the closure of
an operational smooth domain.

The proof first raises the exponent to the supercritical value `2n`, then
applies completed-space Morrey reconstruction. No order-`k` extension
operator or boundary-reconstruction hypothesis is assumed.
-/
theorem hasClassicalRepresentativesOnClosure
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega) :
    ∀ (m : ℕ) (W : W^{m + n + 1,2}(Omega)),
      ∃ v : ℝ^n → ℝ,
        ContDiffOn ℝ m v (closure Omega) ∧
          v =ᵐ[domainMeasure n Omega] baseRepresentative W := by
  intro m W
  obtain ⟨jet, hjet⟩ :=
    exists_supercriticalSobolevJet hOmega m W
  obtain ⟨v, hvRegular, hvAE⟩ :=
    exists_supercriticalSobolevJet_classical_on_closure
      hOmega m jet
  exact ⟨v, hvRegular, hvAE.trans hjet⟩

/--
Coherent extraction of one smooth representative on the open domain from
all finite Sobolev orders.

At each order, the operational Sobolev iteration first reaches the
supercritical exponent `2n`. Morrey reconstruction then produces a
classical representative on `Omega`. All of these representatives agree
almost everywhere with `g`; continuity and positivity of Lebesgue measure
on nonempty open sets make them agree pointwise. One representative
therefore inherits every finite differentiability order.
-/
theorem exists_interior_smoothRepresentative_of_all_orders
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (g : ℝ^n → ℝ)
    (allOrders : ∀ order, ∃ W : W^{order,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega] g) :
    ∃ v : ℝ^n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v Omega ∧
        v =ᵐ[domainMeasure n Omega] g := by
  classical
  choose W hW using allOrders
  choose jet hjet using fun m ↦
    exists_supercriticalSobolevJet hOmega m (W (m + n + 1))
  choose v hvRegular hvAE using fun m ↦
    exists_supercriticalSobolevJet_classical hOmega m (jet m)
  have hvg : ∀ m : ℕ,
      v m =ᵐ[domainMeasure n Omega] g := fun m ↦
    (hvAE m).trans ((hjet m).trans (hW (m + n + 1)))
  exact MeasureTheory.exists_contDiffOn_ae_eq_of_forall_nat
    (𝕜 := ℝ) (μ := volume) hOmega.toC1ExtensionAtlas.isOpen
    (Subset.refl Omega) subset_closure
    (fun m ↦ ⟨v m, hvRegular m, by simpa only [domainMeasure] using hvg m⟩)

/--
Coherent extraction of one smooth representative from all finite Sobolev
orders.

This theorem performs the coherence step from `W^{k,2}` for every `k` to
`C∞`.  For each
`m`, the embedding hypothesis produces a possibly different `C^m`
representative `v_m`.  All `v_m` represent the same `g` almost everywhere.
Since Lebesgue measure is positive on nonempty open sets, continuous
almost-everywhere-equal functions agree pointwise on `Omega`; continuity
then extends the equality to `closure Omega`.  Hence `v_0` is `C^m` for
every finite `m`, which is exactly `ContDiffOn ℝ ∞` in mathlib.
-/
theorem exists_smoothRepresentativeOnClosure_of_all_orders
    {Omega : Set (ℝ^n)} (hOmegaOpen : IsOpen Omega)
    (g : ℝ^n → ℝ)
    (allOrders : ∀ order, ∃ W : W^{order,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega] g)
    (hclassical :
      ∀ (m : ℕ) (W : W^{m + n + 1,2}(Omega)),
        ∃ v : ℝ^n → ℝ,
          ContDiffOn ℝ m v (closure Omega) ∧
            v =ᵐ[domainMeasure n Omega] baseRepresentative W) :
    ∃ v : ℝ^n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (closure Omega) ∧
        v =ᵐ[domainMeasure n Omega] g := by
  classical
  choose W hW using allOrders
  choose v hvRegular hvAE using fun m ↦
    hclassical m (W (m + n + 1))
  have hvg : ∀ m : ℕ,
      v m =ᵐ[domainMeasure n Omega] g := fun m ↦
    (hvAE m).trans (hW (m + n + 1))
  exact MeasureTheory.exists_contDiffOn_ae_eq_of_forall_nat
    (𝕜 := ℝ) (μ := volume) hOmegaOpen subset_closure (Subset.refl (closure Omega))
    (fun m ↦ ⟨v m, hvRegular m, by simpa only [domainMeasure] using hvg m⟩)

/--
Interior smoothness for a weak divergence-form solution with all-order
smooth data.

The higher-order elliptic bootstrap supplies compatible Sobolev
representatives at every finite order. In every positive dimension, the
operational Sobolev iteration and Morrey reconstruction of
`exists_interior_smoothRepresentative_of_all_orders` produce one
representative that is `C∞` throughout `Omega`. No boundary reconstruction
hypothesis is required.
-/
theorem exists_interior_smoothRepresentative_of_isWeakDivergenceSolution
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (data : AllOrderPrincipalData hOmega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (data.coefficientBase 0)
      (data.forcingBase 0)
      u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (data.coefficient x) alpha) :
    ∃ v : ℝ^n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v Omega ∧
        v =ᵐ[domainMeasure n Omega] weakSolutionBase u := by
  exact exists_interior_smoothRepresentative_of_all_orders
    hOmega (weakSolutionBase u)
      (exists_allOrderSobolevRepresentatives_of_isWeakDivergenceSolution
        hOmega data u hu alpha halpha hElliptic)

/--
Evans's §6.3.2, Theorem 6, for operational smooth boundary data.

Under smooth compatible charts and coefficients, all-order compatible
forcing, and uniform ellipticity, the weak solution has one representative
that is infinitely differentiable on the closure and agrees almost
everywhere with the original `H¹₀` solution. The operational Sobolev
iteration, completed-space Morrey reconstruction, and coherence argument
are all discharged by the proof.
-/
theorem exists_smoothRepresentativeOnClosure_of_isWeakDivergenceSolution
    {Omega : Set (ℝ^n)}
    [Fact (0 < n)]
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (data : AllOrderPrincipalData hOmega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (data.coefficientBase 0)
      (data.forcingBase 0)
      u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (data.coefficient x) alpha) :
    ∃ v : ℝ^n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (closure Omega) ∧
        v =ᵐ[domainMeasure n Omega] weakSolutionBase u := by
  exact exists_smoothRepresentativeOnClosure_of_all_orders
    hOmega.toC1ExtensionAtlas.isOpen
    (weakSolutionBase u)
    (exists_allOrderSobolevRepresentatives_of_isWeakDivergenceSolution
      hOmega data u hu alpha halpha hElliptic)
    (hasClassicalRepresentativesOnClosure hOmega)

end SobolevSpace.GraphSpace.BoundaryRegularity
