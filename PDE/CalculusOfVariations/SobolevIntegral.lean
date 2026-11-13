/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ConvexIntegral
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.Analysis.MeasureTheory.Lp.Superposition
import PDE.CalculusOfVariations.DirectMethod
import PDE.CalculusOfVariations.WeakLowerSemicontinuity
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Convex integral functionals on `H¹`

We carry the convex direct method from `L²` to the
base-plus-gradient coordinates of `H¹(Ω)`, following Evans, §8.2.1 and §8.2.2.
`H1SpaceOn` is the weak-derivative graph space. When `Ω` is open it is
the Sobolev space of Evans; on an arbitrary set it is the generalized graph
space.

For a scalar Sobolev field `u`, its first-order pointwise jet is the pair
`(u(x), Du(x))`, formed from the canonical `L²` representatives in the
Sobolev bundle.  Given an integrand `F`, this defines the integral
functional

`J_F(u) = ∫_Ω F(x, u(x), Du(x)) dx`.

Almost-everywhere joint convexity of `F(x, ·)` and integrability of the densities
imply convexity of `J_F`.  Strong lower semicontinuity then implies weak lower
semicontinuity, and coercivity gives a minimizer by the direct method.

The concrete specialization

`J_g(u) = ∫_Ω (|u-g|² + ∑ᵢ |Dᵢu-Dᵢg|²)`

is treated directly.  Its density is integrable, it equals the
squared `H¹` distance, is weakly lower semicontinuous and coercive, and has
the prescribed Sobolev field `g` as its unique global minimizer.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.1, (1), and §8.2.2.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

open Filter Set
open MeasureTheory

open scoped ENNReal InnerProductSpace MeasureTheory

namespace PDE.CalculusOfVariations

open SobolevSpace
open SobolevSpace.GraphSpace

noncomputable section

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-! ## Integral functionals of `(x, u, Du)` -/

/-- The pointwise first-order jet `(u(x), Du(x))` of a scalar `H¹` field.

The first component is the canonical `L²` representative of `u`; the second
is the finite Euclidean vector of canonical representatives of its first
weak derivatives. -/
def firstOrderSobolevJet (u : H¹(Ω)) (x : ℝ^n) : ℝ × ℝ^n :=
  ((((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) x),
    WithLp.toLp 2 fun i : Fin n ↦
      (((u : WkpAmbientOn n 1 2 Ω)
        (singleDerivIndex (n := n) i)) x))

/-- The scalar first-order integral functional of Evans, §8.2.1, equation (1):

`J_F(u) = ∫_Ω F(x, u(x), Du(x)) dx`.

The second argument of `F` bundles the scalar value and Euclidean weak
gradient as `(u(x), Du(x))`. This definition uses Mathlib's totalized Bochner
integral. Quadratic growth gives integrability below; more general densities
require a separate integrability hypothesis for integral order arguments. -/
def firstOrderSobolevIntegralEnergy
    (F : ℝ^n → (ℝ × ℝ^n) → ℝ) (u : H¹(Ω)) : ℝ :=
  ∫ x, F x (firstOrderSobolevJet u x) ∂domainMeasure n Ω

section JetCoordinates

local notation "μ" => domainMeasure n Ω

/-- The bundled `L²` gradient represents the gradient component of the
first-order Sobolev jet almost everywhere. No openness or boundary assumption
is needed for this identity between the graph-space coordinates. -/
theorem wkpGradientCLM_eq_firstOrderSobolevJet_ae (u : H¹(Ω)) :
    (fun x ↦ ∇ u x) =ᵐ[μ]
      (fun x ↦ (firstOrderSobolevJet u x).2) := by
  filter_upwards [wkpGradientCLM_apply_ae u] with x hx
  apply PiLp.ext
  intro i
  simpa only [firstOrderSobolevJet, PiLp.toLp_apply] using hx i

/-- The first-order Sobolev jet agrees almost everywhere with the pair of
the bundled base coordinate and weak gradient. Representatives need not
agree at every point. -/
theorem firstOrderSobolevJet_eq_base_gradient_ae (u : H¹(Ω)) :
    firstOrderSobolevJet u =ᵐ[μ] fun x ↦
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) u x,
        ∇ u x) := by
  filter_upwards [wkpGradientCLM_eq_firstOrderSobolevJet_ae u] with x hx
  exact Prod.ext rfl hx.symm

/-- A first-order Sobolev integral can be evaluated on the bundled `L²`
base coordinate and gradient. Integrability is a separate assertion,
proved below under quadratic growth. -/
theorem firstOrderSobolevIntegralEnergy_eq_integral_base_gradient
    (F : ℝ^n → ℝ × ℝ^n → ℝ) (u : H¹(Ω)) :
    firstOrderSobolevIntegralEnergy F u =
      ∫ x, F x
        (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) u x,
          ∇ u x) ∂μ := by
  exact integral_congr_ae
    ((firstOrderSobolevJet_eq_base_gradient_ae u).mono fun x hx ↦ congrArg (F x) hx)

/-- A jointly measurable density with absolute quadratic growth is integrable
on a scalar and vector `L²` pair. The offset belongs to `L¹`; the product
norm is the maximum of the two coordinate norms. -/
theorem integrable_mixed_L2_density_of_quadratic_growth
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {a : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : Integrable a μ)
    (hFgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ 2)
    (v : Lp ℝ 2 μ) (q : Lp (ℝ^n) 2 μ) :
    Integrable (fun x ↦ F x (v x, q x)) μ := by
  have hpair : MemLp (fun x ↦ (v x, q x)) 2 μ := by
    have hleft := (Lp.memLp v).continuousLinearMap_comp
      (ContinuousLinearMap.inl ℝ ℝ (ℝ^n))
    have hright := (Lp.memLp q).continuousLinearMap_comp
      (ContinuousLinearMap.inr ℝ ℝ (ℝ^n))
    apply MemLp.ae_eq (hf_Lp := hleft.add hright)
    exact ae_of_all μ fun x ↦ by
      change (v x + 0, 0 + q x) = (v x, q x)
      exact Prod.ext (add_zero _) (zero_add _)
  apply hpair.integrable_comp_of_norm_rpow_le (by simp) (by simp) hF ha
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using hFgrowth

/-- Joint measurability and quadratic growth with an integrable offset make
the density of every `H¹` field integrable. The product norm is
`max |u| |Du|`. No domain boundedness, convexity, or derivative hypothesis
is needed to establish that these energies are finite. -/
theorem integrable_firstOrderSobolevJet_of_quadratic_growth
    {F : ℝ^n → ℝ × ℝ^n → ℝ} {a : ℝ^n → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (ha : Integrable a μ)
    (hFgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ 2)
    (u : H¹(Ω)) :
    Integrable (fun x ↦ F x (firstOrderSobolevJet u x)) μ := by
  apply (integrable_mixed_L2_density_of_quadratic_growth hF ha hFgrowth
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) u)
    (∇ u)).congr
  exact (firstOrderSobolevJet_eq_base_gradient_ae u).symm.mono
    fun x hx ↦ congrArg (F x) hx

end JetCoordinates

/-- Canonical `L²` representatives preserve affine combinations in the
first-order jet almost everywhere. -/
theorem firstOrderSobolevJet_affine_ae
    (u v : H¹(Ω)) (a b : ℝ) :
    (fun x ↦ firstOrderSobolevJet (a • u + b • v) x)
      =ᵐ[domainMeasure n Ω]
    (fun x ↦ a • firstOrderSobolevJet u x +
      b • firstOrderSobolevJet v x) := by
  have hcoordinate (q : DerivIndex n 1) :
      (fun x ↦
        (((a • u + b • v : H¹(Ω)) :
          WkpAmbientOn n 1 2 Ω) q) x)
        =ᵐ[domainMeasure n Ω]
      (fun x ↦
        a • (((u : WkpAmbientOn n 1 2 Ω) q) x) +
          b • (((v : WkpAmbientOn n 1 2 Ω) q) x)) := by
    filter_upwards [
      MeasureTheory.Lp.coeFn_add
        (a • ((u : WkpAmbientOn n 1 2 Ω) q))
        (b • ((v : WkpAmbientOn n 1 2 Ω) q)),
      MeasureTheory.Lp.coeFn_smul a
        ((u : WkpAmbientOn n 1 2 Ω) q),
      MeasureTheory.Lp.coeFn_smul b
        ((v : WkpAmbientOn n 1 2 Ω) q)] with x hadd ha' hb'
    change
      (a • ((u : WkpAmbientOn n 1 2 Ω) q) +
        b • ((v : WkpAmbientOn n 1 2 Ω) q)) x =
      a • ((u : WkpAmbientOn n 1 2 Ω) q) x +
        b • ((v : WkpAmbientOn n 1 2 Ω) q) x
    rw [hadd, Pi.add_apply, ha', hb', Pi.smul_apply, Pi.smul_apply]
  filter_upwards [
    hcoordinate (baseIndex n 1),
    ae_all_iff.2 fun i : Fin n ↦
      hcoordinate (singleDerivIndex (n := n) i)] with x hbase hgradient
  apply Prod.ext
  · simpa only [firstOrderSobolevJet, Prod.fst_add, Prod.smul_fst] using hbase
  · apply PiLp.ext
    intro i
    simpa only [firstOrderSobolevJet, Prod.snd_add, Prod.smul_snd,
      PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply] using hgradient i

/-- Almost-everywhere joint convexity in `(u, Du)`, together with integrability of
every admissible density, implies convexity of the integral functional. -/
theorem convexOn_firstOrderSobolevIntegralEnergy
    (F : ℝ^n → (ℝ × ℝ^n) → ℝ)
    (hFconvex : ∀ᵐ x ∂domainMeasure n Ω, ConvexOn ℝ Set.univ (F x))
    (hFintegrable : ∀ u : H¹(Ω),
      Integrable (fun x ↦ F x (firstOrderSobolevJet u x))
        (domainMeasure n Ω)) :
    ConvexOn ℝ Set.univ
      (firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hjet := firstOrderSobolevJet_affine_ae
    (n := n) (Ω := Ω) u v a b
  have hpointwise :
      (fun x ↦ F x (firstOrderSobolevJet (a • u + b • v) x))
        ≤ᵐ[domainMeasure n Ω]
      (fun x ↦
        a • F x (firstOrderSobolevJet u x) +
          b • F x (firstOrderSobolevJet v x)) := by
    filter_upwards [hjet, hFconvex] with x hx hconvex
    rw [hx]
    exact hconvex.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hau :
      Integrable (fun x ↦ a • F x (firstOrderSobolevJet u x))
        (domainMeasure n Ω) :=
    (hFintegrable u).smul (c := a)
  have hbv :
      Integrable (fun x ↦ b • F x (firstOrderSobolevJet v x))
        (domainMeasure n Ω) :=
    (hFintegrable v).smul (c := b)
  unfold firstOrderSobolevIntegralEnergy
  calc
    (∫ x, F x (firstOrderSobolevJet (a • u + b • v) x)
        ∂domainMeasure n Ω)
        ≤ ∫ x, (a • F x (firstOrderSobolevJet u x) +
            b • F x (firstOrderSobolevJet v x))
          ∂domainMeasure n Ω := by
      exact integral_mono_ae
        (hFintegrable (a • u + b • v))
        (hau.add hbv)
        hpointwise
    _ = a • (∫ x, F x (firstOrderSobolevJet u x)
          ∂domainMeasure n Ω) +
        b • (∫ x, F x (firstOrderSobolevJet v x)
          ∂domainMeasure n Ω) := by
      rw [integral_add hau hbv, integral_smul, integral_smul]

/-- A strongly lower-semicontinuous first-order integral functional with
almost-everywhere joint convexity in `(u, Du)` is lower semicontinuous for the weak
`H¹` topology.

This is an abstract convex-functional route: strong lower semicontinuity and
joint convexity in `(u, Du)` are explicit hypotheses. -/
theorem lowerSemicontinuous_weakSpace_firstOrderSobolevIntegralEnergy
    (F : ℝ^n → (ℝ × ℝ^n) → ℝ)
    (hFconvex : ∀ᵐ x ∂domainMeasure n Ω, ConvexOn ℝ Set.univ (F x))
    (hFintegrable : ∀ u : H¹(Ω),
      Integrable (fun x ↦ F x (firstOrderSobolevJet u x))
        (domainMeasure n Ω))
    (hstrong :
      LowerSemicontinuous
        (firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F)) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ (H¹(Ω)) ↦
        firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F
          ((toWeakSpace ℝ (H¹(Ω))).symm w)) := by
  exact lowerSemicontinuous_weakSpace_of_convex
    (firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F)
    (convexOn_firstOrderSobolevIntegralEnergy F hFconvex hFintegrable)
    hstrong

/-- An unconstrained direct-method theorem for the concrete integral
`∫_Ω F(x, u(x), Du(x)) dx`: almost-everywhere joint convexity, assumed strong lower
semicontinuity, and assumed coercivity give a global minimizer in the
first-order graph space.

The admissible class here is the whole graph space, and coercivity is a
hypothesis on the integral functional. -/
theorem exists_global_minimizer_firstOrderSobolevIntegralEnergy
    (F : ℝ^n → (ℝ × ℝ^n) → ℝ)
    (hFconvex : ∀ᵐ x ∂domainMeasure n Ω, ConvexOn ℝ Set.univ (F x))
    (hFintegrable : ∀ u : H¹(Ω),
      Integrable (fun x ↦ F x (firstOrderSobolevJet u x))
        (domainMeasure n Ω))
    (hstrong :
      LowerSemicontinuous
        (firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F))
    (hcoercive :
      Tendsto (firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F)
        (Bornology.cobounded (H¹(Ω))) atTop) :
    ∃ u : H¹(Ω), ∀ v : H¹(Ω),
      firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F u ≤
        firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F v := by
  exact exists_global_minimizer_of_weak_lowerSemicontinuous_of_coercive
    (firstOrderSobolevIntegralEnergy (n := n) (Ω := Ω) F)
    (lowerSemicontinuous_weakSpace_firstOrderSobolevIntegralEnergy
      F hFconvex hFintegrable hstrong)
    hcoercive

/-! ## The quadratic base-plus-gradient integral -/

/-- The quadratic Sobolev integral

`∫_Ω (|u-g|² + ∑ᵢ |Dᵢu-Dᵢg|²)`.

All terms use the canonical `L²` representatives stored in the `H¹`
coordinate bundle. -/
def quadraticSobolevIntegralEnergy
    (g u : H¹(Ω)) : ℝ :=
  ∫ x,
    ‖((((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) -
        ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))) x)‖ ^ 2 +
      ∑ i : Fin n,
        ‖((((u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i)) -
          ((g : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))) x)‖ ^ 2
    ∂domainMeasure n Ω

/-- The base-plus-gradient density of
`quadraticSobolevIntegralEnergy` is integrable. -/
theorem integrable_quadraticSobolevIntegralEnergy_density
    (g u : H¹(Ω)) :
    Integrable
      (fun x ↦
        ‖((((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) -
          ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))) x)‖ ^ 2 +
        ∑ i : Fin n,
          ‖((((u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i)) -
            ((g : WkpAmbientOn n 1 2 Ω)
              (singleDerivIndex (n := n) i))) x)‖ ^ 2)
      (domainMeasure n Ω) := by
  have hbase :
      Integrable
        (fun x ↦
          ‖((((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) -
            ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))) x)‖ ^ 2)
        (domainMeasure n Ω) :=
    integrable_quadraticIntegralEnergy_density
      ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
      ((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
  have hgradient :
      Integrable
        (fun x ↦
          ∑ i : Fin n,
            ‖((((u : WkpAmbientOn n 1 2 Ω)
              (singleDerivIndex (n := n) i)) -
              ((g : WkpAmbientOn n 1 2 Ω)
                (singleDerivIndex (n := n) i))) x)‖ ^ 2)
        (domainMeasure n Ω) := by
    exact integrable_finsetSum Finset.univ fun i _ ↦
      integrable_quadraticIntegralEnergy_density
        ((g : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))
        ((u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))
  exact hbase.add hgradient

/-- The Sobolev integral splits into the quadratic `L²` fidelity energy of
the base coordinate and those of all first weak derivatives. -/
theorem quadraticSobolevIntegralEnergy_eq_coordinate_sum
    (g u : H¹(Ω)) :
    quadraticSobolevIntegralEnergy g u =
      quadraticIntegralEnergy
        ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
        ((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) +
      ∑ i : Fin n,
        quadraticIntegralEnergy
          ((g : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))
          ((u : WkpAmbientOn n 1 2 Ω)
            (singleDerivIndex (n := n) i)) := by
  have hbase :
      Integrable
        (fun x ↦
          ‖((((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) -
            ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))) x)‖ ^ 2)
        (domainMeasure n Ω) :=
    integrable_quadraticIntegralEnergy_density
      ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
      ((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
  have hcoordinate :
      ∀ i : Fin n,
        Integrable
          (fun x ↦
            ‖((((u : WkpAmbientOn n 1 2 Ω)
              (singleDerivIndex (n := n) i)) -
              ((g : WkpAmbientOn n 1 2 Ω)
                (singleDerivIndex (n := n) i))) x)‖ ^ 2)
          (domainMeasure n Ω) := by
    intro i
    exact integrable_quadraticIntegralEnergy_density
      ((g : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))
      ((u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))
  unfold quadraticSobolevIntegralEnergy
  rw [integral_add hbase (integrable_finsetSum Finset.univ fun i _ ↦ hcoordinate i)]
  rw [integral_finsetSum Finset.univ fun i _ ↦ hcoordinate i]
  rfl

/-- The quadratic base-plus-gradient integral is exactly the squared `H¹`
distance. -/
theorem quadraticSobolevIntegralEnergy_eq_norm_sq
    (g u : H¹(Ω)) :
    quadraticSobolevIntegralEnergy g u = ‖u - g‖ ^ 2 := by
  rw [quadraticSobolevIntegralEnergy_eq_coordinate_sum]
  simp_rw [quadraticIntegralEnergy_eq_norm_sq]
  have hdecomp :=
    ambient_norm_sq_eq_base_sq_add_sum_deriv_sq
      (n := n) (Ω := Ω)
      ((u : WkpAmbientOn n 1 2 Ω) -
        (g : WkpAmbientOn n 1 2 Ω))
  calc
    ‖((u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) -
          ((g : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))‖ ^ 2 +
        ∑ i : Fin n,
          ‖((u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i)) -
            ((g : WkpAmbientOn n 1 2 Ω) (singleDerivIndex (n := n) i))‖ ^ 2 =
      ‖(u : WkpAmbientOn n 1 2 Ω) -
        (g : WkpAmbientOn n 1 2 Ω)‖ ^ 2 := by
          simpa only [PiLp.sub_apply] using hdecomp.symm
    _ = ‖u - g‖ ^ 2 := rfl

/-- The quadratic Sobolev integral vanishes exactly at its prescribed field. -/
@[simp]
theorem quadraticSobolevIntegralEnergy_eq_zero_iff
    (g u : H¹(Ω)) :
    quadraticSobolevIntegralEnergy g u = 0 ↔ u = g := by
  rw [quadraticSobolevIntegralEnergy_eq_norm_sq, sq_eq_zero_iff,
    norm_eq_zero, sub_eq_zero]

/-- The quadratic Sobolev integral is continuous in the strong `H¹`
topology. -/
theorem continuous_quadraticSobolevIntegralEnergy
    (g : H¹(Ω)) :
    Continuous (quadraticSobolevIntegralEnergy g) := by
  rw [show quadraticSobolevIntegralEnergy g =
      fun u ↦ ‖u - g‖ ^ 2 by
    funext u
    exact quadraticSobolevIntegralEnergy_eq_norm_sq g u]
  fun_prop

/-- The quadratic Sobolev integral is convex on `H¹(Ω)`. -/
theorem convexOn_quadraticSobolevIntegralEnergy
    (g : H¹(Ω)) :
    ConvexOn ℝ Set.univ (quadraticSobolevIntegralEnergy g) := by
  rw [show quadraticSobolevIntegralEnergy g =
      fun u ↦ ‖u - g‖ ^ 2 by
    funext u
    exact quadraticSobolevIntegralEnergy_eq_norm_sq g u]
  have hconvex := (convexOn_univ_dist g).pow (fun _ _ ↦ dist_nonneg) 2
  rw [show (fun u : H¹(Ω) ↦ ‖u - g‖ ^ 2) =
      (fun u : H¹(Ω) ↦ dist u g) ^ 2 by
    funext u
    simp only [Pi.pow_apply, dist_eq_norm]]
  exact hconvex

/-- The quadratic base-plus-gradient integral is lower semicontinuous for
the weak `H¹` topology. -/
theorem lowerSemicontinuous_weakSpace_quadraticSobolevIntegralEnergy
    (g : H¹(Ω)) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ (H¹(Ω)) ↦
        quadraticSobolevIntegralEnergy g
          ((toWeakSpace ℝ (H¹(Ω))).symm w)) := by
  exact lowerSemicontinuous_weakSpace_of_convex
    (quadraticSobolevIntegralEnergy g)
    (convexOn_quadraticSobolevIntegralEnergy g)
    (continuous_quadraticSobolevIntegralEnergy g).lowerSemicontinuous

/-- The quadratic Sobolev integral tends to infinity with the `H¹` norm. -/
theorem quadraticSobolevIntegralEnergy_coercive
    (g : H¹(Ω)) :
    Tendsto (quadraticSobolevIntegralEnergy g)
      (Bornology.cobounded (H¹(Ω))) atTop := by
  have hdistance :
      Tendsto (fun u : H¹(Ω) ↦ ‖u - g‖)
        (Bornology.cobounded (H¹(Ω))) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_sub_const_cobounded g)
  have hsquare :
      Tendsto (fun u : H¹(Ω) ↦ ‖u - g‖ ^ 2)
        (Bornology.cobounded (H¹(Ω))) atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp hdistance
  rw [show quadraticSobolevIntegralEnergy g =
      fun u ↦ ‖u - g‖ ^ 2 by
    funext u
    exact quadraticSobolevIntegralEnergy_eq_norm_sq g u]
  exact hsquare

/-- The direct method gives the unique minimizer of the quadratic
base-plus-gradient integral, namely the prescribed Sobolev field. -/
theorem existsUnique_global_minimizer_quadraticSobolevIntegralEnergy
    (g : H¹(Ω)) :
    ∃! u : H¹(Ω), ∀ v : H¹(Ω),
      quadraticSobolevIntegralEnergy g u ≤
        quadraticSobolevIntegralEnergy g v := by
  obtain ⟨u, hu⟩ :=
    exists_global_minimizer_of_weak_lowerSemicontinuous_of_coercive
      (quadraticSobolevIntegralEnergy g)
      (lowerSemicontinuous_weakSpace_quadraticSobolevIntegralEnergy g)
      (quadraticSobolevIntegralEnergy_coercive g)
  have minimizer_eq_data :
      ∀ {w : H¹(Ω)},
        (∀ v, quadraticSobolevIntegralEnergy g w ≤
          quadraticSobolevIntegralEnergy g v) →
        w = g := by
    intro w hw
    have hzero : ‖w - g‖ ^ 2 ≤ 0 := by
      calc
        ‖w - g‖ ^ 2 = quadraticSobolevIntegralEnergy g w :=
          (quadraticSobolevIntegralEnergy_eq_norm_sq g w).symm
        _ ≤ quadraticSobolevIntegralEnergy g g := hw g
        _ = ‖g - g‖ ^ 2 :=
          quadraticSobolevIntegralEnergy_eq_norm_sq g g
        _ = 0 := by simp
    have hsquare_zero : ‖w - g‖ ^ 2 = 0 :=
      le_antisymm hzero (sq_nonneg _)
    have hnorm : ‖w - g‖ = 0 := sq_eq_zero_iff.mp hsquare_zero
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact (minimizer_eq_data hv).trans (minimizer_eq_data hu).symm

end

end PDE.CalculusOfVariations
