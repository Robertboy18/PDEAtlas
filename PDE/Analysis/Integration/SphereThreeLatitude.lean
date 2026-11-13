/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.EuclideanBall
public import PDE.Analysis.Integration.Polar
public import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder
import CAS.IntegrationTactic

/-!
# Latitude integration on the three-sphere

For a bounded measurable scalar function F, integrate F of one coordinate on
S³ by the latitude formula with density 4π sin² θ. The proof compares polar
and cylindrical integration over the unit ball in ℝ⁴.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter LineDeriv SobolevSpace
open scoped ENNReal RealInnerProductSpace Topology

namespace PDE.Analysis

/-- Fubini on the coordinate-pair upper half-plane.  This version is phrased
through the measure-preserving profile-coordinate equivalence and is useful
when the integrable function is naturally defined on `(ℝ^2)`.
-/
theorem integral_pair_upperHalfPlane_iterated
    (q : (ℝ^2) → ℝ) (hq : Integrable q volume) :
    (∫ p in {p : ℝ × ℝ | 0 < p.2},
      q (PDE.Analysis.planeEquiv.symm p)) =
      ∫ t : ℝ, ∫ ρ in Set.Ioi (0 : ℝ),
        q (PDE.Analysis.planeEquiv.symm (t, ρ)) := by
  let e := PDE.Analysis.planeEquiv
  let G : ℝ × ℝ → ℝ := fun p ↦ q (e.symm p)
  let U : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hU : MeasurableSet U := measurableSet_lt measurable_const measurable_snd
  have hG : Integrable G volume := by
    simpa [G, Function.comp_def] using (PDE.Analysis.measurePreserving_planeEquiv.symm e
      |>.integrable_comp_emb e.symm.measurableEmbedding (g := q)).2 hq
  calc
    (∫ p in {p : ℝ × ℝ | 0 < p.2}, q (PDE.Analysis.planeEquiv.symm p)) =
        ∫ p, U.indicator G p := by rw [integral_indicator hU]
    _ = ∫ t : ℝ, ∫ ρ : ℝ, U.indicator G (t, ρ) := integral_prod _ (hG.indicator hU)
    _ = _ := integral_congr_ae (.of_forall fun t ↦ by
      rw [← integral_indicator measurableSet_Ioi]
      exact integral_congr_ae (.of_forall fun ρ ↦ by by_cases hρ : 0 < ρ <;> simp [U, G, e, hρ]))

/-- Embed one distinguished coordinate and a three-dimensional orthogonal
block into `ℝ⁴`.
-/
def onePlusThreePoint
    (t : ℝ) (u : ℝ^3) : ℝ^4 :=
  (PDE.Analysis.euclideanSumMeasurableEquiv 1 3).symm
    (EuclideanSpace.single 0 t, u)

/-- Distinguished coordinate of the one-plus-three embedding.
-/
@[simp]
theorem onePlusThreePoint_zero
    (t : ℝ) (u : ℝ^3) :
    onePlusThreePoint t u 0 = t := by
  let y := onePlusThreePoint t u
  have hy := congrArg Prod.fst
    (PDE.Analysis.euclideanSumMeasurableEquiv 1 3 |>.apply_symm_apply
      (EuclideanSpace.single 0 t, u))
  exact congrArg (fun v : ℝ^1 ↦ v 0) hy

/-- The one-plus-three coordinate split is orthogonal, so its squared norm is
the sum of the squared norms of the distinguished coordinate and the
three-dimensional block.
-/
theorem onePlusThreePoint_norm_sq
    (t : ℝ) (u : ℝ^3) :
    ‖onePlusThreePoint t u‖ ^ 2 = t ^ 2 + ‖u‖ ^ 2 := by
  change ‖(PDE.Analysis.euclideanSumLinearIsometry 1 3).symm
      (WithLp.toLp 2 (EuclideanSpace.single 0 t, u))‖ ^ 2 = _
  rw [(PDE.Analysis.euclideanSumLinearIsometry 1 3).symm.norm_map,
    WithLp.prod_norm_eq_add (by norm_num)]
  simpa [PiLp.norm_single, Real.norm_eq_abs, sq_abs] using
    (Real.rpow_inv_natCast_pow
      (n := 2) (add_nonneg (sq_nonneg t) (sq_nonneg ‖u‖)) (by decide))

/-- On a unit direction in the three-dimensional block, the orthogonal split
has the usual two-dimensional radial norm formula.
-/
theorem onePlusThreePoint_smul_sphere_norm_sq
    (t ρ : ℝ) (η : Metric.sphere (0 : ℝ^3) 1) :
    ‖onePlusThreePoint t
        (ρ • (η : ℝ^3))‖ ^ 2 = t ^ 2 + ρ ^ 2 := by
  rw [onePlusThreePoint_norm_sq]
  have hη := η.property
  rw [mem_sphere_zero_iff_norm] at hη
  rw [norm_smul, hη]
  simp [sq_abs]

/-- Norm form of the preceding orthogonal-coordinate identity. -/
theorem onePlusThreePoint_smul_sphere_norm
    (t ρ : ℝ) (η : Metric.sphere (0 : ℝ^3) 1) :
    ‖onePlusThreePoint t
        (ρ • (η : ℝ^3))‖ =
      √(t ^ 2 + ρ ^ 2) := by
  have h := congrArg Real.sqrt
    (onePlusThreePoint_smul_sphere_norm_sq t ρ η)
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

/-- Under upper-half-plane polar coordinates, the four-dimensional radius is
the planar radial variable. -/
theorem onePlusThreePoint_polar_norm
    (r θ : ℝ) (hr : 0 ≤ r)
    (η : Metric.sphere (0 : ℝ^3) 1) :
    ‖onePlusThreePoint (r * Real.cos θ)
        ((r * Real.sin θ) • (η : ℝ^3))‖ = r := by
  rw [onePlusThreePoint_smul_sphere_norm]
  have htrig : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [htrig, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

/-- The normalized distinguished coordinate in the same polar chart is
exactly `cos θ`.
-/
theorem onePlusThreePoint_polar_normalized_zero
    (r θ : ℝ) (hr : 0 < r)
    (η : Metric.sphere (0 : ℝ^3) 1) :
    (onePlusThreePoint (r * Real.cos θ)
        ((r * Real.sin θ) • (η : ℝ^3))) 0 /
      ‖onePlusThreePoint (r * Real.cos θ)
        ((r * Real.sin θ) • (η : ℝ^3))‖ =
      Real.cos θ := by
  rw [onePlusThreePoint_zero, onePlusThreePoint_polar_norm r θ hr.le]
  exact mul_div_cancel_left₀ (Real.cos θ) hr.ne'

/-- Fubini and three-dimensional polar integration for the splitting
`ℝ⁴ = ℝ × ℝ³`.
-/
theorem integral_onePlusThreePoint_polar
    (g : ℝ^4 → ℝ) (hg : Integrable g volume) :
    (∫ y : ℝ^4, g y) =
      ∫ t : ℝ, ∫ ρ in Set.Ioi (0 : ℝ), ρ ^ 2 *
        ∫ η : Metric.sphere (0 : ℝ^3) 1,
          g (onePlusThreePoint t
            (ρ • (η : ℝ^3)))
          ∂(volume : Measure (ℝ^3)).toSphere := by
  let e := PDE.Analysis.euclideanSumMeasurableEquiv 1 3
  let G : ℝ^1 × ℝ^3 → ℝ := fun p ↦ g (e.symm p)
  have hG : Integrable G volume := by
    simpa [G, Function.comp_def] using
      ((PDE.Analysis.euclideanSumMeasurableEquiv_measurePreserving 1 3).symm e
        |>.integrable_comp_emb e.symm.measurableEmbedding (g := g)).2 hg
  calc
    (∫ y : ℝ^4, g y) = ∫ t : ℝ^1, ∫ u : ℝ^3, G (t, u) := by
      rw [PDE.Analysis.integral_euclideanSum 1 3 g]
      exact integral_prod G hG
    _ = ∫ t : ℝ^1, ∫ ρ in Set.Ioi (0 : ℝ), ρ ^ 2 * ∫ η : Metric.sphere (0 : ℝ^3) 1,
          g (onePlusThreePoint (t 0) (ρ • (η : ℝ^3))) ∂(volume : Measure (ℝ^3)).toSphere := by
      refine integral_congr_ae (hG.prod_right_ae.mono fun t ht ↦ ?_)
      have hpolar := PDE.Analysis.integral_polar_addHaar_iterated (volume : Measure (ℝ^3))
        (fun u : ℝ^3 ↦ G (t, u)) ht
      have ht' : t = EuclideanSpace.single 0 (t 0) := by ext i; fin_cases i; simp
      simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hpolar
      simpa only [G, e, onePlusThreePoint, ← ht'] using hpolar
    _ = _ := ((PiLp.volume_preserving_ofLp (Fin 1)).trans
        (volume_preserving_funUnique (Fin 1) ℝ)).integral_comp
          ((MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
            (MeasurableEquiv.funUnique (Fin 1) ℝ)).measurableEmbedding fun t ↦
        ∫ ρ in Set.Ioi (0 : ℝ), ρ ^ 2 * ∫ η : Metric.sphere (0 : ℝ^3) 1,
          g (onePlusThreePoint t (ρ • (η : ℝ^3))) ∂(volume : Measure (ℝ^3)).toSphere

/-- The `S²` latitude fiber in the `ℝ ⊕ ℝ³` decomposition has area `4π`.
For an angular function depending only on the normalized distinguished
coordinate, the fiber integral therefore collapses to its value at `cos θ`
times `4π`.
-/
theorem integral_threeSphereLatitudeFiber
    (F : ℝ → ℝ) (r θ : ℝ) (hr : 0 < r) :
    (∫ η : Metric.sphere (0 : ℝ^3) 1,
      F ((onePlusThreePoint (r * Real.cos θ)
          ((r * Real.sin θ) •
            (η : ℝ^3))) 0 /
        ‖onePlusThreePoint (r * Real.cos θ)
          ((r * Real.sin θ) •
            (η : ℝ^3))‖)
      ∂(volume : Measure (ℝ^3)).toSphere) =
      4 * Real.pi * F (Real.cos θ) := by
  have hfun : (fun η : Metric.sphere
      (0 : ℝ^3) 1 ↦
      F ((onePlusThreePoint (r * Real.cos θ)
          ((r * Real.sin θ) •
            (η : ℝ^3))) 0 /
        ‖onePlusThreePoint (r * Real.cos θ)
          ((r * Real.sin θ) •
            (η : ℝ^3))‖)) =
      fun _ ↦ F (Real.cos θ) := by
    funext η
    rw [onePlusThreePoint_polar_normalized_zero r θ hr η]
  rw [hfun, integral_const]
  change PDE.Analysis.unitSphereArea 3 * F (Real.cos θ) = _
  rw [PDE.Analysis.unitSphereArea_three]

/-- Including the `ρ²` Jacobian from three-dimensional polar coordinates,
the latitude fiber contributes the factor `4π r² sin² θ`.
-/
theorem integral_threeSphereLatitudeFiber_withJacobian
    (F : ℝ → ℝ) (r θ : ℝ) (hr : 0 < r) :
    (∫ η : Metric.sphere (0 : ℝ^3) 1,
      (r * Real.sin θ) ^ 2 *
        F ((onePlusThreePoint (r * Real.cos θ)
            ((r * Real.sin θ) •
              (η : ℝ^3))) 0 /
          ‖onePlusThreePoint (r * Real.cos θ)
            ((r * Real.sin θ) •
              (η : ℝ^3))‖)
      ∂(volume : Measure (ℝ^3)).toSphere) =
      4 * Real.pi * r ^ 2 * Real.sin θ ^ 2 * F (Real.cos θ) := by
  rw [integral_const_mul,
    integral_threeSphereLatitudeFiber F r θ hr]
  ring

/-- The latitude-fiber formula with an additional radial multiplier.  The
orthogonal norm identity makes the multiplier constant on the entire fiber.
-/
theorem integral_threeSphereLatitudeFiber_radial
    (a F : ℝ → ℝ) (r θ : ℝ) (hr : 0 < r) :
    (∫ η : Metric.sphere (0 : ℝ^3) 1,
      (r * Real.sin θ) ^ 2 *
        (a ‖onePlusThreePoint (r * Real.cos θ)
            ((r * Real.sin θ) •
              (η : ℝ^3))‖ *
          F ((onePlusThreePoint (r * Real.cos θ)
              ((r * Real.sin θ) •
                (η : ℝ^3))) 0 /
            ‖onePlusThreePoint (r * Real.cos θ)
              ((r * Real.sin θ) •
                (η : ℝ^3))‖))
      ∂(volume : Measure (ℝ^3)).toSphere) =
      4 * Real.pi * r ^ 2 * Real.sin θ ^ 2 *
        (a r * F (Real.cos θ)) := by
  convert integral_threeSphereLatitudeFiber_withJacobian
    (fun u ↦ a r * F u) r θ hr using 1
  apply integral_congr_ae
  filter_upwards [] with η
  rw [onePlusThreePoint_polar_norm r θ hr.le]

/-- A bounded measurable angular function has an integrable extension over a
finite four-dimensional radial ball.  This is the domination input used to
justify both Fubini decompositions in the latitude argument.
-/
theorem integrable_closedBall_angularExtension
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ u, |F u| ≤ C) :
    Integrable ((Metric.closedBall
        (0 : ℝ^4) 1).indicator
      (fun Y ↦ F (Y 0 / ‖Y‖))) volume := by
  let q : ℝ^4 → ℝ := fun Y ↦ F (Y 0 / ‖Y‖)
  have hcoord : Measurable (fun Y : ℝ^4 ↦ Y 0) := by
    fun_prop
  have hq : AEStronglyMeasurable q volume :=
    (hF.comp (hcoord.div measurable_norm)).aestronglyMeasurable
  have hqOn : IntegrableOn q
      (Metric.closedBall (0 : ℝ^4) 1) volume := by
    refine Measure.integrableOn_of_bounded (M := C)
      measure_closedBall_lt_top.ne hq ?_
    filter_upwards [] with Y
    simpa [q, Real.norm_eq_abs] using hC (Y 0 / ‖Y‖)
  exact (integrable_indicator_iff measurableSet_closedBall).2 hqOn

/-- The radial integral `∫₀¹ r³ dr = 1/4` of four-dimensional polar coordinates. -/
private theorem integral_Ioc_zero_one_pow_three : (∫ r in Set.Ioc (0 : ℝ) 1, r ^ 3) = 1 / 4 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  cas

/-- Four-dimensional polar integration of the bounded angular extension.
The radial integral over the unit ball is exactly `∫₀¹ r³ dr = 1/4`.
-/
theorem integral_closedBall_angularExtension_polar
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ u, |F u| ≤ C) :
    (∫ Y : ℝ^4,
      (Metric.closedBall (0 : ℝ^4) 1).indicator
        (fun Z ↦ F (Z 0 / ‖Z‖)) Y) =
      (1 / 4 : ℝ) *
        ∫ σ : Metric.sphere (0 : ℝ^4) 1,
          F ((σ : ℝ^4) 0)
          ∂(volume : Measure (ℝ^4)).toSphere := by
  set S : ℝ := ∫ σ : Metric.sphere (0 : ℝ^4) 1, F ((σ : ℝ^4) 0)
    ∂(volume : Measure (ℝ^4)).toSphere
  -- on the sphere of radius `r`, the angular extension is `F (σ 0)` inside the ball, `0` outside
  have hinner (r : ℝ) (hr : r ∈ Set.Ioi (0 : ℝ)) :
      (∫ σ : Metric.sphere (0 : ℝ^4) 1,
        (Metric.closedBall (0 : ℝ^4) 1).indicator (fun Z ↦ F (Z 0 / ‖Z‖)) (r • (σ : ℝ^4))
        ∂(volume : Measure (ℝ^4)).toSphere) = if r ≤ 1 then S else 0 := by
    have hσ (σ : Metric.sphere (0 : ℝ^4) 1) : ‖r • (σ : ℝ^4)‖ = r := by
      rw [norm_smul, mem_sphere_zero_iff_norm.mp σ.property, mul_one, Real.norm_eq_abs,
        abs_of_pos hr]
    by_cases hr1 : r ≤ 1 <;>
      simp [hσ, hr1, S, mul_div_cancel_left₀ _ (ne_of_gt hr)]
  have hp := PDE.Analysis.integral_polar_addHaar_iterated (volume : Measure (ℝ^4)) _
    (integrable_closedBall_angularExtension F hF C hC)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hp
  calc _ = ∫ r in Set.Ioi (0 : ℝ), (Set.Iic (1 : ℝ)).indicator (fun r ↦ r ^ 3 * S) r := by
        rw [hp]
        refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        rw [hinner r hr]
        by_cases hr1 : r ≤ 1 <;> simp [hr1]
    _ = (1 / 4 : ℝ) * S := by
        rw [setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic, integral_mul_const,
          integral_Ioc_zero_one_pow_three]

/-- The `S²` fiber formula before making the planar polar substitution.  It
expresses the angular average at arbitrary cylindrical coordinates `(t,ρ)`.
-/
theorem integral_threeSphereFiber
    (F : ℝ → ℝ) (t ρ : ℝ) :
    (∫ η : Metric.sphere (0 : ℝ^3) 1,
      F ((onePlusThreePoint t
          (ρ • (η : ℝ^3))) 0 /
        ‖onePlusThreePoint t
          (ρ • (η : ℝ^3))‖)
      ∂(volume : Measure (ℝ^3)).toSphere) =
      4 * Real.pi * F (t / √(t ^ 2 + ρ ^ 2)) := by
  have hfun : (fun η : Metric.sphere
      (0 : ℝ^3) 1 ↦
      F ((onePlusThreePoint t
          (ρ • (η : ℝ^3))) 0 /
        ‖onePlusThreePoint t
          (ρ • (η : ℝ^3))‖)) =
      fun _ ↦ F (t / √(t ^ 2 + ρ ^ 2)) := by
    funext η
    rw [onePlusThreePoint_zero,
      onePlusThreePoint_smul_sphere_norm]
  rw [hfun, integral_const]
  change PDE.Analysis.unitSphereArea 3 *
      F (t / √(t ^ 2 + ρ ^ 2)) = _
  rw [PDE.Analysis.unitSphereArea_three]

/-- The explicit planar density obtained after integrating the `S²` fiber is
integrable on the unit disk.  Its `ρ²` factor is the three-dimensional radial
Jacobian.
-/
theorem integrable_closedBall_cylindricalAngularDensity
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ u, |F u| ≤ C) :
    Integrable ((Metric.closedBall
        (0 : ℝ^2) 1).indicator
      (fun p ↦ 4 * Real.pi * p 1 ^ 2 *
        F (p 0 / ‖p‖))) volume := by
  let q : ℝ^2 → ℝ := fun p ↦
    4 * Real.pi * p 1 ^ 2 * F (p 0 / ‖p‖)
  have hqMeas : AEStronglyMeasurable q volume := by
    have h0 : Measurable (fun p : ℝ^2 ↦ p 0) := by fun_prop
    exact (measurable_const.mul ((by fun_prop : Measurable (fun p : ℝ^2 ↦ p 1)).pow_const 2)
      |>.mul (hF.comp (h0.div measurable_norm))).aestronglyMeasurable
  have hqOn : IntegrableOn q
      (Metric.closedBall (0 : ℝ^2) 1) volume := by
    refine Measure.integrableOn_of_bounded (M := 4 * Real.pi * C)
      measure_closedBall_lt_top.ne hqMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with p hp
    have hp1 : p 1 ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2
      ((PiLp.norm_apply_le p 1).trans (by simpa [dist_zero_right] using hp))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (by positivity : 0 < 4 * Real.pi),
      sq_abs]
    calc 4 * Real.pi * p 1 ^ 2 * |F (p 0 / ‖p‖)| ≤ 4 * Real.pi * 1 * C := by gcongr; exact hC _
      _ = 4 * Real.pi * C := by ring
  exact (integrable_indicator_iff measurableSet_closedBall).2 hqOn

/-- Pointwise identification of the cylindrical `S²` average with the
explicit planar density used for Fubini and the upper-half-plane polar map.
-/
theorem closedBall_angularExtension_threeFiber
    (F : ℝ → ℝ) (t ρ : ℝ) :
    ρ ^ 2 *
      (∫ η : Metric.sphere (0 : ℝ^3) 1,
        (Metric.closedBall (0 : ℝ^4) 1).indicator
          (fun Y ↦ F (Y 0 / ‖Y‖))
          (onePlusThreePoint t
            (ρ • (η : ℝ^3)))
        ∂(volume : Measure (ℝ^3)).toSphere) =
      if √(t ^ 2 + ρ ^ 2) ≤ 1 then
        4 * Real.pi * ρ ^ 2 * F (t / √(t ^ 2 + ρ ^ 2))
      else 0 := by
  have hmem (η : Metric.sphere (0 : ℝ^3) 1) : onePlusThreePoint t (ρ • (η : ℝ^3)) ∈
      Metric.closedBall (0 : ℝ^4) 1 ↔ √(t ^ 2 + ρ ^ 2) ≤ 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, onePlusThreePoint_smul_sphere_norm]
  by_cases hrad : √(t ^ 2 + ρ ^ 2) ≤ 1
  · simp_rw [Set.indicator_of_mem ((hmem _).2 hrad), integral_threeSphereFiber F t ρ,
      ite_eq_left hrad]
    ring
  · simp_rw [Set.indicator_of_notMem (mt (hmem _).1 hrad), ite_eq_right hrad]
    simp

/-- The four-dimensional ball integral equals the explicit cylindrical
upper-half-plane integral after the `S²` fiber has been evaluated.
-/
theorem integral_closedBall_angularExtension_cylindrical
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ u, |F u| ≤ C) :
    (∫ Y : ℝ^4,
      (Metric.closedBall (0 : ℝ^4) 1).indicator
        (fun Z ↦ F (Z 0 / ‖Z‖)) Y) =
      ∫ p in {p : ℝ × ℝ | 0 < p.2},
        (Metric.closedBall (0 : (ℝ^2)) 1).indicator
          (fun y ↦ 4 * Real.pi * y 1 ^ 2 * F (y 0 / ‖y‖))
          (PDE.Analysis.planeEquiv.symm p) := by
  rw [integral_onePlusThreePoint_polar _ (integrable_closedBall_angularExtension F hF C hC),
    integral_pair_upperHalfPlane_iterated _
      (integrable_closedBall_cylindricalAngularDensity F hF C hC)]
  refine integral_congr_ae (.of_forall fun t ↦
    setIntegral_congr_fun measurableSet_Ioi fun ρ _ ↦ ?_)
  have hynorm : ‖EuclideanSpace.single (0 : Fin 2) t + EuclideanSpace.single 1 ρ‖ =
      √(t ^ 2 + ρ ^ 2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, add_comm]
  rw [closedBall_angularExtension_threeFiber, PDE.Analysis.planeEquiv_symm_apply_eq_add]
  by_cases hrad : √(t ^ 2 + ρ ^ 2) ≤ 1
  · rw [ite_eq_left hrad, Set.indicator_of_mem (by
      simpa [Metric.mem_closedBall, dist_zero_right, hynorm] using hrad)]
    simp [hynorm]
  · rw [ite_eq_right hrad, Set.indicator_of_notMem (by
      simpa [Metric.mem_closedBall, dist_zero_right, hynorm] using hrad)]

/-- Latitude formula for `S³`, with the exact surface-measure normalization
used by the five-dimensional Newtonian kernel.
-/
theorem integral_sphereThree_latitude
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ u, |F u| ≤ C) :
    (∫ σ : Metric.sphere (0 : ℝ^4) 1,
      F ((σ : ℝ^4) 0)
      ∂(volume : Measure (ℝ^4)).toSphere) =
      4 * Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ ^ 2 * F (Real.cos θ) := by
  let Q : ℝ × ℝ → ℝ := fun p ↦ (Metric.closedBall (0 : (ℝ^2)) 1).indicator
    (fun y ↦ 4 * Real.pi * y 1 ^ 2 * F (y 0 / ‖y‖)) (PDE.Analysis.planeEquiv.symm p)
  have hpolarPoint (p : ℝ × ℝ) (hp : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi) :
      p.1 * Q (p.1 * Real.cos p.2, p.1 * Real.sin p.2) =
        (Set.Iic (1 : ℝ)).indicator (fun r ↦ 4 * Real.pi * r ^ 3) p.1 *
          (Real.sin p.2 ^ 2 * F (Real.cos p.2)) := by
    have hr : 0 < p.1 := hp.1
    have hnorm : √((p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2) = p.1 := by
      rw [show (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 by
        linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq p.2, Real.sqrt_sq hr.le]
    by_cases hr1 : p.1 ≤ 1
    · simpa [Q, PDE.Analysis.planeEquiv_symm_apply_eq_add, Metric.mem_closedBall,
        dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two, hnorm, hr1] using
        (show p.1 * (4 * Real.pi * (p.1 * Real.sin p.2) ^ 2 * F (p.1 * Real.cos p.2 / p.1)) =
          4 * Real.pi * p.1 ^ 3 * (Real.sin p.2 ^ 2 * F (Real.cos p.2)) by
          rw [mul_div_cancel_left₀ _ hr.ne']; ring)
    · simp [Q, PDE.Analysis.planeEquiv_symm_apply_eq_add, Metric.mem_closedBall,
        dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two, hnorm, hr1]
  -- the radial factor integrates to `π`, the angular factor is the latitude integral
  have hD : (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
      p.1 * Q (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) =
      Real.pi * ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 2 * F (Real.cos θ) := by
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hpolarPoint,
      Measure.volume_eq_prod, setIntegral_prod_mul ((Set.Iic (1 : ℝ)).indicator _)
        (fun θ ↦ Real.sin θ ^ 2 * F (Real.cos θ)), setIntegral_indicator measurableSet_Iic,
      Set.Ioi_inter_Iic, integral_const_mul, integral_Ioc_zero_one_pow_three,
      intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]
    ring
  have h := (integral_closedBall_angularExtension_polar F hF C hC).symm.trans
    ((integral_closedBall_angularExtension_cylindrical F hF C hC).trans
      ((PDE.Analysis.integral_upperHalfPlane_polar Q).trans hD))
  linarith

end PDE.Analysis
