/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.MeridionalBlock
public import PDE.Fluid.Stokes.Ball.Azimuthal
public import PDE.Fluid.Stokes.Ball.ModeSpan
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PDE.Analysis.SpecialFunctions.Legendre.SphereExpansion

/-!
# Weak Neumann-Stokes eigenfunctions lie in the closed span of the modes

Let `u` be a weak eigenfunction of the Neumann-type Stokes problem on the ball `B(0, R)` in
one of the two axisymmetric sectors: `u` and its weak derivatives are square integrable, `u` is
weakly divergence free, invariant under rotations about the symmetry axis and of parity
`sectorSign odd` under the equatorial reflection, and `∫ ∇u : ∇v = μ ∫ ⟪u, v⟫` for every smooth
divergence-free field `v` of the same sector. Then the `L²(B)` class of `u` lies in the closed
linear span of the modes of eigenvalue `μ` (`eigen_mem_closure_modes`).

## How it works

We separate variables. An equivariant representative `w` of `u` has, at almost every radius, a
square-integrable meridian profile, whose vector harmonic expansion converges in `L²(sin θ dθ)`. In
each degree `l ≥ 1` the azimuthal coefficient is that of a multiple of an azimuthal mode of
eigenvalue `μ` (`meridianCoefficient_azimuthal_of_weak_eigen`) and the two meridional coefficients
are those of a multiple of a meridional mode of eigenvalue `μ` (`meridional_block_of_weak_eigen`);
the radial coefficient of degree zero vanishes by the divergence relation. The partial sums of these
mode multiples converge to `u` in `L²(B)`, by dominated convergence in the radius with the bound
`4 ‖w(r ·)‖²` from Bessel's inequality.

Hou, Wang and Yang expand in vector spherical harmonics in the same way in the proof of their
Lemma 4 (Appendix E, Step 2). We carry out the expansion for weak eigenfunctions and prove the
convergence of the partial sums.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 6.2, Lemma 4, pp. 50-51,
  and Appendix E, Steps 2-5 of the proof of Lemma 4, pp. 63-65.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial Filter
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff Topology

namespace PDE.Fluid.Stokes.Ball

/-- The azimuthal mode on the meridian: `(c • ψ)(point r θ 0) = c Z(r) Z_l(θ)`. -/
theorem smul_mode_azimuthal_point (c R : ℝ) (l : ℕ) (α r θ : ℝ) :
    (c • mode R .azimuthal l α) (point r θ 0) =
      ∑ k, (![0, 0, c * azimuthalProfile R l α r] : Fin 3 → ℝ) k • vectorHarmonic l k θ := by
  rw [Pi.smul_apply, mode_azimuthal_point, Fin.sum_univ_three]
  simp only [vectorHarmonic, vectorHarmonicProfile, frame, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    smul_smul, show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  simp only [zero_mul, zero_smul, zero_add, mul_assoc]

/-- The meridional mode on the meridian, in vector harmonics of degree `l`. -/
theorem smul_mode_meridional_point (c R : ℝ) (l : ℕ) (α r θ : ℝ) :
    (c • mode R .meridional l α) (point r θ 0) =
      ∑ k, (![c * radialProfile l (meridionalFactorA l ((α / R) ^ 2))
        (fun s ↦ meridionalFactorB l ((α / R) ^ 2) s + boundaryCoefficient l α) r,
        c * polarProfile l (fun s ↦ meridionalFactorB l ((α / R) ^ 2) s +
          boundaryCoefficient l α) r, 0] : Fin 3 → ℝ) k • vectorHarmonic l k θ := by
  rw [Pi.smul_apply, mode_meridional_eq, meridionalTest_point, Fin.sum_univ_three]
  simp only [radialProfile, polarProfile, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_smul, add_zero, smul_add,
    smul_smul]

/-- **The azimuthal block of a weak eigenfunction.** For a weak eigenfunction of azimuthal
parity and degree `l ≥ 1`, the meridian coefficient of `w` on `Z_l` is almost everywhere that of
`c • mode R .azimuthal l α`, where `c = 0` or `α` is a root of the azimuthal boundary function
with `(α / R)² = μ`. -/
theorem azimuthal_block_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
    (hpar : modeParity .azimuthal l = ε) {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = ε • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w) :
    ∃ c α : ℝ, (c = 0 ∨ (boundaryFunction .azimuthal l α = 0 ∧ (α / R) ^ 2 = μ)) ∧
      meridianCoefficient w l 2 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (c • mode R .azimuthal l α) l 2 := by
  obtain ⟨A, hA, hcase⟩ := meridianCoefficient_azimuthal_of_weak_eigen hR hl hpar hu hDu hweak
    heig hwm hw hwint huw
  have hcoef (c α r : ℝ) : meridianCoefficient (c • mode R .azimuthal l α) l 2 r =
      c * azimuthalProfile R l α r * vectorHarmonicNormSq l 2 := by
    rw [meridianCoefficient_eq_of_point (smul_mode_azimuthal_point c R l α r)]
    simp
  have hN2 : 0 < vectorHarmonicNormSq l 2 := by
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    simp only [vectorHarmonicNormSq, show (2 : Fin 3) ≠ 0 by decide, ↓reduceIte]
    positivity
  rcases hcase with hA0 | ⟨hμ, hbF⟩
  · subst hA0
    refine ⟨0, 0, Or.inl rfl, ?_⟩
    filter_upwards [hA] with r hr
    rw [hr, hcoef]
    ring
  · set α := √μ * R with hα
    have hαR : (α / R) ^ 2 = μ := by
      rw [hα, mul_div_assoc, div_self hR.ne', mul_one, Real.sq_sqrt hμ.le]
    refine ⟨A / vectorHarmonicNormSq l 2, α, Or.inr ⟨hbF, hαR⟩, ?_⟩
    filter_upwards [hA] with r hr
    rw [hr, hcoef, azimuthalProfile, besselRadial, besselFactor, radialSolution, hαR]
    field_simp

/-- **The radial coefficient of degree zero vanishes.** For a weakly divergence-free field with
equivariant representative `w`, the meridian coefficient of `w` on `Y_0` vanishes almost
everywhere on `(0, R)`: the divergence relation with the tests `f(‖x‖²)`, which need not
vanish at the origin, gives `∫ r³ ψ(r) a(r) dr = 0` for every test `ψ`. -/
theorem meridianCoefficient_degree_zero_of_weak {R : ℝ} (hR : 0 < R) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w) :
    meridianCoefficient w 0 0 =ᵐ[volume.restrict (Ioo 0 R)] 0 := by
  set a := meridianCoefficient w 0 0 with ha
  have hal := locallyIntegrableOn_meridianCoefficient hwm hw hwint 0 0
  have hb0 : ∀ r, meridianCoefficient w 0 1 r = 0 := by
    intro r
    simp [meridianCoefficient, vectorHarmonic, vectorHarmonicProfile, zonalHarmonicDeriv_zero]
  set q : ℝ → ℝ := fun r ↦ r ^ 3 * a r with hq
  have hql : LocallyIntegrableOn q (Ioo 0 R) :=
    hal.continuousOn_mul (g := fun r : ℝ ↦ r ^ 3) (continuous_pow 3).continuousOn
      isOpen_Ioo.isLocallyClosed
  have hq0 := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hql fun ψ hψ hψcs hψs ↦ by
    have hzero {x : ℝ} (hx : x ∉ Ioo 0 R) : ψ x • q x = 0 := by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψs h), zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo 0 R) fun x hx ↦ hzero hx]
    obtain ⟨F, hF, -, -, -, hFψ⟩ := exists_pow_mul_comp_sq_eq hR hψ hψcs hψs 0
    set f : ℝ → ℝ := fun s ↦ ∫ t in R ^ 2..s, F t with hf
    have hfd : deriv f = F := funext fun s ↦ Continuous.deriv_integral F hF.continuous (R ^ 2) s
    have hfC : ContDiff ℝ ∞ f := by
      rw [contDiff_infty_iff_deriv, hfd]
      exact ⟨fun s ↦ (hF.continuous.integral_hasStrictDerivAt _ s).hasDerivAt.differentiableAt,
        hF⟩
    have hfR : f (R ^ 2) = 0 := intervalIntegral.integral_same
    have hD := integral_divergence_meridian hR 0 hu hDu hweak hdiv hwm hw hwint huw hfC hfR
    simp only [hb0, mul_zero, add_zero, hfd, CharP.cast_eq_zero, zero_mul, zero_add] at hD
    have h2 : ∫ r in Ioo 0 R, ψ r • q r = (1 / 2) * ∫ r in Ioo 0 R, r ^ 2 *
        (r ^ (0 + 1) * (2 * F (r ^ 2)) * a r) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      have h := hFψ r hr.1
      simp only [pow_zero, one_mul] at h
      simp only [hq, smul_eq_mul, ← h]
      ring
    rw [h2, hD, mul_zero]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mpr hq0,
    ae_restrict_mem measurableSet_Ioo] with r hr hrI
  simp only [hq] at hr
  exact (mul_eq_zero.mp hr).resolve_left (pow_ne_zero 3 hrI.1.ne')


private theorem meridianCoefficient_zero_fun (l : ℕ) (k : Fin 3) (r : ℝ) :
    meridianCoefficient (fun _ ↦ (0 : ℝ^3)) l k r = 0 := by
  simp [meridianCoefficient]

/-- A combination of a meridional and an azimuthal mode of degree `l`, each with a zero
coefficient or a root of eigenvalue `μ` and the parity of the sector, has its `L²(B)` class in
the span of the modes. -/
theorem toLp_smul_add_smul_mem_span {R μ : ℝ} {odd : Bool} {l : ℕ} (hl : 1 ≤ l)
    {c α c' α' : ℝ} (h : c = 0 ∨ (boundaryFunction .meridional l α = 0 ∧ (α / R) ^ 2 = μ ∧
      modeParity .meridional l = sectorSign odd))
    (h' : c' = 0 ∨ (boundaryFunction .azimuthal l α' = 0 ∧ (α' / R) ^ 2 = μ ∧
      modeParity .azimuthal l = sectorSign odd)) :
    (((memLp_mode R .meridional l α).const_smul c).add
      ((memLp_mode R .azimuthal l α').const_smul c')).toLp
        (c • mode R .meridional l α + c' • mode R .azimuthal l α') ∈
      Submodule.span ℝ (ballModes R μ odd) := by
  rw [MemLp.toLp_add ((memLp_mode R .meridional l α).const_smul c)
    ((memLp_mode R .azimuthal l α').const_smul c'),
    MemLp.toLp_const_smul c (memLp_mode R .meridional l α),
    MemLp.toLp_const_smul c' (memLp_mode R .azimuthal l α')]
  refine Submodule.add_mem _ ?_ ?_
  · rcases h with rfl | ⟨hb, hμ, hp⟩
    · simp
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (toLp_mode_mem_ballModes hb hμ hl hp))
  · rcases h' with rfl | ⟨hb, hμ, hp⟩
    · simp
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (toLp_mode_mem_ballModes hb hμ hl hp))

/-- **The blocks of a weak eigenfunction.** For a weak eigenfunction in the sector `odd` with
equivariant representative `w` of parity `sectorSign odd`, every degree `l` has a smooth
equivariant field `Z`, a combination of modes of eigenvalue `μ`, whose values on the meridian
at almost every radius are the degree-`l` part `∑ₖ (a_{l,k}(r) / ‖X_{l,k}‖²) X_{l,k}` of the
vector harmonic expansion of `w`. -/
theorem exists_degree_block_of_weak_eigen {R μ : ℝ} (hR : 0 < R) (odd : Bool)
    {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = sectorSign odd • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwpar : ∀ x, w (equatorialReflection x) = sectorSign odd • equatorialReflection (w x))
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w)
    {e : ℝ^3 → ℝ^3} (hem : Measurable e) (he : IsEquivariantUnderAxisRotation e)
    (heint : IntegrableOn e (Metric.ball (0 : ℝ^3) R))
    (hepair : ∀ Φ : ℝ^3 → ℝ^3, Continuous Φ → IsEquivariantUnderAxisRotation Φ →
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪e x, Φ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, Φ x⟫) (l : ℕ) :
    ∃ Z : ℝ^3 → ℝ^3, ContDiff ℝ ∞ Z ∧ IsEquivariantUnderAxisRotation Z ∧
      (∃ hZ : MemLp Z 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)),
        hZ.toLp Z ∈ Submodule.span ℝ (ballModes R μ odd)) ∧
      ∀ᵐ r ∂(volume.restrict (Ioo 0 R)), ∀ θ, Z (point r θ 0) =
        ∑ k, (meridianCoefficient w l k r / vectorHarmonicNormSq l k) • vectorHarmonic l k θ := by
  set ε := sectorSign odd with hε
  rcases Nat.eq_zero_or_pos l with hl0 | hl
  · -- degree zero
    subst hl0
    refine ⟨0, contDiff_zero_fun, fun θ x ↦ by simp [← axialRotation_apply], ?_, ?_⟩
    · exact ⟨MemLp.zero, by rw [MemLp.toLp_zero]; exact Submodule.zero_mem _⟩
    · filter_upwards [meridianCoefficient_degree_zero_of_weak hR hu hDu hweak hdiv hwm hw hwint
        huw] with r hr θ
      have hv (k : Fin 3) (hk : k ≠ 0) : vectorHarmonic 0 k θ = 0 := by
        simp [vectorHarmonic, vectorHarmonicProfile, hk, zonalHarmonicDeriv_zero]
      rw [Fin.sum_univ_three, hv 1 (by decide), hv 2 (by decide), hr]
      simp
  -- the meridional block
  have hmer : ∃ c α : ℝ, (c = 0 ∨ (boundaryFunction .meridional l α = 0 ∧ (α / R) ^ 2 = μ ∧
      modeParity .meridional l = ε)) ∧
      meridianCoefficient w l 0 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (c • mode R .meridional l α) l 0 ∧
      meridianCoefficient w l 1 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (c • mode R .meridional l α) l 1 := by
    by_cases hp : modeParity .meridional l = ε
    · obtain ⟨c, α, hc, h0, h1⟩ := meridional_block_of_weak_eigen hR hl hp hu hDu hweak hdiv heig
        hwm hw hwint huw hem he heint hepair
      exact ⟨c, α, hc.imp_right fun h ↦ ⟨h.1, h.2, hp⟩, h0, h1⟩
    · refine ⟨0, 0, Or.inl rfl, ?_, ?_⟩ <;>
      · refine ae_of_all _ fun r ↦ ?_
        rw [zero_smul, meridianCoefficient_eq_zero_of_parity hwpar ?_ r]
        · exact (meridianCoefficient_zero_fun _ _ r).symm
        · exact fun h ↦ hp (by rw [h]; simp [vectorHarmonicParity, modeParity])
  -- the azimuthal block
  have haz : ∃ c α : ℝ, (c = 0 ∨ (boundaryFunction .azimuthal l α = 0 ∧ (α / R) ^ 2 = μ ∧
      modeParity .azimuthal l = ε)) ∧
      meridianCoefficient w l 2 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (c • mode R .azimuthal l α) l 2 := by
    by_cases hp : modeParity .azimuthal l = ε
    · obtain ⟨c, α, hc, h2⟩ := azimuthal_block_of_weak_eigen hR hl hp hu hDu hweak heig hwm hw
        hwint huw
      exact ⟨c, α, hc.imp_right fun h ↦ ⟨h.1, h.2, hp⟩, h2⟩
    · refine ⟨0, 0, Or.inl rfl, ae_of_all _ fun r ↦ ?_⟩
      rw [zero_smul, meridianCoefficient_eq_zero_of_parity hwpar ?_ r]
      · exact (meridianCoefficient_zero_fun _ _ r).symm
      · exact fun h ↦ hp (by rw [h]; simp [vectorHarmonicParity, modeParity])
  obtain ⟨c, α, hc, ha0, ha1⟩ := hmer
  obtain ⟨c', α', hc', ha2⟩ := haz
  refine ⟨c • mode R .meridional l α + c' • mode R .azimuthal l α',
    (contDiff_const.smul (mode_contDiff R _ l α)).add
      (contDiff_const.smul (mode_contDiff R _ l α')),
    fun θ x ↦ ?_, ⟨_, toLp_smul_add_smul_mem_span hl hc hc'⟩, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, mode_axisRotation]
    simp only [← axialRotation_apply, map_add, map_smul]
  · have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hN (k : Fin 3) : vectorHarmonicNormSq l k ≠ 0 := by
      unfold vectorHarmonicNormSq
      split_ifs <;> positivity
    filter_upwards [ha0, ha1, ha2] with r h0 h1 h2 θ
    rw [meridianCoefficient_eq_of_point (smul_mode_meridional_point c R l α r)] at h0 h1
    rw [meridianCoefficient_eq_of_point (smul_mode_azimuthal_point c' R l α' r)] at h2
    simp only [↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    rw [Pi.add_apply, smul_mode_meridional_point, smul_mode_azimuthal_point,
      ← Finset.sum_add_distrib, Fin.sum_univ_three, Fin.sum_univ_three, h0, h1, h2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ← add_smul, mul_div_cancel_right₀ _ (hN _), add_zero,
      zero_add]

/-- The vector harmonic coefficients of the meridian profile at radius `r` are the meridian
coefficients divided by the squared norms. -/
theorem vectorHarmonicCoeff_meridian {W : ℝ^3 → ℝ^3} {r : ℝ}
    (hv : MemLp (fun θ ↦ W (point r θ 0)) 2 polarAngleMeasure) (l : ℕ) (k : Fin 3) :
    vectorHarmonicCoeff (hv.toLp _) l k =
      meridianCoefficient W l k r / vectorHarmonicNormSq l k := by
  rw [vectorHarmonicCoeff_toLp, meridianCoefficient]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [vectorHarmonic, real_inner_smul_right, real_inner_comm]

/-- **Weak Neumann-Stokes eigenfunctions lie in the closed span of the modes.** Let `u` be
square integrable on the ball `B(0, R)` with square-integrable weak derivatives `Du`, weakly
divergence free, invariant under the rotations about the symmetry axis and of parity
`sectorSign odd` under the equatorial reflection, almost everywhere, and let
`∫ ∇u : ∇v = μ ∫ ⟪u, v⟫` for every smooth divergence-free equivariant field `v` of the same
parity. Then the `L²(B)` class of `u` lies in the closed linear span of the classes of the modes
of eigenvalue `μ`. -/
theorem eigen_mem_closure_modes {R μ : ℝ} (hR : 0 < R) (odd : Bool) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : MemLp u 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)))
    (hDu : ∀ i j, MemLp (Du i j) 2 (volume.restrict (Metric.ball (0 : ℝ^3) R)))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    (hrot : ∀ θ, ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      u (axisRotation θ x) = axisRotation θ (u x))
    (hrefl : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      u (equatorialReflection x) = sectorSign odd • equatorialReflection (u x))
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = sectorSign odd • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫) :
    hu.toLp u ∈ (Submodule.span ℝ (ballModes R μ odd)).topologicalClosure := by
  set B := Metric.ball (0 : ℝ^3) R with hBdef
  have hfinB : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using measure_ball_lt_top⟩
  have hu1 : Integrable u (volume.restrict B) := hu.integrable one_le_two
  have hui (i : Fin 3) : IntegrableOn (fun x ↦ u x i) B :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).integrable_comp hu1
  have hDu1 (i j : Fin 3) : IntegrableOn (Du i j) B := (hDu i j).integrable one_le_two
  obtain ⟨w, hwsm, hw, hwpar, huw⟩ :=
    exists_equivariant_representative_ball (sectorSign_sq odd) hu.aestronglyMeasurable hrot hrefl
  have hwm : Measurable w := hwsm.measurable
  have hwint : IntegrableOn w B := hu1.congr huw
  have hw2 : MemLp w 2 (volume.restrict B) := hu.ae_eq huw
  obtain ⟨e, hem, he, heint, hepair⟩ := exists_average_representative (integrableOn_eulerField hDu1)
  -- the blocks of every degree
  choose Z hZC hZeq hZmem hZpt using fun l ↦ exists_degree_block_of_weak_eigen hR odd hui hDu1
    hweak hdiv heig hwm hw hwpar hwint huw hem he heint hepair l
  set S : ℕ → ℝ^3 → ℝ^3 := fun N x ↦ ∑ l ∈ Finset.range N, Z l x with hS
  have hSsucc (N : ℕ) : S (N + 1) = S N + Z N := by
    funext x
    simp only [hS, Finset.sum_range_succ, Pi.add_apply]
  have hSmem : ∀ N, ∃ h : MemLp (S N) 2 (volume.restrict B),
      h.toLp (S N) ∈ Submodule.span ℝ (ballModes R μ odd) := by
    intro N
    induction N with
    | zero =>
      rw [show S 0 = 0 by funext x; simp [hS]]
      exact ⟨MemLp.zero, by rw [MemLp.toLp_zero]; exact Submodule.zero_mem _⟩
    | succ N ih =>
      obtain ⟨⟨h, hmem⟩, hz, hzmem⟩ := And.intro ih (hZmem N)
      rw [hSsucc]
      exact ⟨h.add hz, by rw [MemLp.toLp_add h hz]; exact Submodule.add_mem _ hmem hzmem⟩
  choose hSm hSspan using hSmem
  have hSC (N : ℕ) : Continuous (S N) :=
    continuous_finsetSum _ fun l _ ↦ (hZC l).continuous
  have hSeq (N : ℕ) : IsEquivariantUnderAxisRotation (S N) := by
    intro θ x
    simp only [hS]
    rw [Finset.sum_congr rfl fun l _ ↦ hZeq l θ x, ← axialRotation_apply, map_sum]
    rfl
  -- the good radii
  have hgood : ∀ᵐ r ∂(volume.restrict (Ioo 0 R)),
      ∃ hv : MemLp (fun θ ↦ w (point r θ 0)) 2 polarAngleMeasure, ∀ N θ,
        S N (point r θ 0) = ∑ l ∈ Finset.range N, ∑ k : Fin 3,
          vectorHarmonicCoeff (hv.toLp _) l k • vectorHarmonic l k θ := by
    filter_upwards [ae_memLp_meridian hwm hw hw2, ae_all_iff.mpr hZpt] with r hv hpt
    refine ⟨hv, fun N θ ↦ ?_⟩
    simp only [hS, vectorHarmonicCoeff_meridian hv]
    exact Finset.sum_congr rfl fun l _ ↦ hpt l θ
  -- the squared distances in polar form
  set g : ℕ → ℝ^3 → ENNReal := fun N ↦ B.indicator fun x ↦ ENNReal.ofReal (‖w x - S N x‖ ^ 2)
    with hg
  set gw : ℝ^3 → ENNReal := B.indicator fun x ↦ ENNReal.ofReal (‖w x‖ ^ 2) with hgw
  have hginv (N : ℕ) : IsInvariantUnderAxisRotation (g N) :=
    (isInvariantUnderAxisRotation_comp_norm_sub hw (hSeq N)
      fun t ↦ ENNReal.ofReal (t ^ 2)).indicator_ball R
  have hgwinv : IsInvariantUnderAxisRotation gw :=
    (isInvariantUnderAxisRotation_comp_norm hw fun t ↦ ENNReal.ofReal (t ^ 2)).indicator_ball R
  have hgm (N : ℕ) : Measurable (g N) :=
    (((hwm.sub (hSC N).measurable).norm.pow_const 2).ennreal_ofReal).indicator
      Metric.isOpen_ball.measurableSet
  have hgwm : Measurable gw :=
    ((hwm.norm.pow_const 2).ennreal_ofReal).indicator Metric.isOpen_ball.measurableSet
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ℝ → ENNReal, H = fun N r ↦
      ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * g N (point r θ 0) := ⟨_, rfl⟩
  obtain ⟨Hw, hHw⟩ : ∃ Hw : ℝ → ENNReal, Hw = fun r ↦
      ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * gw (point r θ 0) := ⟨_, rfl⟩
  have hpair : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.1 ^ 2 * sin p.2) :=
    ((continuous_fst.pow 2).mul (continuous_sin.comp continuous_snd)).measurable.ennreal_ofReal
  have hHm (N : ℕ) : Measurable (H N) :=
    hH ▸ Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦
      ENNReal.ofReal (p.1 ^ 2 * sin p.2) * g N (point p.1 p.2 0))
      (hpair.mul ((hgm N).comp continuous_point_meridian.measurable))
  have hgw_fin : ∫⁻ x, gw x < ⊤ := by
    rw [hgw, MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
    exact ((memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2).lintegral_lt_top
  have hHw_fin : ∫⁻ r in Ioi 0, Hw r ≠ ⊤ := fun h ↦ by
    rw [hHw] at h
    rw [lintegral_volume_of_axisymmetric hgwinv hgwm, h, ENNReal.mul_top (by simp [pi_pos])]
      at hgw_fin
    exact lt_irrefl _ hgw_fin
  -- outside the ball the integrands vanish
  have hout {r : ℝ} (hr : R ≤ r) (θ : ℝ) {f : ℝ^3 → ENNReal} (hf : ∀ x, x ∉ B → f x = 0) :
      ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) = 0 := by
    have hr0 : 0 < r := hR.trans_le hr
    rw [hf _ (by simp only [hBdef, Metric.mem_ball, dist_zero_right, norm_point hr0]; linarith),
      mul_zero]
  have hgood' : ∀ᵐ r ∂(volume.restrict (Ioi 0)), 0 < r ∧ (r < R →
      ∃ hv : MemLp (fun θ ↦ w (point r θ 0)) 2 polarAngleMeasure, ∀ N θ,
        S N (point r θ 0) = ∑ l ∈ Finset.range N, ∑ k : Fin 3,
          vectorHarmonicCoeff (hv.toLp _) l k • vectorHarmonic l k θ) := by
    filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hgood),
      ae_restrict_mem measurableSet_Ioi] with r hr hr0 using ⟨hr0, fun hrR ↦ hr ⟨hr0, hrR⟩⟩
  have hHwm : Measurable Hw :=
    hHw ▸ Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦
      ENNReal.ofReal (p.1 ^ 2 * sin p.2) * gw (point p.1 p.2 0))
      (hpair.mul (hgwm.comp continuous_point_meridian.measurable))
  -- the radial integrands at good radii
  have hpB {r : ℝ} (hr0 : 0 < r) (hrR : r < R) (θ : ℝ) : point r θ 0 ∈ B := by
    simpa only [hBdef, Metric.mem_ball, dist_zero_right, norm_point hr0] using hrR
  have hHr {r : ℝ} (hr0 : 0 < r) (hrR : r < R)
      (hv : MemLp (fun θ ↦ w (point r θ 0)) 2 polarAngleMeasure)
      (hpt : ∀ N θ, S N (point r θ 0) = ∑ l ∈ Finset.range N, ∑ k : Fin 3,
          vectorHarmonicCoeff (hv.toLp _) l k • vectorHarmonic l k θ) (N : ℕ) :
      H N r = ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (∫ θ, ‖w (point r θ 0) -
        ∑ l ∈ Finset.range N, ∑ k : Fin 3, vectorHarmonicCoeff (hv.toLp _) l k •
          vectorHarmonic l k θ‖ ^ 2 ∂polarAngleMeasure) := by
    have hexp := tendsto_integral_norm_sub_partialSum hv
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ^3, Q = fun θ ↦ ∑ l ∈ Finset.range N, ∑ k : Fin 3,
        vectorHarmonicCoeff (hv.toLp _) l k • vectorHarmonic l k θ := ⟨_, rfl⟩
    have hQc : Continuous Q := by
      rw [hQ]
      exact continuous_finsetSum _ fun l _ ↦ continuous_finsetSum _ fun k _ ↦
        (continuous_vectorHarmonic l k).const_smul (vectorHarmonicCoeff (hv.toLp _) l k)
    have hgN (θ : ℝ) : g N (point r θ 0) = ENNReal.ofReal (‖w (point r θ 0) - Q θ‖ ^ 2) := by
      simp only [hg, Set.indicator_of_mem (hpB hr0 hrR θ), hpt N θ, hQ]
    have hwv : Measurable fun θ ↦ w (point r θ 0) :=
      hwm.comp (continuous_point_meridian_angle r).measurable
    have hmeas : Measurable fun θ ↦ ‖w (point r θ 0) - Q θ‖ ^ 2 :=
      (hwv.sub hQc.measurable).norm.pow_const 2
    have hint : Integrable (fun θ ↦ ‖w (point r θ 0) - Q θ‖ ^ 2) polarAngleMeasure :=
      hQ ▸ hexp.2.2 N
    simp only [hH, hgN]
    rw [lintegral_meridian_ofReal hmeas hint fun θ ↦ sq_nonneg _, hQ]
  have hHwr {r : ℝ} (hr0 : 0 < r) (hrR : r < R)
      (hv : MemLp (fun θ ↦ w (point r θ 0)) 2 polarAngleMeasure) :
      Hw r = ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal (∫ θ, ‖w (point r θ 0)‖ ^ 2 ∂polarAngleMeasure) := by
    have hgw' (θ : ℝ) : gw (point r θ 0) = ENNReal.ofReal (‖w (point r θ 0)‖ ^ 2) := by
      simp only [hgw, Set.indicator_of_mem (hpB hr0 hrR θ)]
    simp only [hHw, hgw']
    exact lintegral_meridian_ofReal
      ((hwm.comp (continuous_point_meridian_angle r).measurable).norm.pow_const 2)
      ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv) fun θ ↦ sq_nonneg _
  have hHout {r : ℝ} (hrR : R ≤ r) (N : ℕ) : H N r = 0 := by
    simp only [hH, hout hrR _ (f := g N) fun x hx ↦ Set.indicator_of_notMem hx _, lintegral_zero]
  -- dominated convergence in the radius
  have hbound (N : ℕ) : H N ≤ᵐ[volume.restrict (Ioi 0)] fun r ↦ 4 * Hw r := by
    filter_upwards [hgood'] with r ⟨hr0, hP⟩
    by_cases hrR : r < R
    · obtain ⟨hv, hpt⟩ := hP hrR
      rw [hHr hr0 hrR hv hpt N, hHwr hr0 hrR hv]
      calc _ ≤ ENNReal.ofReal (r ^ 2) *
            ENNReal.ofReal (4 * ∫ θ, ‖w (point r θ 0)‖ ^ 2 ∂polarAngleMeasure) := by
            gcongr
            exact (tendsto_integral_norm_sub_partialSum hv).2.1 N
        _ = _ := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
            ring
    · rw [hHout (not_lt.mp hrR) N]
      exact zero_le
  have hlimr : ∀ᵐ r ∂(volume.restrict (Ioi 0)), Tendsto (fun N ↦ H N r) atTop (𝓝 0) := by
    filter_upwards [hgood'] with r ⟨hr0, hP⟩
    by_cases hrR : r < R
    · obtain ⟨hv, hpt⟩ := hP hrR
      simp only [hHr hr0 hrR hv hpt]
      simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (r ^ 2))
        (ENNReal.tendsto_ofReal (tendsto_integral_norm_sub_partialSum hv).1)
        (Or.inr ENNReal.ofReal_ne_top)
    · simpa only [hHout (not_lt.mp hrR)] using tendsto_const_nhds
  have hlimL : Tendsto (fun N ↦ ∫⁻ r in Ioi 0, H N r) atTop (𝓝 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence (fun r ↦ 4 * Hw r) hHm hbound
      (by rw [lintegral_const_mul _ hHwm]; exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top hHw_fin)
      hlimr
  have hlimg : Tendsto (fun N ↦ ∫⁻ x, g N x) atTop (𝓝 0) := by
    have heq (N : ℕ) : ∫⁻ x, g N x = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi 0, H N r := by
      rw [lintegral_volume_of_axisymmetric (hginv N) (hgm N), hH]
    simpa [heq] using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * π)) hlimL
      (Or.inr ENNReal.ofReal_ne_top)
  -- the `L²(B)` distances
  have heL (N : ℕ) : eLpNorm (S N - u) 2 (volume.restrict B) = (∫⁻ x, g N x) ^ (1 / 2 : ℝ) := by
    have hae : S N - u =ᵐ[volume.restrict B] S N - w := by
      filter_upwards [huw] with x hx
      simp only [Pi.sub_apply, hx]
    rw [eLpNorm_congr_ae hae, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top (((hSC N).aestronglyMeasurable).sub hwm.aestronglyMeasurable),
      hg, MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
    congr 2
    funext x
    rw [Pi.sub_apply, enorm_sub_rev, ← ofReal_norm, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hlim : Tendsto (fun N ↦ (hSm N).toLp (S N)) atTop (𝓝 (hu.toLp u)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' S hSm u hu]
    simp only [heL]
    have h := hlimg.ennrpow_const (1 / 2 : ℝ)
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hSspan)

end PDE.Fluid.Stokes.Ball
