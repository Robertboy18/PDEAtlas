/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric.Regularity
public import PDE.CoordinateSystems.Spherical.Inverse
public import PDE.CoordinateSystems.Spherical.Matrix
public import PDE.FDeriv.Laplacian.Spherical
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Analysis.Calculus.DivergenceTrace

/-!
# Axisymmetric vector fields in the spherical frame

An axisymmetric vector field with swirl is given by its radial, polar and azimuthal components
`f r θ : Fin 3 → ℝ` as functions of the radius and the polar angle:

`axisymmetricField f x = f₀ e_r + f₁ e_θ + f₂ e_φ`,

with the components and the frame evaluated at `(‖x‖, polarAngle x, azimuthalAngle x)`. Away
from the symmetry axis the field is as regular as `f`, since the frame is a smooth function of
the Cartesian coordinates there.

At a spherical point off the axis the frame derivative, the advective derivative and the vector
Laplacian are given in frame components by the classical formulas of Batchelor, Appendix 2. For
example the radial component of `(u·∇)u` is `u_r ∂_r u_r + (u_θ / r) ∂_θ u_r - (u_θ² + u_φ²)/r` and
the azimuthal component of `Δu` is `Δu_φ - u_φ / (r² sin² θ)`. They follow from the derivatives of
the frame along the coordinate lines: in components, differentiation in `θ` adds `polarConnection`
and differentiation in `φ` applies `azimuthalConnection θ`. The divergence, and the gradient and
Laplacian of axisymmetric functions, are computed the same way.

The statements are made at `point r θ φ` with `r > 0` and `θ ∈ (0, π)`; every point off the
axis has this form. A field that has the frame components `f r θ` at these points agrees with
`axisymmetricField f` near each of them, so it has the same derivatives there. On the axis two
different arguments apply. The points off the axis are dense on the unit sphere, which extends
identities between continuous functions of the point, such as norms, to the poles. Frame
components are not continuous functions of the point across the axis; for them
`frame_fderiv_eq_of_meridian` passes to the limit along one meridian, where the frame is
continuous.

## References

* G. K. Batchelor, *An Introduction to Fluid Dynamics*, Cambridge University Press, 1967;
  Cambridge Mathematical Library edition, 2000, Appendix 2, "Expressions for some common vector
  differential quantities in orthogonal curvilinear co-ordinate systems", pp. 598-603.
  <https://doi.org/10.1017/CBO9780511800955>
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open scoped RealInnerProductSpace Topology
open Set

/-! ### Angles of a point off the symmetry axis -/

/-- The spherical frame depends on the azimuth only through its cosine and sine. -/
theorem frame_congr_azimuth {φ ψ : ℝ} (hc : Real.cos φ = Real.cos ψ)
    (hs : Real.sin φ = Real.sin ψ) (θ : ℝ) : frame θ φ = frame θ ψ := by
  simp only [frame, radialFrame, polarFrame, azimuthalFrame, hc, hs]

/-- Scaling a spherical point scales its radius. -/
theorem smul_point (c r θ φ : ℝ) : c • point r θ φ = point (c * r) θ φ := by
  rw [point, point, smul_smul]

/-- A multiple of a unit vector is the spherical point with the angles of the unit vector. -/
theorem smul_eq_point_of_mem_sphere (c : ℝ) (ω : Metric.sphere (0 : ℝ^3) 1) :
    c • (ω : ℝ^3) = point c (polarAngle ω) (azimuthalAngle ω) := by
  have hω : (ω : ℝ^3) ≠ 0 := ne_zero_of_mem_unit_sphere ω
  have hn : ‖(ω : ℝ^3)‖ = 1 := by simp
  conv_lhs => rw [← point_norm_polarAngle_azimuthalAngle hω, hn, smul_point, mul_one]

/-- A spherical point of positive radius and polar angle in `(0, π)` is off the axis. -/
theorem point_notMem_symmetryAxis {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi)
    (φ : ℝ) : point r θ φ ∉ symmetryAxis := by
  intro h
  rw [mem_symmetryAxis_iff] at h
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h0 : r * (Real.sin θ * Real.cos φ) = 0 := h.1
  have h1 : r * (Real.sin θ * Real.sin φ) = 0 := h.2
  have hc : Real.cos φ = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hr.ne'
    · exact (mul_eq_zero.mp h).resolve_left hs.ne'
  have hsφ : Real.sin φ = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hr.ne'
    · exact (mul_eq_zero.mp h).resolve_left hs.ne'
  have := Real.sin_sq_add_cos_sq φ
  rw [hc, hsφ] at this
  norm_num at this

/-- At a spherical point off the axis the frame of the total angles is the frame of the
given angles. -/
theorem frame_polarAngle_azimuthalAngle_point {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) :
    frame (polarAngle (point r θ φ)) (azimuthalAngle (point r θ φ)) = frame θ φ := by
  have hx := point_notMem_symmetryAxis hr hθ φ
  rw [polarAngle_point hr (Ioo_subset_Icc_self hθ)]
  have hρ : cylindricalRadius (point r θ φ) = r * Real.sin θ := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    rw [cylindricalRadius, cylindricalRadiusSq]
    change √((r * (Real.sin θ * Real.cos φ)) ^ 2 + (r * (Real.sin θ * Real.sin φ)) ^ 2) = _
    rw [show (r * (Real.sin θ * Real.cos φ)) ^ 2 + (r * (Real.sin θ * Real.sin φ)) ^ 2 =
      (r * Real.sin θ) ^ 2 by linear_combination (r * Real.sin θ) ^ 2 * Real.sin_sq_add_cos_sq φ,
      Real.sqrt_sq (mul_pos hr hs).le]
  have hne : Real.sin θ ≠ 0 := right_ne_zero_of_mul (hρ ▸ (cylindricalRadius_pos hx).ne')
  apply frame_congr_azimuth _ _ θ
  · rw [cos_azimuthalAngle hx, hρ]
    change r * (Real.sin θ * Real.cos φ) / _ = _
    field_simp
  · rw [sin_azimuthalAngle, hρ]
    change r * (Real.sin θ * Real.sin φ) / _ = _
    field_simp

/-! ### Regularity off the axis -/

/-- The points of the unit sphere off the symmetry axis are dense in the sphere: every pole is
a limit of points `point 1 t φ` with `t ∈ (0, π)`. This extends identities between continuous
functions on the sphere to the poles; for frame components see `frame_fderiv_eq_of_meridian`. -/
theorem dense_sphere_notMem_symmetryAxis :
    Dense {ω : Metric.sphere (0 : ℝ^3) 1 | (ω : ℝ^3) ∉ symmetryAxis} := by
  intro ω
  have hω : (ω : ℝ^3) ≠ 0 := ne_zero_of_mem_unit_sphere ω
  have hn : ‖(ω : ℝ^3)‖ = 1 := by simp
  let c : ℝ → Metric.sphere (0 : ℝ^3) 1 := fun t ↦
    ⟨point 1 t (azimuthalAngle ω), by simp [norm_point one_pos]⟩
  have h0 : Continuous fun t : ℝ ↦ radialFrame t (azimuthalAngle ω) :=
    continuous_radialFrame.comp (f := fun t : ℝ ↦ (t, azimuthalAngle ω)) (by fun_prop)
  have h1 : Continuous fun t : ℝ ↦ point 1 t (azimuthalAngle ω) := by simpa [point] using h0
  have hc : Continuous c := h1.subtype_mk _
  have hc0 : c (polarAngle ω) = ω := by
    apply Subtype.ext
    change point 1 (polarAngle ω) (azimuthalAngle ω) = ω
    have h : point 1 (polarAngle ω) (azimuthalAngle ω) =
        point ‖(ω : ℝ^3)‖ (polarAngle ω) (azimuthalAngle ω) := by rw [hn]
    rw [h]
    exact point_norm_polarAngle_azimuthalAngle hω
  have hmem : polarAngle ω ∈ closure (Ioo 0 Real.pi) := by
    rw [closure_Ioo Real.pi_pos.ne]
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  rw [← hc0]
  exact map_mem_closure hc hmem fun t ht ↦ point_notMem_symmetryAxis one_pos ht _

private theorem contDiffAt_coord {n : WithTop ℕ∞} (i : Fin 3) (x : ℝ^3) :
    ContDiffAt ℝ n (fun y : ℝ^3 ↦ y i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt

private def trigFrame (a b c d : ℝ) : Fin 3 → ℝ^3 :=
  ![WithLp.toLp 2 ![b * c, b * d, a], WithLp.toLp 2 ![a * c, a * d, -b],
    WithLp.toLp 2 ![-d, c, 0]]

private theorem frame_eq_trigFrame (θ φ : ℝ) :
    frame θ φ = trigFrame (Real.cos θ) (Real.sin θ) (Real.cos φ) (Real.sin φ) := rfl

private theorem contDiffAt_trigFrame {n : WithTop ℕ∞} {a b c d : ℝ^3 → ℝ} {x : ℝ^3}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) (hc : ContDiffAt ℝ n c x)
    (hd : ContDiffAt ℝ n d x) (k : Fin 3) :
    ContDiffAt ℝ n (fun y ↦ trigFrame (a y) (b y) (c y) (d y) k) x := by
  refine contDiffAt_piLp' _ fun i ↦ ?_
  fin_cases k <;> fin_cases i <;> simp only [trigFrame] <;> dsimp
  all_goals first
    | exact hb.mul hc | exact hb.mul hd | exact ha | exact ha.mul hc | exact ha.mul hd
    | exact hb.neg | exact hd.neg | exact hc | exact contDiffAt_const

/-- The spherical frame at the angles of `x` is a smooth function of `x` off the symmetry axis,
including across the branch cut of the azimuth. -/
theorem contDiffAt_frame_polarAngle_azimuthalAngle {n : WithTop ℕ∞} {x : ℝ^3}
    (hx : x ∉ symmetryAxis) (k : Fin 3) :
    ContDiffAt ℝ n (fun y ↦ frame (polarAngle y) (azimuthalAngle y) k) x := by
  have hx0 := ne_zero_of_notMem_symmetryAxis hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hρ := (cylindricalRadius_pos hx).ne'
  have hnorm : ContDiffAt ℝ n (fun y : ℝ^3 ↦ ‖y‖) x := contDiffAt_norm ℝ hx0
  have hcyl : ContDiffAt ℝ n cylindricalRadius x := contDiffAt_cylindricalRadius hx
  have h := contDiffAt_trigFrame ((contDiffAt_coord 2 x).div hnorm hn) (hcyl.div hnorm hn)
    ((contDiffAt_coord 0 x).div hcyl hρ) ((contDiffAt_coord 1 x).div hcyl hρ) k
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isClosed_symmetryAxis.isOpen_compl.mem_nhds hx] with y hy
  have hy0 := ne_zero_of_notMem_symmetryAxis hy
  rw [frame_eq_trigFrame, cos_polarAngle, sin_polarAngle hy0, cos_azimuthalAngle hy,
    sin_azimuthalAngle]
  rfl

/-! ### Axisymmetric vector fields -/

/-- The axisymmetric vector field with radial, polar and azimuthal components `f r θ`, where
`r = ‖x‖` and `θ` is the polar angle of `x`. On the symmetry axis the azimuth is `0`. -/
def axisymmetricField (f : ℝ → ℝ → Fin 3 → ℝ) (x : ℝ^3) : ℝ^3 :=
  frameVector (polarAngle x) (azimuthalAngle x) (f ‖x‖ (polarAngle x))

/-- At a spherical point off the axis the field has the frame components `f r θ`. -/
theorem axisymmetricField_point (f : ℝ → ℝ → Fin 3 → ℝ) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) :
    axisymmetricField f (point r θ φ) = frameVector θ φ (f r θ) := by
  have h := frame_polarAngle_azimuthalAngle_point hr hθ φ
  simp only [axisymmetricField, frameVector]
  rw [h, norm_point hr, polarAngle_point hr (Ioo_subset_Icc_self hθ)]

/-- A field with frame components `f r θ` at every spherical point off the axis agrees with
`axisymmetricField f` off the axis. -/
theorem eqOn_axisymmetricField {f : ℝ → ℝ → Fin 3 → ℝ} {u : ℝ^3 → ℝ^3}
    (hu : ∀ r θ φ, 0 < r → θ ∈ Ioo 0 Real.pi → u (point r θ φ) = frameVector θ φ (f r θ)) :
    EqOn u (axisymmetricField f) symmetryAxisᶜ := by
  intro y hy
  have hy0 := ne_zero_of_notMem_symmetryAxis hy
  rw [← point_norm_polarAngle_azimuthalAngle hy0, hu _ _ _ (norm_pos_iff.mpr hy0)
    (polarAngle_mem_Ioo hy), point_norm_polarAngle_azimuthalAngle hy0]
  rfl

/-- Such a field agrees with `axisymmetricField f` near every point off the axis, so the two
have the same derivatives and Laplacian there. -/
theorem eventuallyEq_axisymmetricField {f : ℝ → ℝ → Fin 3 → ℝ} {u : ℝ^3 → ℝ^3} {x : ℝ^3}
    (hu : ∀ r θ φ, 0 < r → θ ∈ Ioo 0 Real.pi → u (point r θ φ) = frameVector θ φ (f r θ))
    (hx : x ∉ symmetryAxis) : u =ᶠ[𝓝 x] axisymmetricField f :=
  Filter.eventuallyEq_of_mem (isClosed_symmetryAxis.isOpen_compl.mem_nhds hx)
    (eqOn_axisymmetricField hu)

/-- Off the symmetry axis the field is as regular as its components. -/
theorem contDiffAt_axisymmetricField {n : WithTop ℕ∞} {f : ℝ → ℝ → Fin 3 → ℝ} {x : ℝ^3}
    (hx : x ∉ symmetryAxis) (hf : ContDiffAt ℝ n (Function.uncurry f) (‖x‖, polarAngle x)) :
    ContDiffAt ℝ n (axisymmetricField f) x := by
  have hpair : ContDiffAt ℝ n (fun y : ℝ^3 ↦ (‖y‖, polarAngle y)) x :=
    (contDiffAt_norm ℝ (ne_zero_of_notMem_symmetryAxis hx)).prodMk (contDiffAt_polarAngle hx)
  have hc := hf.comp x hpair
  have hk (k : Fin 3) : ContDiffAt ℝ n (fun y : ℝ^3 ↦ f ‖y‖ (polarAngle y) k) x :=
    contDiffAt_pi.mp hc k
  have heq : axisymmetricField f = fun y ↦
      ∑ k, f ‖y‖ (polarAngle y) k • frame (polarAngle y) (azimuthalAngle y) k := by
    funext y
    simp only [axisymmetricField, frameVector, Fintype.linearCombination_apply]
  rw [heq]
  exact ContDiffAt.sum fun k _ ↦ (hk k).smul (contDiffAt_frame_polarAngle_azimuthalAngle hx k)

/-! ### Derivatives in the frame directions -/

section Sections

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem contDiffAt_radialSection {n : WithTop ℕ∞} {f : ℝ → ℝ → G} {r θ : ℝ}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (r, θ)) : ContDiffAt ℝ n (fun s ↦ f s θ) r := by
  have h := hf.comp r (contDiffAt_id.prodMk contDiffAt_const)
  exact h

private theorem contDiffAt_polarSection {n : WithTop ℕ∞} {f : ℝ → ℝ → G} {r θ : ℝ}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (r, θ)) : ContDiffAt ℝ n (fun t ↦ f r t) θ := by
  have h := hf.comp θ (contDiffAt_const.prodMk contDiffAt_id)
  exact h

private theorem eventually_differentiableAt_of_contDiffAt {g : ℝ → G} {a : ℝ}
    (hg : ContDiffAt ℝ 2 g a) : ∀ᶠ t in 𝓝 a, DifferentiableAt ℝ g t :=
  (hg.eventually (by simp)).mono fun _ ht ↦ ht.differentiableAt (by norm_num)

private theorem differentiableAt_deriv_of_contDiffAt {g : ℝ → G} {a : ℝ}
    (hg : ContDiffAt ℝ 2 g a) : DifferentiableAt ℝ (deriv g) a := by
  have h := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const (1 : ℝ))
  exact h

end Sections

variable {f : ℝ → ℝ → Fin 3 → ℝ} {r θ φ : ℝ}

/-- The field is as regular at a spherical point off the axis as its components are at
`(r, θ)`. -/
theorem contDiffAt_axisymmetricField_point {n : WithTop ℕ∞} (hr : 0 < r)
    (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) (hf : ContDiffAt ℝ n (Function.uncurry f) (r, θ)) :
    ContDiffAt ℝ n (axisymmetricField f) (point r θ φ) := by
  apply contDiffAt_axisymmetricField (point_notMem_symmetryAxis hr hθ φ)
  rwa [norm_point hr, polarAngle_point hr (Ioo_subset_Icc_self hθ)]

/-- The radial derivative of the field has the radial derivatives of the components as
frame components. -/
theorem fderiv_axisymmetricField_radialFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    fderiv ℝ (axisymmetricField f) (point r θ φ) (radialFrame θ φ) =
      frameVector θ φ (deriv (fun s ↦ f s θ) r) := by
  have hU := (contDiffAt_axisymmetricField_point hr hθ φ hf).differentiableAt (by norm_num)
  rw [fderiv_apply_radialFrame hU]
  have heq : (fun s ↦ axisymmetricField f (point s θ φ)) =ᶠ[𝓝 r]
      fun s ↦ frameVector θ φ (f s θ) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact axisymmetricField_point f hs hθ φ
  rw [heq.deriv_eq, deriv_frameVector_radial]

/-- The derivative of the field in the direction of the position vector is `r ∂_r f`. -/
theorem fderiv_axisymmetricField_point_self (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    fderiv ℝ (axisymmetricField f) (point r θ φ) (point r θ φ) =
      frameVector θ φ (r • deriv (fun s ↦ f s θ) r) := by
  rw [show point r θ φ = r • radialFrame θ φ from rfl, map_smul, map_smul,
    ← show point r θ φ = r • radialFrame θ φ from rfl,
    fderiv_axisymmetricField_radialFrame hr hθ hf]

/-- The polar derivative of the field: `∂_θ f + polarConnection f`, divided by `r`. -/
theorem fderiv_axisymmetricField_polarFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    fderiv ℝ (axisymmetricField f) (point r θ φ) (polarFrame θ φ) =
      r⁻¹ • frameVector θ φ (deriv (fun t ↦ f r t) θ + polarConnection (f r θ)) := by
  have hU := (contDiffAt_axisymmetricField_point hr hθ φ hf).differentiableAt (by norm_num)
  rw [fderiv_apply_polarFrame hr.ne' hU]
  have heq : (fun t ↦ axisymmetricField f (point r t φ)) =ᶠ[𝓝 θ]
      fun t ↦ frameVector t φ (f r t) := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    exact axisymmetricField_point f hr ht φ
  rw [heq.deriv_eq, (hasDerivAt_frameVector_polar φ
    ((contDiffAt_polarSection hf).differentiableAt (by norm_num)).hasDerivAt).deriv]

/-- The azimuthal derivative of the field: `azimuthalConnection θ f`, divided by `r sin θ`. -/
theorem fderiv_axisymmetricField_azimuthalFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    fderiv ℝ (axisymmetricField f) (point r θ φ) (azimuthalFrame φ) =
      (r * Real.sin θ)⁻¹ • frameVector θ φ (azimuthalConnection θ (f r θ)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hU := (contDiffAt_axisymmetricField_point hr hθ φ hf).differentiableAt (by norm_num)
  rw [fderiv_apply_azimuthalFrame hr.ne' hs.ne' hU]
  have heq : (fun t ↦ axisymmetricField f (point r θ t)) = fun t ↦ frameVector θ t (f r θ) :=
    funext fun t ↦ axisymmetricField_point f hr hθ t
  rw [heq, (hasDerivAt_frameVector_azimuthal (f r θ) θ φ).deriv]

/-- The derivative of the field applied to the vector with frame components `c`. -/
theorem fderiv_axisymmetricField_frameVector (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) (c : Fin 3 → ℝ) :
    fderiv ℝ (axisymmetricField f) (point r θ φ) (frameVector θ φ c) =
      frameVector θ φ (c 0 • deriv (fun s ↦ f s θ) r +
        (c 1 / r) • (deriv (fun t ↦ f r t) θ + polarConnection (f r θ)) +
        (c 2 / (r * Real.sin θ)) • azimuthalConnection θ (f r θ)) := by
  rw [frameVector_apply θ φ c, map_add, map_add, map_smul, map_smul, map_smul,
    fderiv_axisymmetricField_radialFrame hr hθ hf, fderiv_axisymmetricField_polarFrame hr hθ hf,
    fderiv_axisymmetricField_azimuthalFrame hr hθ hf]
  simp only [map_add, map_smul, smul_smul, div_eq_mul_inv]

/-- The advective derivative `(v·∇)u` of two axisymmetric fields in frame components. -/
theorem advectiveDerivative_axisymmetricField_point {g : ℝ → ℝ → Fin 3 → ℝ} (hr : 0 < r)
    (hθ : θ ∈ Ioo 0 Real.pi) (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    PDE.advectiveDerivative (axisymmetricField g) (axisymmetricField f) (point r θ φ) =
      frameVector θ φ (g r θ 0 • deriv (fun s ↦ f s θ) r +
        (g r θ 1 / r) • (deriv (fun t ↦ f r t) θ + polarConnection (f r θ)) +
        (g r θ 2 / (r * Real.sin θ)) • azimuthalConnection θ (f r θ)) := by
  rw [PDE.advectiveDerivative, axisymmetricField_point g hr hθ φ,
    fderiv_axisymmetricField_frameVector hr hθ hf]

/-- The vector Laplacian of the field in frame components, written with the connections. -/
theorem laplacian_axisymmetricField_point (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (r, θ)) :
    PDE.laplacian (axisymmetricField f) (point r θ φ) =
      frameVector θ φ (deriv (deriv fun s ↦ f s θ) r + (2 / r) • deriv (fun s ↦ f s θ) r +
        (r ^ 2)⁻¹ • (deriv (deriv fun t ↦ f r t) θ +
          (2 : ℝ) • polarConnection (deriv (fun t ↦ f r t) θ) +
          polarConnection (polarConnection (f r θ)) +
          (Real.cos θ / Real.sin θ) • (deriv (fun t ↦ f r t) θ + polarConnection (f r θ))) +
        (r ^ 2 * Real.sin θ ^ 2)⁻¹ • azimuthalConnection θ (azimuthalConnection θ (f r θ))) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [laplacian_point (contDiffAt_axisymmetricField_point hr hθ φ hf) hr.ne' hs.ne']
  have hrad : (fun s ↦ axisymmetricField f (point s θ φ)) =ᶠ[𝓝 r]
      fun s ↦ frameVector θ φ (f s θ) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact axisymmetricField_point f hs hθ φ
  have hradD : (deriv fun s ↦ frameVector θ φ (f s θ)) =
      fun s ↦ frameVector θ φ (deriv (fun s ↦ f s θ) s) :=
    funext fun s ↦ deriv_frameVector_radial θ φ _ s
  have hsec := contDiffAt_polarSection hf
  have hpol : (fun t ↦ axisymmetricField f (point r t φ)) =ᶠ[𝓝 θ]
      fun t ↦ frameVector t φ (f r t) := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    exact axisymmetricField_point f hr ht φ
  have hpolD : (deriv fun t ↦ frameVector t φ (f r t)) =ᶠ[𝓝 θ]
      fun t ↦ frameVector t φ (deriv (fun t ↦ f r t) t + polarConnection (f r t)) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hsec] with t ht
    exact (hasDerivAt_frameVector_polar φ ht.hasDerivAt).deriv
  have hD : HasDerivAt (fun t ↦ deriv (fun t ↦ f r t) t + polarConnection (f r t))
      (deriv (deriv fun t ↦ f r t) θ + polarConnection (deriv (fun t ↦ f r t) θ)) θ :=
    (differentiableAt_deriv_of_contDiffAt hsec).hasDerivAt.add
      (polarConnection.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ
        (hsec.differentiableAt (by norm_num)).hasDerivAt)
  have hazi : (fun t ↦ axisymmetricField f (point r θ t)) = fun t ↦ frameVector θ t (f r θ) :=
    funext fun t ↦ axisymmetricField_point f hr hθ t
  have haziD : (deriv fun t ↦ frameVector θ t (f r θ)) =
      fun t ↦ frameVector θ t (azimuthalConnection θ (f r θ)) :=
    funext fun t ↦ (hasDerivAt_frameVector_azimuthal (f r θ) θ t).deriv
  rw [hrad.deriv.deriv_eq, hrad.deriv_eq, hradD, deriv_frameVector_radial,
    hpol.deriv.deriv_eq, hpolD.deriv_eq, hpol.deriv_eq, hpolD.eq_of_nhds,
    (hasDerivAt_frameVector_polar φ hD).deriv, hazi, haziD,
    (hasDerivAt_frameVector_azimuthal _ θ φ).deriv]
  simp only [map_add, map_smul]
  module

/-! ### Frame components -/

/-- The components of `v` in the spherical frame at the angles of `x`. -/
def frameCoords (x v : ℝ^3) : Fin 3 → ℝ :=
  fun k ↦ ⟪frame (polarAngle x) (azimuthalAngle x) k, v⟫

/-- At a spherical point off the axis the frame components use the frame of its angles. -/
theorem frameCoords_point (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) (v : ℝ^3) :
    frameCoords (point r θ φ) v = fun k ↦ ⟪frame θ φ k, v⟫ := by
  funext k
  change ⟪frame (polarAngle (point r θ φ)) (azimuthalAngle (point r θ φ)) k, v⟫ = _
  rw [frame_polarAngle_azimuthalAngle_point hr hθ φ]

/-- The frame components of a frame vector at a spherical point off the axis. -/
@[simp]
theorem frameCoords_point_frameVector (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ)
    (c : Fin 3 → ℝ) : frameCoords (point r θ φ) (frameVector θ φ c) = c := by
  rw [frameCoords_point hr hθ φ]
  exact funext fun k ↦ inner_frame_frameVector θ φ c k

/-- Frame components are additive. -/
theorem frameCoords_add (x v w : ℝ^3) :
    frameCoords x (v + w) = frameCoords x v + frameCoords x w :=
  funext fun _ ↦ inner_add_right _ _ _

/-- The Euclidean norm squared is the sum of the squared frame components. -/
theorem sum_sq_frameCoords (x v : ℝ^3) : ∑ k, frameCoords x v k ^ 2 = ‖v‖ ^ 2 := by
  have h := norm_sq_frameVector (polarAngle x) (azimuthalAngle x) (frameCoords x v)
  rw [show frameVector _ _ (frameCoords x v) = v from frameVector_inner_frame _ _ v] at h
  exact h.symm

section Components

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The Laplacian `∂_r² g + (2/r) ∂_r g + r⁻² (∂_θ² g + cot θ ∂_θ g)` of a function of the
radius and the polar angle. -/
def sphericalLaplacian (g : ℝ → ℝ → G) (r θ : ℝ) : G :=
  deriv (deriv fun s ↦ g s θ) r + (2 / r) • deriv (fun s ↦ g s θ) r +
    (r ^ 2)⁻¹ • (deriv (deriv fun t ↦ g r t) θ +
      (Real.cos θ / Real.sin θ) • deriv (fun t ↦ g r t) θ)

end Components

private theorem deriv_apply_of_differentiableAt {c : ℝ → Fin 3 → ℝ} {a : ℝ}
    (hc : DifferentiableAt ℝ c a) (k : Fin 3) : deriv c a k = deriv (fun s ↦ c s k) a := by
  rw [deriv_pi fun i ↦ differentiableAt_pi.mp hc i]

private theorem deriv_deriv_apply_of_contDiffAt {c : ℝ → Fin 3 → ℝ} {a : ℝ}
    (hc : ContDiffAt ℝ 2 c a) (k : Fin 3) :
    deriv (deriv c) a k = deriv (deriv fun s ↦ c s k) a := by
  rw [deriv_apply_of_differentiableAt (differentiableAt_deriv_of_contDiffAt hc) k]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_differentiableAt_of_contDiffAt hc] with s hs
  exact deriv_apply_of_differentiableAt hs k

/-! ### Classical component formulas -/

/-- The frame matrix `⟪e_i, (Du) e_j⟫` of the derivative of an axisymmetric field with
components `(u_r, u_θ, u_φ) = f r θ`. -/
def sphericalGradientMatrix (f : ℝ → ℝ → Fin 3 → ℝ) (r θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![deriv (fun s ↦ f s θ 0) r, (deriv (fun t ↦ f r t 0) θ - f r θ 1) / r, -f r θ 2 / r;
    deriv (fun s ↦ f s θ 1) r, (deriv (fun t ↦ f r t 1) θ + f r θ 0) / r,
      -(Real.cos θ / Real.sin θ * f r θ 2) / r;
    deriv (fun s ↦ f s θ 2) r, deriv (fun t ↦ f r t 2) θ / r,
      (f r θ 0 + Real.cos θ / Real.sin θ * f r θ 1) / r]

/-- The frame components of the derivative of an axisymmetric field off the axis. -/
theorem frame_fderiv_axisymmetricField (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) (i j : Fin 3) :
    ⟪frame θ φ i, fderiv ℝ (axisymmetricField f) (point r θ φ) (frame θ φ j)⟫ =
      sphericalGradientMatrix f r θ i j := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hrad := (contDiffAt_radialSection hf).differentiableAt (by norm_num)
  have hpol := (contDiffAt_polarSection hf).differentiableAt (by norm_num)
  have hcol : fderiv ℝ (axisymmetricField f) (point r θ φ) (frame θ φ j) =
      frameVector θ φ (fun i ↦ sphericalGradientMatrix f r θ i j) := by
    fin_cases j
    · change fderiv ℝ (axisymmetricField f) (point r θ φ) (radialFrame θ φ) = _
      rw [fderiv_axisymmetricField_radialFrame hr hθ hf]
      congr 1
      ext i
      fin_cases i <;> exact deriv_apply_of_differentiableAt hrad _
    · change fderiv ℝ (axisymmetricField f) (point r θ φ) (polarFrame θ φ) = _
      rw [fderiv_axisymmetricField_polarFrame hr hθ hf, ← map_smul]
      congr 1
      ext i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.smul_apply, Pi.add_apply,
          smul_eq_mul, polarConnection_apply, sphericalGradientMatrix, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons, deriv_apply_of_differentiableAt hpol] <;>
        field_simp <;> ring
    · change fderiv ℝ (axisymmetricField f) (point r θ φ) (azimuthalFrame φ) = _
      rw [fderiv_axisymmetricField_azimuthalFrame hr hθ hf, ← map_smul]
      congr 1
      ext i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.smul_apply, smul_eq_mul,
          azimuthalConnection_apply, sphericalGradientMatrix, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons] <;> field_simp
  rw [hcol, inner_frame_frameVector]

/-- The derivative of an axisymmetric field off the axis is the Cartesian operator with
frame matrix `sphericalGradientMatrix f r θ`. -/
theorem fderiv_axisymmetricField_eq_matrixInFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    fderiv ℝ (axisymmetricField f) (point r θ φ) =
      matrixInFrame θ φ (sphericalGradientMatrix f r θ) := by
  apply ContinuousLinearMap.coe_injective
  refine (frameBasis θ φ).toBasis.ext fun j ↦ ext_frame (θ := θ) (φ := φ) fun i ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis, frameBasis_apply]
  rw [frame_fderiv_axisymmetricField hr hθ hf, real_inner_comm, inner_matrixInFrame]
  simp [frameBasis_repr_apply, orthonormal_iff_ite.mp (orthonormal_frame θ φ), Matrix.mulVec,
    dotProduct]

/-- A frame component of a derivative that is known on the open meridian of a nonzero point `x`
extends to `x`, including the points of the axis: if `u` is `C¹` at `x` and
`⟪e_i, Du e_j⟫ = a t` at `point ‖x‖ t (azimuthalAngle x)` for every `t ∈ (0, π)`, with `a`
continuous at the polar angle of `x`, then the same holds at `x`. The frame components are not
continuous functions of the point across the axis, so density of the points off the axis does
not give this; along one meridian the frame is continuous. -/
theorem frame_fderiv_eq_of_meridian {u : ℝ^3 → ℝ^3} {x : ℝ^3} (hx : x ≠ 0)
    (hu : ContDiffAt ℝ 1 u x) {a : ℝ → ℝ} (hA : ContinuousAt a (polarAngle x)) (i j : Fin 3)
    (h : ∀ t ∈ Ioo 0 Real.pi,
      ⟪frame t (azimuthalAngle x) i,
        fderiv ℝ u (point ‖x‖ t (azimuthalAngle x)) (frame t (azimuthalAngle x) j)⟫ = a t) :
    ⟪frame (polarAngle x) (azimuthalAngle x) i,
      fderiv ℝ u x (frame (polarAngle x) (azimuthalAngle x) j)⟫ = a (polarAngle x) := by
  have hpt : point ‖x‖ (polarAngle x) (azimuthalAngle x) = x :=
    point_norm_polarAngle_azimuthalAngle hx
  have hfr (k : Fin 3) : Continuous fun t : ℝ ↦ frame t (azimuthalAngle x) k :=
    (continuous_frame k).comp (f := fun t : ℝ ↦ (t, azimuthalAngle x)) (by fun_prop)
  have hline : Continuous fun t : ℝ ↦ point ‖x‖ t (azimuthalAngle x) :=
    (continuous_const (y := ‖x‖)).smul
      (show Continuous fun t : ℝ ↦ radialFrame t (azimuthalAngle x) from hfr 0)
  have hD : ContinuousAt (fderiv ℝ u) x := (hu.fderiv_right (m := 0) le_rfl).continuousAt
  have h1 : ContinuousAt (fun t ↦ fderiv ℝ u (point ‖x‖ t (azimuthalAngle x))) (polarAngle x) :=
    ContinuousAt.comp (g := fderiv ℝ u) (by rw [hpt]; exact hD) hline.continuousAt
  have hF : ContinuousAt (fun t ↦ ⟪frame t (azimuthalAngle x) i,
      fderiv ℝ u (point ‖x‖ t (azimuthalAngle x)) (frame t (azimuthalAngle x) j)⟫)
      (polarAngle x) :=
    ((hfr i).continuousAt).inner (h1.clm_apply (hfr j).continuousAt)
  have hmem : polarAngle x ∈ closure (Ioo 0 Real.pi) := by
    rw [closure_Ioo Real.pi_pos.ne]
    exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have : (𝓝[Ioo 0 Real.pi] polarAngle x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hmem
  have heq := eventually_nhdsWithin_of_forall (s := Ioo 0 Real.pi) (a := polarAngle x) h
  have hlim := tendsto_nhds_unique
    ((hF.continuousWithinAt (s := Ioo 0 Real.pi)).tendsto.congr' heq)
    (hA.continuousWithinAt (s := Ioo 0 Real.pi)).tendsto
  rw [hpt] at hlim
  exact hlim

/-- The divergence of an axisymmetric field off the axis:
`∂_r u_r + 2 u_r / r + (∂_θ u_θ + cot θ u_θ) / r`; the swirl does not contribute. -/
theorem divergence_axisymmetricField_point (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    PDE.divergence (axisymmetricField f) (point r θ φ) =
      deriv (fun s ↦ f s θ 0) r + 2 * f r θ 0 / r +
        (deriv (fun t ↦ f r t 1) θ + Real.cos θ / Real.sin θ * f r θ 1) / r := by
  have hU := (contDiffAt_axisymmetricField_point hr hθ φ hf).differentiableAt (by norm_num)
  have h := PDE.Analysis.divergence_eq_trace_fderiv hU
  change PDE.divergence _ _ = _ at h
  rw [h, LinearMap.trace_eq_sum_inner _ (frameBasis θ φ), Fin.sum_univ_three]
  simp only [frameBasis_apply, ContinuousLinearMap.coe_coe,
    frame_fderiv_axisymmetricField hr hθ hf, sphericalGradientMatrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-- The advective derivative `(v·∇)u` of two axisymmetric fields in frame components,
with `(v_r, v_θ, v_φ) = g r θ` and `(u_r, u_θ, u_φ) = f r θ`. -/
theorem frame_advectiveDerivative_axisymmetricField_axisymmetricField {g : ℝ → ℝ → Fin 3 → ℝ}
    (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi) (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    frameCoords (point r θ φ)
        (PDE.advectiveDerivative (axisymmetricField g) (axisymmetricField f) (point r θ φ)) =
      ![g r θ 0 * deriv (fun s ↦ f s θ 0) r + g r θ 1 / r * deriv (fun t ↦ f r t 0) θ -
          (g r θ 1 * f r θ 1 + g r θ 2 * f r θ 2) / r,
        g r θ 0 * deriv (fun s ↦ f s θ 1) r + g r θ 1 / r * deriv (fun t ↦ f r t 1) θ +
          (g r θ 1 * f r θ 0 - Real.cos θ / Real.sin θ * g r θ 2 * f r θ 2) / r,
        g r θ 0 * deriv (fun s ↦ f s θ 2) r + g r θ 1 / r * deriv (fun t ↦ f r t 2) θ +
          (g r θ 2 * f r θ 0 + Real.cos θ / Real.sin θ * g r θ 2 * f r θ 1) / r] := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hrad := (contDiffAt_radialSection hf).differentiableAt (by norm_num)
  have hpol := (contDiffAt_polarSection hf).differentiableAt (by norm_num)
  rw [advectiveDerivative_axisymmetricField_point hr hθ hf, frameCoords_point_frameVector hr hθ]
  ext k
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, polarConnection_apply, azimuthalConnection_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      deriv_apply_of_differentiableAt hrad, deriv_apply_of_differentiableAt hpol] <;>
    field_simp <;> ring

/-- The convective term `(u·∇)u` of an axisymmetric field with swirl in frame components:
`u_r ∂_r u_r + (u_θ / r) ∂_θ u_r - (u_θ² + u_φ²) / r` and its polar and azimuthal
companions. -/
theorem frame_advectiveDerivative_axisymmetricField (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 1 (Function.uncurry f) (r, θ)) :
    frameCoords (point r θ φ)
        (PDE.advectiveDerivative (axisymmetricField f) (axisymmetricField f) (point r θ φ)) =
      ![f r θ 0 * deriv (fun s ↦ f s θ 0) r + f r θ 1 / r * deriv (fun t ↦ f r t 0) θ -
          (f r θ 1 ^ 2 + f r θ 2 ^ 2) / r,
        f r θ 0 * deriv (fun s ↦ f s θ 1) r + f r θ 1 / r * deriv (fun t ↦ f r t 1) θ +
          (f r θ 0 * f r θ 1 - Real.cos θ / Real.sin θ * f r θ 2 ^ 2) / r,
        f r θ 0 * deriv (fun s ↦ f s θ 2) r + f r θ 1 / r * deriv (fun t ↦ f r t 2) θ +
          (f r θ 0 * f r θ 2 + Real.cos θ / Real.sin θ * f r θ 1 * f r θ 2) / r] := by
  rw [frame_advectiveDerivative_axisymmetricField_axisymmetricField hr hθ hf]
  ext k
  fin_cases k <;> simp <;> ring

/-- The vector Laplacian of an axisymmetric field with swirl in frame components:
`Δu_r - 2u_r/r² - (2/(r² sin θ)) ∂_θ(sin θ u_θ)`, `Δu_θ + (2/r²) ∂_θ u_r - u_θ/(r² sin² θ)` and
`Δu_φ - u_φ/(r² sin² θ)`, with `Δ` the scalar `sphericalLaplacian`. -/
theorem frame_laplacian_axisymmetricField (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (r, θ)) :
    frameCoords (point r θ φ) (PDE.laplacian (axisymmetricField f) (point r θ φ)) =
      ![sphericalLaplacian (fun r θ ↦ f r θ 0) r θ - 2 * f r θ 0 / r ^ 2 -
          2 / (r ^ 2 * Real.sin θ) * deriv (fun t ↦ Real.sin t * f r t 1) θ,
        sphericalLaplacian (fun r θ ↦ f r θ 1) r θ + 2 / r ^ 2 * deriv (fun t ↦ f r t 0) θ -
          f r θ 1 / (r ^ 2 * Real.sin θ ^ 2),
        sphericalLaplacian (fun r θ ↦ f r θ 2) r θ - f r θ 2 / (r ^ 2 * Real.sin θ ^ 2)] := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hrad := contDiffAt_radialSection hf
  have hpol := contDiffAt_polarSection hf
  have hpol1 (k : Fin 3) : DifferentiableAt ℝ (fun t ↦ f r t k) θ :=
    differentiableAt_pi.mp (hpol.differentiableAt (by norm_num)) k
  have hprod : deriv (fun t ↦ Real.sin t * f r t 1) θ =
      Real.cos θ * f r θ 1 + Real.sin θ * deriv (fun t ↦ f r t 1) θ := by
    rw [deriv_fun_mul Real.differentiableAt_sin (hpol1 1), Real.deriv_sin]
  rw [laplacian_axisymmetricField_point hr hθ hf, frameCoords_point_frameVector hr hθ, hprod]
  ext k
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, polarConnection_apply, azimuthalConnection_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      sphericalLaplacian, deriv_deriv_apply_of_contDiffAt hrad,
      deriv_deriv_apply_of_contDiffAt hpol,
      deriv_apply_of_differentiableAt (hrad.differentiableAt (by norm_num)),
      deriv_apply_of_differentiableAt (hpol.differentiableAt (by norm_num))] <;>
    field_simp <;>
    first
      | ring1
      | linear_combination (-f r θ 1) * Real.sin_sq_add_cos_sq θ
      | linear_combination (-f r θ 2) * Real.sin_sq_add_cos_sq θ

/-! ### Axisymmetric functions -/

/-- The axisymmetric function with value `p r θ` at radius `r` and polar angle `θ`. -/
def axisymmetricFunction {G : Type*} (p : ℝ → ℝ → G) (x : ℝ^3) : G := p ‖x‖ (polarAngle x)

/-- At a spherical point the axisymmetric function takes the value `p r θ`. -/
theorem axisymmetricFunction_point {G : Type*} (p : ℝ → ℝ → G) (hr : 0 < r)
    (hθ : θ ∈ Icc 0 Real.pi) (φ : ℝ) : axisymmetricFunction p (point r θ φ) = p r θ := by
  rw [axisymmetricFunction, norm_point hr, polarAngle_point hr hθ]

/-- A function with value `p r θ` at every spherical point off the axis agrees with
`axisymmetricFunction p` off the axis. -/
theorem eqOn_axisymmetricFunction {G : Type*} {p : ℝ → ℝ → G} {P : ℝ^3 → G}
    (hP : ∀ r θ φ, 0 < r → θ ∈ Ioo 0 Real.pi → P (point r θ φ) = p r θ) :
    EqOn P (axisymmetricFunction p) symmetryAxisᶜ := by
  intro y hy
  have hy0 := ne_zero_of_notMem_symmetryAxis hy
  rw [← point_norm_polarAngle_azimuthalAngle hy0, hP _ _ _ (norm_pos_iff.mpr hy0)
    (polarAngle_mem_Ioo hy), point_norm_polarAngle_azimuthalAngle hy0]
  rfl

/-- Such a function agrees with `axisymmetricFunction p` near every point off the axis. -/
theorem eventuallyEq_axisymmetricFunction {G : Type*} {p : ℝ → ℝ → G} {P : ℝ^3 → G}
    {x : ℝ^3} (hP : ∀ r θ φ, 0 < r → θ ∈ Ioo 0 Real.pi → P (point r θ φ) = p r θ)
    (hx : x ∉ symmetryAxis) : P =ᶠ[𝓝 x] axisymmetricFunction p :=
  Filter.eventuallyEq_of_mem (isClosed_symmetryAxis.isOpen_compl.mem_nhds hx)
    (eqOn_axisymmetricFunction hP)

section Function

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {p : ℝ → ℝ → G}

/-- Off the symmetry axis an axisymmetric function is as regular as its profile. -/
theorem contDiffAt_axisymmetricFunction {n : WithTop ℕ∞} {x : ℝ^3} (hx : x ∉ symmetryAxis)
    (hp : ContDiffAt ℝ n (Function.uncurry p) (‖x‖, polarAngle x)) :
    ContDiffAt ℝ n (axisymmetricFunction p) x := by
  have hpair : ContDiffAt ℝ n (fun y : ℝ^3 ↦ (‖y‖, polarAngle y)) x :=
    (contDiffAt_norm ℝ (ne_zero_of_notMem_symmetryAxis hx)).prodMk (contDiffAt_polarAngle hx)
  have h := hp.comp x hpair
  exact h

/-- At a spherical point off the axis an axisymmetric function is as regular as its profile is
at `(r, θ)`. -/
theorem contDiffAt_axisymmetricFunction_point {n : WithTop ℕ∞} (hr : 0 < r)
    (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) (hp : ContDiffAt ℝ n (Function.uncurry p) (r, θ)) :
    ContDiffAt ℝ n (axisymmetricFunction p) (point r θ φ) := by
  apply contDiffAt_axisymmetricFunction (point_notMem_symmetryAxis hr hθ φ)
  rwa [norm_point hr, polarAngle_point hr (Ioo_subset_Icc_self hθ)]

/-- The radial derivative of an axisymmetric function is `∂_r p`. -/
theorem fderiv_axisymmetricFunction_radialFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hp : ContDiffAt ℝ 1 (Function.uncurry p) (r, θ)) :
    fderiv ℝ (axisymmetricFunction p) (point r θ φ) (radialFrame θ φ) =
      deriv (fun s ↦ p s θ) r := by
  have hP := (contDiffAt_axisymmetricFunction_point hr hθ φ hp).differentiableAt (by norm_num)
  rw [fderiv_apply_radialFrame hP]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact axisymmetricFunction_point p hs (Ioo_subset_Icc_self hθ) φ

/-- The polar derivative of an axisymmetric function is `r⁻¹ ∂_θ p`. -/
theorem fderiv_axisymmetricFunction_polarFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hp : ContDiffAt ℝ 1 (Function.uncurry p) (r, θ)) :
    fderiv ℝ (axisymmetricFunction p) (point r θ φ) (polarFrame θ φ) =
      r⁻¹ • deriv (fun t ↦ p r t) θ := by
  have hP := (contDiffAt_axisymmetricFunction_point hr hθ φ hp).differentiableAt (by norm_num)
  rw [fderiv_apply_polarFrame hr.ne' hP]
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
  exact axisymmetricFunction_point p hr (Ioo_subset_Icc_self ht) φ

/-- An axisymmetric function does not change in the azimuthal direction. -/
theorem fderiv_axisymmetricFunction_azimuthalFrame (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hp : ContDiffAt ℝ 1 (Function.uncurry p) (r, θ)) :
    fderiv ℝ (axisymmetricFunction p) (point r θ φ) (azimuthalFrame φ) = 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hP := (contDiffAt_axisymmetricFunction_point hr hθ φ hp).differentiableAt (by norm_num)
  rw [fderiv_apply_azimuthalFrame hr.ne' hs.ne' hP]
  have h : (fun t ↦ axisymmetricFunction p (point r θ t)) = fun _ ↦ p r θ :=
    funext fun t ↦ axisymmetricFunction_point p hr (Ioo_subset_Icc_self hθ) t
  rw [h, deriv_const, smul_zero]

/-- The Laplacian of an axisymmetric function off the axis is its spherical Laplacian. -/
theorem laplacian_axisymmetricFunction_point (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi)
    (hp : ContDiffAt ℝ 2 (Function.uncurry p) (r, θ)) :
    PDE.laplacian (axisymmetricFunction p) (point r θ φ) = sphericalLaplacian p r θ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  rw [laplacian_point (contDiffAt_axisymmetricFunction_point hr hθ φ hp) hr.ne' hs.ne']
  have hrad : (fun s ↦ axisymmetricFunction p (point s θ φ)) =ᶠ[𝓝 r] fun s ↦ p s θ := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact axisymmetricFunction_point p hs (Ioo_subset_Icc_self hθ) φ
  have hpol : (fun t ↦ axisymmetricFunction p (point r t φ)) =ᶠ[𝓝 θ] fun t ↦ p r t := by
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht
    exact axisymmetricFunction_point p hr (Ioo_subset_Icc_self ht) φ
  have hazi : (fun t ↦ axisymmetricFunction p (point r θ t)) = fun _ ↦ p r θ :=
    funext fun t ↦ axisymmetricFunction_point p hr (Ioo_subset_Icc_self hθ) t
  have hconst : (deriv fun _ : ℝ ↦ p r θ) = fun _ ↦ 0 := funext fun _ ↦ deriv_const _ _
  rw [hrad.deriv.deriv_eq, hrad.deriv_eq, hpol.deriv.deriv_eq, hpol.deriv_eq, hazi, hconst,
    deriv_const, smul_zero, add_zero, sphericalLaplacian]

end Function

/-- The gradient of a scalar axisymmetric function in frame components:
`(∂_r p, r⁻¹ ∂_θ p, 0)`. -/
theorem frame_gradient_axisymmetricFunction {p : ℝ → ℝ → ℝ} (hr : 0 < r)
    (hθ : θ ∈ Ioo 0 Real.pi) (hp : ContDiffAt ℝ 1 (Function.uncurry p) (r, θ)) :
    frameCoords (point r θ φ) (gradient (axisymmetricFunction p) (point r θ φ)) =
      ![deriv (fun s ↦ p s θ) r, deriv (fun t ↦ p r t) θ / r, 0] := by
  rw [frameCoords_point hr hθ]
  ext k
  fin_cases k
  · change ⟪radialFrame θ φ, _⟫ = _
    rw [real_inner_comm, inner_gradient_left, fderiv_axisymmetricFunction_radialFrame hr hθ hp]
    rfl
  · change ⟪polarFrame θ φ, _⟫ = _
    rw [real_inner_comm, inner_gradient_left, fderiv_axisymmetricFunction_polarFrame hr hθ hp,
      smul_eq_mul, inv_mul_eq_div]
    rfl
  · change ⟪azimuthalFrame φ, _⟫ = _
    rw [real_inner_comm, inner_gradient_left, fderiv_axisymmetricFunction_azimuthalFrame hr hθ hp]
    rfl

end PDE.CoordinateSystems.Spherical
