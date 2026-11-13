/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.EnergyMethods.Dirichlet.Basic
import PDE.FDeriv.Calculus

/-!
# Green Identities and Dirichlet Uniqueness on Coordinate Boxes

We specialize classical energy methods to coordinate boxes, where Mathlib's divergence theorem
gives the boundary-flux formula.

The main results are Green's first and second identities, vanishing-energy rigidity for harmonic
functions with homogeneous face data, and uniqueness for the classical Dirichlet problem on a
nondegenerate box.

The uniqueness theorem is the energy proof of Evans, §2.2.5(a), Theorem 16, on a box. Green's
identities are the box forms of Evans, Appendix C.2, Theorem 3, which is stated for bounded open
sets with `C¹` boundary; on a box the boundary integral is the oriented face sum `boxFlux`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.5(a), (46) and Theorem 16, pp. 41-42, and
  Appendix C.2, Theorem 3, p. 712.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

namespace Energy

section GreensBox

open MeasureTheory

variable {m : ℕ}

/-- The coordinatewise preorder transported from `Fin (m + 1) → ℝ`, used to express
axis-aligned integration boxes as order intervals. -/
noncomputable local instance euclideanSpaceCoordinatePreorder : Preorder (ℝ^(m + 1)) :=
  Preorder.lift (fun x : ℝ^(m + 1) ↦ x.ofLp)

private theorem equiv_symm_pi_single (i : Fin (m + 1)) :
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Pi.single i (1 : ℝ)) =
      EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [EuclideanSpace.equiv]
  · simp [EuclideanSpace.equiv,  hji]

/-- Boundary flux term for a vector field over a box `[a,b]` in `ℝ^(m + 1)`. -/
noncomputable def boxFlux
    (a b : ℝ^(m + 1))
    (f : Fin (m + 1) → ℝ^(m + 1) → ℝ) : ℝ :=
  ∑ i : Fin (m + 1),
    ((∫ x in Set.Icc (a.ofLp ∘ i.succAbove) (b.ofLp ∘ i.succAbove),
        f i (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (b i) x))) -
      ∫ x in Set.Icc (a.ofLp ∘ i.succAbove) (b.ofLp ∘ i.succAbove),
        f i (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i) x)))

/-- Vanishing Dirichlet data on every lower and upper face of the box `[a,b]`.

This is the coordinate-face form of the boundary condition needed by the box divergence
theorem. Degenerate boxes are allowed; in that case the same point can lie on several faces. -/
def VanishesOnBoxFaces
    (a b : ℝ^(m + 1))
    (u : ℝ^(m + 1) → ℝ) : Prop :=
  ∀ (i : Fin (m + 1))
      (x : Fin m → ℝ),
    x ∈ Set.Icc (a.ofLp ∘ i.succAbove) (b.ofLp ∘ i.succAbove) →
      u (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (b i) x)) = 0 ∧
      u (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i) x)) = 0

/-- Two functions have the same Dirichlet data on every coordinate face of `[a,b]`. -/
def AgreeOnBoxFaces
    (a b : ℝ^(m + 1))
    (u v : ℝ^(m + 1) → ℝ) : Prop :=
  ∀ (i : Fin (m + 1))
      (x : Fin m → ℝ),
    x ∈ Set.Icc (a.ofLp ∘ i.succAbove) (b.ofLp ∘ i.succAbove) →
      u (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (b i) x)) =
          v (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (b i) x)) ∧
      u (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i) x)) =
          v (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i) x))

/-- Subtracting functions with equal face data produces homogeneous Dirichlet data. -/
theorem vanishesOnBoxFaces_sub_of_agreeOnBoxFaces
    (a b : ℝ^(m + 1))
    {u v : ℝ^(m + 1) → ℝ}
    (h : AgreeOnBoxFaces (m := m) a b u v) :
    VanishesOnBoxFaces (m := m) a b (fun x ↦ u x - v x) := by
  simp only [AgreeOnBoxFaces] at h
  simp only [VanishesOnBoxFaces]
  intro i x hx
  constructor
  · rw [(h i x hx).1, sub_self]
  · rw [(h i x hx).2, sub_self]

/-- A flux of the form `u F` vanishes when `u` has zero Dirichlet data on every face. -/
theorem boxFlux_mul_eq_zero_of_vanishesOnBoxFaces
    (a b : ℝ^(m + 1))
    {u : ℝ^(m + 1) → ℝ}
    (hu : VanishesOnBoxFaces (m := m) a b u)
    (F : Fin (m + 1) → ℝ^(m + 1) → ℝ) :
    boxFlux (m := m) a b (fun i x ↦ u x * F i x) = 0 := by
  classical
  simp only [VanishesOnBoxFaces] at hu
  simp only [boxFlux]
  apply Finset.sum_eq_zero
  intro i _
  have hupper :
      (∫ x in Set.Icc (a.ofLp ∘ i.succAbove) (b.ofLp ∘ i.succAbove),
          u (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (b i) x)) *
            F i (WithLp.toLp 2
              (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (b i) x))) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [(hu i x hx).1]
    simp
  have hlower :
      (∫ x in Set.Icc (a.ofLp ∘ i.succAbove) (b.ofLp ∘ i.succAbove),
          u (WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i) x)) *
            F i (WithLp.toLp 2
              (i.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i) x))) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [(hu i x hx).2]
    simp
  rw [hupper, hlower, sub_self]

private theorem isCompact_Icc_euclidean
    (a b : ℝ^(m + 1)) :
    IsCompact (Set.Icc a b) := by
  let eL : ℝ^(m + 1) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (m + 1)) ℝ
  have htarget : IsCompact (Set.Icc (eL a) (eL b)) := isCompact_Icc
  have hpreimage : IsCompact (eL ⁻¹' Set.Icc (eL a) (eL b)) :=
    eL.toHomeomorph.isCompact_preimage.mpr htarget
  change IsCompact (eL ⁻¹' Set.Icc (eL a) (eL b))
  exact hpreimage

private theorem convex_Icc_euclidean
    (a b : ℝ^(m + 1)) :
    Convex ℝ (Set.Icc a b) := by
  let eL : ℝ^(m + 1) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (m + 1)) ℝ
  have htarget : Convex ℝ (Set.Icc (eL a) (eL b)) := convex_Icc _ _
  have hpreimage := htarget.linear_preimage eL.toLinearMap
  change Convex ℝ (eL ⁻¹' Set.Icc (eL a) (eL b))
  exact hpreimage

private theorem interior_Icc_nonempty_of_forall_lt
    (a b : ℝ^(m + 1))
    (hab : ∀ i, a i < b i) :
    (interior (Set.Icc a b)).Nonempty := by
  let eL : ℝ^(m + 1) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (m + 1)) ℝ
  let c : ℝ^(m + 1) :=
    eL.symm (fun i ↦ (a i + b i) / 2)
  refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
  have hlower : ∀ i, (eL a) i < (eL c) i := by
    intro i
    change a i < (a i + b i) / 2
    linarith [hab i]
  have hupper : ∀ i, (eL c) i < (eL b) i := by
    intro i
    change (a i + b i) / 2 < b i
    linarith [hab i]
  have htarget : Set.Icc (eL a) (eL b) ∈ nhds (eL c) :=
    pi_Icc_mem_nhds hlower hupper
  have hpreimage := eL.continuous.continuousAt.preimage_mem_nhds htarget
  change eL ⁻¹' Set.Icc (eL a) (eL b) ∈ nhds c
  exact hpreimage

/-- Gauss's divergence theorem on a coordinate box.

The boundary integral is the explicit oriented face sum `boxFlux`: upper
faces carry the positive coordinate normal and lower faces the negative
coordinate normal. -/
theorem integral_divergence_eq_boxFlux_Icc
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    (F : Fin (m + 1) → ℝ^(m + 1) → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) :
    (∫ x in Set.Icc a b,
        ∑ i : Fin (m + 1), (∂[i] (F i)) x) =
      boxFlux (m := m) a b F := by
  let eL : ℝ^(m + 1) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (m + 1)) ℝ
  have he_ord :
      ∀ x y : ℝ^(m + 1), eL x ≤ eL y ↔ x ≤ y := by
    intro x y
    rfl
  have he_vol : MeasurePreserving eL volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
      (Fin (m + 1))
  let F' : Fin (m + 1) → ℝ^(m + 1) → ℝ^(m + 1) →L[ℝ] ℝ :=
    fun i x ↦ fderiv ℝ (F i) x
  have hContinuous :
      ∀ i, ContinuousOn (F i) (Set.Icc a b) :=
    fun i ↦ (hF i).continuous.continuousOn
  have hDerivative :
      ∀ x ∈ interior (Set.Icc a b) \ (∅ : Set (ℝ^(m + 1))),
        ∀ i, HasFDerivAt (F i) (F' i x) x := by
    intro x _ i
    exact
      ((hF i).differentiable (by norm_num) x).hasFDerivAt
  let divF : ℝ^(m + 1) → ℝ :=
    fun x ↦ ∑ i : Fin (m + 1), (∂[i] (F i)) x
  have hdivF :
      ∀ x, divF x =
        ∑ i, F' i x (eL.symm (Pi.single i 1)) := by
    intro x
    simp [divF, F', partialDeriv, eL,
      equiv_symm_pi_single (m := m)]
  have hInt : IntegrableOn divF (Set.Icc a b) volume := by
    have hdivContinuous : Continuous divF := by
      dsimp only [divF]
      apply continuous_finsetSum
      intro i _
      exact
        (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) (hF i)).continuous
    exact hdivContinuous.continuousOn.integrableOn_compact
      (isCompact_Icc_euclidean (m := m) a b)
  have hmain :=
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv
      (n := m) (eL := eL) (he_ord := he_ord) (he_vol := he_vol)
      (f := F) (f' := F') (s := (∅ : Set (ℝ^(m + 1))))
      (hs := Set.countable_empty)
      (a := a) (b := b) (hle := hle)
      (Hc := hContinuous) (Hd := hDerivative)
      (DF := divF) (hDF := hdivF) (Hi := hInt)
  have heL_a : eL a = a.ofLp := rfl
  have heL_b : eL b = b.ofLp := rfl
  have heL_symm :
      (eL.symm : (Fin (m + 1) → ℝ) → ℝ^(m + 1)) =
        WithLp.toLp 2 := rfl
  simpa [divF, boxFlux, heL_a, heL_b, heL_symm] using hmain

/-- The divergence theorem applied to `u ∇v` on a coordinate box.

The integrand is expanded using `div (u ∇v) = ∇u · ∇v + u Δv`; the right-hand side is the
oriented sum of the upper and lower face integrals. -/
theorem integral_gradient_add_mul_laplacian_eq_boxFlux_Icc
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) :
    (∫ x in Set.Icc a b,
          (∑ i : Fin (m + 1), (∂[i] u) x * (∂[i] v) x) +
            u x * laplacian v x) =
      boxFlux (m := m) a b (fun i x ↦ u x * (∂[i] v) x) := by
  classical
  let F : Fin (m + 1) → ℝ^(m + 1) → ℝ :=
    fun i x ↦ u x * (∂[i] v) x
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    exact hu.mul (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv)
  have hdiv :
      (fun x ↦ ∑ i : Fin (m + 1), (∂[i] (F i)) x) =
        fun x ↦
          (∑ i : Fin (m + 1), (∂[i] u) x * (∂[i] v) x) +
            u x * laplacian v x := by
    funext x
    have huDiff : DifferentiableAt ℝ u x :=
      (hu.differentiable (by norm_num)).differentiableAt
    have hvDiff :
        ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] v) y) x := by
      intro i
      exact
        ((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv).differentiable
          (by norm_num)).differentiableAt
    change ∇·
      (fun y ↦ WithLp.toLp 2 fun i ↦ u y * (∂[i] v) y) x = _
    exact divergence_of_u_grad_v (n := m + 1) (u := u) (v := v) huDiff hvDiff
  change
    (∫ x in Set.Icc a b,
        (∑ i : Fin (m + 1), (∂[i] u) x * (∂[i] v) x) +
          u x * laplacian v x) =
      boxFlux (m := m) a b F
  rw [← hdiv]
  exact integral_divergence_eq_boxFlux_Icc (m := m) a b hle F hF

/-- Green's first identity on a coordinate box.

This is the box form of Evans, Appendix C.2, Theorem 3(ii): the boundary integral is represented
by the explicit oriented face sum `boxFlux`. -/
theorem greens_first_identity_Icc
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v) :
    (∫ x in Set.Icc a b, u x * laplacian v x) =
      -(∫ x in Set.Icc a b, ∑ i : Fin (m + 1),
            (∂[i] u) x * (∂[i] v) x) +
        boxFlux (m := m) a b (fun i x ↦ u x * (∂[i] v) x) := by
  have hcompact := isCompact_Icc_euclidean (m := m) a b
  have hGrad : IntegrableOn
      (fun x ↦ ∑ i : Fin (m + 1), (∂[i] u) x * (∂[i] v) x)
      (Set.Icc a b) volume := by
    have hcont : Continuous
        (fun x ↦ ∑ i : Fin (m + 1), (∂[i] u) x * (∂[i] v) x) := by
      apply continuous_finsetSum
      intro i _
      exact
        (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hu).continuous.mul
          (PDE.contDiff_partialDeriv_of_succ
            (m := 0) (i := i) (hv.of_le (by norm_num))).continuous
    exact hcont.continuousOn.integrableOn_compact hcompact
  have hLap : IntegrableOn (fun x ↦ u x * laplacian v x)
      (Set.Icc a b) volume := by
    have hlaplacian : Continuous (laplacian v) := by
      unfold laplacian
      apply continuous_finsetSum
      intro i _
      exact
        (PDE.contDiff_partialDeriv_of_succ
          (m := 0) (i := i)
          (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv)).continuous
    exact (hu.continuous.mul hlaplacian).continuousOn.integrableOn_compact hcompact
  have hmain := integral_gradient_add_mul_laplacian_eq_boxFlux_Icc
    (m := m) a b hle hu hv
  rw [MeasureTheory.integral_add hGrad hLap] at hmain
  linarith

/-- Green's first identity on a box with homogeneous Dirichlet data on every face. -/
theorem greens_first_identity_Icc_zero_boundary
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (huFace : VanishesOnBoxFaces (m := m) a b u) :
    (∫ x in Set.Icc a b, u x * laplacian v x) =
      -(∫ x in Set.Icc a b, ∑ i : Fin (m + 1),
        (∂[i] u) x * (∂[i] v) x) := by
  rw [greens_first_identity_Icc (m := m) a b hle hu hv,
    boxFlux_mul_eq_zero_of_vanishesOnBoxFaces (m := m) a b huFace]
  simp

/-- The squared coordinate-gradient integrand of a globally `C²` function is integrable on
every compact coordinate box. -/
theorem integrableOn_gradient_sq_Icc
    (a b : ℝ^(m + 1))
    {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) :
    IntegrableOn
      (fun x ↦ ∑ i : Fin (m + 1),
        (∂[i] u) x * (∂[i] u) x)
      (Set.Icc a b) volume := by
  have hpartial : ∀ i : Fin (m + 1),
      Continuous (fun x ↦ (∂[i] u) x) :=
    fun i ↦ (PDE.contDiff_partialDeriv_of_succ (n := m + 1) (i := i) hu).continuous
  have hcont : Continuous (fun x ↦ ∑ i : Fin (m + 1),
      (∂[i] u) x * (∂[i] u) x) := by
    rw [show
        (fun x ↦ ∑ i : Fin (m + 1),
          (∂[i] u) x * (∂[i] u) x) =
          fun x ↦ ∑ i : Fin (m + 1),
            ((fun y ↦ (∂[i] u) y) *
              fun y ↦ (∂[i] u) y) x by rfl]
    exact continuous_finsetSum Finset.univ fun i _ ↦ (hpartial i).mul (hpartial i)
  exact hcont.continuousOn.integrableOn_compact (isCompact_Icc_euclidean (m := m) a b)

/-- A classical harmonic function with homogeneous Dirichlet data on a box has zero
Dirichlet energy. This is the standard energy consequence of Green's first identity. -/
theorem harmonic_dirichlet_energy_zero_Icc
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u)
    (huHarmonic : ∀ x ∈ Set.Icc a b, laplacian u x = 0)
    (huFace : VanishesOnBoxFaces (m := m) a b u) :
    (∫ x in Set.Icc a b, ∑ i : Fin (m + 1),
      (∂[i] u) x * (∂[i] u) x) = 0 := by
  have hGreen := greens_first_identity_Icc_zero_boundary (m := m) a b hle
    (hu.of_le (by norm_num)) hu huFace
  have hleft : (∫ x in Set.Icc a b, u x * laplacian u x) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by
      simp [huHarmonic x hx]
  rw [hleft] at hGreen
  linarith

/-- Uniqueness on a nondegenerate coordinate box by the energy method.

A globally `C²` harmonic function that vanishes on every face of a box with positive side
lengths vanishes throughout the closed box. The proof is that of Evans, §2.2.5(a), Theorem 16:
Green's identity gives zero Dirichlet energy, positivity and continuity force the gradient to
vanish in the interior, convexity makes the function constant there, and continuity extends the
constant to the boundary where the Dirichlet data fixes it to zero. -/
theorem harmonic_eq_zero_Icc_of_vanishesOnBoxFaces
    (a b : ℝ^(m + 1))
    (hab : ∀ i, a i < b i)
    {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u)
    (huHarmonic : ∀ x ∈ Set.Icc a b, laplacian u x = 0)
    (huFace : VanishesOnBoxFaces (m := m) a b u) :
    ∀ x ∈ Set.Icc a b, u x = 0 := by
  let density : ℝ^(m + 1) → ℝ := fun x ↦
    ∑ i : Fin (m + 1),
      (∂[i] u) x * (∂[i] u) x
  have hle : a ≤ b := by
    intro i
    exact (hab i).le
  have hzero : (∫ x in Set.Icc a b, density x) = 0 := by
    simpa [density] using harmonic_dirichlet_energy_zero_Icc
      (m := m) a b hle hu huHarmonic huFace
  have hint : IntegrableOn density (Set.Icc a b) volume := by
    simpa [density] using integrableOn_gradient_sq_Icc (m := m) a b hu
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc a b)] density := by
    filter_upwards with x
    dsimp only [density]
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  have hae : density =ᵐ[volume.restrict (Set.Icc a b)] 0 :=
    (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae hnonneg hint).1 hzero
  have hpartialCont : ∀ i : Fin (m + 1),
      Continuous (fun x ↦ (∂[i] u) x) :=
    fun i ↦ (PDE.contDiff_partialDeriv_of_succ (n := m + 1) (i := i) hu).continuous
  have hdensityCont : Continuous density := by
    dsimp only [density]
    rw [show
        (fun x ↦ ∑ i : Fin (m + 1),
          (∂[i] u) x * (∂[i] u) x) =
          fun x ↦ ∑ i : Fin (m + 1),
            ((fun y ↦ (∂[i] u) y) *
              fun y ↦ (∂[i] u) y) x by rfl]
    exact continuous_finsetSum Finset.univ fun i _ ↦
      (hpartialCont i).mul (hpartialCont i)
  have haeInterior :
      density =ᵐ[volume.restrict (interior (Set.Icc a b))] 0 :=
    ae_restrict_of_ae_restrict_of_subset interior_subset hae
  have hdensityZero : Set.EqOn density 0 (interior (Set.Icc a b)) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq haeInterior isOpen_interior
      hdensityCont.continuousOn continuous_const.continuousOn
  have hpartialZero : ∀ x ∈ interior (Set.Icc a b),
      ∀ i, (∂[i] u) x = 0 := by
    intro x hx i
    have hsum : density x = 0 := hdensityZero hx
    have hterm :
        (∂[i] u) x ^ 2 ≤ density x := by
      dsimp only [density]
      simpa [pow_two] using
        (Finset.single_le_sum
          (fun j (_hj : j ∈ Finset.univ) ↦
            sq_nonneg ((∂[j] u) x))
          (Finset.mem_univ i))
    nlinarith [sq_nonneg ((∂[i] u) x)]
  have hfderivZero : Set.EqOn (fderiv ℝ u) 0 (interior (Set.Icc a b)) := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.ext
    intro i
    simpa [partialDeriv] using hpartialZero x hx i
  have hconvex : Convex ℝ (Set.Icc a b) := convex_Icc_euclidean (m := m) a b
  obtain ⟨c, hc⟩ := interior_Icc_nonempty_of_forall_lt (m := m) a b hab
  have hconstInterior : Set.EqOn u (fun _ ↦ u c) (interior (Set.Icc a b)) := by
    intro x hx
    exact isOpen_interior.is_const_of_fderiv_eq_zero
      hconvex.interior.isPreconnected
      (hu.differentiable (by decide)).differentiableOn hfderivZero hx hc
  have hclosure : closure (interior (Set.Icc a b)) = Set.Icc a b := by
    calc
      closure (interior (Set.Icc a b)) = closure (Set.Icc a b) :=
        hconvex.closure_interior_eq_closure_of_nonempty_interior ⟨c, hc⟩
      _ = Set.Icc a b := (isCompact_Icc_euclidean (m := m) a b).isClosed.closure_eq
  have hconstBox : Set.EqOn u (fun _ ↦ u c) (Set.Icc a b) := by
    rw [← hclosure]
    exact hconstInterior.closure hu.continuous continuous_const
  let i0 : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
  let eL : ℝ^(m + 1) ≃L[ℝ] (Fin (m + 1) → ℝ) :=
    EuclideanSpace.equiv (Fin (m + 1)) ℝ
  let z : Fin m → ℝ := fun j ↦ c (i0.succAbove j)
  have hcIcc : c ∈ Set.Icc a b := interior_subset hc
  have hz : z ∈ Set.Icc (a ∘ i0.succAbove) (b ∘ i0.succAbove) := by
    constructor
    · intro j
      exact hcIcc.1 (i0.succAbove j)
    · intro j
      exact hcIcc.2 (i0.succAbove j)
  let y : ℝ^(m + 1) :=
    eL.symm (i0.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i0) z)
  have hyIcc : y ∈ Set.Icc a b := by
    change i0.insertNth (α := fun _ : Fin (m + 1) ↦ ℝ) (a i0) z ∈
      Set.Icc (eL a) (eL b)
    rw [Fin.insertNth_mem_Icc]
    exact ⟨⟨le_rfl, hle i0⟩, hz⟩
  have hyZero : u y = 0 := by
    simpa [y, eL] using (huFace i0 z hz).2
  have hcZero : u c = 0 := (hconstBox hyIcc).symm.trans hyZero
  intro x hx
  exact (hconstBox hx).trans hcZero

/-- Classical Dirichlet uniqueness on a nondegenerate coordinate box.

Two globally `C²` functions with the same Laplacian on the box and the same values on every
face agree throughout the closed box.  This is the uniqueness theorem for the Poisson Dirichlet
problem; the harmonic case is obtained by taking both Laplacians to be zero. -/
theorem eqOn_Icc_of_laplacian_eq_of_agreeOnBoxFaces
    (a b : ℝ^(m + 1))
    (hab : ∀ i, a i < b i)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hlaplacian : ∀ x ∈ Set.Icc a b,
      laplacian u x = laplacian v x)
    (hface : AgreeOnBoxFaces (m := m) a b u v) :
    Set.EqOn u v (Set.Icc a b) := by
  let w : ℝ^(m + 1) → ℝ := fun x ↦ u x - v x
  have hw : ContDiff ℝ 2 w := hu.sub hv
  have hwHarmonic : ∀ x ∈ Set.Icc a b, laplacian w x = 0 := by
    intro x hx
    rw [show laplacian w x =
        laplacian u x - laplacian v x by
      exact PDE.laplacian_sub (n := m + 1) u v x hu.contDiffAt hv.contDiffAt]
    exact sub_eq_zero.mpr (hlaplacian x hx)
  have hwFace : VanishesOnBoxFaces (m := m) a b w := by
    simpa [w] using vanishesOnBoxFaces_sub_of_agreeOnBoxFaces
      (m := m) a b hface
  have hwZero := harmonic_eq_zero_Icc_of_vanishesOnBoxFaces
    (m := m) a b hab hw hwHarmonic hwFace
  intro x hx
  exact sub_eq_zero.mp (hwZero x hx)

/-- Harmonic specialization of classical Dirichlet uniqueness on a nondegenerate box. -/
theorem harmonic_eqOn_Icc_of_agreeOnBoxFaces
    (a b : ℝ^(m + 1))
    (hab : ∀ i, a i < b i)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huHarmonic : ∀ x ∈ Set.Icc a b, laplacian u x = 0)
    (hvHarmonic : ∀ x ∈ Set.Icc a b, laplacian v x = 0)
    (hface : AgreeOnBoxFaces (m := m) a b u v) :
    Set.EqOn u v (Set.Icc a b) := by
  apply eqOn_Icc_of_laplacian_eq_of_agreeOnBoxFaces
    (m := m) a b hab hu hv _ hface
  intro x hx
  rw [huHarmonic x hx, hvHarmonic x hx]

/-- Green's second identity on a coordinate box.

This is Evans, Appendix C.2, Theorem 3(iii), with the boundary integral represented by the
explicit oriented face sum for `u∇v - v∇u`. -/
theorem greens_second_identity_Icc
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    (∫ x in Set.Icc a b, u x * laplacian v x - v x * laplacian u x) =
      boxFlux (m := m) a b
        (fun i x ↦ u x * (∂[i] v) x - v x * (∂[i] u) x) := by
  classical
  let F : Fin (m + 1) → ℝ^(m + 1) → ℝ :=
    fun i x ↦ u x * (∂[i] v) x - v x * (∂[i] u) x
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    exact
      ((hu.of_le (by norm_num)).mul
        (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv)).sub
      ((hv.of_le (by norm_num)).mul
        (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hu))
  have hdiv :
      (fun x ↦ ∑ i : Fin (m + 1), (∂[i] (F i)) x) =
        fun x ↦ u x * laplacian v x - v x * laplacian u x := by
    funext x
    have huDiff : DifferentiableAt ℝ u x :=
      (hu.differentiable (by norm_num)).differentiableAt
    have hvDiff : DifferentiableAt ℝ v x :=
      (hv.differentiable (by norm_num)).differentiableAt
    have hDu :
        ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] u) y) x := by
      intro i
      exact
        ((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hu).differentiable
          (by norm_num)).differentiableAt
    have hDv :
        ∀ i, DifferentiableAt ℝ (fun y ↦ (∂[i] v) y) x := by
      intro i
      exact
        ((PDE.contDiff_partialDeriv_of_succ (m := 1) (i := i) hv).differentiable
          (by norm_num)).differentiableAt
    change ∇·
      (fun y ↦ WithLp.toLp 2 fun i ↦
        u y * (∂[i] v) y - v y * (∂[i] u) y) x = _
    exact
      divergence_u_grad_v_sub_v_grad_u (n := m + 1) (u := u) (v := v)
        huDiff hvDiff hDu hDv
  change
    (∫ x in Set.Icc a b, u x * laplacian v x - v x * laplacian u x) =
      boxFlux (m := m) a b F
  rw [← hdiv]
  exact integral_divergence_eq_boxFlux_Icc (m := m) a b hle F hF

/-- For two classical harmonic functions, the boundary commutator flux in Green's second
identity vanishes. -/
theorem harmonic_boxFlux_commutator_eq_zero
    (a b : ℝ^(m + 1)) (hle : a ≤ b)
    {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huHarmonic : ∀ x ∈ Set.Icc a b, laplacian u x = 0)
    (hvHarmonic : ∀ x ∈ Set.Icc a b, laplacian v x = 0) :
    boxFlux (m := m) a b
      (fun i x ↦ u x * (∂[i] v) x -
        v x * (∂[i] u) x) = 0 := by
  have hGreen := greens_second_identity_Icc (m := m) a b hle hu hv
  have hleft :
      (∫ x in Set.Icc a b,
        u x * laplacian v x - v x * laplacian u x) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ by
      simp [huHarmonic x hx, hvHarmonic x hx]
  exact hGreen ▸ hleft

/-! ## Green's theorem and planar Stokes -/

/-- Counterclockwise circulation of the planar field `(P,Q)` around a
coordinate rectangle, written as the oriented face sum used by the box
divergence theorem. -/
noncomputable def rectangleCirculation
    (a b : ℝ^2) (P Q : ℝ^2 → ℝ) : ℝ :=
  boxFlux (m := 1) a b
    (fun i x ↦ if i = (0 : Fin 2) then Q x else -P x)

/-- Outward flux of the planar field `(P,Q)` across the boundary of a
coordinate rectangle. -/
noncomputable def rectangleOutwardFlux
    (a b : ℝ^2) (P Q : ℝ^2 → ℝ) : ℝ :=
  boxFlux (m := 1) a b
    (fun i x ↦ if i = (0 : Fin 2) then P x else Q x)

/-- Green's theorem in circulation form on a coordinate rectangle.

Equivalently, this is the planar Stokes theorem:
`∫∫ (∂ₓQ - ∂ᵧP) = ∮ P dx + Q dy`. -/
theorem greens_circulation_theorem_Icc
    (a b : ℝ^2) (hle : a ≤ b)
    {P Q : ℝ^2 → ℝ}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    (∫ x in Set.Icc a b,
        (∂[(0 : Fin 2)] Q) x -
          (∂[(1 : Fin 2)] P) x) =
      rectangleCirculation a b P Q := by
  let F : Fin 2 → ℝ^2 → ℝ :=
    fun i x ↦ if i = (0 : Fin 2) then Q x else -P x
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hQ
    · simpa [F] using hP.neg
  have hdiv :
      (fun x ↦ ∑ i : Fin 2, (∂[i] (F i)) x) =
        fun x ↦
          (∂[(0 : Fin 2)] Q) x -
            (∂[(1 : Fin 2)] P) x := by
    funext x
    rw [Fin.sum_univ_two]
    simp [F, partialDeriv, sub_eq_add_neg]
  have hGauss :=
    integral_divergence_eq_boxFlux_Icc
      (m := 1) a b hle F hF
  change
    (∫ x in Set.Icc a b,
        (∂[(0 : Fin 2)] Q) x -
          (∂[(1 : Fin 2)] P) x) =
      boxFlux (m := 1) a b F
  rw [← hdiv]
  exact hGauss

/-- Green's theorem in outward-flux form on a coordinate rectangle:
`∫∫ (∂ₓP + ∂ᵧQ) = ∮ (P,Q) · n`. -/
theorem greens_flux_theorem_Icc
    (a b : ℝ^2) (hle : a ≤ b)
    {P Q : ℝ^2 → ℝ}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    (∫ x in Set.Icc a b,
        (∂[(0 : Fin 2)] P) x +
          (∂[(1 : Fin 2)] Q) x) =
      rectangleOutwardFlux a b P Q := by
  let F : Fin 2 → ℝ^2 → ℝ :=
    fun i x ↦ if i = (0 : Fin 2) then P x else Q x
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hP
    · simpa [F] using hQ
  have hdiv :
      (fun x ↦ ∑ i : Fin 2, (∂[i] (F i)) x) =
        fun x ↦
          (∂[(0 : Fin 2)] P) x +
            (∂[(1 : Fin 2)] Q) x := by
    funext x
    rw [Fin.sum_univ_two]
    simp [F]
  have hGauss :=
    integral_divergence_eq_boxFlux_Icc
      (m := 1) a b hle F hF
  change
    (∫ x in Set.Icc a b,
        (∂[(0 : Fin 2)] P) x +
          (∂[(1 : Fin 2)] Q) x) =
      boxFlux (m := 1) a b F
  rw [← hdiv]
  exact hGauss

end GreensBox

end Energy
