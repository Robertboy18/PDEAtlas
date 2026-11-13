/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Potential.Local
public import PDE.DistributionTheory.TestFunction.ConstantFunctional
import PDE.DistributionTheory.TestFunction.Integral
import PDE.Common.Euclidean.OpenBox
import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality
import PDE.Analysis.MeasureTheory.Function.Gluing
import PDE.Analysis.MeasureTheory.Function.LocalL2
import PDE.DistributionTheory.Distribution.Regular.Evaluation

/-!
# Sobolev representatives of algebraic potentials

A scalar functional on compact tests whose derivatives are locally L² has a
locally L² weak potential on an arbitrary open domain. Local potentials on balls
are adjusted on smaller boxes: their difference from the functional annihilates
derivatives, hence is integration against a constant. The adjusted functions
represent the same functional and therefore agree almost everywhere on overlaps.
No simple connectedness or global L² estimate is used.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal Distributions Sobolev

namespace SobolevSpace

open GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem setIntegral_mul_test_eq_integral
    (f : ℝ^n → ℝ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    {U : Set (ℝ^n)} (hφ : tsupport φ ⊆ U) :
    (∫ x in U, f x * φ x) = ∫ x, f x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφ h)), mul_zero]

/-- A local weak potential can be normalized to represent a prescribed algebraic
functional on a smaller box. The normalization uses the functional, so it does
not impose any topology on the original domain. -/
theorem exists_local_representative_of_linearMap_partialDeriv
    (q : 𝓓((⊤ : Opens (ℝ^n)), ℝ) →ₗ[ℝ] ℝ) (F : ℝ^n → ℝ^n)
    (hq : ∀ j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      q (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ) =
        -(∫ x in Ω, F x j * φ x))
    (x : ℝ^n) {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ Ω)
    (w : W^{1,2}(ball x r))
    (hw : (∇ w : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (ball x r)] F) :
    ∃ U : Set (ℝ^n), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∃ p : ℝ^n → ℝ, MemLp p 2 (domainMeasure n U) ∧
        (∀ j : Fin n, HasWeakDerivativeOn U [j] p (fun y ↦ F y j)) ∧
        ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ U →
          q φ = ∫ y in U, p y * φ y := by
  obtain ⟨a, b, hab, hx, hbox⟩ :=
    EuclideanSpace.exists_box_subset_of_mem_open (x := x) isOpen_ball (mem_ball_self hr)
  let U : Set (ℝ^n) := {y | ∀ i, y i ∈ Ioo (a i) (b i)}
  have hopen : IsOpen U := EuclideanSpace.isOpen_box a b
  have hf : LocallyIntegrable (baseRepresentative w) (domainMeasure n (ball x r)) :=
    (Lp.memLp (wkpBaseCoordinateCLM w)).locallyIntegrable (by norm_num)
  let L := TestFunction.integralMulLinearMap (domainMeasure n (ball x r))
    (baseRepresentative w) hf
  have hzero (j : Fin n) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφ : tsupport φ ⊆ U) :
      (q - L) (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ) = 0 := by
    have hd := (hasWeakDerivativeOn_wkpGradientCLM w j).congr_ae
      Filter.EventuallyEq.rfl (hw.mono fun _ h ↦ congrArg (fun z : ℝ^n ↦ z j) h)
    have hi := hd φ (hφ.trans hbox)
    change (∫ y in ball x r, baseRepresentative w y * (∂[j] (φ : ℝ^n → ℝ)) y) =
      (-1 : ℝ) ^ 1 * ∫ y in ball x r, F y j * φ y at hi
    simp only [pow_one, neg_one_mul] at hi
    rw [LinearMap.sub_apply, hq j φ ((hφ.trans hbox).trans hball)]
    change -(∫ y in Ω, F y j * φ y) -
      (∫ y in ball x r, baseRepresentative w y *
        (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ) y) = 0
    simp only [testFunction_lineDerivCLM_apply]
    change -(∫ y in Ω, F y j * φ y) -
      (∫ y in ball x r, baseRepresentative w y * (∂[j] (φ : ℝ^n → ℝ)) y) = 0
    rw [hi, setIntegral_mul_test_eq_integral _ φ ((hφ.trans hbox).trans hball),
      setIntegral_mul_test_eq_integral _ φ (hφ.trans hbox), sub_self]
  obtain ⟨c, hc⟩ :=
    TestFunction.exists_eq_mul_integral_of_partialDeriv_eq_zero_on_box a b hab (q - L) hzero
  have : IsFiniteMeasure (domainMeasure n (ball x r)) :=
    isFiniteMeasure_domainMeasure_of_isBounded isBounded_ball
  let W : W^{1,2}(ball x r) := w + wkpConstant c
  have hbase : baseRepresentative W =ᵐ[domainMeasure n (ball x r)]
      fun y ↦ baseRepresentative w y + c := by
    change (wkpBaseCoordinateCLM W : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball x r)] _
    dsimp only [W]
    rw [map_add]
    filter_upwards [Lp.coeFn_add (wkpBaseCoordinateCLM w)
      (wkpBaseCoordinateCLM (wkpConstant (p := 2) (Ω := ball x r) c)),
      wkpConstant_base_ae (p := 2) (Ω := ball x r) c] with y hy hc
    rw [hy, Pi.add_apply, hc]
    rfl
  have hgrad : (∇ W : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (ball x r)] F := by
    simpa only [W, map_add, wkpGradientCLM_constant, add_zero] using hw
  refine ⟨U, hopen, hx, hbox.trans hball, baseRepresentative W,
    (Lp.memLp (wkpBaseCoordinateCLM W)).mono_measure
      (Measure.restrict_mono hbox le_rfl), ?_, ?_⟩
  · intro j
    exact ((hasWeakDerivativeOn_wkpGradientCLM W j).congr_ae Filter.EventuallyEq.rfl
      (hgrad.mono fun _ h ↦ congrArg (fun z : ℝ^n ↦ z j) h)).mono
        hopen.measurableSet hbox
  · intro φ hφ
    have hi := hc φ hφ
    change q φ - (∫ y in ball x r, baseRepresentative w y * φ y) =
      c * ∫ y, φ y at hi
    rw [setIntegral_mul_test_eq_integral _ φ hφ,
      ← setIntegral_mul_test_eq_integral _ φ (hφ.trans hbox)]
    calc
      q φ = (∫ y in ball x r, baseRepresentative w y * φ y) + c * ∫ y, φ y :=
        (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
      _ = ∫ y in ball x r, (baseRepresentative w y + c) * φ y := by
        have hmul : Integrable (fun y ↦ baseRepresentative w y * φ y)
            (domainMeasure n (ball x r)) :=
          hf.integrable_smul_right_of_hasCompactSupport
            φ.contDiff.continuous φ.hasCompactSupport
        simp only [add_mul]
        rw [integral_add hmul
          ((φ.contDiff.continuous.integrable_of_hasCompactSupport
            φ.hasCompactSupport).mono_measure Measure.restrict_le_self |>.const_mul c),
          integral_const_mul]
        congr 1
        congr 1
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
          image_eq_zero_of_notMem_tsupport (fun h ↦ hy ((hφ.trans hbox) h))
      _ = ∫ y in ball x r, baseRepresentative W y * φ y :=
        integral_congr_ae (hbase.mono fun y hy ↦ congrArg (· * φ y) hy.symm)

/-- An algebraic primitive removes the topological obstruction to gluing local
weak potentials. The resulting pressure is locally L² and has the prescribed
weak gradient; no estimate on its norm over the whole domain is asserted. -/
theorem exists_weak_potential_of_linearMap_partialDeriv
    [Fact (0 < n)]
    (hΩ : IsOpen Ω) (F : ℝ^n → ℝ^n)
    (hF : ∀ i : Fin n, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
      MemLp (fun x ↦ F x i) 2 (volume.restrict K))
    (hweak : ∀ i j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      (∫ x in Ω, F x j * (∂[i] (φ : ℝ^n → ℝ)) x) =
        ∫ x in Ω, F x i * (∂[j] (φ : ℝ^n → ℝ)) x)
    (q : 𝓓((⊤ : Opens (ℝ^n)), ℝ) →ₗ[ℝ] ℝ)
    (hq : ∀ j : Fin n, ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ ⊆ Ω →
      q (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ) =
        -(∫ x in Ω, F x j * φ x)) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp p 2 (domainMeasure n K)) ∧
      ∀ j : Fin n, HasWeakDerivativeOn Ω [j] p (fun x ↦ F x j) := by
  classical
  have hlocal (x : Ω) := exists_local_weak_potential hΩ F hF hweak x
  choose r hr hsub w hw using hlocal
  choose V hopen hpoint hVsub p hp hD hqrep using
    fun x : Ω ↦ exists_local_representative_of_linearMap_partialDeriv q F hq
      x.val (hr x) (hsub x) (w x) (hw x)
  obtain ⟨c, hc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover V hopen
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hpoint ⟨x, hx⟩⟩)
  have : Countable c := hc.to_subtype
  let U (i : c) := V i.val
  have hcov : Ω ⊆ ⋃ i : c, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have hpair (i j : c) : p i.val =ᵐ[volume.restrict (U i ∩ U j)] p j.val := by
    let O : Opens (ℝ^n) := ⟨U i ∩ U j, (hopen i.val).inter (hopen j.val)⟩
    have hi : LocallyIntegrableOn (p i.val) O volume :=
      (memLp_locallyIntegrableOn_domain (hp i.val) (by norm_num)).mono_set inter_subset_left
    have hj : LocallyIntegrableOn (p j.val) O volume :=
      (memLp_locallyIntegrableOn_domain (hp j.val) (by norm_num)).mono_set inter_subset_right
    apply Distribution.ofFun_injective (n := ⊤) hi hj
    ext φ
    let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
    rw [Distribution.ofFun_apply_eq_setIntegral_mul hi,
      Distribution.ofFun_apply_eq_setIntegral_mul hj]
    have hψ : tsupport ψ ⊆ U i ∩ U j := φ.tsupport_subset
    change (∫ x in U i ∩ U j, p i.val x * ψ x) =
      ∫ x in U i ∩ U j, p j.val x * ψ x
    rw [setIntegral_mul_test_eq_integral _ ψ hψ,
      setIntegral_mul_test_eq_integral _ ψ hψ,
      ← setIntegral_mul_test_eq_integral _ ψ (hψ.trans inter_subset_left),
      ← setIntegral_mul_test_eq_integral _ ψ (hψ.trans inter_subset_right)]
    exact (hqrep i.val ψ (hψ.trans inter_subset_left)).symm.trans
      (hqrep j.val ψ (hψ.trans inter_subset_right))
  obtain ⟨g, hg, hgp⟩ := exists_aestronglyMeasurable_of_ae_eq_on_intersections U
    (fun i ↦ (hopen i.val).measurableSet) (fun i ↦ p i.val)
    (fun i ↦ (hp i.val).aestronglyMeasurable) hpair
  have hgΩ := hg.mono_measure (Measure.restrict_mono hcov le_rfl)
  have hmem (i : c) : MemLp g 2 (domainMeasure n (U i)) :=
    (memLp_congr_ae (hgp i)).mpr (hp i.val)
  refine ⟨g, hgΩ, fun K hK hKΩ ↦ memLp_two_on_compact_of_open_cover U
    (fun i ↦ hopen i.val) hcov hmem hK hKΩ, fun j ↦ ?_⟩
  exact hasWeakDerivativeOn_single_of_open_cover U (fun i ↦ hopen i.val) hcov j
    (fun i ↦ (hD i.val j).congr_ae (hgp i).symm Filter.EventuallyEq.rfl)

end SobolevSpace
