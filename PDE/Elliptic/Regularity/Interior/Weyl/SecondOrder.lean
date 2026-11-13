/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates.IntegralGrowth
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PDE.FDeriv.Calculus
import PDE.FDeriv.Calculus.Convolution
import PDE.FDeriv.PartialDeriv.Support
public import PDE.FDeriv.PartialDeriv.Smooth
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# Second-order distributions that annihilate Laplacians

A distribution of order two on `ℝⁿ` with locally integrable coefficients `a`, `bⱼ`, `c` acts on
a test function `ψ` by

`T ψ = ∫ a ψ + Σⱼ ∫ bⱼ ∂ⱼψ + ∫ c Δψ`.

If `T (Δψ) = 0` for every test function, then `T` is harmonic: its mollification
`x ↦ T (ρ (x - ·))` is a classical harmonic function for every smooth compactly supported `ρ`.
If moreover the coefficients have controlled growth on balls,
`∫_{B(x,r)} |coefficient| ≤ C (1 + ‖x‖ + r) r^a` for `r ≥ 1` with `a + 1 < n`, then every
mollification inherits this growth and vanishes by Liouville's theorem, so `T = 0`. In
particular a square-integrable function on `ℝⁿ`, `n ≥ 2`, that annihilates the Laplacian of every
test function vanishes (`ae_eq_zero_of_integral_mul_laplacian_eq_zero`).
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter ContinuousLinearMap PDE.Analysis
open MeasureTheory.LocallyIntegrable (integrable_mul_right_of_hasCompactSupport)
open scoped Convolution ENNReal NNReal

namespace LaplacianEquation

variable {n : ℕ}

/-- The second-order distribution `ψ ↦ ∫ a ψ + Σⱼ ∫ bⱼ ∂ⱼψ + ∫ c Δψ`. -/
noncomputable def secondOrderPairing (a : ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ψ : ℝ^n → ℝ) : ℝ :=
  (∫ y, a y * ψ y) + (∑ j, ∫ y, b j y * PDE.partialDeriv j ψ y) +
    ∫ y, c y * PDE.laplacian ψ y

/-- The mollification `x ↦ T (ρ (x - ·))` of the second-order distribution, written as
convolutions. -/
noncomputable def secondOrderMollification (a : ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ)
    (c : ℝ^n → ℝ) (ρ : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  (a ⋆[mul ℝ ℝ, volume] ρ) x -
    (∑ j, (b j ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.partialDeriv j ρ y) x) +
    (c ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.laplacian ρ y) x

/-- The Laplacian of a reflected translate is the reflected translate of the Laplacian. -/
theorem laplacian_comp_const_sub {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (x y : ℝ^n) :
    PDE.laplacian (fun z ↦ ρ (x - z)) y = PDE.laplacian ρ (x - y) := by
  unfold PDE.laplacian
  apply Finset.sum_congr rfl
  intro i _
  simpa [iteratedPartialDeriv] using
    SobolevSpace.Approximation.iteratedPartialDeriv_comp_const_sub [i, i] hρ x y

/-- The pairing with a reflected translate is the mollification. -/
theorem secondOrderPairing_comp_const_sub (a : ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ)
    (c : ℝ^n → ℝ) {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (x : ℝ^n) :
    secondOrderPairing a b c (fun y ↦ ρ (x - y)) = secondOrderMollification a b c ρ x := by
  have hd (j : Fin n) (y : ℝ^n) :
      PDE.partialDeriv j (fun z ↦ ρ (x - z)) y = -PDE.partialDeriv j ρ (x - y) := by
    simpa [iteratedPartialDeriv] using
      SobolevSpace.Approximation.iteratedPartialDeriv_comp_const_sub [j] hρ x y
  simp only [secondOrderPairing, secondOrderMollification, convolution_def, mul_apply', hd,
    laplacian_comp_const_sub hρ, mul_neg, integral_neg, Finset.sum_neg_distrib]
  ring

/-- The coordinate Laplacian of a finite sum of `C²` functions is the sum of the Laplacians. -/
theorem laplacian_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ^n → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : ℝ^n) :
    PDE.laplacian (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, PDE.laplacian (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PDE.laplacian, PDE.partialDeriv]
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    rw [PDE.laplacian_add _ _ x ((hf k (Finset.mem_insert_self k s)).contDiffAt)
      (ContDiff.contDiffAt (ContDiff.sum fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- If a second-order distribution with locally integrable coefficients annihilates the
Laplacian of every test function, then each of its mollifications is harmonic. -/
theorem isHarmonicPDE_secondOrderMollification {a c : ℝ^n → ℝ} {b : Fin n → ℝ^n → ℝ}
    (ha : LocallyIntegrable a volume) (hb : ∀ j, LocallyIntegrable (b j) volume)
    (hc : LocallyIntegrable c volume)
    (hT : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      secondOrderPairing a b c (fun y ↦ PDE.laplacian ψ y) = 0)
    {ρ : ℝ^n → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    IsHarmonicPDE n (secondOrderMollification a b c ρ) univ := by
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hd (j : Fin n) := PDE.contDiff_top_partialDeriv (i := j) hρ
  have hdc (j : Fin n) : HasCompactSupport (fun y ↦ PDE.partialDeriv j ρ y) :=
    hρc.partialDeriv j
  have hl := PDE.contDiff_laplacian_coord hρ
  have hlc := HasCompactSupport.coordinate_laplacian hρc
  have cA : ContDiff ℝ (⊤ : ℕ∞) (a ⋆[mul ℝ ℝ, volume] ρ) :=
    hρc.contDiff_convolution_right (mul ℝ ℝ) ha hρ
  have cB (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞)
      (b j ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.partialDeriv j ρ y) :=
    (hdc j).contDiff_convolution_right (mul ℝ ℝ) (hb j) (hd j)
  have cC : ContDiff ℝ (⊤ : ℕ∞) (c ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.laplacian ρ y) :=
    hlc.contDiff_convolution_right (mul ℝ ℝ) hc hl
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (secondOrderMollification a b c ρ) := by
    unfold secondOrderMollification
    exact (cA.sub (ContDiff.sum fun j _ ↦ cB j)).add cC
  refine ⟨(hsmooth.of_le h2).contDiffOn, fun x _ ↦ ?_⟩
  have hsum : ContDiff ℝ 2 (fun y ↦ ∑ j, (b j ⋆[mul ℝ ℝ, volume]
      fun z ↦ PDE.partialDeriv j ρ z) y) :=
    (ContDiff.sum fun j _ ↦ cB j).of_le h2
  have hsplit : PDE.laplacian (secondOrderMollification a b c ρ) x =
      PDE.laplacian (a ⋆[mul ℝ ℝ, volume] ρ) x -
        (∑ j, PDE.laplacian (b j ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.partialDeriv j ρ y) x) +
        PDE.laplacian (c ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.laplacian ρ y) x := by
    change PDE.laplacian (fun y ↦ ((a ⋆[mul ℝ ℝ, volume] ρ) y -
        ∑ j, (b j ⋆[mul ℝ ℝ, volume] fun z ↦ PDE.partialDeriv j ρ z) y) +
        (c ⋆[mul ℝ ℝ, volume] fun z ↦ PDE.laplacian ρ z) y) x = _
    rw [PDE.laplacian_add _ _ x ((cA.of_le h2).sub hsum).contDiffAt (cC.of_le h2).contDiffAt,
      PDE.laplacian_sub _ _ x (cA.of_le h2).contDiffAt hsum.contDiffAt,
      laplacian_finsetSum _ (fun j _ ↦ (cB j).of_le h2)]
  rw [hsplit, PDE.laplacian_convolution_right ha hρc (hρ.of_le h2),
    PDE.laplacian_convolution_right hc hlc (hl.of_le h2)]
  have hB (j : Fin n) : PDE.laplacian (b j ⋆[mul ℝ ℝ, volume]
      fun y ↦ PDE.partialDeriv j ρ y) x =
      (b j ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.partialDeriv j (fun z ↦ PDE.laplacian ρ z) y) x := by
    rw [PDE.laplacian_convolution_right (hb j) (hdc j) ((hd j).of_le h2)]
    exact congrArg (fun φ ↦ (b j ⋆[mul ℝ ℝ, volume] φ) x)
      (funext fun y ↦ PDE.laplacian_partialDeriv_eq hρ j y)
  simp only [hB]
  have hρx : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ ρ (x - y)) := hρ.comp (by fun_prop)
  have hT' := hT (fun y ↦ ρ (x - y)) hρx (hρc.comp_homeomorph (Homeomorph.subLeft x))
  have hlap : (fun y ↦ PDE.laplacian (fun z ↦ ρ (x - z)) y) =
      fun y ↦ (fun z ↦ PDE.laplacian ρ z) (x - y) := by
    funext y
    exact laplacian_comp_const_sub hρ x y
  rw [hlap, secondOrderPairing_comp_const_sub a b c hl x] at hT'
  rw [← hT', secondOrderMollification]

/-- A locally integrable function times a continuous function is locally integrable. -/
theorem locallyIntegrable_continuous_mul {f g : ℝ^n → ℝ} (hg : Continuous g)
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun x ↦ g x * f x) volume :=
  locallyIntegrable_iff.2 fun _ hK ↦
    (hf.integrableOn_isCompact hK).continuousOn_mul hg.continuousOn hK


/-- The pairing of the zero test function vanishes. -/
theorem secondOrderPairing_zero (a : ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ) :
    secondOrderPairing a b c (fun _ ↦ 0) = 0 := by
  simp [secondOrderPairing, PDE.laplacian, PDE.partialDeriv]

/-- The second-order pairing is additive under subtraction of smooth compactly supported test
functions, for locally integrable coefficients. -/
theorem secondOrderPairing_sub {a c : ℝ^n → ℝ} {b : Fin n → ℝ^n → ℝ}
    (ha : LocallyIntegrable a volume) (hb : ∀ j, LocallyIntegrable (b j) volume)
    (hc : LocallyIntegrable c volume) {f g : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    secondOrderPairing a b c (fun y ↦ f y - g y) =
      secondOrderPairing a b c f - secondOrderPairing a b c g := by
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hdf (j : Fin n) (y : ℝ^n) : PDE.partialDeriv j (fun z ↦ f z - g z) y =
      PDE.partialDeriv j f y - PDE.partialDeriv j g y :=
    PDE.partialDeriv_sub ((hf.differentiable (by simp)) y) ((hg.differentiable (by simp)) y)
  have hlf (y : ℝ^n) : PDE.laplacian (fun z ↦ f z - g z) y =
      PDE.laplacian f y - PDE.laplacian g y :=
    PDE.laplacian_sub f g y (hf.of_le h2).contDiffAt (hg.of_le h2).contDiffAt
  have iA := integrable_mul_right_of_hasCompactSupport ha hf.continuous hfc
  have iA' := integrable_mul_right_of_hasCompactSupport ha hg.continuous hgc
  have iB (j : Fin n) : Integrable (fun x ↦ b j x * PDE.partialDeriv j f x) volume :=
    integrable_mul_right_of_hasCompactSupport (hb j)
      (PDE.contDiff_top_partialDeriv (i := j) hf).continuous (hfc.partialDeriv j)
  have iB' (j : Fin n) : Integrable (fun x ↦ b j x * PDE.partialDeriv j g x) volume :=
    integrable_mul_right_of_hasCompactSupport (hb j)
      (PDE.contDiff_top_partialDeriv (i := j) hg).continuous (hgc.partialDeriv j)
  have iC := integrable_mul_right_of_hasCompactSupport hc (PDE.contDiff_laplacian_coord
      hf).continuous
    (HasCompactSupport.coordinate_laplacian hfc)
  have iC' := integrable_mul_right_of_hasCompactSupport hc (PDE.contDiff_laplacian_coord
      hg).continuous
    (HasCompactSupport.coordinate_laplacian hgc)
  simp only [secondOrderPairing, hdf, hlf, mul_sub]
  rw [integral_sub iA iA', integral_sub iC iC']
  have hB : ∑ j, ∫ y, (b j y * PDE.partialDeriv j f y - b j y * PDE.partialDeriv j g y) =
      (∑ j, ∫ y, b j y * PDE.partialDeriv j f y) - ∑ j, ∫ y, b j y * PDE.partialDeriv j g y := by
    rw [Finset.sum_congr rfl fun j _ ↦ integral_sub (iB j) (iB' j)]
    simp only [Finset.sum_sub_distrib]
  rw [hB]
  ring

/-- The pairing is additive in the coefficients: subtracting two coefficient triples
subtracts the pairings. -/
theorem secondOrderPairing_sub_coefficients {a c a' c' : ℝ^n → ℝ} {b b' : Fin n → ℝ^n → ℝ}
    (ha : LocallyIntegrable a volume) (hb : ∀ j, LocallyIntegrable (b j) volume)
    (hc : LocallyIntegrable c volume) (ha' : LocallyIntegrable a' volume)
    (hb' : ∀ j, LocallyIntegrable (b' j) volume) (hc' : LocallyIntegrable c' volume)
    {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    secondOrderPairing a b c ψ - secondOrderPairing a' b' c' ψ =
      secondOrderPairing (fun y ↦ a y - a' y) (fun j y ↦ b j y - b' j y)
        (fun y ↦ c y - c' y) ψ := by
  have hd (j : Fin n) := (PDE.contDiff_top_partialDeriv (i := j) hψ).continuous
  have hl := (PDE.contDiff_laplacian_coord hψ).continuous
  have hlc := HasCompactSupport.coordinate_laplacian hψc
  have iB (j : Fin n) : Integrable (fun y ↦ b j y * PDE.partialDeriv j ψ y) volume :=
    integrable_mul_right_of_hasCompactSupport (hb j) (hd j) (hψc.partialDeriv j)
  have iB' (j : Fin n) : Integrable (fun y ↦ b' j y * PDE.partialDeriv j ψ y) volume :=
    integrable_mul_right_of_hasCompactSupport (hb' j) (hd j) (hψc.partialDeriv j)
  simp only [secondOrderPairing, sub_mul]
  rw [integral_sub (integrable_mul_right_of_hasCompactSupport ha hψ.continuous hψc)
      (integrable_mul_right_of_hasCompactSupport ha' hψ.continuous hψc),
    integral_sub (integrable_mul_right_of_hasCompactSupport hc hl hlc)
      (integrable_mul_right_of_hasCompactSupport hc' hl hlc),
    Finset.sum_congr rfl fun j _ ↦ integral_sub (iB j) (iB' j), Finset.sum_sub_distrib]
  ring

/-- Adding a locally integrable function to the zeroth-order coefficient adds its pairing. -/
theorem secondOrderPairing_add_zeroth {a c f : ℝ^n → ℝ} {b : Fin n → ℝ^n → ℝ}
    (ha : LocallyIntegrable a volume) (hf : LocallyIntegrable f volume) {ψ : ℝ^n → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    secondOrderPairing (fun y ↦ f y + a y) b c ψ =
      (∫ y, f y * ψ y) + secondOrderPairing a b c ψ := by
  simp only [secondOrderPairing, add_mul]
  rw [integral_add (integrable_mul_right_of_hasCompactSupport hf hψ hψc)
    (integrable_mul_right_of_hasCompactSupport ha hψ hψc)]
  ring

/-! ## Growth on balls -/

/-- Ball growth `∫_{B(x,r)} |G| ≤ C (1 + ‖x‖ + r) r^a` for every center `x` and radius
`r ≥ 1`, stated for the lower Lebesgue integral. -/
def BallGrowth (G : ℝ^n → ℝ) (C a : ℝ) : Prop :=
  ∀ x r, 1 ≤ r → ∫⁻ y in Metric.ball x r, ‖G y‖ₑ ≤ ENNReal.ofReal (C * (1 + ‖x‖ + r) * r ^ a)

/-- Ball growth with exponent `a` implies ball growth with every larger exponent. -/
theorem BallGrowth.mono_exponent {G : ℝ^n → ℝ} {C a b : ℝ} (hG : BallGrowth G C a)
    (hC : 0 ≤ C) (hab : a ≤ b) : BallGrowth G C b := by
  intro x r hr
  refine (hG x r hr).trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr hab)
  have : 0 ≤ 1 + ‖x‖ + r := by linarith [norm_nonneg x]
  positivity

/-- A field bounded by the sum of two fields with ball growth has ball growth. -/
theorem ballGrowth_of_norm_le_add {G H K : ℝ^n → ℝ} {C D a : ℝ} (hG : BallGrowth G C a)
    (hH : BallGrowth H D a) (hGm : AEStronglyMeasurable G volume) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK : ∀ y, ‖K y‖ ≤ ‖G y‖ + ‖H y‖) : BallGrowth K (C + D) a := by
  intro x r hr
  have hr0 : 0 ≤ r := by linarith
  have hpos : 0 ≤ (1 + ‖x‖ + r) * r ^ a := by
    have : 0 ≤ 1 + ‖x‖ + r := by linarith [norm_nonneg x]
    positivity
  calc ∫⁻ y in Metric.ball x r, ‖K y‖ₑ ≤ ∫⁻ y in Metric.ball x r, (‖G y‖ₑ + ‖H y‖ₑ) := by
        apply lintegral_mono
        intro y
        simp only [← ofReal_norm]
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hK y)
    _ = (∫⁻ y in Metric.ball x r, ‖G y‖ₑ) + ∫⁻ y in Metric.ball x r, ‖H y‖ₑ :=
        lintegral_add_left' hGm.enorm.restrict _
    _ ≤ ENNReal.ofReal (C * (1 + ‖x‖ + r) * r ^ a) +
        ENNReal.ofReal (D * (1 + ‖x‖ + r) * r ^ a) := add_le_add (hG x r hr) (hH x r hr)
    _ = ENNReal.ofReal ((C + D) * (1 + ‖x‖ + r) * r ^ a) := by
        rw [← ENNReal.ofReal_add (by rw [mul_assoc]; positivity) (by rw [mul_assoc]; positivity)]
        congr 1
        ring

/-- Ball growth with constant `C` implies ball growth with every larger constant. -/
theorem BallGrowth.mono_const {G : ℝ^n → ℝ} {C C' a : ℝ} (hG : BallGrowth G C a)
    (hCC : C ≤ C') : BallGrowth G C' a := by
  intro x r hr
  refine (hG x r hr).trans (ENNReal.ofReal_le_ofReal ?_)
  have : 0 ≤ (1 + ‖x‖ + r) * r ^ a := by
    have : 0 ≤ 1 + ‖x‖ + r := by linarith [norm_nonneg x]
    have : 0 ≤ r ^ a := Real.rpow_nonneg (by linarith) a
    positivity
  nlinarith

/-- The zero field has ball growth with every constant and exponent. -/
theorem BallGrowth.zero (C a : ℝ) : BallGrowth (fun _ : ℝ^n ↦ (0 : ℝ)) C a := by
  intro x r hr
  simp

/-- A finite sum of fields with ball growth has ball growth. -/
theorem ballGrowth_finsetSum {ι : Type*} (s : Finset ι) {G : ι → ℝ^n → ℝ} {C : ι → ℝ} {a : ℝ}
    (hG : ∀ i ∈ s, BallGrowth (G i) (C i) a) (hm : ∀ i ∈ s, AEStronglyMeasurable (G i) volume)
    (hC : ∀ i ∈ s, 0 ≤ C i) : BallGrowth (fun y ↦ ∑ i ∈ s, G i y) (∑ i ∈ s, C i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BallGrowth.zero (n := n) 0 a
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    refine ballGrowth_of_norm_le_add (hG k (Finset.mem_insert_self k s))
      (ih (fun i hi ↦ hG i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hm i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hC i (Finset.mem_insert_of_mem hi)))
      (hm k (Finset.mem_insert_self k s)) (hC k (Finset.mem_insert_self k s))
      (Finset.sum_nonneg fun i hi ↦ hC i (Finset.mem_insert_of_mem hi)) fun y ↦ ?_
    rw [Finset.sum_insert hk]
    exact norm_add_le _ _

/-- Convolution with a continuous kernel supported in `B(0, R)` preserves ball growth. -/
theorem BallGrowth.convolution {G g : ℝ^n → ℝ} {C a R : ℝ} (hG : BallGrowth G C a)
    (hGm : AEStronglyMeasurable G volume) (hC : 0 ≤ C) (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hg : Continuous g) (hgs : ∀ y, R < ‖y‖ → g y = 0) (hgi : Integrable g volume) :
    BallGrowth (G ⋆[mul ℝ ℝ, volume] g)
      (C * (1 + R) ^ (1 + a) * (∫⁻ y, ‖g y‖ₑ).toReal) a := by
  intro x r hr
  set K := ∫⁻ y, ‖g y‖ₑ with hKdef
  have hK : K ≠ ⊤ := hgi.2.ne
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hpoint (y : ℝ^n) : ‖(G ⋆[mul ℝ ℝ, volume] g) y‖ₑ ≤ ∫⁻ t, ‖G t‖ₑ * ‖g (y - t)‖ₑ := by
    rw [convolution_def]
    simpa only [mul_apply', enorm_mul] using
      enorm_integral_le_lintegral_enorm (μ := volume) (fun t ↦ G t * g (y - t))
  have hmeas : AEMeasurable (Function.uncurry fun (y t : ℝ^n) ↦ ‖G t‖ₑ * ‖g (y - t)‖ₑ)
      ((volume.restrict (Metric.ball x r)).prod volume) :=
    hGm.enorm.comp_snd.mul (hg.comp continuous_sub).measurable.enorm.aemeasurable
  have hinner (t : ℝ^n) : ∫⁻ y in Metric.ball x r, ‖G t‖ₑ * ‖g (y - t)‖ₑ ≤
      (Metric.ball x (r + R)).indicator (fun t ↦ ‖G t‖ₑ * K) t := by
    by_cases ht : t ∈ Metric.ball x (r + R)
    · rw [Set.indicator_of_mem ht, lintegral_const_mul' _ _ enorm_ne_top]
      gcongr
      calc ∫⁻ y in Metric.ball x r, ‖g (y - t)‖ₑ ≤ ∫⁻ y, ‖g (y - t)‖ₑ :=
            setLIntegral_le_lintegral _ _
        _ = K := lintegral_sub_right_eq_self (fun y ↦ ‖g y‖ₑ) t
    · have hgt (y : ℝ^n) (hy : y ∈ Metric.ball x r) : ‖G t‖ₑ * ‖g (y - t)‖ₑ = 0 := by
        have := not_lt.mp (Metric.mem_ball.not.mp ht)
        rw [hgs _ (by rw [← dist_eq_norm, dist_comm]; linarith [dist_triangle t y x,
          Metric.mem_ball.mp hy]), enorm_zero, mul_zero]
      rw [Set.indicator_of_notMem ht, setLIntegral_congr_fun measurableSet_ball hgt, lintegral_zero]
  calc ∫⁻ y in Metric.ball x r, ‖(G ⋆[mul ℝ ℝ, volume] g) y‖ₑ
      ≤ ∫⁻ y in Metric.ball x r, ∫⁻ t, ‖G t‖ₑ * ‖g (y - t)‖ₑ := lintegral_mono hpoint
    _ = ∫⁻ t, ∫⁻ y in Metric.ball x r, ‖G t‖ₑ * ‖g (y - t)‖ₑ := lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ t, (Metric.ball x (r + R)).indicator (fun t ↦ ‖G t‖ₑ * K) t := lintegral_mono hinner
    _ = (∫⁻ t in Metric.ball x (r + R), ‖G t‖ₑ) * K := by
        rw [lintegral_indicator measurableSet_ball, lintegral_mul_const' _ _ hK]
    _ ≤ ENNReal.ofReal (C * (1 + ‖x‖ + (r + R)) * (r + R) ^ a) * ENNReal.ofReal K.toReal := by
        rw [ENNReal.ofReal_toReal hK]
        gcongr
        exact hG x (r + R) (by linarith)
    _ ≤ ENNReal.ofReal (C * (1 + R) ^ (1 + a) * K.toReal * (1 + ‖x‖ + r) * r ^ a) := by
        rw [← ENNReal.ofReal_mul (by
          have : 0 ≤ 1 + ‖x‖ + (r + R) := by linarith [norm_nonneg x]
          positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 + ‖x‖ + (r + R) ≤ (1 + R) * (1 + ‖x‖ + r) := by
          nlinarith [norm_nonneg x]
        have h2 : (r + R) ^ a ≤ (1 + R) ^ a * r ^ a := by
          rw [← Real.mul_rpow (by linarith) hr0.le]
          exact Real.rpow_le_rpow (by linarith) (by nlinarith) ha
        have h3 : (1 + R) ^ (1 + a) = (1 + R) * (1 + R) ^ a := by
          rw [Real.rpow_add (by linarith), Real.rpow_one]
        rw [h3]
        have hKr : 0 ≤ K.toReal := ENNReal.toReal_nonneg
        have hxa : 0 ≤ 1 + ‖x‖ + r := by linarith [norm_nonneg x]
        have hra : 0 ≤ r ^ a := Real.rpow_nonneg hr0.le a
        have hRa : 0 ≤ (1 + R) ^ a := Real.rpow_nonneg (by linarith) a
        calc C * (1 + ‖x‖ + (r + R)) * (r + R) ^ a * K.toReal
            ≤ C * ((1 + R) * (1 + ‖x‖ + r)) * ((1 + R) ^ a * r ^ a) * K.toReal := by
              gcongr
          _ = _ := by ring

/-- Hölder's inequality on balls: an `Lᵖ` field has mass at most
`‖G‖ₚ (α r^n)^{1 - 1/p}` on every ball of radius `r`, where `α` is the unit-ball volume. -/
theorem lintegral_ball_enorm_le_of_memLp [Fact (0 < n)] {G : ℝ^n → ℝ} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p)
    (hG : MemLp G p volume) (x : ℝ^n) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ y in Metric.ball x r, ‖G y‖ₑ ≤ ENNReal.ofReal ((eLpNorm G p volume).toReal *
      (unitBallVolume n * r ^ n) ^ (1 - 1 / p.toReal)) := by
  have : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hvol : volume (Metric.ball x r) = ENNReal.ofReal (unitBallVolume n * r ^ n) := by
    rw [EuclideanSpace.volume_ball (Fin n) x r, Fintype.card_fin, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (by positivity), mul_comm]
    rfl
  have hθ : 0 ≤ 1 - 1 / p.toReal := by
    rcases eq_or_ne p ⊤ with rfl | hpt
    · simp
    · have h1 : 1 ≤ p.toReal := by
        have := ENNReal.toReal_mono hpt hp1
        simpa using this
      have : 1 / p.toReal ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact h1
      linarith
  have hHolder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict (Metric.ball x r)) hp1 hG.aestronglyMeasurable.restrict
  rw [eLpNorm_one_eq_lintegral_enorm hG.aestronglyMeasurable.restrict,
    Measure.restrict_apply_univ, hvol] at hHolder
  simp only [ENNReal.toReal_one, div_one] at hHolder
  refine hHolder.trans ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hG.eLpNorm_ne_top,
    ← ENNReal.ofReal_rpow_of_nonneg (by have := unitBallVolume_pos n; positivity) hθ]
  gcongr
  exact Measure.restrict_le_self

/-- An `Lᵖ` field, `1 ≤ p < ∞`, has mass at most `M r^{n(1 - 1/p)}` on balls of radius `r`. -/
theorem exists_lintegral_ball_le_of_memLp [Fact (0 < n)] {G : ℝ^n → ℝ} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hG : MemLp G p volume) :
    ∃ M, 0 ≤ M ∧ ∀ x r, 0 ≤ r → ∫⁻ y in Metric.ball x r, ‖G y‖ₑ ≤
      ENNReal.ofReal (M * r ^ ((n : ℝ) * (1 - 1 / p.toReal))) := by
  have hα := unitBallVolume_pos n
  have hθ : 0 ≤ 1 - 1 / p.toReal := by
    rcases eq_or_ne p ⊤ with rfl | hpt
    · simp
    · have h1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hpt hp1
      have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
      linarith
  refine ⟨(eLpNorm G p volume).toReal * unitBallVolume n ^ (1 - 1 / p.toReal),
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hα.le _), fun x r hr ↦ ?_⟩
  refine (lintegral_ball_enorm_le_of_memLp hp1 hG x hr).trans (le_of_eq ?_)
  congr 1
  rw [Real.mul_rpow hα.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr]
  ring

/-- A mass bound `∫_{B(x,r)} |G| ≤ M r^b` gives ball growth with exponent `b - 1`. -/
theorem ballGrowth_of_lintegral_ball_le {G : ℝ^n → ℝ} {M b : ℝ} (hM : 0 ≤ M)
    (h : ∀ x r, 1 ≤ r → ∫⁻ y in Metric.ball x r, ‖G y‖ₑ ≤ ENNReal.ofReal (M * r ^ b)) :
    BallGrowth G M (b - 1) := by
  intro x r hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  refine (h x r hr).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.rpow_sub hr0, Real.rpow_one, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hM
  rw [mul_div_assoc', le_div_iff₀ hr0]
  have : 0 ≤ r ^ b := Real.rpow_nonneg hr0.le b
  nlinarith [norm_nonneg x]

/-- An `Lᵖ` field, `1 ≤ p`, has ball growth with every exponent `e ≥ n (1 - 1/p) - 1`. -/
theorem exists_ballGrowth_of_memLp [Fact (0 < n)] {G : ℝ^n → ℝ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hG : MemLp G p volume) {e : ℝ} (he : (n : ℝ) * (1 - 1 / p.toReal) - 1 ≤ e) :
    ∃ C, 0 ≤ C ∧ BallGrowth G C e := by
  obtain ⟨M, hM, hMb⟩ := exists_lintegral_ball_le_of_memLp hp1 hG
  exact ⟨M, hM, (ballGrowth_of_lintegral_ball_le hM fun x r hr ↦
    hMb x r (by linarith)).mono_exponent hM he⟩

/-- A field bounded by `‖y‖ |G y|`, where `G` has mass `M r^b` on balls, has ball growth with
exponent `b`. -/
theorem ballGrowth_of_norm_le_norm_mul {G H : ℝ^n → ℝ} {M b : ℝ} (hM : 0 ≤ M)
    (h : ∀ x r, 1 ≤ r → ∫⁻ y in Metric.ball x r, ‖G y‖ₑ ≤ ENNReal.ofReal (M * r ^ b))
    (hH : ∀ y, ‖H y‖ ≤ ‖y‖ * ‖G y‖) : BallGrowth H M b := by
  intro x r hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  calc ∫⁻ y in Metric.ball x r, ‖H y‖ₑ
      ≤ ∫⁻ y in Metric.ball x r, ENNReal.ofReal (‖x‖ + r) * ‖G y‖ₑ := by
        apply setLIntegral_mono' measurableSet_ball
        intro y hy
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by linarith [norm_nonneg x])]
        apply ENNReal.ofReal_le_ofReal
        refine (hH y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        rw [Metric.mem_ball, dist_eq_norm] at hy
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ ‖x‖ + r := by linarith
    _ = ENNReal.ofReal (‖x‖ + r) * ∫⁻ y in Metric.ball x r, ‖G y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (‖x‖ + r) * ENNReal.ofReal (M * r ^ b) := by gcongr; exact h x r hr
    _ ≤ ENNReal.ofReal (M * (1 + ‖x‖ + r) * r ^ b) := by
        rw [← ENNReal.ofReal_mul (by linarith [norm_nonneg x])]
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ M * r ^ b := mul_nonneg hM (Real.rpow_nonneg hr0.le b)
        nlinarith [norm_nonneg x]

/-- A compactly supported function vanishes outside some closed ball centred at the origin. -/
theorem exists_norm_bound_of_hasCompactSupport {g : ℝ^n → ℝ} (hg : HasCompactSupport g) :
    ∃ R, 0 ≤ R ∧ ∀ y, R < ‖y‖ → g y = 0 := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun y hy ↦ image_eq_zero_of_notMem_tsupport fun hy' ↦ ?_⟩
  have h := hR hy'
  rw [Metric.mem_closedBall, dist_zero_right] at h
  linarith [le_max_left R 0]

/-- Convolution of a field with ball growth and a smooth compactly supported kernel has ball
growth with the same exponent. -/
theorem exists_ballGrowth_convolution {G g : ℝ^n → ℝ} {C a : ℝ} (hG : BallGrowth G C a)
    (hGm : AEStronglyMeasurable G volume) (hC : 0 ≤ C) (ha : 0 ≤ a) (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ∃ D, 0 ≤ D ∧ BallGrowth (G ⋆[mul ℝ ℝ, volume] g) D a := by
  obtain ⟨R, hR, hRg⟩ := exists_norm_bound_of_hasCompactSupport hgc
  refine ⟨_, ?_, hG.convolution hGm hC ha hR hg hRg (hg.integrable_of_hasCompactSupport hgc)⟩
  have : 0 ≤ (1 + R) ^ (1 + a) := Real.rpow_nonneg (by linarith) _
  have : 0 ≤ (∫⁻ y, ‖g y‖ₑ).toReal := ENNReal.toReal_nonneg
  positivity

/-- **Vanishing of harmonic second-order distributions.** A second-order distribution on `ℝⁿ`
whose locally integrable coefficients have ball growth with exponent `e`, `0 ≤ e`,
`e + 1 < n`, and which annihilates the Laplacian of every test function, vanishes on every
test function. -/
theorem secondOrderPairing_eq_zero [Fact (0 < n)] {a c : ℝ^n → ℝ} {b : Fin n → ℝ^n → ℝ}
    (ha : LocallyIntegrable a volume) (hb : ∀ j, LocallyIntegrable (b j) volume)
    (hc : LocallyIntegrable c volume)
    (hT : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      secondOrderPairing a b c (fun y ↦ PDE.laplacian ψ y) = 0)
    {C e : ℝ} (hC : 0 ≤ C) (he0 : 0 ≤ e) (he : e + 1 < n)
    (hga : BallGrowth a C e) (hgb : ∀ j, BallGrowth (b j) C e) (hgc : BallGrowth c C e)
    {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    secondOrderPairing a b c ψ = 0 := by
  set ρ : ℝ^n → ℝ := fun y ↦ ψ (-y) with hρdef
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := hψ.comp contDiff_neg
  have hρc : HasCompactSupport ρ := hψc.comp_homeomorph (Homeomorph.neg _)
  have hharm := isHarmonicPDE_secondOrderMollification ha hb hc hT hρ hρc
  have hd (j : Fin n) := PDE.contDiff_top_partialDeriv (i := j) hρ
  have hdc (j : Fin n) : HasCompactSupport (fun y ↦ PDE.partialDeriv j ρ y) :=
    hρc.partialDeriv j
  have hl := PDE.contDiff_laplacian_coord hρ
  have hlc := HasCompactSupport.coordinate_laplacian hρc
  obtain ⟨DA, hDA, gA⟩ := exists_ballGrowth_convolution hga ha.aestronglyMeasurable hC he0
    hρ.continuous hρc
  have hB (j : Fin n) := exists_ballGrowth_convolution (hgb j) (hb j).aestronglyMeasurable hC
    he0 (hd j).continuous (hdc j)
  choose DB hDB gB using hB
  obtain ⟨DC, hDC, gC⟩ := exists_ballGrowth_convolution hgc hc.aestronglyMeasurable hC he0
    hl.continuous hlc
  have cA : Continuous (a ⋆[mul ℝ ℝ, volume] ρ) :=
    (hρc.contDiff_convolution_right (mul ℝ ℝ) ha hρ).continuous
  have cB (j : Fin n) : Continuous
      (b j ⋆[mul ℝ ℝ, volume] fun y ↦ PDE.partialDeriv j ρ y) :=
    ((hdc j).contDiff_convolution_right (mul ℝ ℝ) (hb j) (hd j)).continuous
  have gSum := ballGrowth_finsetSum Finset.univ (fun j _ ↦ gB j)
    (fun j _ ↦ (cB j).aestronglyMeasurable) (fun j _ ↦ hDB j)
  have gAB := ballGrowth_of_norm_le_add gA gSum cA.aestronglyMeasurable hDA
    (Finset.sum_nonneg fun j _ ↦ hDB j)
    (K := fun y ↦ (a ⋆[mul ℝ ℝ, volume] ρ) y -
      ∑ j, (b j ⋆[mul ℝ ℝ, volume] fun z ↦ PDE.partialDeriv j ρ z) y)
    (fun y ↦ norm_sub_le _ _)
  have gH := ballGrowth_of_norm_le_add gAB gC
    (cA.sub (continuous_finsetSum _ fun j _ ↦ cB j)).aestronglyMeasurable
    (add_nonneg hDA (Finset.sum_nonneg fun j _ ↦ hDB j)) hDC
    (K := secondOrderMollification a b c ρ) (fun y ↦ norm_add_le _ _)
  set D := DA + ∑ j, DB j + DC
  have hcont : Continuous (secondOrderMollification a b c ρ) :=
    continuousOn_univ.mp hharm.contDiffOn.continuousOn
  have hzero := hharm.eq_zero_of_integral_abs_le he (C := D) fun x r hr ↦ by
    have h := gH x r hr
    have hr0 : 0 ≤ r := by linarith
    have : 0 ≤ D := add_nonneg (add_nonneg hDA (Finset.sum_nonneg fun j _ ↦ hDB j)) hDC
    have hnn : 0 ≤ D * (1 + ‖x‖ + r) * r ^ e := by positivity
    simp only [← Real.norm_eq_abs]
    rw [integral_norm_eq_lintegral_enorm hcont.aestronglyMeasurable.restrict]
    exact ENNReal.toReal_le_of_le_ofReal hnn h
  have h0 := congrFun hzero 0
  rw [← secondOrderPairing_comp_const_sub a b c hρ 0] at h0
  simpa [hρdef] using h0

/-- **Square-integrable weakly harmonic functions vanish.** On `ℝⁿ`, `n ≥ 2`, a square-integrable
function whose integral against the Laplacian of every smooth compactly supported function is
zero vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_mul_laplacian_eq_zero (hn : 2 ≤ n) {f : ℝ^n → ℝ}
    (hf : MemLp f 2 volume)
    (h : ∀ χ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      ∫ x, f x * PDE.laplacian χ x = 0) :
    f =ᵐ[volume] 0 := by
  have : Fact (0 < n) := ⟨by omega⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable one_le_two
  obtain ⟨C, hC, hgC⟩ := exists_ballGrowth_of_memLp (G := f) (p := 2) one_le_two hf
    (e := (n : ℝ) / 2 - 1) (by norm_num; linarith)
  have hzero : BallGrowth (0 : ℝ^n → ℝ) C ((n : ℝ) / 2 - 1) := fun x r hr ↦ by
    simp
  have hT : ∀ ψ : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      secondOrderPairing f (fun _ ↦ 0) 0 (fun y ↦ PDE.laplacian ψ y) = 0 := by
    intro ψ hψ hc
    simp [secondOrderPairing, h ψ hψ hc]
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc ↦ ?_
  have h0 := secondOrderPairing_eq_zero (b := fun _ ↦ 0) (c := 0) hloc
    (fun _ ↦ locallyIntegrable_zero) locallyIntegrable_zero hT hC (by linarith)
    (by linarith) hgC (fun _ ↦ hzero) hzero (ψ := g) hg hgc
  simp only [secondOrderPairing, zero_mul, integral_zero, Finset.sum_const_zero, add_zero,
    Pi.zero_apply] at h0
  simpa [smul_eq_mul, mul_comm] using h0

end LaplacianEquation
