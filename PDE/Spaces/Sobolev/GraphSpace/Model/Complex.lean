/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Complex
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import Mathlib.Analysis.Complex.OperatorNorm
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Complex Sobolev graphs

The ambient norm is the `ℓ²` norm of the complex `L²` weak derivatives, indexed by the
symmetric multi-indices. The graph is the intersection of the inverse images of
the real Sobolev graph under real and imaginary projection. Thus its definition uses weak
derivatives, independently of Fourier transforms.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Complex `L²` coordinates for all derivatives of order at most `k`. -/
abbrev ComplexWkAmbientOn (n k : ℕ) (Ω : Set (ℝ^n)) :=
  PiLp 2 (fun _ : DerivIndex n k ↦ Lp ℂ 2 (domainMeasure n Ω))

/-- Apply a real coordinate functional to each complex derivative. -/
def realCoordinateTuple (L : ℂ →L[ℝ] ℝ) :
    ComplexWkAmbientOn n k Ω →ₗ[ℝ] WkpAmbientOn n k 2 Ω where
  toFun U := WithLp.toLp 2 fun a ↦ L.compLpL 2 (domainMeasure n Ω) (U a)
  map_add' U V := by
    apply PiLp.ext
    intro a
    exact map_add (L.compLpL 2 (domainMeasure n Ω)) (U a) (V a)
  map_smul' c U := by
    apply PiLp.ext
    intro a
    exact map_smul (L.compLpL 2 (domainMeasure n Ω)) c (U a)

/-- Coordinatewise contractions contract the Hilbert sum of derivative norms. -/
theorem norm_realCoordinateTuple_le (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (U : ComplexWkAmbientOn n k Ω) : ‖realCoordinateTuple L U‖ ≤ ‖U‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro a _
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((L.compLpL 2 (domainMeasure n Ω)).le_opNorm (U a)).trans
    (by
      calc
        _ ≤ ‖L‖ * ‖U a‖ :=
          mul_le_mul_of_nonneg_right L.norm_compLpL_le (norm_nonneg _)
        _ ≤ ‖U a‖ := mul_le_of_le_one_left (norm_nonneg _) hL)

/-- The complex graph is defined by the real weak-derivative constraints in both coordinates. -/
def complexWkSubmoduleOn (n k : ℕ) (Ω : Set (ℝ^n)) :
    Submodule ℝ (ComplexWkAmbientOn n k Ω) :=
  (wkpSubmoduleOn n k 2 Ω).comap (realCoordinateTuple Complex.reCLM) ⊓
    (wkpSubmoduleOn n k 2 Ω).comap (realCoordinateTuple Complex.imCLM)

/-- Complex `H^k(Ω)` defined by square-integrable weak derivatives, with the graph norm. -/
abbrev ComplexWkSpaceOn (n k : ℕ) (Ω : Set (ℝ^n)) : Type :=
  complexWkSubmoduleOn n k Ω

/-- The real weak-derivative graph of a complex graph. -/
def ComplexWkSpaceOn.re (U : ComplexWkSpaceOn n k Ω) : W^{k,2}(Ω) :=
  ⟨realCoordinateTuple Complex.reCLM U.1, U.2.1⟩

/-- The imaginary weak-derivative graph of a complex graph. -/
def ComplexWkSpaceOn.im (U : ComplexWkSpaceOn n k Ω) : W^{k,2}(Ω) :=
  ⟨realCoordinateTuple Complex.imCLM U.1, U.2.2⟩

theorem ComplexWkSpaceOn.norm_re_le (U : ComplexWkSpaceOn n k Ω) : ‖U.re‖ ≤ ‖U‖ :=
  norm_realCoordinateTuple_le Complex.reCLM (by simp) U.1

theorem ComplexWkSpaceOn.norm_im_le (U : ComplexWkSpaceOn n k Ω) : ‖U.im‖ ≤ ‖U‖ :=
  norm_realCoordinateTuple_le Complex.imCLM (by simp) U.1

/-- The graph constraints give the complex distributional derivatives of the base function. -/
theorem ComplexWkSpaceOn.hasComplexWeakDerivativeOn
    (U : ComplexWkSpaceOn n k Ω) (a : DerivIndex n k) :
    HasComplexWeakDerivativeOn Ω a.toList (U.1 (baseIndex n k)) (U.1 a) :=
  ⟨(U.re.2 a).congr_ae (Complex.reCLM.coeFn_compLpL _)
      (Complex.reCLM.coeFn_compLpL _),
    (U.im.2 a).congr_ae (Complex.imCLM.coeFn_compLpL _)
      (Complex.imCLM.coeFn_compLpL _)⟩

/-- Conversely, complex weak derivatives satisfy the graph constraints. -/
theorem mem_complexWkSubmoduleOn_iff (U : ComplexWkAmbientOn n k Ω) :
    U ∈ complexWkSubmoduleOn n k Ω ↔
      ∀ a : DerivIndex n k,
        HasComplexWeakDerivativeOn Ω a.toList (U (baseIndex n k)) (U a) := by
  constructor
  · intro h a
    exact ComplexWkSpaceOn.hasComplexWeakDerivativeOn ⟨U, h⟩ a
  · intro h
    constructor <;> intro a
    · exact ((h a).1).congr_ae (Complex.reCLM.coeFn_compLpL _).symm
        (Complex.reCLM.coeFn_compLpL _).symm
    · exact ((h a).2).congr_ae (Complex.imCLM.coeFn_compLpL _).symm
        (Complex.imCLM.coeFn_compLpL _).symm

/-- Assemble real and imaginary `L²` functions as a complex function. -/
def complexLp (f g : Lp ℝ 2 (domainMeasure n Ω)) :
    Lp ℂ 2 (domainMeasure n Ω) :=
  Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) f +
    Complex.I • Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) g

theorem coeFn_complexLp (f g : Lp ℝ 2 (domainMeasure n Ω)) :
    (complexLp f g : ℝ^n → ℂ) =ᵐ[domainMeasure n Ω]
      fun x ↦ (f x : ℂ) + Complex.I * (g x : ℂ) := by
  filter_upwards
    [Lp.coeFn_add (Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) f)
        (Complex.I • Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) g),
      Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) g),
      Complex.ofRealCLM.coeFn_compLpL f, Complex.ofRealCLM.coeFn_compLpL g]
    with x ha hs hf hg
  simp only [complexLp, ha, Pi.add_apply, hs, Pi.smul_apply, hf, hg,
    Complex.ofRealCLM_apply, smul_eq_mul]

/-- The real and imaginary components of the assembled `L²` function. -/
theorem re_im_complexLp (f g : Lp ℝ 2 (domainMeasure n Ω)) :
    Complex.reCLM.compLpL 2 (domainMeasure n Ω) (complexLp f g) = f ∧
      Complex.imCLM.compLpL 2 (domainMeasure n Ω) (complexLp f g) = g := by
  constructor <;> apply Lp.ext
  · filter_upwards [Complex.reCLM.coeFn_compLpL (complexLp f g), coeFn_complexLp f g]
      with x hr hx
    simp [hr, hx]
  · filter_upwards [Complex.imCLM.coeFn_compLpL (complexLp f g), coeFn_complexLp f g]
      with x hi hx
    simp [hi, hx]

/-- Recombine two real Sobolev graphs, retaining the complex `ℓ²(L²)` norm. -/
def complexOfRealGraphs (U V : W^{k,2}(Ω)) : ComplexWkSpaceOn n k Ω :=
  ⟨WithLp.toLp 2 (fun a ↦ complexLp (U.1 a) (V.1 a)), by
    constructor
    · have heq : realCoordinateTuple Complex.reCLM
          (WithLp.toLp 2 (fun a ↦ complexLp (U.1 a) (V.1 a))) = U.1 := by
        apply PiLp.ext
        intro a
        exact (re_im_complexLp (U.1 a) (V.1 a)).1
      change realCoordinateTuple Complex.reCLM _ ∈ wkpSubmoduleOn n k 2 Ω
      rw [heq]
      exact U.2
    · have heq : realCoordinateTuple Complex.imCLM
          (WithLp.toLp 2 (fun a ↦ complexLp (U.1 a) (V.1 a))) = V.1 := by
        apply PiLp.ext
        intro a
        exact (re_im_complexLp (U.1 a) (V.1 a)).2
      change realCoordinateTuple Complex.imCLM _ ∈ wkpSubmoduleOn n k 2 Ω
      rw [heq]
      exact V.2⟩

/-- Complexification of a real derivative tuple is a contraction. -/
theorem norm_ofReal_tuple_le (U : WkpAmbientOn n k 2 Ω) :
    ‖(WithLp.toLp 2 fun a ↦
      Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) (U a) :
        ComplexWkAmbientOn n k Ω)‖ ≤ ‖U‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro a _
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact ((Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω)).le_opNorm (U a)).trans
    (by
      simpa using mul_le_mul_of_nonneg_right
        (Complex.ofRealCLM.norm_compLpL_le (p := 2) (μ := domainMeasure n Ω))
        (norm_nonneg (U a)))

/-- Recombination is bounded by the sum of the two real Sobolev norms. -/
theorem norm_complexOfRealGraphs_le (U V : W^{k,2}(Ω)) :
    ‖complexOfRealGraphs U V‖ ≤ ‖U‖ + ‖V‖ := by
  let A (W : WkpAmbientOn n k 2 Ω) : ComplexWkAmbientOn n k Ω :=
    WithLp.toLp 2 fun a ↦ Complex.ofRealCLM.compLpL 2 (domainMeasure n Ω) (W a)
  have heq : (complexOfRealGraphs U V).1 = A U.1 + Complex.I • A V.1 := by
    apply PiLp.ext
    intro a
    rfl
  change ‖(complexOfRealGraphs U V).1‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖A U.1‖ + ‖Complex.I • A V.1‖ := norm_add_le _ _
    _ = ‖A U.1‖ + ‖A V.1‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ ‖U‖ + ‖V‖ := add_le_add (norm_ofReal_tuple_le U.1) (norm_ofReal_tuple_le V.1)

/-- Every derivative word of length at most `k` is represented in the complex graph. -/
theorem ComplexWkSpaceOn.hasComplexWeakDerivativeOn_list
    (U : ComplexWkSpaceOn n k Ω) (α : List (Fin n)) (hα : α.length ≤ k) :
    HasComplexWeakDerivativeOn Ω α (U.1 (baseIndex n k))
      (U.1 (derivIndexOfList α hα)) :=
  (U.hasComplexWeakDerivativeOn (derivIndexOfList α hα)).perm
    (derivIndexOfList_toList_perm α hα)

/-- On an open domain the base function determines all complex weak-derivative coordinates. -/
theorem ComplexWkSpaceOn.ext_base_ae (hΩ : IsOpen Ω) {U V : ComplexWkSpaceOn n k Ω}
    (hbase : U.1 (baseIndex n k) =ᵐ[domainMeasure n Ω] V.1 (baseIndex n k)) :
    U = V := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  have hu := (U.hasComplexWeakDerivativeOn a).congr_ae hbase
    (Filter.EventuallyEq.refl _ _)
  have hv := V.hasComplexWeakDerivativeOn a
  filter_upwards [hu.1.unique_ae hΩ hv.1, hu.2.unique_ae hΩ hv.2] with x hr hi
  exact Complex.ext hr hi

end SobolevSpace.GraphSpace
