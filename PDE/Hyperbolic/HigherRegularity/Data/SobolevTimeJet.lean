/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PrincipalForms
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic

/-!
# Sobolev time jets for higher-order wave regularity

Evans's higher-order wave argument repeatedly differentiates in time while
losing one spatial Sobolev order.  `SobolevTimeJet` records this decreasing
scale together with the weak derivative identity between every adjacent pair:

`f ∈ L²_t H^m_x`, `f_t ∈ L²_t H^{m-1}_x`, ..., `∂ₜ^m f ∈ L²_t L²_x`.

We also define the canonical maps from Sobolev-valued trajectories
to the `L²` pivot and Dirichlet dual used by the weak wave equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, conclusion (63), and step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace
open PDE.Analysis.Evolution
open scoped ENNReal

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
Apply the canonical restriction `H^{m+1}(Omega) → H^m(Omega)` to a
Bochner trajectory.

Keeping this as a bounded map on `L²` classes is important: the derivative
relation below is independent of all choices of pointwise representatives.
-/
noncomputable def lowerOrderTimeLp
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)) :=
  (lowerOrderCLM (n := n) (p := 2) (Ω := Omega)
    (Nat.le_succ m)).compLpL 2 (volume.restrict (Set.Ioc t0 t1)) f

/-- `lowerOrderTimeLp` acts pointwise almost everywhere. -/
theorem lowerOrderTimeLp_apply_ae
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    (lowerOrderTimeLp f : ℝ → W^{m,2}(Omega)) =ᵐ[ (volume.restrict (Set.Ioc t0 t1))] fun t ↦
      lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (f t) :=
  (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m)).coeFn_compLpL f

/--
Take the order-zero spatial coordinate of a Sobolev-valued Bochner
trajectory.

The weak-wave theory uses `L²(Omega)` as its pivot space, whereas the
higher-order induction stores every time derivative in its precise Sobolev
space.  This bounded map is the canonical passage between those two
representations; it does not choose pointwise representatives.
-/
noncomputable def baseCoordinateTimeLp
    (f : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)) :=
  (wkpBaseCoordinateCLM
    (n := n) (m := m) (p := 2) (Ω := Omega)).compLpL
      2 (volume.restrict (Set.Ioc t0 t1)) f

/-- `baseCoordinateTimeLp` is pointwise the Sobolev base coordinate a.e. -/
theorem baseCoordinateTimeLp_apply_ae
    (f : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    (baseCoordinateTimeLp f : ℝ → DerivLp n 2 Omega) =ᵐ[ (volume.restrict (Set.Ioc t0 t1))] fun t ↦
      wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) (f t) :=
  (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega)).coeFn_compLpL f

/-- Apply the pivot-to-dual map of a Gelfand triple to a pivot-valued `L²` trajectory. -/
noncomputable def liftPivotToDualTimeLp
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : PDE.Analysis.Evolution.GelfandTriple (V := V) (H := H))
    (f : Lp H 2 (volume.restrict (Set.Ioc t0 t1))) :
    Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc t0 t1)) :=
  T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc t0 t1)) f

private theorem liftPivotToDualTimeLp_apply_ae {V H : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : PDE.Analysis.Evolution.GelfandTriple (V := V) (H := H))
    (f : Lp H 2 (volume.restrict (Set.Ioc t0 t1))) :
    (liftPivotToDualTimeLp T f : ℝ → StrongDual ℝ V) =ᵐ[ volume.restrict (Set.Ioc t0 t1)] fun t ↦
      T.pivotToDual (f t) :=
  T.pivotToDual.coeFn_compLpL f

/--
Embed a Sobolev-valued trajectory into the Dirichlet dual
`L²_t H⁻¹_x`.

At almost every time this is the load

`v ↦ ⟪f(t), v⟫_{L²(Omega)}`.

Consequently the forcing and acceleration fields in the concrete
`H¹₀ ↪ L² ↪ H⁻¹` weak-wave equation can be supplied directly by members of
the decreasing Sobolev time jet.
-/
noncomputable def dirichletLoadTimeLp
    (hOmegaOpen : IsOpen Omega)
    (f : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    Lp (StrongDual ℝ
      (H¹₀(Omega)))
        2 (volume.restrict (Set.Ioc t0 t1)) :=
  liftPivotToDualTimeLp
    (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen)
    (baseCoordinateTimeLp f)

/-- The Dirichlet dual load map has its expected pointwise realization. -/
theorem dirichletLoadTimeLp_apply_ae (hOmegaOpen : IsOpen Omega)
    (f : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    (dirichletLoadTimeLp hOmegaOpen f : ℝ → StrongDual ℝ (H¹₀(Omega)))
      =ᵐ[ (volume.restrict (Set.Ioc t0 t1))] fun t ↦ loadFunctional (n := n) (Ω := Omega)
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) (f t)) := by
  have hdual := liftPivotToDualTimeLp_apply_ae
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen) (baseCoordinateTimeLp f)
  filter_upwards [hdual, baseCoordinateTimeLp_apply_ae f] with
    t hdual hbase
  rw [show dirichletLoadTimeLp hOmegaOpen f t = (SobolevSpace.GraphSpace.h10L2GelfandTriple
        hOmegaOpen).pivotToDual (baseCoordinateTimeLp f t) by
      simpa only [dirichletLoadTimeLp] using! hdual, hbase]
  rfl

/--
The recursive derivative data underlying an order-`m` Sobolev time jet.

At order zero there is only an `L²_t L²_x` trajectory.  At successor order,
the head is `H^{m+1}`-valued, its weak time derivative is an `H^m`-valued
trajectory, and that derivative itself carries the remaining order-`m`
jet.  The canonical map `H^{m+1} → H^m` is inserted before stating the
weak derivative identity in the identity Gelfand triple on `H^m`.

This is an ordinary Hilbert-valued weak derivative, not an additional PDE
assumption.  The Gelfand form is used because the
Lions-Magenes theorem then supplies the canonical representative continuous
through both time endpoints.

This recursive shape avoids storing the same analytic object at unrelated
dependent indices.  It makes the induction in Evans
literal: differentiating once means taking the recursive tail.
-/
inductive SobolevTimeJetCore
    (n : ℕ) (Omega : Set (ℝ^n)) (t0 t1 : ℝ) :
    (m : ℕ) →
      Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)) → Type
  | zero
      (f : Lp (W^{0,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
      SobolevTimeJetCore n Omega t0 t1 0 f
  | succ {m : ℕ}
      (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
      (df : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
      (derivative :
        PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
          (PDE.Analysis.Evolution.GelfandTriple.identity
            (W^{m,2}(Omega)))
          (lowerOrderTimeLp f)
          (PDE.Analysis.Evolution.rieszToDualLp df))
      (tail : SobolevTimeJetCore n Omega t0 t1 m df) :
      SobolevTimeJetCore n Omega t0 t1 (m + 1) f

/--
An order-`m` time jet whose successive derivatives take values in

`H^m(Omega), H^{m-1}(Omega), ..., H^0(Omega)`.

Each time derivative spends one spatial derivative in this regularity budget;
see Evans, §7.2.3, Theorem 6 for its use in the wave equation. The recursive core
requires adjacent entries to be weak time derivatives, so the entries
describe one trajectory and its derivatives.
-/
structure SobolevTimeJet
    (n m : ℕ) (Omega : Set (ℝ^n)) (t0 t1 : ℝ) where
  /-- The undifferentiated `H^m`-valued trajectory. -/
  head : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))
  /-- All weak derivatives through order `m`. -/
  derivatives : SobolevTimeJetCore n Omega t0 t1 m head

namespace SobolevTimeJet

/-- The order-zero jet of an `L²_t L²_x` trajectory. -/
def zero
    (f : Lp (W^{0,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))) :
    SobolevTimeJet n 0 Omega t0 t1 :=
  ⟨f, SobolevTimeJetCore.zero f⟩

/--
Adjoin one more regular trajectory and its verified time derivative to a
jet.
-/
def succ
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (dF : SobolevTimeJet n m Omega t0 t1)
    (hderiv :
      PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
        (PDE.Analysis.Evolution.GelfandTriple.identity
          (W^{m,2}(Omega)))
        (lowerOrderTimeLp f)
        (PDE.Analysis.Evolution.rieszToDualLp dF.head)) :
    SobolevTimeJet n (m + 1) Omega t0 t1 :=
  ⟨f, SobolevTimeJetCore.succ f dF.head hderiv dF.derivatives⟩

/--
Drop the undifferentiated entry from an order-`m+1` jet.

Analytically this is

`(f, fₜ, ..., ∂ₜ^{m+1}f) ↦ (fₜ, ..., ∂ₜ^{m+1}f)`.

The result has precisely the decreasing Sobolev scale required by the
induction hypothesis in Evans's proof.
-/
def timeDerivative
    (F : SobolevTimeJet n (m + 1) Omega t0 t1) :
    SobolevTimeJet n m Omega t0 t1 := by
  cases F.derivatives with
  | succ _ df _ tail =>
      exact ⟨df, tail⟩

/--
The head and the time-derivative tail satisfy the weak derivative identity
in `H^m(Omega)`.
-/
theorem hasWeakTimeDerivative_timeDerivative (F : SobolevTimeJet n (m + 1) Omega t0 t1) :
    HasWeakTimeDerivativeOn (Set.Ioo t0 t1) (fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega)
      (Nat.le_succ m) (F.head t)) (fun t ↦ F.timeDerivative.head t) := by
  cases F with
  | mk head derivatives =>
      cases derivatives with
      | succ _ df hderiv _ =>
          have h := hderiv.identity_hasWeakTimeDerivativeOn
          have hhead : (fun t ↦ lowerOrderTimeLp head t) =ᵐ[ (volume.restrict (Set.Ioc t0 t1))]
                fun t ↦ lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (Nat.le_succ m) (head t) :=
            lowerOrderTimeLp_apply_ae head
          exact h.congr_ae_restrict measurableSet_Ioo (hhead.filter_mono (MeasureTheory.ae_mono
                ((volume : Measure ℝ).restrict_mono_set Set.Ioo_subset_Ioc_self)))
            Filter.EventuallyEq.rfl

namespace Core

/--
Every trajectory in a recursive Sobolev jet is essentially bounded in its
own spatial Sobolev space.
-/
def IsEssentiallyBounded :
    {m : ℕ} →
      {f : Lp (W^{m,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1))} →
      SobolevTimeJetCore n Omega t0 t1 m f → Prop
  | 0, f, .zero _ =>
      MemLp (fun t ↦ f t) (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1))
  | _ + 1, f, .succ _ _ _ tail =>
      MemLp (fun t ↦ f t) (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1)) ∧
        IsEssentiallyBounded tail

end Core

/--
The `L∞` conclusion associated with a Sobolev time jet.

For a solution jet of order `m+1`, this is exactly Evans's assertion

`∂ₜᵏ u ∈ L∞(t0,t1; H^{m+1-k}(Omega))`

for every `0 ≤ k ≤ m+1`.
-/
def IsEssentiallyBounded
    (F : SobolevTimeJet n m Omega t0 t1) : Prop :=
  Core.IsEssentiallyBounded F.derivatives

/--
Essential boundedness descends to the differentiated tail of a solution
jet.  This is the regularity bookkeeping used in the induction step.
-/
theorem IsEssentiallyBounded.timeDerivative {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    (hF : F.IsEssentiallyBounded) :
    F.timeDerivative.IsEssentiallyBounded := by
  cases F with
  | mk head derivatives =>
      cases derivatives with
      | succ _ _ _ _ =>
          exact hF.2

/--
Adjoining an essentially bounded head to an essentially bounded derivative
jet produces an essentially bounded successor jet.
-/
theorem succ_isEssentiallyBounded
    (f : Lp (W^{(m + 1),2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (dF : SobolevTimeJet n m Omega t0 t1)
    (hderiv : PDE.Analysis.Evolution.HasGelfandWeakTimeDerivativeOn
      (PDE.Analysis.Evolution.GelfandTriple.identity (W^{m,2}(Omega))) (lowerOrderTimeLp f)
      (PDE.Analysis.Evolution.rieszToDualLp dF.head))
    (hf : MemLp (fun t ↦ f t) (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1)))
    (hdF : dF.IsEssentiallyBounded) :
    (SobolevTimeJet.succ f dF hderiv).IsEssentiallyBounded :=
  ⟨hf, hdF⟩

/-- The leading trajectory of an essentially bounded jet is in `L∞`. -/
theorem IsEssentiallyBounded.head {F : SobolevTimeJet n m Omega t0 t1}
    (hF : F.IsEssentiallyBounded) :
    MemLp (fun t ↦ F.head t) (⊤ : ℝ≥0∞) (volume.restrict (Set.Ioc t0 t1)) := by
  cases F with
  | mk head derivatives =>
      cases derivatives with
      | zero =>
          exact hF
      | succ =>
          exact hF.1

/--
Choose a real almost-everywhere bound for the leading trajectory of an
essentially bounded Sobolev time jet.

The predicate `IsEssentiallyBounded` stores the
representative-invariant `MemLp · ∞` statement.  The elliptic estimate,
however, is most useful with a concrete real bound.  Finiteness of the
essential supremum supplies such a constant without strengthening the
induction hypothesis.
-/
theorem IsEssentiallyBounded.exists_head_bound {F : SobolevTimeJet n m Omega t0 t1}
    (hF : F.IsEssentiallyBounded) :
    ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), ‖F.head t‖ ≤ C := by
  have htop := hF.head
  have hess :
      eLpNormEssSup (fun t ↦ F.head t) (volume.restrict (Set.Ioc t0 t1)) < ⊤ := by
    simpa only [eLpNorm_exponent_top htop.aestronglyMeasurable] using htop.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hess
  refine ⟨(C : ℝ), ?_⟩
  filter_upwards [hC] with t ht
  exact_mod_cast ht

end SobolevTimeJet

end Hyperbolic.HigherRegularity
