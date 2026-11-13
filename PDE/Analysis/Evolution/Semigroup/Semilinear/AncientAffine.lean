/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientWeighted
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Ancient evolution with linear, quadratic and external forcing

A coefficient path in weight `η` multiplies a solution path in weight `η` to
give forcing in weight `2η`, and a bounded bilinear nonlinearity applied to a
path of weight `η` gives forcing in weight `2η`. Together with an external
forcing path these are the three terms of a localized ancient mild equation.
The coefficient is either a bounded continuous path of operators or a uniformly
bounded family whose action is jointly continuous; the second form covers
coefficients built from dilations, which are only strongly continuous.

Any Green operator with an explicit norm bound turns explicit source and
coefficient budgets into a unique fixed point on a closed ball, and the budgets
close at sufficiently early terminal times.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set Filter
open scoped BoundedContinuousFunction Topology

namespace PDE.Analysis.Evolution

variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]

/-- Apply a bounded bilinear nonlinearity pointwise to a bounded continuous path.
When `u` represents a path of weight `η`, this represents its quadratic forcing
in weight `2η`. -/
def quadraticPath (B : E →L[ℝ] E →L[ℝ] F) (u : X →ᵇ E) : X →ᵇ F :=
  ofNormedAddCommGroup (fun t ↦ B (u t) (u t))
    ((B.continuous.comp u.continuous).clm_apply u.continuous)
    (‖B‖ * ‖u‖ ^ 2) fun t ↦ by
      calc
        ‖B (u t) (u t)‖ ≤ ‖B‖ * ‖u t‖ * ‖u t‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * ‖u‖ * ‖u‖ := by gcongr <;> exact u.norm_coe_le_norm t
        _ = ‖B‖ * ‖u‖ ^ 2 := by ring

/-- Evaluation of the represented quadratic forcing. -/
@[simp]
theorem quadraticPath_apply (B : E →L[ℝ] E →L[ℝ] F) (u : X →ᵇ E) (t : X) :
    quadraticPath B u t = B (u t) (u t) :=
  rfl

/-- The pointwise quadratic forcing obeys the bilinear norm bound in uniform norm. -/
theorem norm_quadraticPath_le (B : E →L[ℝ] E →L[ℝ] F) (u : X →ᵇ E) :
    ‖quadraticPath B u‖ ≤ ‖B‖ * ‖u‖ ^ 2 := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro t
  change ‖B (u t) (u t)‖ ≤ _
  calc
    _ ≤ ‖B‖ * ‖u t‖ * ‖u t‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * ‖u‖ * ‖u‖ := by gcongr <;> exact u.norm_coe_le_norm t
    _ = _ := by ring

/-- The quadratic forcing is Lipschitz on every norm ball, with the explicit
factor supplied by polarization of the two bilinear factors. -/
theorem norm_quadraticPath_sub_le (B : E →L[ℝ] E →L[ℝ] F) (u v : X →ᵇ E) :
    ‖quadraticPath B u - quadraticPath B v‖ ≤
      ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro t
  change ‖B (u t) (u t) - B (v t) (v t)‖ ≤ _
  have hsplit : B (u t) (u t) - B (v t) (v t) =
      B (u t) (u t - v t) + B (u t - v t) (v t) := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖B (u t) (u t - v t)‖ + ‖B (u t - v t) (v t)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u t‖ * ‖u t - v t‖ + ‖B‖ * ‖u t - v t‖ * ‖v t‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * ‖u‖ * ‖u - v‖ + ‖B‖ * ‖u - v‖ * ‖v‖ := by
      gcongr
      · exact u.norm_coe_le_norm t
      · exact (u - v).norm_coe_le_norm t
      · exact (u - v).norm_coe_le_norm t
      · exact v.norm_coe_le_norm t
    _ = _ := by ring

/-- Pointwise multiplication by a uniformly bounded coefficient family whose
action is jointly continuous. Continuity in operator norm is not required. -/
def linearPathOperatorOfJoint (L : X → E →L[ℝ] F)
    (hL : Continuous fun p : X × E ↦ L p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hLC : ∀ t, ‖L t‖ ≤ C) : (X →ᵇ E) →L[ℝ] (X →ᵇ F) := by
  have hcont (u : X →ᵇ E) : Continuous fun t ↦ L t (u t) :=
    hL.comp (continuous_id.prodMk u.continuous)
  have hbound (u : X →ᵇ E) (t : X) : ‖L t (u t)‖ ≤ C * ‖u‖ :=
    ((L t).le_opNorm _).trans
      (mul_le_mul (hLC t) (u.norm_coe_le_norm t) (norm_nonneg _) hC)
  let T : (X →ᵇ E) →ₗ[ℝ] (X →ᵇ F) :=
    { toFun u := ofNormedAddCommGroup (fun t ↦ L t (u t)) (hcont u) (C * ‖u‖) (hbound u)
      map_add' u v := by
        apply BoundedContinuousFunction.ext
        intro t
        exact map_add (L t) _ _
      map_smul' c u := by
        apply BoundedContinuousFunction.ext
        intro t
        change L t (c • u t) = c • L t (u t)
        exact map_smul (L t) c _ }
  exact T.mkContinuous C fun u ↦
    norm_ofNormedAddCommGroup_le (hcont u) (mul_nonneg hC (norm_nonneg u)) (hbound u)

/-- Evaluation is application of the coefficient at the same time. -/
@[simp]
theorem linearPathOperatorOfJoint_apply (L : X → E →L[ℝ] F)
    (hL : Continuous fun p : X × E ↦ L p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hLC : ∀ t, ‖L t‖ ≤ C) (u : X →ᵇ E) (t : X) :
    linearPathOperatorOfJoint L hL hC hLC u t = L t (u t) :=
  rfl

/-- The uniform coefficient bound bounds the multiplication operator. -/
theorem norm_linearPathOperatorOfJoint_le (L : X → E →L[ℝ] F)
    (hL : Continuous fun p : X × E ↦ L p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hLC : ∀ t, ‖L t‖ ≤ C) :
    ‖linearPathOperatorOfJoint L hL hC hLC‖ ≤ C := by
  unfold linearPathOperatorOfJoint
  exact LinearMap.mkContinuous_norm_le _ hC _

/-- Pointwise multiplication by a bounded continuous linear coefficient path. -/
def linearPathOperator (L : X →ᵇ (E →L[ℝ] F)) : (X →ᵇ E) →L[ℝ] (X →ᵇ F) :=
  linearPathOperatorOfJoint L ((L.continuous.comp continuous_fst).clm_apply continuous_snd)
    (norm_nonneg L) L.norm_coe_le_norm

/-- Evaluation is application of the coefficient at the same time. -/
@[simp]
theorem linearPathOperator_apply (L : X →ᵇ (E →L[ℝ] F)) (u : X →ᵇ E) (t : X) :
    linearPathOperator L u t = L t (u t) :=
  rfl

/-- The uniform coefficient norm bounds its multiplication operator. -/
theorem norm_linearPathOperator_le (L : X →ᵇ (E →L[ℝ] F)) :
    ‖linearPathOperator L‖ ≤ ‖L‖ :=
  norm_linearPathOperatorOfJoint_le _ _ _ _

/-- External forcing, a bounded linear path operator and a quadratic nonlinearity. -/
def affinePathForcing (T : (X →ᵇ E) →L[ℝ] (X →ᵇ F)) (B : E →L[ℝ] E →L[ℝ] F)
    (f : X →ᵇ F) (u : X →ᵇ E) : X →ᵇ F :=
  f + T u + quadraticPath B u

/-- The affine forcing obeys an explicit affine-quadratic norm bound. -/
theorem norm_affinePathForcing_le (T : (X →ᵇ E) →L[ℝ] (X →ᵇ F)) {ℓ : ℝ} (hT : ‖T‖ ≤ ℓ)
    (B : E →L[ℝ] E →L[ℝ] F) (f : X →ᵇ F) (u : X →ᵇ E) :
    ‖affinePathForcing T B f u‖ ≤ ‖f‖ + ℓ * ‖u‖ + ‖B‖ * ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖f + T u‖ + ‖quadraticPath B u‖ := norm_add_le _ _
    _ ≤ (‖f‖ + ‖T u‖) + ‖quadraticPath B u‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl (T.le_of_opNorm_le hT u))
      (norm_quadraticPath_le B u)

/-- Forcing differences have the operator's linear contribution plus the
polarized quadratic contribution. -/
theorem norm_affinePathForcing_sub_le (T : (X →ᵇ E) →L[ℝ] (X →ᵇ F)) {ℓ : ℝ}
    (hT : ‖T‖ ≤ ℓ) (B : E →L[ℝ] E →L[ℝ] F) (f : X →ᵇ F) (u v : X →ᵇ E) :
    ‖affinePathForcing T B f u - affinePathForcing T B f v‖ ≤
      (ℓ + ‖B‖ * (‖u‖ + ‖v‖)) * ‖u - v‖ := by
  have hsplit : affinePathForcing T B f u - affinePathForcing T B f v =
      T (u - v) + (quadraticPath B u - quadraticPath B v) := by
    simp only [affinePathForcing, map_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖T (u - v)‖ + ‖quadraticPath B u - quadraticPath B v‖ := norm_add_le _ _
    _ ≤ ℓ * ‖u - v‖ + ‖B‖ * (‖u‖ + ‖v‖) * ‖u - v‖ :=
      add_le_add (T.le_of_opNorm_le hT _) (norm_quadraticPath_sub_le B u v)
    _ = _ := by ring

/-- External, linear and quadratic forcing in bounded path representatives. -/
def fullPathForcing (L : X →ᵇ (E →L[ℝ] F)) (B : E →L[ℝ] E →L[ℝ] F)
    (f : X →ᵇ F) (u : X →ᵇ E) : X →ᵇ F :=
  f + linearPathOperator L u + quadraticPath B u

/-- The full forcing obeys an explicit affine-quadratic norm bound. -/
theorem norm_fullPathForcing_le (L : X →ᵇ (E →L[ℝ] F))
    (B : E →L[ℝ] E →L[ℝ] F) (f : X →ᵇ F) (u : X →ᵇ E) :
    ‖fullPathForcing L B f u‖ ≤ ‖f‖ + ‖L‖ * ‖u‖ + ‖B‖ * ‖u‖ ^ 2 :=
  norm_affinePathForcing_le _ (norm_linearPathOperator_le L) B f u

/-- Forcing differences have the coefficient's linear contribution plus the
polarized quadratic contribution. -/
theorem norm_fullPathForcing_sub_le (L : X →ᵇ (E →L[ℝ] F))
    (B : E →L[ℝ] E →L[ℝ] F) (f : X →ᵇ F) (u v : X →ᵇ E) :
    ‖fullPathForcing L B f u - fullPathForcing L B f v‖ ≤
      (‖L‖ + ‖B‖ * (‖u‖ + ‖v‖)) * ‖u - v‖ :=
  norm_affinePathForcing_sub_le _ (norm_linearPathOperator_le L) B f u v

/-- A coefficient family in weight `η` acting on a path in weight `η` gives
forcing in weight `2η`; the physical coefficient at time `t` is
`exp (η * t) • L t`. -/
theorem ancientLift_linearPathOperatorOfJoint {a : ℝ} (η : ℝ) (L : Iic a → E →L[ℝ] F)
    (hL : Continuous fun p : Iic a × E ↦ L p.1 p.2) {C : ℝ} (hC : 0 ≤ C)
    (hLC : ∀ t, ‖L t‖ ≤ C) (u : Iic a →ᵇ E) (t : ℝ) :
    ancientLift (2 * η) (linearPathOperatorOfJoint L hL hC hLC u) t =
      Real.exp (η * t) • L ⟨min t a, min_le_right t a⟩ (ancientLift η u t) := by
  simp only [ancientLift, ContinuousMap.coe_mk, linearPathOperatorOfJoint_apply, map_smul,
    smul_smul]
  rw [← Real.exp_add]
  congr 2
  ring

/-- Decoding keeps the external forcing, the decoded linear term and the
quadratic nonlinearity. -/
theorem ancientLift_affinePathForcing {a : ℝ} (η : ℝ)
    (T : (Iic a →ᵇ E) →L[ℝ] (Iic a →ᵇ F)) (B : E →L[ℝ] E →L[ℝ] F)
    (f : Iic a →ᵇ F) (u : Iic a →ᵇ E) (t : ℝ) :
    ancientLift (2 * η) (affinePathForcing T B f u) t =
      ancientLift (2 * η) f t + ancientLift (2 * η) (T u) t +
        B (ancientLift η u t) (ancientLift η u t) := by
  simp only [ancientLift, ContinuousMap.coe_mk, affinePathForcing,
    BoundedContinuousFunction.add_apply, quadraticPath_apply, smul_add, map_smul,
    _root_.smul_apply, smul_smul]
  have hexp : Real.exp ((2 * η) * t) = Real.exp (η * t) * Real.exp (η * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- Decoding retains the external forcing, the time-dependent linear
coefficient and the quadratic nonlinearity exactly. -/
theorem ancientLift_fullPathForcing {a : ℝ} (η : ℝ)
    (L : Iic a →ᵇ (E →L[ℝ] F)) (B : E →L[ℝ] E →L[ℝ] F)
    (f : Iic a →ᵇ F) (u : Iic a →ᵇ E) (t : ℝ) :
    ancientLift (2 * η) (fullPathForcing L B f u) t =
      ancientLift (2 * η) f t + ancientLift η L t (ancientLift η u t) +
        B (ancientLift η u t) (ancientLift η u t) := by
  rw [show fullPathForcing L B f u = affinePathForcing (linearPathOperator L) B f u from rfl,
    ancientLift_affinePathForcing, linearPathOperator, ancientLift_linearPathOperatorOfJoint]
  rfl

variable [CompleteSpace E]

/-- A Green operator with a proved bound and a linear path operator with a proved
bound construct the affine-quadratic fixed point from explicit budgets. -/
theorem existsUnique_affinePath_fixedPoint
    (A : (X →ᵇ F) →L[ℝ] (X →ᵇ E)) {C R ℓ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hA : ‖A‖ ≤ C)
    (T : (X →ᵇ E) →L[ℝ] (X →ᵇ F)) (hT : ‖T‖ ≤ ℓ) (B : E →L[ℝ] E →L[ℝ] F)
    (f : X →ᵇ F) (b : X →ᵇ E)
    (hsource : ‖b‖ + C * (‖f‖ + ℓ * R + ‖B‖ * R ^ 2) ≤ R)
    (hsmall : C * (ℓ + 2 * ‖B‖ * R) < 1) :
    ∃! u : X →ᵇ E, ‖u‖ ≤ R ∧ u = b + A (affinePathForcing T B f u) := by
  have hℓ : 0 ≤ ℓ := (norm_nonneg T).trans hT
  let Φ (u : X →ᵇ E) := b + A (affinePathForcing T B f u)
  have hmaps : MapsTo Φ (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro u hu
    have hunorm : ‖u‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    change dist (Φ u) 0 ≤ R
    rw [dist_zero_right]
    calc
      ‖Φ u‖ ≤ ‖b‖ + ‖A (affinePathForcing T B f u)‖ := norm_add_le _ _
      _ ≤ ‖b‖ + C * (‖f‖ + ℓ * ‖u‖ + ‖B‖ * ‖u‖ ^ 2) :=
        add_le_add le_rfl ((A.le_of_opNorm_le hA _).trans
          (mul_le_mul_of_nonneg_left (norm_affinePathForcing_le T hT B f u) hC))
      _ ≤ ‖b‖ + C * (‖f‖ + ℓ * R + ‖B‖ * R ^ 2) := by
        gcongr
      _ ≤ R := hsource
  let q : NNReal := ⟨C * (ℓ + 2 * ‖B‖ * R), by positivity⟩
  have hq : q < 1 := hsmall
  have hlip : LipschitzOnWith q Φ (Metric.closedBall 0 R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    have hunorm : ‖u‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    have hvnorm : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    change dist (b + A (affinePathForcing T B f u)) (b + A (affinePathForcing T B f v)) ≤ _
    rw [dist_add_left, dist_eq_norm, ← A.map_sub, dist_eq_norm]
    calc
      _ ≤ C * ‖affinePathForcing T B f u - affinePathForcing T B f v‖ :=
        A.le_of_opNorm_le hA _
      _ ≤ C * ((ℓ + ‖B‖ * (‖u‖ + ‖v‖)) * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (norm_affinePathForcing_sub_le T hT B f u v) hC
      _ ≤ C * ((ℓ + ‖B‖ * (R + R)) * ‖u - v‖) := by gcongr
      _ = (q : ℝ) * ‖u - v‖ := by
        change C * ((ℓ + ‖B‖ * (R + R)) * ‖u - v‖) = (C * (ℓ + 2 * ‖B‖ * R)) * ‖u - v‖
        ring
  have hc : ContractingWith q (hmaps.restrict Φ _ _) := ⟨hq, hlip.mapsToRestrict hmaps⟩
  obtain ⟨u, hu, hfix, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hc
    (Metric.mem_closedBall_self hR) (edist_ne_top _ _)
  refine ⟨u, ⟨?_, hfix.eq.symm⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  · intro v hv
    have hvmem : v ∈ Metric.closedBall 0 R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv.1
    have hvfix : Φ v = v := hv.2.symm
    have hdist := hlip.dist_le_mul v hvmem u hu
    rw [hvfix, hfix.eq] at hdist
    apply dist_eq_zero.mp
    have hqreal : (q : ℝ) < 1 := hq
    nlinarith [dist_nonneg (x := v) (y := u)]

/-- A Green operator with a proved bound constructs the full affine-quadratic
fixed point from explicit source and coefficient budgets. -/
theorem existsUnique_fullPath_fixedPoint
    (A : (X →ᵇ F) →L[ℝ] (X →ᵇ E)) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hA : ‖A‖ ≤ C)
    (L : X →ᵇ (E →L[ℝ] F)) (B : E →L[ℝ] E →L[ℝ] F)
    (f : X →ᵇ F) (b : X →ᵇ E)
    (hsource : ‖b‖ + C * (‖f‖ + ‖L‖ * R + ‖B‖ * R ^ 2) ≤ R)
    (hsmall : C * (‖L‖ + 2 * ‖B‖ * R) < 1) :
    ∃! u : X →ᵇ E, ‖u‖ ≤ R ∧ u = b + A (fullPathForcing L B f u) :=
  existsUnique_affinePath_fixedPoint A hC hR hA _ (norm_linearPathOperator_le L) B f b
    hsource hsmall

omit [CompleteSpace E] in
/-- Both full-source budgets close at sufficiently early times whenever the
fixed homogeneous-source budget lies strictly below the solution radius. -/
theorem exists_early_fullPath_budgets {η C P Q R S : ℝ}
    (hη : 0 < η) (hmargin : S < R) :
    ∃ a₀ : ℝ, ∀ a ≤ a₀,
      S + (C * Real.exp (η * a)) * P ≤ R ∧ (C * Real.exp (η * a)) * Q < 1 := by
  have he : Tendsto (fun a : ℝ ↦ Real.exp (η * a)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos hη).mpr tendsto_id)
  have hs : Tendsto (fun a : ℝ ↦ (C * Real.exp (η * a)) * P) atBot (𝓝 0) := by
    simpa using (he.const_mul C).mul_const P
  have hq : Tendsto (fun a : ℝ ↦ (C * Real.exp (η * a)) * Q) atBot (𝓝 0) := by
    simpa using (he.const_mul C).mul_const Q
  obtain ⟨a₀, ha₀⟩ := eventually_atBot.mp
    ((hs.eventually_lt_const (sub_pos.mpr hmargin)).and
      (hq.eventually_lt_const (zero_lt_one : (0 : ℝ) < 1)))
  refine ⟨a₀, fun a ha ↦ ?_⟩
  obtain ⟨hs', hq'⟩ := ha₀ a ha
  exact ⟨by linarith, hq'⟩

end PDE.Analysis.Evolution
