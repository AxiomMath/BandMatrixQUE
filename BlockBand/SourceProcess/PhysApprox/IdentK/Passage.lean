module

public import BlockBand.SourceProcess.PhysApprox.IdentK.Statements
public import BlockBand.SourceProcess.PhysApprox.IdentK.PassageCore
public import BlockBand.SourceProcess.PhysApprox.B3FddCoord
public import BlockBand.SourceProcess.PhysApprox.B3Ident2Closed
public import BlockBand.SourceProcess.PhysApprox.B3FeasBridge
public import BlockBand.SourceProcess.PhysApprox.B3FddMain

/-!
# The `𝒦` fdd passage `KFddPassage`

* `cK`, `gOf`, `kOf`, `stOf`: the drift-free state `stZKObs` as a continuous function of the
  jumps `jt t = (J_t, J^𝒦_t)` and of the coordinate vectors at `t` and `0` (`stZKObs_eq`, `rfl`);
  `genObs = mgen cK (fF F) (gL Λ)` (`genObs_eq_mgen`, `rfl`).
* Clipping: `fC`, `gC` (`F`, `Λ` times a continuous cutoff of the coordinate norms) are
  continuous, uniformly bounded (`exists_bound_fC`, `exists_bound_gC`: the jumps take finitely
  many values), `gC` is jointly measurable; on paths with feasible Gram states the clipped process
  is `genObs` (`mgen_clip_eq`).
* `measurable_uncurry_b3ObsAll` (step processes in time), `measurable_uncurry_complexObs`
  (continuity of `G − J`, `𝒦 − J_𝒦`).
* **`kFddPassage`**: the tested increments of the clipped process converge
  (`Core.IsFddOff.tendsto_test_mgen`, after shifting past the frame index); the cap mass tends to
  the positive entrance mass (`CapCond.tendsto_capProb`); so the limit tested increment is `0`,
  and it equals that of `genObs (complexObs …)` by a.s. feasibility (`ae_feasible_all`).
  Integrability at every time: the clipped process is bounded and measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.Core
open scoped NNReal ENNReal ComplexConjugate

variable {K np : ℕ}

/-- The coordinates read by the drift-free state: Gram entries and `𝒦` entries. -/
abbrev KCo (K np : ℕ) := GIdx K np ⊕ KIdx np

/-- Their observable indices. -/
def cK : KCo K np → B3.LIdx K np := Sum.elim Sum.inl fun ij => Sum.inr (Sum.inr ij)

/-- The Gram state of a coordinate vector. -/
def gOf (x : KCo K np → ℂ) : GSt K np := gramOfEntries fun e => x (Sum.inl e)

/-- The `𝒦` matrix of a coordinate vector. -/
def kOf (x : KCo K np → ℂ) : KSt np := Matrix.of fun i j => x (Sum.inr (i, j))

/-- The jumps at time `t`. -/
def jt (b E s : ℝ) (τ m : Fin np → ℝ) (t : ℝ≥0) : GSt K np × KSt np :=
  (gramJ b s τ m t, kJ E s τ m t)

/-- The drift-free state from the jumps `J` and the coordinates at `t` and `0`. -/
def stOf (b E s : ℝ) (τ m : Fin np → ℝ) (J : GSt K np × KSt np) (x x0 : KCo K np → ℂ) :
    ZK K np :=
  ((gOf x - J.1, 0, gOf x0 - gramJ b s τ m 0), kOf x - J.2,
    fun a => (kOf x - J.2) a.1 a.2 - (kOf x0 - kJ E s τ m 0) a.1 a.2, kOf x0 - kJ E s τ m 0)

variable {Ω : Type*}

theorem stZKObs_eq (b E s : ℝ) (τ m : Fin np → ℝ) (obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ)
    (u : ℝ≥0) (ω : Ω) :
    stZKObs b E s τ m obs u ω =
      stOf b E s τ m (jt b E s τ m u) (xv cK obs u ω) (xv cK obs 0 ω) := rfl

/-- `F` along the state. -/
def fF (b E s : ℝ) (τ m : Fin np → ℝ) (F : ZK K np → ℂ) (t : ℝ≥0) (x x0 : KCo K np → ℂ) : ℂ :=
  F (stOf b E s τ m (jt b E s τ m t) x x0)

/-- `Λ` along the state. -/
def gL (b E s : ℝ) (τ m : Fin np → ℝ) (Λ : GSt K np × ZK K np → ℂ) (t : ℝ≥0)
    (x x0 : KCo K np → ℂ) : ℂ :=
  Λ (gramJ b s τ m t, stOf b E s τ m (jt b E s τ m t) x x0)

theorem genObs_eq_mgen (b E s : ℝ) (τ m : Fin np → ℝ) (obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ)
    (F : ZK K np → ℂ) (Λ : GSt K np × ZK K np → ℂ) :
    genObs b E s τ m obs F Λ = mgen cK (fF b E s τ m F) (gL b E s τ m Λ) obs := rfl

/-!
## Clipping
-/

/-- `1` on `‖x‖ ≤ R`, `0` on `‖x‖ ≥ R + 1`. -/
def clip (R : ℝ) (x : KCo K np → ℂ) : ℝ := max 0 (min 1 (R + 1 - ‖x‖))

theorem continuous_clip (R : ℝ) : Continuous (clip (K := K) (np := np) R) := by
  unfold clip; fun_prop

theorem clip_nonneg (R : ℝ) (x : KCo K np → ℂ) : 0 ≤ clip R x := le_max_left _ _

theorem clip_le_one (R : ℝ) (x : KCo K np → ℂ) : clip R x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem clip_eq_one {R : ℝ} {x : KCo K np → ℂ} (h : ‖x‖ ≤ R) : clip R x = 1 := by
  unfold clip
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem norm_lt_of_clip_ne_zero {R : ℝ} {x : KCo K np → ℂ} (h : clip R x ≠ 0) :
    ‖x‖ < R + 1 := by
  by_contra h'
  push Not at h'
  apply h
  unfold clip
  exact max_eq_left (min_le_of_right_le (by linarith))

/-!
## The jumps
-/

theorem exists_norm_kJ_le (E s : ℝ) (τ m : Fin np → ℝ) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ t (a : KIdx np), ‖kJ E s τ m t a.1 a.2‖ ≤ CK := by
  refine ⟨∑ j, ‖matchedA E * (m j : ℂ)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
    fun t a => ?_⟩
  unfold kJ kBirthJump
  rw [Matrix.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  split_ifs
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Matrix.single_apply]
    split_ifs <;> simp
  · simp only [Matrix.zero_apply, norm_zero]
    exact norm_nonneg _

theorem finite_range_kJ (E s : ℝ) (τ m : Fin np → ℝ) :
    (Set.range fun t : ℝ≥0 => kJ E s τ m t).Finite := by
  refine (Set.finite_range fun x : Fin np → Bool => (∑ j, if x j then
      (matchedA E * (m j : ℂ)) • Matrix.single j j (1 : ℂ) else 0 : KSt np)).subset ?_
  rintro _ ⟨t, rfl⟩
  refine ⟨fun j => decide (τ j - s ≤ (t : ℝ)), ?_⟩
  simp only [kJ, kBirthJump, decide_eq_true_eq]

theorem finite_range_jt (b E s : ℝ) (τ m : Fin np → ℝ) :
    (Set.range fun t : ℝ≥0 => jt (K := K) b E s τ m t).Finite :=
  ((finite_range_gramJ (K := K) b s τ m).prod (finite_range_kJ E s τ m)).subset
    (by rintro _ ⟨t, rfl⟩; exact ⟨⟨t, rfl⟩, ⟨t, rfl⟩⟩)

theorem stronglyMeasurable_kJ (E s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun t : ℝ≥0 => kJ E s τ m t := by
  unfold kJ kBirthJump
  exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    StronglyMeasurable.ite (measurableSet_le measurable_const measurable_coe_nnreal_real)
      stronglyMeasurable_const stronglyMeasurable_const

theorem stronglyMeasurable_gramJ (b s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun t : ℝ≥0 => gramJ (K := K) b s τ m t := by
  unfold gramJ birthJump
  exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
    StronglyMeasurable.ite (measurableSet_le measurable_const measurable_coe_nnreal_real)
      stronglyMeasurable_const stronglyMeasurable_const

theorem stronglyMeasurable_jt (b E s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun t : ℝ≥0 => jt (K := K) b E s τ m t :=
  (stronglyMeasurable_gramJ b s τ m).prodMk (stronglyMeasurable_kJ E s τ m)

theorem continuous_gOf : Continuous (gOf (K := K) (np := np)) :=
  continuous_gramOfEntries.comp (continuous_pi fun _ => continuous_apply _)

theorem continuous_kOf : Continuous (kOf (K := K) (np := np)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _

theorem continuous_stOf (b E s : ℝ) (τ m : Fin np → ℝ) :
    Continuous fun q : (GSt K np × KSt np) × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      stOf b E s τ m q.1 q.2.1 q.2.2 := by
  have hg := continuous_gOf (K := K) (np := np)
  have hk := continuous_kOf (K := K) (np := np)
  unfold stOf
  refine Continuous.prodMk (Continuous.prodMk ((hg.comp (continuous_fst.comp continuous_snd)).sub
    (continuous_fst.comp continuous_fst)) (continuous_const.prodMk
    ((hg.comp (continuous_snd.comp continuous_snd)).sub continuous_const)))
    (Continuous.prodMk ((hk.comp (continuous_fst.comp continuous_snd)).sub
      (continuous_snd.comp continuous_fst)) (Continuous.prodMk (continuous_pi fun a => ?_)
      ((hk.comp (continuous_snd.comp continuous_snd)).sub continuous_const)))
  exact (((hk.comp (continuous_fst.comp continuous_snd)).sub
      (continuous_snd.comp continuous_fst)).matrix_elem a.1 a.2).sub
    (((hk.comp (continuous_snd.comp continuous_snd)).sub continuous_const).matrix_elem a.1 a.2)

/-!
## Feasible states in the cut region are bounded
-/

theorem norm_entry_le_of_qK {Rξ : ℝ} {y : KSt np} (hy : |qK y| ≤ Rξ) (a : KIdx np) :
    ‖y a.1 a.2‖ ≤ Rξ + 1 := by
  have h1 : ‖y a.1 a.2‖ ^ 2 ≤ qK y :=
    Finset.single_le_sum (f := fun a : KIdx np => ‖y a.1 a.2‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a)
  have h2 := norm_le_sq_add_one (y a.1 a.2)
  linarith [le_abs_self (qK y)]

theorem exists_norm_le_of_cutReg (b E s : ℝ) (τ m : Fin np → ℝ) (Rχ Rξ : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (J : GSt K np) (t : ℝ≥0) (x x0 : KCo K np → ℂ),
      GramFeasible (srcSignature K (Fin np)) (gOf x) →
      GramFeasible (srcSignature K (Fin np)) (gOf x0) →
      CutReg Rχ Rξ (J, stOf b E s τ m (jt b E s τ m t) x x0) → ‖x‖ ≤ R ∧ ‖x0‖ ≤ R := by
  obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
  obtain ⟨CK, -, hCK⟩ := exists_norm_kJ_le E s τ m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  set R := max (max (BY + CJ) (Rξ + 1 + CK)) 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRG : BY + CJ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRK : Rξ + 1 + CK ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hG : ∀ (x : KCo K np → ℂ) (v : ℝ≥0), GramFeasible (srcSignature K (Fin np)) (gOf x) →
      |trRe (gOf x - gramJ b s τ m v)| ≤ Rχ → ∀ e, ‖x (Sum.inl e)‖ ≤ R := fun x v hx hr e => by
    have h1 := entry_sub_le_of_feasible hx (hCJ v) (abs_trRe_gramJ_le hCJ v) hr e
    have h2 : x (Sum.inl e) = gramEntry e (gOf x - gramJ b s τ m v) +
        gramEntry e (gramJ (K := K) b s τ m v) := by
      rw [gramEntry_sub', sub_add_cancel, gOf, Fdd.gramEntry_gramOfEntries]
    rw [h2]
    exact (norm_add_le _ _).trans ((add_le_add h1 (hCJ v e)).trans hRG)
  have hK : ∀ (x : KCo K np → ℂ) (v : ℝ≥0), |qK (kOf x - kJ E s τ m v)| ≤ Rξ →
      ∀ a : KIdx np, ‖x (Sum.inr a)‖ ≤ R := fun x v hr a => by
    have h1 := norm_entry_le_of_qK hr a
    have h2 : x (Sum.inr a) = (kOf x - kJ E s τ m v) a.1 a.2 + kJ E s τ m v a.1 a.2 := by
      rw [Matrix.sub_apply, sub_add_cancel]; rfl
    rw [h2]
    exact (norm_add_le _ _).trans ((add_le_add h1 (hCK v a)).trans hRK)
  refine ⟨R, hR0, fun J t x x0 hx hx0 ⟨h1, h2, h3, h4⟩ => ⟨?_, ?_⟩⟩
  · refine (pi_norm_le_iff_of_nonneg hR0).2 fun k => ?_
    rcases k with e | a
    · exact hG x t hx h1 e
    · exact hK x t h3 a
  · refine (pi_norm_le_iff_of_nonneg hR0).2 fun k => ?_
    rcases k with e | a
    · exact hG x0 0 hx0 h2 e
    · exact hK x0 0 h4 a

/-!
## The clipped coefficients
-/

/-- The clipped `F` coefficient. -/
def fC (b E s : ℝ) (τ m : Fin np → ℝ) (F : ZK K np → ℂ) (R : ℝ) (t : ℝ≥0)
    (x x0 : KCo K np → ℂ) : ℂ :=
  ((clip R x * clip R x0 : ℝ) : ℂ) * fF b E s τ m F t x x0

/-- The clipped `Λ` coefficient. -/
def gC (b E s : ℝ) (τ m : Fin np → ℝ) (Λ : GSt K np × ZK K np → ℂ) (R : ℝ) (t : ℝ≥0)
    (x x0 : KCo K np → ℂ) : ℂ :=
  ((clip R x * clip R x0 : ℝ) : ℂ) * gL b E s τ m Λ t x x0

section Clipped

variable {b E s : ℝ} {τ m : Fin np → ℝ} {F : ZK K np → ℂ} {Λ : GSt K np × ZK K np → ℂ}
  {Rχ Rξ R : ℝ}

theorem continuous_fC (hF : Continuous F) (R : ℝ) (t : ℝ≥0) :
    Continuous fun p : (KCo K np → ℂ) × (KCo K np → ℂ) => fC b E s τ m F R t p.1 p.2 := by
  have h : Continuous fun p : (KCo K np → ℂ) × (KCo K np → ℂ) =>
      F (stOf b E s τ m (jt b E s τ m t) p.1 p.2) :=
    hF.comp ((continuous_stOf b E s τ m).comp (continuous_const.prodMk continuous_id))
  exact (Complex.continuous_ofReal.comp (((continuous_clip R).comp continuous_fst).mul
    ((continuous_clip R).comp continuous_snd))).mul h

theorem continuous_gC (hΛ : Continuous Λ) (R : ℝ) (t : ℝ≥0) :
    Continuous fun p : (KCo K np → ℂ) × (KCo K np → ℂ) => gC b E s τ m Λ R t p.1 p.2 := by
  have h : Continuous fun p : (KCo K np → ℂ) × (KCo K np → ℂ) =>
      Λ (gramJ b s τ m t, stOf b E s τ m (jt b E s τ m t) p.1 p.2) :=
    hΛ.comp (continuous_const.prodMk ((continuous_stOf b E s τ m).comp
      (continuous_const.prodMk continuous_id)))
  exact (Complex.continuous_ofReal.comp (((continuous_clip R).comp continuous_fst).mul
    ((continuous_clip R).comp continuous_snd))).mul h

theorem measurable_gC (hΛ : Continuous Λ) (R : ℝ) :
    Measurable fun q : ℝ≥0 × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      gC b E s τ m Λ R q.1 q.2.1 q.2.2 := by
  have hc : Continuous fun q : (GSt K np × KSt np) × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      ((clip R q.2.1 * clip R q.2.2 : ℝ) : ℂ) * Λ (q.1.1, stOf b E s τ m q.1 q.2.1 q.2.2) :=
    (Complex.continuous_ofReal.comp (((continuous_clip R).comp (continuous_fst.comp
      continuous_snd)).mul ((continuous_clip R).comp (continuous_snd.comp continuous_snd)))).mul
      (hΛ.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_stOf b E s τ m)))
  exact (hc.comp_stronglyMeasurable (((stronglyMeasurable_jt (K := K) b E s τ m).comp_measurable
    measurable_fst).prodMk measurable_snd.stronglyMeasurable)).measurable

theorem exists_bound_fC (hF : Continuous F) (R : ℝ) :
    ∃ C : ℝ, ∀ t x x0, ‖fC b E s τ m F R t x x0‖ ≤ C := by
  have hc : Continuous fun q : (GSt K np × KSt np) × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      F (stOf b E s τ m q.1 q.2.1 q.2.2) := hF.comp (continuous_stOf b E s τ m)
  obtain ⟨C, hC⟩ := IdentGram.exists_bound_finite_compact hc (finite_range_jt (K := K) b E s τ m)
    ((isCompact_closedBall (0 : KCo K np → ℂ) (R + 1)).prod (isCompact_closedBall 0 (R + 1)))
  refine ⟨max C 0, fun t x x0 => ?_⟩
  by_cases h0 : clip R x * clip R x0 = 0
  · simp [fC, h0]
  · have hx : clip R x ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hx0 : clip R x0 ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    have hb := hC _ ⟨t, rfl⟩ (x, x0) ⟨by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (norm_lt_of_clip_ne_zero hx).le, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (norm_lt_of_clip_ne_zero hx0).le⟩
    rw [fC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (clip_nonneg R x) (clip_nonneg R x0))]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb.trans (le_max_left _ _))
    exact (mul_le_of_le_one_left (clip_nonneg R x0) (clip_le_one R x)).trans (clip_le_one R x0)

theorem exists_bound_gC (hΛ : Continuous Λ) (R : ℝ) :
    ∃ C : ℝ, ∀ t x x0, ‖gC b E s τ m Λ R t x x0‖ ≤ C := by
  have hc : Continuous fun q : (GSt K np × KSt np) × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      Λ (q.1.1, stOf b E s τ m q.1 q.2.1 q.2.2) :=
    hΛ.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_stOf b E s τ m))
  obtain ⟨C, hC⟩ := IdentGram.exists_bound_finite_compact hc (finite_range_jt (K := K) b E s τ m)
    ((isCompact_closedBall (0 : KCo K np → ℂ) (R + 1)).prod (isCompact_closedBall 0 (R + 1)))
  refine ⟨max C 0, fun t x x0 => ?_⟩
  by_cases h0 : clip R x * clip R x0 = 0
  · simp [gC, h0]
  · have hx : clip R x ≠ 0 := fun h => h0 (by rw [h, zero_mul])
    have hx0 : clip R x0 ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    have hb := hC _ ⟨t, rfl⟩ (x, x0) ⟨by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (norm_lt_of_clip_ne_zero hx).le, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (norm_lt_of_clip_ne_zero hx0).le⟩
    rw [gC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (clip_nonneg R x) (clip_nonneg R x0))]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb.trans (le_max_left _ _))
    exact (mul_le_of_le_one_left (clip_nonneg R x0) (clip_le_one R x)).trans (clip_le_one R x0)

variable (hR : ∀ (J : GSt K np) (t : ℝ≥0) (x x0 : KCo K np → ℂ),
    GramFeasible (srcSignature K (Fin np)) (gOf x) →
    GramFeasible (srcSignature K (Fin np)) (gOf x0) →
    CutReg Rχ Rξ (J, stOf b E s τ m (jt b E s τ m t) x x0) → ‖x‖ ≤ R ∧ ‖x0‖ ≤ R)
include hR

theorem fC_eq (hFv : ∀ z, F z ≠ 0 → CutReg Rχ Rξ ((0 : GSt K np), z)) {t : ℝ≥0}
    {x x0 : KCo K np → ℂ} (hx : GramFeasible (srcSignature K (Fin np)) (gOf x))
    (hx0 : GramFeasible (srcSignature K (Fin np)) (gOf x0)) :
    fC b E s τ m F R t x x0 = fF b E s τ m F t x x0 := by
  by_cases h0 : fF b E s τ m F t x x0 = 0
  · rw [fC, h0, mul_zero]
  · obtain ⟨h1, h2⟩ := hR 0 t x x0 hx hx0 (hFv _ h0)
    rw [fC, clip_eq_one h1, clip_eq_one h2, mul_one, Complex.ofReal_one, one_mul]

theorem gC_eq (hΛv : ∀ p, Λ p ≠ 0 → CutReg Rχ Rξ p) {t : ℝ≥0}
    {x x0 : KCo K np → ℂ} (hx : GramFeasible (srcSignature K (Fin np)) (gOf x))
    (hx0 : GramFeasible (srcSignature K (Fin np)) (gOf x0)) :
    gC b E s τ m Λ R t x x0 = gL b E s τ m Λ t x x0 := by
  by_cases h0 : gL b E s τ m Λ t x x0 = 0
  · rw [gC, h0, mul_zero]
  · obtain ⟨h1, h2⟩ := hR _ t x x0 hx hx0 (hΛv _ h0)
    rw [gC, clip_eq_one h1, clip_eq_one h2, mul_one, Complex.ofReal_one, one_mul]

/-- **On paths with feasible Gram states, the clipped generator process is `genObs`.** -/
theorem mgen_clip_eq (hFv : ∀ z, F z ≠ 0 → CutReg Rχ Rξ ((0 : GSt K np), z))
    (hΛv : ∀ p, Λ p ≠ 0 → CutReg Rχ Rξ p) {obs : B3.LIdx K np → ℝ≥0 → Ω → ℂ} {ω : Ω}
    (hfe : ∀ u, GramFeasible (srcSignature K (Fin np)) (gOf (xv cK obs u ω))) (t : ℝ≥0) :
    mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R) obs t ω = genObs b E s τ m obs F Λ t ω := by
  rw [genObs_eq_mgen, mgen, mgen, fC_eq hR hFv (hfe t) (hfe 0)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  exact gC_eq hR hΛv (hfe _) (hfe 0)

end Clipped

/-!
## Joint measurability of the observables
-/

theorem measurable_uncurry_of_factor {α : Type*} [MeasurableSpace α] {L : ℝ≥0 → ℕ}
    (hL : Measurable L) {f : ℝ≥0 → α → ℂ} (hf : ∀ u, Measurable (f u))
    (hfac : ∀ u v, L u = L v → f u = f v) : Measurable (Function.uncurry f) := by
  classical
  let pick : ℕ → ℝ≥0 := fun j => if h : ∃ u, L u = j then h.choose else 0
  have hpick : ∀ u, L (pick (L u)) = L u := fun u => by
    have h : ∃ v, L v = L u := ⟨u, rfl⟩
    simp only [pick, h, ↓reduceDIte]
    exact h.choose_spec
  have hΦ : Measurable fun q : α × ℕ => f (pick q.2) q.1 :=
    measurable_from_prod_countable_left fun j => hf (pick j)
  have e : Function.uncurry f = fun q : ℝ≥0 × α => f (pick (L q.1)) q.2 := by
    funext q
    rw [hfac _ _ (hpick q.1)]
    rfl
  rw [e]
  exact hΦ.comp (measurable_snd.prodMk (hL.comp measurable_fst))

/-- **The finite-`W` observables are jointly measurable** (step processes in time). -/
theorem measurable_uncurry_b3ObsAll {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (i : B3.LIdx K np) :
    Measurable (Function.uncurry (b3ObsAll b E s h τ m W Vs i)) := by
  refine measurable_uncurry_of_factor (L := limLenAll s W)
    (Nat.measurable_floor.comp (measurable_const.mul
      (measurable_const.add measurable_coe_nnreal_real))) (fun u => ?_) (fun u v huv => ?_)
  · have e : b3ObsAll b E s h τ m W Vs i u =
        fun y => Fdd.fddCoord b E s h τ m W Vs i u y + Fdd.jumpAll b E s τ m W i u := by
      funext y
      rw [Fdd.fddCoord_eq, sub_add_cancel]
    rw [e]
    exact (Fdd.measurable_fddCoord hV i u.2).add measurable_const
  · rcases i with e | k | ij <;> funext y <;> simp only [b3ObsAll, huv]

/-- **The candidate's observables are jointly measurable** (continuity of `G − J`, `𝒦 − J_𝒦`). -/
theorem measurable_uncurry_complexObs [MeasurableSpace Ω] {b E s : ℝ} {τ m : Fin np → ℝ}
    {tseq : Ω → ℕ → ℝ} {G : ℝ≥0 → Ω → GSt K np} {Kc : ℝ≥0 → Ω → KSt np}
    (htm : Measurable tseq) (hG : ∀ u, StronglyMeasurable (G u))
    (hK : ∀ u, StronglyMeasurable (Kc u)) (hGc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hKc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u) (i : B3.LIdx K np) :
    Measurable (Function.uncurry (complexObs tseq G Kc i)) := by
  rcases i with e | k | ij
  · have h1 : Measurable (Function.uncurry fun u ω => gramEntry e (G u ω - gramJ b s τ m u)) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (ClosedLimit.continuous_gramEntry e).comp (hGc ω))
        (fun u => ((ClosedLimit.continuous_gramEntry e).comp_stronglyMeasurable
          ((hG u).sub stronglyMeasurable_const)).measurable)
    have h2 : Measurable fun q : ℝ≥0 × Ω => gramEntry e (gramJ (K := K) b s τ m q.1) :=
      (((ClosedLimit.continuous_gramEntry e).comp_stronglyMeasurable
        (stronglyMeasurable_gramJ b s τ m)).measurable).comp measurable_fst
    have e' : Function.uncurry (complexObs tseq G Kc (Sum.inl e)) =
        (Function.uncurry fun u ω => gramEntry e (G u ω - gramJ b s τ m u)) +
          fun q : ℝ≥0 × Ω => gramEntry e (gramJ (K := K) b s τ m q.1) := by
      funext q
      simp only [Function.uncurry, Pi.add_apply, complexObs, gramEntry_sub', sub_add_cancel]
    rw [e']
    exact h1.add h2
  · exact Complex.measurable_ofReal.comp ((measurable_pi_iff.1 htm k).comp measurable_snd)
  · have h1 : Measurable (Function.uncurry fun u ω => (Kc u ω - kJ E s τ m u) ij.1 ij.2) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (hKc ω).matrix_elem ij.1 ij.2)
        (fun u => ((continuous_id.matrix_elem ij.1 ij.2).comp_stronglyMeasurable
          ((hK u).sub stronglyMeasurable_const)).measurable)
    have h2 : Measurable fun q : ℝ≥0 × Ω => kJ E s τ m q.1 ij.1 ij.2 :=
      (((continuous_id.matrix_elem ij.1 ij.2).comp_stronglyMeasurable
        (stronglyMeasurable_kJ E s τ m)).measurable).comp measurable_fst
    have e' : Function.uncurry (complexObs tseq G Kc (Sum.inr (Sum.inr ij))) =
        (Function.uncurry fun u ω => (Kc u ω - kJ E s τ m u) ij.1 ij.2) +
          fun q : ℝ≥0 × Ω => kJ E s τ m q.1 ij.1 ij.2 := by
      funext q
      simp only [Function.uncurry, Pi.add_apply, complexObs, Matrix.sub_apply, sub_add_cancel]
    rw [e']
    exact h1.add h2

/-!
## Feasibility and the cap-restricted increment
-/

theorem gOf_b3ObsAll (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (u : ℝ≥0)
    (y : ProbedPath W np × ℝ) :
    gOf (xv cK (b3ObsAll b E s h τ m W Vs) u y) =
      b3ClosedGramAt b E s h τ m W (limLenAll s W u) Vs y :=
  gramOfEntries_gramEntry _

theorem gOf_complexObs (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GSt K np) (Kc : ℝ≥0 → Ω → KSt np)
    (u : ℝ≥0) (ω : Ω) : gOf (xv cK (complexObs tseq G Kc) u ω) = G u ω :=
  gramOfEntries_gramEntry _

/-- **Finite-`W` feasibility on the Borel cap event, at every time**, eventually along `φ`. -/
theorem eventually_ae_feasible_capM {b E : ℝ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ∀ᶠ n in atTop, ∀ᵐ y ∂closedLaw b (φ n) np, y ∈ Fdd.capM b E s h K (φ n) np →
      ∀ u, GramFeasible (srcSignature K (Fin np))
        (gOf (xv cK (b3ObsAll b E s h τ m (φ n) (Vs (φ n))) u y)) := by
  obtain ⟨⟨-, hb, hE1, hE2, -⟩, -⟩ := id hD
  have hb1 : b < 1 := by linarith
  filter_upwards [hφ.eventually (complexClosedFeasible_holds b E np τ m T s h K Vs hD)] with n hn
  filter_upwards [hn, Fdd.capC_ae_eq (W := φ n) (np := np) (K := K) hb1 hE1 hE2 s h]
    with y hy heq hyM u
  rw [gOf_b3ObsAll]
  exact hy (heq.mpr hyM) _ (Nat.floor_le_floor (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right u.2) (Nat.cast_nonneg _)))

section CapInc

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {F : ZK K np → ℂ} {Λ : GSt K np × ZK K np → ℂ}
  {Rχ Rξ R : ℝ}

/-- **The cap-restricted increment is the cap mass times the conditioned increment of the
clipped process** (an identity of Bochner integrals; no integrability is used). -/
theorem capIncW_eq (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hR : ∀ (J : GSt K np) (t : ℝ≥0) (x x0 : KCo K np → ℂ),
      GramFeasible (srcSignature K (Fin np)) (gOf x) →
      GramFeasible (srcSignature K (Fin np)) (gOf x0) →
      CutReg Rχ Rξ (J, stOf b E s τ m (jt b E s τ m t) x x0) → ‖x‖ ≤ R ∧ ‖x0‖ ≤ R)
    (hFv : ∀ z, F z ≠ 0 → CutReg Rχ Rξ ((0 : GSt K np), z))
    (hΛv : ∀ p, Λ p ≠ 0 → CutReg Rχ Rξ p)
    (hfe : ∀ᵐ y ∂closedLaw b W np, y ∈ Fdd.capM b E s h K W np →
      ∀ u, GramFeasible (srcSignature K (Fin np)) (gOf (xv cK (b3ObsAll b E s h τ m W Vs) u y)))
    (hm : growthPathLaw W b (physCapEventC b E s h K W) ≠ 0) {r : ℕ}
    (i : Fin r → B3.LIdx K np) (u : Fin r → ℝ≥0) (ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ)
    (t t' : ℝ≥0) :
    capIncW b E s h τ m W Vs F Λ i u ψ t t' =
      (growthPathLaw W b (physCapEventC b E s h K W)).toReal •
        ∫ y, ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) •
          (mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R) (b3ObsAll b E s h τ m W Vs) t' y -
            mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R) (b3ObsAll b E s h τ m W Vs) t y)
          ∂Fdd.condL b E s h K W np := by
  set f : ProbedPath W np × ℝ → ℂ := fun y => ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) •
    (mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R) (b3ObsAll b E s h τ m W Vs) t' y -
      mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R) (b3ObsAll b E s h τ m W Vs) t y) with hf
  have e1 : capIncW b E s h τ m W Vs F Λ i u ψ t t' =
      ∫ y, (Fdd.capM b E s h K W np).indicator f y ∂closedLaw b W np := by
    unfold capIncW
    refine integral_congr_ae ?_
    filter_upwards [hfe, Fdd.capC_ae_eq (W := W) (np := np) (K := K) hb hE1 hE2 s h]
      with y hy heq
    by_cases hyM : y ∈ Fdd.capM b E s h K W np
    · have hc : y.1.1 ∈ physCapEventC b E s h K W := heq.mpr hyM
      rw [indicator_of_mem hyM, indicator_of_mem hc, one_mul, hf]
      simp only [mgen_clip_eq hR hFv hΛv (hy hyM)]
    · have hc : y.1.1 ∉ physCapEventC b E s h K W := fun h' => hyM (heq.mp h')
      rw [indicator_of_notMem hyM, indicator_of_notMem hc, zero_mul, zero_smul]
  rw [e1, integral_indicator (Fdd.measurableSet_capM b E s h K W np), Fdd.condL,
    ProbabilityTheory.cond, integral_smul_measure, smul_smul, ENNReal.toReal_inv,
    Fdd.closedLaw_capM hb hE1 hE2 s h, mul_inv_cancel₀, one_smul]
  exact ENNReal.toReal_ne_zero.2 ⟨hm, measure_ne_top _ _⟩

end CapInc

/-!
## The passage
-/

/-- **`KFddPassage`** (the passage to the limit, drift-free tests). -/
theorem kFddPassage : KFddPassage := by
  intro hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hPr F Λ Rχ Rξ hFc hΛc hFv hΛv
    hW
  obtain ⟨hD, hlim, hA, hne, hφ, hLD, hF⟩ := hPr
  obtain ⟨hQ, htm, hGm, hKm, hGc, hKc⟩ := hLD
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, hs, hτ, hh, -, hfr⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hBc : (birthTimes s τ).Countable := (birthTimes_finite s τ).countable
  have h0B : (0 : ℝ≥0) ∉ birthTimes s τ := fun ⟨j, hj⟩ => by
    rw [NNReal.coe_zero, add_zero] at hj
    exact (hτ j).ne hj
  have hobs := measurable_complexObs htm hGm hKm
  have hjm := measurable_uncurry_complexObs (b := b) (E := E) (s := s) (τ := τ) (m := m) htm hGm
    hKm hGc hKc
  have hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0 :=
    hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh hA hne)
  have hfeQ := ae_feasible_all hD hφ hF hobs hcap hGc
  obtain ⟨R, -, hR⟩ := exists_norm_le_of_cutReg (K := K) b E s τ m Rχ Rξ
  obtain ⟨CF, hCF⟩ := exists_bound_fC (b := b) (E := E) (s := s) (τ := τ) (m := m) hFc R
  obtain ⟨CG, hCG⟩ := exists_bound_gC (b := b) (E := E) (s := s) (τ := τ) (m := m) hΛc R
  have hCF' : ∀ t x y, ‖fC b E s τ m F R t x y‖ ≤ max CF CG := fun t x y =>
    (hCF t x y).trans (le_max_left _ _)
  have hCG' : ∀ t x y, ‖gC b E s τ m Λ R t x y‖ ≤ max CF CG := fun t x y =>
    (hCG t x y).trans (le_max_right _ _)
  have hQeq : ∀ᵐ ω ∂Q, ∀ t, mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R)
      (complexObs tseq G Kc) t ω = genObs b E s τ m (complexObs tseq G Kc) F Λ t ω := by
    filter_upwards [hfeQ] with ω hω t
    exact mgen_clip_eq hR hFv hΛv (fun u => by rw [gOf_complexObs]; exact hω u) t
  refine ⟨fun t => ?_, fun s' t hst hs' ht' r i u hu hub ψ => ?_⟩
  · exact (integrable_mgen (c := cK) Q hjm (continuous_fC hFc R) hCF' hCG'
      (measurable_gC hΛc R) t).congr (hQeq.mono fun ω hω => hω t)
  -- the fdd along `φ`, as integrals under the conditioned laws, shifted past the frame index
  have hfddL : IsFddOff (birthTimes s τ) (fun n => Fdd.condL b E s h K (φ n) np)
      (fun n => b3ObsAll b E s h τ m (φ n) (Vs (φ n))) Q (complexObs tseq G Kc) :=
    fun ι _ i u hu ψ => (hF ι i u (fun l j hj => hu l ⟨j, hj⟩) ψ).congr fun n =>
      Fdd.condObsTestAll_eq hb1 hE1 hE2 s h τ m (Vs (φ n)) i u ψ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hφ.eventually hfr)
  have hfddS : IsFddOff (birthTimes s τ) (fun n => Fdd.condL b E s h K (φ (n + N)) np)
      (fun n => b3ObsAll b E s h τ m (φ (n + N)) (Vs (φ (n + N)))) Q (complexObs tseq G Kc) :=
    fun ι _ i u hu ψ => (hfddL ι i u hu ψ).comp (tendsto_add_atTop_nat N)
  have hmS : ∀ n i', Measurable (Function.uncurry
      (b3ObsAll b E s h τ m (φ (n + N)) (Vs (φ (n + N))) i')) := fun n i' =>
    measurable_uncurry_b3ObsAll (hN (n + N) (Nat.le_add_left N n)).1 i'
  have : ∀ n, IsFiniteMeasure (Fdd.condL b E s h K (φ (n + N)) np) := fun n => by
    unfold Fdd.condL; infer_instance
  have hX := hfddS.tendsto_test_mgen (c := cK) hBc hmS hjm h0B i u hub ψ (continuous_fC hFc R)
    (continuous_gC hΛc R) hCF' hCG' (measurable_gC hΛc R) hs' ht'
  have hX' := (tendsto_add_atTop_iff_nat (f := fun n =>
    ∫ y, ψ (fun l => b3ObsAll b E s h τ m (φ n) (Vs (φ n)) (i l) (u l) y) •
      (mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R)
          (b3ObsAll b E s h τ m (φ n) (Vs (φ n))) t y -
        mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R)
          (b3ObsAll b E s h τ m (φ n) (Vs (φ n))) s' y) ∂Fdd.condL b E s h K (φ n) np) N).1 hX
  -- the cap mass
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  have hp : (entranceLaw P μ s (capSet K h)).toReal ≠ 0 :=
    (ENNReal.toReal_pos hne (measure_ne_top _ _)).ne'
  have hmass : Tendsto (fun n => (growthPathLaw (φ n) b (physCapEventC b E s h K (φ n))).toReal)
      atTop (𝓝 (entranceLaw P μ s (capSet K h)).toReal) :=
    (CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh K (hA K)).comp hφ
  have hinc : ∀ᶠ n in atTop, capIncW b E s h τ m (φ n) (Vs (φ n)) F Λ i u ψ s' t =
      (growthPathLaw (φ n) b (physCapEventC b E s h K (φ n))).toReal •
        ∫ y, ψ (fun l => b3ObsAll b E s h τ m (φ n) (Vs (φ n)) (i l) (u l) y) •
          (mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R)
              (b3ObsAll b E s h τ m (φ n) (Vs (φ n))) t y -
            mgen cK (fC b E s τ m F R) (gC b E s τ m Λ R)
              (b3ObsAll b E s h τ m (φ n) (Vs (φ n))) s' y) ∂Fdd.condL b E s h K (φ n) np := by
    filter_upwards [hcap, eventually_ae_feasible_capM hD hφ] with n h1 h2
    exact capIncW_eq hb1 hE1 hE2 hR hFv hΛv h2 h1 i u ψ s' t
  have hlim1 := (hmass.smul hX').congr' (hinc.mono fun n hn => hn.symm)
  have hzero := tendsto_nhds_unique hlim1 (hW s' t hst hs' ht' r i u hu hub ψ)
  have hL := (smul_eq_zero.1 hzero).resolve_left hp
  rw [← hL]
  refine integral_congr_ae ?_
  filter_upwards [hQeq] with ω hω
  rw [hω t, hω s']

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK
