module

public import BlockBand.Endpoints.Poisson.SingleCollarMomentStage
public import BlockBand.Endpoints.Response.PathFractionalInverseLaw
public import BlockBand.Endpoints.Sine.GUELawBridge

/-!
# The stage log moment from the passive-log lemma

The stage log-determinant moment bound `ScsStageLogMoment` follows from the passive-log
hypothesis `PassiveLog`, applied to the effective block model of each stage.

* `scsStageLogMoment_of_passiveLog : PassiveLog → ScsStageLogMoment` (`r = 2`, Minkowski).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.Inputs (passiveLog PassiveLog BlockModel gueMatrixLaw)
open BlockBand.Internal.Contracts.Layers (boundaryZ)
open scoped ENNReal ComplexOrder

section Model

open Classical

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

/-!
### Measurability helpers
-/

theorem scm_measurable_submatrix {α ι κ ι' κ' : Type*} [MeasurableSpace α]
    {f : α → Matrix ι κ ℂ} (hf : Measurable f) (r : ι' → ι) (c : κ' → κ) :
    Measurable fun a => (f a).submatrix r c :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [submatrix_apply]
    exact hf.eval_matrix

theorem scm_measurable_smul {α ι κ : Type*} [MeasurableSpace α]
    {f : α → Matrix ι κ ℂ} (hf : Measurable f) (c : ℂ) :
    Measurable fun a => c • f a :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.mul hf.eval_matrix

variable (L s) in
theorem scm_measurable_bondS (π : Pairing) (T : Finset (Fin m)) :
    Measurable (scmBondS (W := W) L s π T) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [scmBondS, submatrix_apply, stageHerm, Pi.zero_apply, Matrix.zero_apply,
    zero_sub, Complex.ofReal_zero]
  have h2 : ∀ p a b, Measurable fun B : ZMod n → Matrix (Fin W) (Fin W) ℂ => B p a b :=
    fun p a b => Matrix.measurable_apply.comp (measurable_pi_apply p)
  refine Measurable.add (Measurable.add ?_ ?_) ?_ <;>
    split_ifs <;>
    first
    | exact measurable_const
    | exact h2 _ _ _
    | exact continuous_star.measurable.comp (h2 _ _ _)

variable (L s) in
theorem scm_measurable_G [NeZero n] (π : Pairing) (T : Finset (Fin m)) :
    Measurable (scmG (W := W) L s π T) := by
  have h := scm_measurable_submatrix (scm_measurable_bondS (W := W) L s π T)
    (fun i : {x : StageSite L s T W // scmIsM L s T x} => i.1)
    (fun i : ScmRest L s T W => i.1)
  exact measurable_mat_mul (measurable_conjTranspose''.comp h) h

/-!
### The site equivalence `R ≃ Fin k × Fin W`
-/

variable (L s) in
/-- The number of non-matched surviving blocks. -/
abbrev scmK (T : Finset (Fin m)) [NeZero n] : ℕ := Fintype.card (ScmBlock L s T)

variable (L s) in
/-- The enumeration of the non-matched surviving blocks. -/
abbrev scmEnum [NeZero n] (T : Finset (Fin m)) : ScmBlock L s T ≃ Fin (scmK L s T) :=
  Fintype.equivFin _

variable (L s W) in
/-- Non-matched sites `≃ Fin k × Fin W`: (enumerated block, internal coordinate). -/
def scmSigma [NeZero n] (T : Finset (Fin m)) : ScmRest L s T W ≃ Fin (scmK L s T) × Fin W where
  toFun x := (scmEnum L s T (scmBlk x), x.1.1.2)
  invFun q := ⟨⟨(((scmEnum L s T).symm q.1).1, q.2), ((scmEnum L s T).symm q.1).2.1⟩,
    ((scmEnum L s T).symm q.1).2.2⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Equiv.symm_apply_apply, scmBlk]
  right_inv q := by
    rcases q with ⟨i, a⟩
    simp only [Prod.mk.injEq, and_true]
    exact (scmEnum L s T).apply_symm_apply i

theorem scm_blk_sigma_symm [NeZero n] (T : Finset (Fin m)) (q : Fin (scmK L s T) × Fin W) :
    scmBlk ((scmSigma W L s T).symm q) = (scmEnum L s T).symm q.1 := rfl

/-!
### The block model
-/

variable (L s) in
/-- The Hermitianized block at enumerated block `j`. -/
def scmA [NeZero n] (T : Finset (Fin m)) (ω : RingCoords n W) :
    Fin (scmK L s T) → Matrix (Fin W) (Fin W) ℂ :=
  fun j => hermBlock (ω.1 ((scmEnum L s T).symm j).1)

theorem scm_D_isHermitian [NeZero n] (π : Pairing) (T : Finset (Fin m)) (z : ℂ)
    (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) : (scmD L s π T z B).IsHermitian := by
  refine ((scm_bondS_isHermitian π T B).submatrix _).sub ?_
  exact (isHermitian_conjTranspose_mul_self _).smul (by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])

theorem scm_Y_posSemidef [NeZero n] (π : Pairing) (T : Finset (Fin m)) {z : ℂ} (hz : 0 ≤ z.im)
    (B : ZMod n → Matrix (Fin W) (Fin W) ℂ) : (scmY L s π T z B).PosSemidef :=
  (posSemidef_conjTranspose_mul_self _).smul
    (Complex.zero_le_real.mpr (div_nonneg hz (Complex.normSq_nonneg z)))

/-- **The effective block model `H_eff`** of stage `T` under the original prior. -/
def scmModel (P : Parameters) (L : Fin m → ℕ) (s : ZMod P.n) (π : Pairing) (T : Finset (Fin m))
    (z : ℂ) (hz : 0 ≤ z.im) : BlockModel (scmK L s T) P.W where
  Ω := RingCoords P.n P.W
  P := ringCoordLaw P.n P.W P.b
  A := scmA L s T
  D := fun ω => reindex (scmSigma P.W L s T) (scmSigma P.W L s T) (scmD L s π T z ω.2)
  Y := fun ω => reindex (scmSigma P.W L s T) (scmSigma P.W L s T) (scmY L s π T z ω.2)
  measurable_A := Measurable.of_eval fun _ => measurable_hermBlock.comp
    ((measurable_pi_apply _).comp measurable_fst)
  measurable_D := (scm_measurable_submatrix (measurable_mat_sub
    (scm_measurable_submatrix (scm_measurable_bondS L s π T) _ _)
    (scm_measurable_smul (scm_measurable_G L s π T) _)) _ _).comp measurable_snd
  measurable_Y := (scm_measurable_submatrix
    (scm_measurable_smul (scm_measurable_G L s π T) _) _ _).comp measurable_snd
  hermitian_A := fun _ _ => hermBlock_isHermitian _
  hermitian_D := fun ω => (scm_D_isHermitian π T z ω.2).submatrix _
  posSemidef_Y := fun ω => (scm_Y_posSemidef π T hz ω.2).submatrix _

theorem scmModel_isIndependent (P : Parameters) (L : Fin m → ℕ) (s : ZMod P.n) (π : Pairing)
    (T : Finset (Fin m)) (z : ℂ) (hz : 0 ≤ z.im) :
    (scmModel P L s π T z hz).IsIndependent (1 - 2 * P.b) := by
  have hR := iIndepFun_ringCoord (n := P.n) (W := P.W) P.b
  refine ⟨fun j => ?_, ?_, ?_⟩
  · have hm := hR.2 (Sum.inl ((scmEnum L s T).symm j).1)
    show HasLaw (hermBlock ∘ ringCoord (W := P.W) (Sum.inl ((scmEnum L s T).symm j).1)) _
      (ringCoordLaw P.n P.W P.b)
    refine ⟨(measurable_hermBlock.comp (measurable_ringCoord _)).aemeasurable, ?_⟩
    rw [← Measure.map_map measurable_hermBlock (measurable_ringCoord _), hm.map_eq]
    show (gueBlockLaw P.W P.b).map hermBlock = _
    rw [gueBlockLaw, gueMeasure_map_hermBlock, gueMeasure_eq_gueMatrixLaw guelawBridge_holds]
  · have hinj : Function.Injective (fun j : Fin (scmK L s T) =>
        (Sum.inl ((scmEnum L s T).symm j).1 : ZMod P.n ⊕ ZMod P.n)) := by
      intro i j h
      simp only [Sum.inl.injEq] at h
      exact (scmEnum L s T).symm.injective (Subtype.ext h)
    exact (hR.1.precomp hinj).comp (fun _ => hermBlock) (fun _ => measurable_hermBlock)
  · show IndepFun _ _ ((Measure.pi _).prod (Measure.pi _))
    have hX : Measurable (fun (a : ZMod P.n → Matrix (Fin P.W) (Fin P.W) ℂ)
        (j : Fin (scmK L s T)) => hermBlock (a ((scmEnum L s T).symm j).1)) :=
      Measurable.of_eval fun _ => measurable_hermBlock.comp (measurable_pi_apply _)
    have hY : Measurable (fun B : ZMod P.n → Matrix (Fin P.W) (Fin P.W) ℂ =>
        (reindex (scmSigma P.W L s T) (scmSigma P.W L s T) (scmD L s π T z B),
          reindex (scmSigma P.W L s T) (scmSigma P.W L s T) (scmY L s π T z B))) :=
      ((scm_measurable_submatrix (measurable_mat_sub
        (scm_measurable_submatrix (scm_measurable_bondS L s π T) _ _)
        (scm_measurable_smul (scm_measurable_G L s π T) _)) _ _)).prodMk
        (scm_measurable_submatrix (scm_measurable_smul (scm_measurable_G L s π T) _) _ _)
    exact (indepFun_prod hX hY).symm

/-- On Hermitian samples, `H + iY` of the model is the reindexed `X = D + ⊕_p A_p + iY`. -/
theorem scmModel_H_add_Y (P : Parameters) (L : Fin m → ℕ) (s : ZMod P.n) (π : Pairing)
    (T : Finset (Fin m)) (z : ℂ) (hz : 0 ≤ z.im) (ω : RingCoords P.n P.W)
    (hω : ∀ p, (ω.1 p).IsHermitian) :
    (scmModel P L s π T z hz).H ω + Complex.I • (scmModel P L s π T z hz).Y ω =
      reindex (scmSigma P.W L s T) (scmSigma P.W L s T) (scmX L s π T z ω) := by
  have hA : ∀ p, hermBlock (ω.1 p) = ω.1 p := fun p =>
    BlockModelCount.toHerm_of_isHermitian (hω p)
  ext q q'
  simp only [BlockModel.H, BlockModel.blockSum, scmModel, scmA, scmX, scmBlocks, reindex_apply,
    submatrix_apply, Matrix.add_apply, Matrix.smul_apply, scm_blk_sigma_symm, hA,
    Equiv.apply_eq_iff_eq]
  rfl

/-- **The stage log ratio is almost surely the passive log of `H_eff`.** -/
theorem scm_stage_log_ae (P : Parameters) {L : Fin m → ℕ} (hL : IsCollarLayout P.n L)
    (s : ZMod P.n) (π : Pairing) (T : Finset (Fin m)) (e : ℝ) {z : ℂ} (hz : 0 < z.im) (buf : ℕ)
    (κ : ℝ) :
    (fun ω => Real.log (‖(stageMatrix L s π T e z buf κ ω).det‖ /
        ‖(stageMatrix L s π T e z buf 0 ω).det‖)) =ᵐ[ringCoordLaw P.n P.W P.b]
      fun ω => passiveLog ((scmModel P L s π T z hz.le).H ω +
          Complex.I • (scmModel P L s π T z hz.le).Y ω)
        (reindex (scmSigma P.W L s T) (scmSigma P.W L s T) (scmQ L s T buf))
        (κ / (P.W : ℝ) ^ 2) e := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  filter_upwards [ringCoordLaw_ae_isHermitian (n := P.n) (W := P.W) P.b] with ω hω
  rw [scm_log_ratio_eq hL π T e hz0 buf κ ω, scmModel_H_add_Y P L s π T z hz.le ω hω,
    scm_passiveLog_reindex]

theorem scm_Q_posSemidef [NeZero n] (T : Finset (Fin m)) (buf : ℕ) :
    (reindex (scmSigma W L s T) (scmSigma W L s T) (scmQ L s T buf)).PosSemidef ∧
      (1 - reindex (scmSigma W L s T) (scmSigma W L s T) (scmQ L s T buf)).PosSemidef := by
  rw [scmQ, reindex_apply, submatrix_diagonal_equiv, ← diagonal_one, diagonal_sub]
  constructor
  · rw [posSemidef_diagonal_iff]
    intro i
    simp only [Function.comp_apply]
    split_ifs <;> simp
  · rw [posSemidef_diagonal_iff]
    intro i
    simp only [Function.comp_apply]
    split_ifs <;> simp

/-- **One stage.** Clause 3 of `PassiveLog` (constant `C` for `r = 2`, `K`, `c = 1 - 2b`), applied to `scmModel` with
`N = nW` (so `(κ/W²) N = κ n/W ≤ K`, `k W ≤ N`), bounds `‖log(|det H_κ|/|det H_0|)‖_{L²}` by `C` at every stage,
bulk energy and source. -/
theorem scm_stage_eLpNorm_le (P : Parameters) {K C : ℝ}
    (hC : ∀ (N k W : ℕ), 0 < W → k * W ≤ N → ∀ M : BlockModel k W,
      M.IsIndependent (1 - 2 * P.b) →
      ∀ Q : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ, Q.PosSemidef → (1 - Q).PosSemidef →
        ∀ (e a : ℝ), 0 ≤ a → a * (N : ℝ) ≤ K →
          eLpNorm (fun w => passiveLog (M.H w + Complex.I • M.Y w) Q a e)
            (ENNReal.ofReal 2) M.P ≤ ENNReal.ofReal C)
    {L : Fin m → ℕ} (hL : IsCollarLayout P.n L) (s : ZMod P.n) (π : Pairing)
    (T : Finset (Fin m)) (buf : ℕ) {e : ℝ} (he1 : -2 < e) (he2 : e < 2) {κ : ℝ} (hκ : 0 ≤ κ)
    (hκK : κ * P.n / P.W ≤ K) :
    eLpNorm (fun ω => Real.log (‖(stageMatrix L s π T e (boundaryZ P.b e) buf κ ω).det‖ /
        ‖(stageMatrix L s π T e (boundaryZ P.b e) buf 0 ω).det‖)) (ENNReal.ofReal 2)
      (ringCoordLaw P.n P.W P.b) ≤ ENNReal.ofReal C := by
  have hz : 0 < (boundaryZ P.b e).im :=
    boundaryZ_im_pos (by linarith [P.b_lt_half]) he1 he2
  have hW : (0 : ℝ) < P.W := Nat.cast_pos.mpr P.W_pos
  have hcard : scmK L s T * P.W ≤ P.n * P.W := by
    refine Nat.mul_le_mul_right _ ?_
    exact (Fintype.card_subtype_le _).trans (ZMod.card P.n).le
  have haK : κ / (P.W : ℝ) ^ 2 * ((P.n * P.W : ℕ) : ℝ) ≤ K := by
    have : κ / (P.W : ℝ) ^ 2 * ((P.n * P.W : ℕ) : ℝ) = κ * P.n / P.W := by
      push_cast; field_simp
    rw [this]; exact hκK
  obtain ⟨hQ1, hQ2⟩ := scm_Q_posSemidef (W := P.W) (L := L) (s := s) T buf
  have h := hC (P.n * P.W) (scmK L s T) P.W P.W_pos hcard (scmModel P L s π T _ hz.le)
    (scmModel_isIndependent P L s π T _ hz.le) _ hQ1 hQ2 e (κ / (P.W : ℝ) ^ 2)
    (div_nonneg hκ (sq_nonneg _)) haK
  exact le_of_eq_of_le (eLpNorm_congr_ae (scm_stage_log_ae P hL s π T e hz buf κ)) h

end Model

/-- **`ScsStageLogMoment` from `PassiveLog`**, with `H_eff = H_path + D + iY`. Only clause 3 of `PassiveLog` is used,
with `r = 2`, `c = 1 - 2b` and the given `K`; `M = 2 max(C, 0)` by Minkowski over the two stages `S` and
`S ∪ {k}`. Uniform in the admissible `P` with `P.b = b`, the layout, pairing, stage, collar, buffer, `e ∈ (-2, 2)`
and `κ ≥ 0` with `κ n/W ≤ K`. It also uses `guelawBridge_holds` (`gueMeasure = gueMatrixLaw`). -/
theorem scsStageLogMoment_of_passiveLog (hPL : PassiveLog) : ScsStageLogMoment := by
  intro b hb0 hb1 K hK
  obtain ⟨C, hC⟩ := hPL.2.2 2 two_pos K (1 - 2 * b) (by linarith)
  refine ⟨2, 2 * max C 0, one_lt_two, ?_⟩
  intro P hPb m L hL π S k _hk buf e he1 he2 κ hκ hκK
  subst hPb
  have hT := fun T : Finset (Fin m) =>
    scm_stage_eLpNorm_le P hC hL 0 π T buf he1 he2 hκ hκK
  have hC0 : ENNReal.ofReal C ≤ ENNReal.ofReal (max C 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  calc eLpNorm (scsStageLogDiff P L π S k e buf κ) (ENNReal.ofReal 2) (ringCoordLaw P.n P.W P.b)
      ≤ eLpNorm (fun ω => Real.log
          (‖(stageMatrix L 0 π S e (boundaryZ P.b e) buf κ ω).det‖ /
            ‖(stageMatrix L 0 π S e (boundaryZ P.b e) buf 0 ω).det‖)) (ENNReal.ofReal 2)
            (ringCoordLaw P.n P.W P.b) +
        eLpNorm (fun ω => Real.log
          (‖(stageMatrix L 0 π (insert k S) e (boundaryZ P.b e) buf κ ω).det‖ /
            ‖(stageMatrix L 0 π (insert k S) e (boundaryZ P.b e) buf 0 ω).det‖))
            (ENNReal.ofReal 2) (ringCoordLaw P.n P.W P.b) :=
        eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal (max C 0) + ENNReal.ofReal (max C 0) :=
        add_le_add ((hT S).trans hC0) ((hT _).trans hC0)
    _ = ENNReal.ofReal (2 * max C 0) := by
        rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), two_mul]

end BlockBand.Endpoints
