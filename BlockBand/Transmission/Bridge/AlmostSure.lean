module

public import BlockBand.Transmission.Bridge.Scattering

/-!
# Almost-sure hypotheses and adaptedness along the near-end-grown path

* `boundaryZ_im`, `boundaryZ_im_pos`: `Im z_∂ = (1-b)√(4-E²)/2 > 0` for `b < 1`, `|E| < 2`;
* `ae_isHermitian_gueMeasure`, `ae_growth_isHermitian`, `ae_passiveSample`: GUE blocks are
  Hermitian almost surely, so `PassiveSample` (the hypothesis of the passivity bridges) holds
  `growthPathLaw`-almost surely for `κ ≥ 0`, `b < 1`, `|E| < 2`;
* `measurable_matrix_inv`, `pathNearSchur_adapted`: `X_r` is `growthSigma W r`-measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped Matrix ComplexConjugate NNReal

variable {W : ℕ}

/-!
## The boundary parameter
-/

theorem boundaryZ_im (b E : ℝ) (hE : E ^ 2 ≤ 4) :
    (boundaryZ b E).im = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 := by
  have hs : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := Real.sq_sqrt (by linarith)
  have hn : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]; simp only [matchedA]; nlinarith
  rw [boundaryZ, Complex.add_im, Complex.inv_im, hn]
  simp [matchedA]
  ring

theorem boundaryZ_im_pos {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    0 < (boundaryZ b E).im := by
  rw [boundaryZ_im b E (by nlinarith)]
  have : 0 < Real.sqrt (4 - E ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have : 0 < 1 - b := by linarith
  positivity

/-!
## Hermitian blocks almost surely
-/

theorem gueSample_isHermitian {ι : Type*} [Fintype ι] (t : ℝ≥0) (X : ι × ι → ℂ) :
    (gueSample t X).IsHermitian := by
  ext a c
  simp only [gueSample, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_add,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem measurableSet_isHermitian (ι : Type*) [Fintype ι] :
    MeasurableSet {M : Matrix ι ι ℂ | M.IsHermitian} := by
  have hc : Continuous (Matrix.conjTranspose : Matrix ι ι ℂ → Matrix ι ι ℂ) :=
    continuous_id.matrix_conjTranspose
  have : {M : Matrix ι ι ℂ | M.IsHermitian} = {M | Mᴴ = M} := rfl
  rw [this]
  exact (isClosed_eq hc continuous_id).measurableSet

theorem ae_isHermitian_gueMeasure (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    ∀ᵐ M ∂gueMeasure ι t, M.IsHermitian := by
  rw [gueMeasure, ae_map_iff (measurable_gueSample t).aemeasurable (measurableSet_isHermitian ι)]
  exact Filter.Eventually.of_forall fun X => gueSample_isHermitian t X

theorem growthPathLaw_map_block (W : ℕ) (b : ℝ) (k : ℕ) :
    (growthPathLaw W b).map (fun ω : GrowthPath W => ω.1 k) =
      gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W)) := by
  have : (fun ω : GrowthPath W => ω.1 k) = (fun a : ℕ → Matrix (Fin W) (Fin W) ℂ => a k) ∘ Prod.fst :=
    rfl
  rw [this, ← Measure.map_map (measurable_pi_apply k) measurable_fst, growthPathLaw,
    Measure.map_fst_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]

/-- Almost surely every GUE block of the growth sample is Hermitian. -/
theorem ae_growth_isHermitian (W : ℕ) (b : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ k, (ω.1 k).IsHermitian := by
  rw [ae_all_iff]
  intro k
  have h := ae_isHermitian_gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  rw [← growthPathLaw_map_block W b k] at h
  exact ae_of_ae_map (measurable_pi_apply k |>.comp measurable_fst).aemeasurable h

/-- **The passivity hypothesis holds almost surely** for `κ ≥ 0`, `b < 1`, `|E| < 2`. -/
theorem ae_passiveSample (W : ℕ) {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) : ∀ᵐ ω ∂growthPathLaw W b, PassiveSample b E κ ω :=
  (ae_growth_isHermitian W b).mono fun _ hA => ⟨hA, hκ, boundaryZ_im_pos hb hE1 hE2⟩

/-!
## Adaptedness
-/

theorem measurable_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable fun M : Matrix n n ℂ => M⁻¹ := by
  have : (fun M : Matrix n n ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).smul
    (continuous_id.matrix_adjugate).measurable

/-- The length-`r` path as a function of the past coordinates. -/
def pathOfPast (W r : ℕ)
    (p : (Fin r → Matrix (Fin W) (Fin W) ℂ) × (Fin (r + 1) → Matrix (Fin W) (Fin W) ℂ)) :
    PathSample W r :=
  (fun i => p.1 ⟨r - 1 - i.val, by omega⟩, fun i => (p.2 ⟨r - 1 - i.val, by omega⟩)ᴴ,
    ![p.2 ⟨r, by omega⟩, p.2 ⟨0, by omega⟩])

theorem pathAt_eq_pathOfPast (W r : ℕ) : pathAt W r = pathOfPast W r ∘ pastCoords W r := by
  funext ω
  simp only [pathAt, pathOfPast, pastCoords, Function.comp]

theorem measurable_matrix_mul' {α l m n : Type*} [MeasurableSpace α] [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → Matrix m n ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ => hf.eval_matrix.mul hg.eval_matrix

theorem measurable_matrix_conjTranspose' {α m n : Type*} [MeasurableSpace α]
    {f : α → Matrix m n ℂ} (hf : Measurable f) : Measurable fun x => (f x)ᴴ := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact Complex.continuous_conj.measurable.comp hf.eval_matrix

/-- `X_r` (any absorption profile) is a measurable function of the path sample. -/
theorem measurable_nearSchur_absorbed (b E : ℝ) {r : ℕ} (ε : Fin r → ℝ) :
    Measurable fun p : PathSample W r =>
      nearSchur (boundaryZ b E) (absorbedPathSchur E ε p) := by
  have hC : Measurable fun p : PathSample W r => pathPortCoupling p := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [pathPortCoupling]
    split_ifs
    · exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp
        (measurable_snd.comp measurable_snd))
    · exact measurable_const
  have hP : Measurable fun p : PathSample W r => pathMatrix p := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [pathMatrix]
    split_ifs
    · exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp measurable_fst)
    · exact Matrix.measurable_apply.comp ((measurable_pi_apply _).comp
        (measurable_fst.comp measurable_snd))
    · exact Complex.continuous_conj.measurable.comp (Matrix.measurable_apply.comp
        ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
    · exact measurable_const
  have hH : Measurable fun p : PathSample W r =>
      pathMatrix p - (E : ℂ) • 1 + absorptionDiag W ε := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]
    exact (hP.eval_matrix.sub measurable_const).add measurable_const
  have hX : Measurable fun p : PathSample W r => absorbedPathSchur E ε p :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hC)
      (measurable_matrix_inv.comp hH)) hC
  have hY : ∀ i j : Fin 2, Measurable fun p : PathSample W r =>
      portBlock (absorbedPathSchur E ε p) i j := fun i j =>
    Measurable.of_eval_matrix _ fun x y => hX.eval_matrix
  have hinv : Measurable fun p : PathSample W r =>
      (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock (absorbedPathSchur E ε p) 1 1)⁻¹ := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub (hY 1 1).eval_matrix
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [nearSchur, Matrix.add_apply]
  exact (hY 0 0).eval_matrix.add (measurable_matrix_mul' (measurable_matrix_mul' (hY 0 1) hinv) (hY 1 0)).eval_matrix

/-- **Adaptedness**: `X_r` is `growthSigma W r`-measurable (: "the lengths
`r = 1,2,…` form a filtration"). -/
theorem pathNearSchur_adapted (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) :
    Measurable[growthSigma W r] (pathNearSchur b E κ W r) := by
  have hpast : Measurable[growthSigma W r] (pastCoords W r) := comap_measurable _
  have hpp : Measurable (pathOfPast W r) := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst
    · exact Measurable.of_eval fun i =>
        measurable_matrix_conjTranspose' ((measurable_pi_apply _).comp measurable_snd)
    · refine Measurable.of_eval fun j => ?_
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        exact (measurable_pi_apply _).comp measurable_snd
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact (measurable_pi_apply _).comp measurable_snd
  have : pathNearSchur b E κ W r = (fun p : PathSample W r =>
      nearSchur (boundaryZ b E) (absorbedPathSchur E (layerAbsorption W κ r) p)) ∘
        pathOfPast W r ∘ pastCoords W r := by
    funext ω; simp only [pathNearSchur, Function.comp]; rfl
  rw [this]
  exact ((measurable_nearSchur_absorbed b E _).comp hpp).comp hpast

end BlockBand.Transmission.Bridge
