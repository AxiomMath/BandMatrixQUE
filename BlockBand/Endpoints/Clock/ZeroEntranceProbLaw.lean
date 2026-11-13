module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbDefs
public import BlockBand.Layers.LayerMeasurability
public import BlockBand.Layers.LayerMeanBounds

/-!
# The zero-entrance lemma: measure-theoretic plumbing of the one-ended path

The induction over the layers in the proof of the zero-entrance lemma conditions on the old path,
which enters only through its Schur complement term. The law is `oneEndedLaw W b J`, the product of
`J` fresh layers `freshLaw W b = layerLaw W b .oneBlockOnePort`. Results (no contract is used):
* `measurable_freshSchur_joint`, `measurable_X`, `measurable_zeTrace_joint`: joint measurability
  of `X₊ = B*(A - e - X)⁻¹ B` in `(X, layer)`, of the chain `X_J` and of `(ζ, ω) ↦ h_J(ζ)`;
* `measurePreserving_initLast`: the law of `J + 1` layers is (past) ⊗ (fresh layer);
* `eLpNorm_prod_le_of_cond`, `eLpNorm_initLast_le`, `eLpNorm_init_eq`: conditioning in `L^p`;
* `ae_X_isHermitian`: almost surely every `X_J` is Hermitian (for Hermitian `D`);
* `norm_zeTrace_le`: then `|h_J(ζ)| ≤ (Im ζ)⁻¹`; `integrable_zeTrace`.

The measurability and conditioning lemmas follow the same route as those for the clock-mixing
lemma.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements (freshSchur freshLaw)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace ZeroEntranceProb

/-!
## Measurability
-/

section Meas

variable {α : Type*} [MeasurableSpace α]

theorem meas_entry {l m : Type*} {f : α → Matrix l m ℂ} (hf : Measurable f) (i : l) (k : m) :
    Measurable (fun a => f a i k) :=
  (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)

theorem meas_of_entries {l m : Type*} {f : α → Matrix l m ℂ}
    (hf : ∀ i k, Measurable (fun a => f a i k)) : Measurable f :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => hf i k

theorem meas_mul {l m o : Type*} [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => f a * g a) := by
  refine meas_of_entries fun i k => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun j _ => (meas_entry hf i j).mul (meas_entry hg j k)

theorem meas_conjTranspose {l m : Type*} {f : α → Matrix l m ℂ}
    (hf : Measurable f) : Measurable (fun a => (f a)ᴴ) := by
  refine meas_of_entries fun i k => ?_
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (meas_entry hf k i)

theorem meas_trace {m : Type*} [Fintype m] {f : α → Matrix m m ℂ} (hf : Measurable f) :
    Measurable (fun a => (f a).trace) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.measurable_sum _ fun j _ => meas_entry hf j j

variable {W : ℕ}

/-- `(X, ζ) ↦ W⁻¹ Tr (ζ - X)⁻¹` is jointly measurable. -/
theorem measurable_nrt_joint :
    Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × ℂ => normalizedResolventTrace q.1 q.2) := by
  have hM : Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × ℂ =>
      q.2 • (1 : Matrix (Fin W) (Fin W) ℂ) - q.1) := by
    refine meas_of_entries fun a c => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (measurable_snd.mul measurable_const).sub (meas_entry measurable_fst a c)
  unfold normalizedResolventTrace
  exact measurable_const.mul (meas_trace (BlockBand.Layers.measurable_matrix_inv.comp hM))

/-- Joint measurability of `X₊ = B*(A - e - X)⁻¹B` in the old input and the fresh layer. -/
theorem measurable_freshSchur_joint (e : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => freshSchur e p.1 p.2) := by
  have hBm : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      bondMatrix .oneBlockOnePort p.2.2) := by
    refine meas_of_entries fun x y => ?_
    unfold bondMatrix
    split_ifs
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
          (measurable_snd.comp measurable_snd))))
    · exact measurable_const
  have hTop : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      (blockDiag p.2.1 - (e : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort)
        (PhysSite W .oneBlockOnePort) ℂ) - cavityLift p.1)⁻¹) := by
    refine BlockBand.Layers.measurable_matrix_inv.comp ?_
    refine meas_of_entries fun x y => ?_
    simp only [Matrix.sub_apply, cavityLift, Matrix.of_apply]
    refine (Measurable.sub ?_ measurable_const).sub ?_
    · unfold Internal.Contracts.Layers.blockDiag
      split_ifs
      · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
          ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
      · exact measurable_const
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)
  have hS : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      layerSchur .oneBlockOnePort e (cavityLift p.1) p.2) :=
    meas_mul (meas_mul (meas_conjTranspose hBm) hTop) hBm
  refine meas_of_entries fun x y => ?_
  exact meas_entry hS _ _

theorem measurable_init (j : ℕ) {S : Type*} [MeasurableSpace S] :
    Measurable (fun ω : Fin (j + 1) → S => Fin.init ω) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem measurable_last (j : ℕ) {S : Type*} [MeasurableSpace S] :
    Measurable (fun ω : Fin (j + 1) → S => ω (Fin.last j)) :=
  measurable_pi_apply _

theorem oneEndedX_succ (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (ω : Fin (j + 1) → OneEndedLayer W) :
    oneEndedX e D (j + 1) ω = freshSchur e (oneEndedX e D j (Fin.init ω)) (ω (Fin.last j)) :=
  rfl

theorem zeTrace_succ (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (ζ : ℂ)
    (ω : Fin (j + 1) → OneEndedLayer W) :
    zeTrace e D (j + 1) ζ ω = cavityHplus e (oneEndedX e D j (Fin.init ω)) ζ (ω (Fin.last j)) :=
  rfl

theorem zeTrace_zero (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ)
    (ω : Fin 0 → OneEndedLayer W) : zeTrace e D 0 ζ ω = normalizedResolventTrace D ζ :=
  rfl

/-- The chain `X_J` is measurable on the product space of the first `J` layers. -/
theorem measurable_X (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (oneEndedX e D j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hp : Measurable (fun ω : Fin (j + 1) → OneEndedLayer W =>
        (oneEndedX e D j (Fin.init ω), ω (Fin.last j))) :=
      (ih.comp (measurable_init j)).prodMk (measurable_last j)
    have h : oneEndedX e D (j + 1) =
        fun ω => freshSchur e (oneEndedX e D j (Fin.init ω)) (ω (Fin.last j)) := rfl
    rw [h]
    have h2 := (measurable_freshSchur_joint (W := W) e).comp hp
    simpa only [Function.comp_def] using h2

/-- `(ζ, ω) ↦ h_J(ζ)(ω)` is jointly measurable. -/
theorem measurable_zeTrace_joint (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) :
    Measurable (fun q : ℂ × (Fin J → OneEndedLayer W) => zeTrace e D J q.1 q.2) := by
  have h1 : Measurable (fun q : ℂ × (Fin J → OneEndedLayer W) =>
      (oneEndedX e D J q.2, q.1)) :=
    ((measurable_X e D J).comp measurable_snd).prodMk measurable_fst
  have h2 := (measurable_nrt_joint (W := W)).comp h1
  unfold zeTrace
  exact h2

theorem measurable_zeTrace (e : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (J : ℕ) (ζ : ℂ) :
    Measurable (zeTrace e D J ζ) := by
  have h := (measurable_zeTrace_joint e D J).comp
    (f := fun ω : Fin J → OneEndedLayer W => (ζ, ω)) (measurable_const.prodMk measurable_id)
  simpa only [Function.comp_def] using h

end Meas

/-!
## The past and the fresh layer
-/

section Split

variable {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

/-- The law of the first `j+1` layers is (past) ⊗ (fresh layer). -/
theorem measurePreserving_initLast (j : ℕ) :
    MeasurePreserving (fun ω : Fin (j + 1) → S => (Fin.init ω, ω (Fin.last j)))
      (Measure.pi fun _ : Fin (j + 1) => ν) ((Measure.pi fun _ : Fin j => ν).prod ν) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (j + 1) => ν) (Fin.last j)
  have h2 := (Measure.measurePreserving_swap (μ := ν)
    (ν := Measure.pi fun _ : Fin j => ν)).comp h1
  convert h2 using 1
  funext ω
  simp only [Function.comp_apply]
  refine Prod.ext ?_ ?_
  · funext k
    simp [MeasurableEquiv.piFinSuccAbove, Fin.init]
  · simp [MeasurableEquiv.piFinSuccAbove]

theorem measurePreserving_init (j : ℕ) :
    MeasurePreserving (fun ω : Fin (j + 1) → S => Fin.init ω)
      (Measure.pi fun _ : Fin (j + 1) => ν) (Measure.pi fun _ : Fin j => ν) :=
  (measurePreserving_fst (μ := Measure.pi fun _ : Fin j => ν) (ν := ν)).comp
    (measurePreserving_initLast ν j)

theorem measurePreserving_last (j : ℕ) :
    MeasurePreserving (fun ω : Fin (j + 1) → S => ω (Fin.last j))
      (Measure.pi fun _ : Fin (j + 1) => ν) ν :=
  (measurePreserving_snd (μ := Measure.pi fun _ : Fin j => ν) (ν := ν)).comp
    (measurePreserving_initLast ν j)

/-- **Conditioning in `L^p`** (Tonelli). -/
theorem eLpNorm_prod_le_of_cond {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {F : Type*} [NormedAddCommGroup F] {G : α × S → F} (hG : AEStronglyMeasurable G (μ.prod ν))
    {p : ℝ} (hp : 0 < p) {h : α → ℝ}
    (hb : ∀ᵐ x ∂μ, eLpNorm (fun y => G (x, y)) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (h x)) :
    eLpNorm G (ENNReal.ofReal p) (μ.prod ν) ≤ eLpNorm h (ENNReal.ofReal p) μ := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  by_cases hh : AEStronglyMeasurable h μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hh]; exact le_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hG,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hh, ENNReal.toReal_ofReal hp.le]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [lintegral_prod _ (hG.enorm.pow_const _)]
  refine lintegral_mono_ae (hb.mono fun x hx => ?_)
  have hfin : eLpNorm (fun y => G (x, y)) (ENNReal.ofReal p) ν ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hmeas := aestronglyMeasurable_of_eLpNorm_ne_top hfin
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hmeas, ENNReal.toReal_ofReal hp.le] at hx
  have hx' : ((∫⁻ y, ‖G (x, y)‖ₑ ^ p ∂ν) ^ (1 / p)) ^ p ≤ (ENNReal.ofReal (h x)) ^ p :=
    ENNReal.rpow_le_rpow hx hp.le
  rw [one_div, ENNReal.rpow_inv_rpow hp.ne'] at hx'
  refine hx'.trans (ENNReal.rpow_le_rpow ?_ hp.le)
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- Conditioning along the chain: a function of (past, fresh layer) on the first `j+1`
layers. -/
theorem eLpNorm_initLast_le (j : ℕ) {F : Type*} [NormedAddCommGroup F]
    {G : (Fin j → S) × S → F}
    (hG : AEStronglyMeasurable G ((Measure.pi fun _ : Fin j => ν).prod ν)) {p : ℝ} (hp : 0 < p)
    {h : (Fin j → S) → ℝ}
    (hb : ∀ᵐ x ∂(Measure.pi fun _ : Fin j => ν),
      eLpNorm (fun y => G (x, y)) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (h x)) :
    eLpNorm (fun ω : Fin (j + 1) → S => G (Fin.init ω, ω (Fin.last j))) (ENNReal.ofReal p)
        (Measure.pi fun _ : Fin (j + 1) => ν) ≤
      eLpNorm h (ENNReal.ofReal p) (Measure.pi fun _ : Fin j => ν) := by
  have hmp := measurePreserving_initLast ν j
  have := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p) hG hmp
  rw [show (fun ω : Fin (j + 1) → S => G (Fin.init ω, ω (Fin.last j))) =
    G ∘ (fun ω : Fin (j + 1) → S => (Fin.init ω, ω (Fin.last j))) from rfl, this]
  exact eLpNorm_prod_le_of_cond ν hG hp hb

/-- A function of the past only has the same `L^p` norm on the first `j+1` layers. -/
theorem eLpNorm_init_eq (j : ℕ) {F : Type*} [NormedAddCommGroup F] {g : (Fin j → S) → F}
    (hg : AEStronglyMeasurable g (Measure.pi fun _ : Fin j => ν)) (p : ℝ≥0∞) :
    eLpNorm (fun ω : Fin (j + 1) → S => g (Fin.init ω)) p
        (Measure.pi fun _ : Fin (j + 1) => ν) =
      eLpNorm g p (Measure.pi fun _ : Fin j => ν) :=
  eLpNorm_comp_measurePreserving hg (measurePreserving_init ν j)

/-- Fubini along the chain. -/
theorem integral_initLast (j : ℕ) {G : (Fin j → S) × S → ℂ}
    (hG : Integrable G ((Measure.pi fun _ : Fin j => ν).prod ν)) :
    ∫ ω, G (Fin.init ω, ω (Fin.last j)) ∂(Measure.pi fun _ : Fin (j + 1) => ν) =
      ∫ x, ∫ y, G (x, y) ∂ν ∂(Measure.pi fun _ : Fin j => ν) := by
  have hmp := measurePreserving_initLast ν j
  rw [← integral_prod _ hG]
  have hG' : AEStronglyMeasurable G
      (Measure.map (fun ω : Fin (j + 1) → S => (Fin.init ω, ω (Fin.last j)))
        (Measure.pi fun _ : Fin (j + 1) => ν)) := by
    rw [hmp.map_eq]; exact hG.aestronglyMeasurable
  rw [← integral_map hmp.measurable.aemeasurable hG', hmp.map_eq]

theorem integral_init (j : ℕ) {g : (Fin j → S) → ℂ}
    (hg : AEStronglyMeasurable g (Measure.pi fun _ : Fin j => ν)) :
    ∫ ω, g (Fin.init ω) ∂(Measure.pi fun _ : Fin (j + 1) => ν) =
      ∫ x, g x ∂(Measure.pi fun _ : Fin j => ν) := by
  have hmp := measurePreserving_init ν j
  rw [← hmp.map_eq] at hg
  rw [← integral_map hmp.measurable.aemeasurable hg, hmp.map_eq]

end Split

/-!
## Hermitian chain and bounded traces
-/

section Herm

variable {W : ℕ}

/-- Almost surely every `X_J` is Hermitian (for Hermitian `D`). -/
theorem ae_X_isHermitian (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ} (hD : D.IsHermitian) (J : ℕ) :
    ∀ᵐ ω ∂oneEndedLaw W b J, (oneEndedX e D J ω).IsHermitian := by
  induction J with
  | zero => exact Filter.Eventually.of_forall fun _ => hD
  | succ J ih =>
    have h1 : ∀ᵐ ω ∂oneEndedLaw W b (J + 1), (oneEndedX e D J (Fin.init ω)).IsHermitian :=
      (measurePreserving_init (freshLaw W b) J).quasiMeasurePreserving.ae ih
    have h2 : ∀ᵐ ω ∂oneEndedLaw W b (J + 1), ∀ j, ((ω (Fin.last J)).1 j).IsHermitian :=
      (measurePreserving_last (freshLaw W b) J).quasiMeasurePreserving.ae
        (BlockBand.Layers.lct_ae_blocks_isHermitian W b .oneBlockOnePort)
    filter_upwards [h1, h2] with ω hω1 hω2
    exact CavityMeanProb.freshSchur_isHermitian e hω1 _ hω2

/-- `|h_J(ζ)| ≤ (Im ζ)⁻¹` whenever `X_J` is Hermitian. -/
theorem norm_zeTrace_le (hW : 0 < W) (e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ} {J : ℕ}
    {ω : Fin J → OneEndedLayer W} (hH : (oneEndedX e D J ω).IsHermitian) {ζ : ℂ}
    (hζ : 0 < ζ.im) : ‖zeTrace e D J ζ ω‖ ≤ 1 / ζ.im :=
  CavityMeanProb.norm_normalizedResolventTrace_le hW hH hζ

theorem ae_norm_zeTrace_le (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    ∀ᵐ ω ∂oneEndedLaw W b J, ‖zeTrace e D J ζ ω‖ ≤ 1 / ζ.im := by
  filter_upwards [ae_X_isHermitian b e hD J] with ω hω
  exact norm_zeTrace_le hW e hω hζ

theorem integrable_zeTrace (hW : 0 < W) (b e : ℝ) {D : Matrix (Fin W) (Fin W) ℂ}
    (hD : D.IsHermitian) (J : ℕ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    Integrable (zeTrace e D J ζ) (oneEndedLaw W b J) :=
  Integrable.of_bound (measurable_zeTrace e D J ζ).aestronglyMeasurable (1 / ζ.im)
    (ae_norm_zeTrace_le hW b e hD J hζ)

end Herm

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
