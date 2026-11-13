module

public import BlockBand.Endpoints.Clock.ClockMixingAlgebra
public import BlockBand.Layers.LayerMeasurability

/-!
# The clock-mixing lemma: measurability of the one-ended chain and the conditioning step

We prove the measurability and conditioning facts used in the proof of the clock-mixing lemma.

* Joint measurability, in the old input `X` and the fresh layer, of `𝒢`, `X₊`, `L`, `C`,
  `L f₊ L*`; measurability of the chain `X_j`, `Y_j`, `Q_j`, `γ_j`, `Z_j`, `√S_j` on the
  product space of the first `j` layers.
* `measurePreserving_initLast`: the law of the first `j+1` layers is the product of the law of
  the first `j` layers (the past) and the fresh layer.
* `eLpNorm_prod_le_of_cond`: conditioning in `L^p`: if for a.e. past `x` the conditional norm
  `‖G(x,·)‖_{L^p(ν)}` is at most `h(x)`, then `‖G‖_{L^p(μ⊗ν)} ≤ ‖h‖_{L^p(μ)}` (Tonelli).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

namespace ClockMixingProb

open ClockMixingAlg

/-!
## 1. Measurability
-/

section Meas

variable {α : Type*} [MeasurableSpace α]

theorem meas_entry {l m : Type*} {f : α → Matrix l m ℂ} (hf : Measurable f) (i : l) (k : m) :
    Measurable (fun a => f a i k) :=
  (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)

theorem meas_mul {l m o : Type*} [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => f a * g a) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun j _ => (meas_entry hf i j).mul (meas_entry hg j k)

theorem meas_smul {l m : Type*} (c : ℂ) {f : α → Matrix l m ℂ} (hf : Measurable f) :
    Measurable (fun a => c • f a) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul (meas_entry hf i k)

theorem meas_conjTranspose {l m : Type*} {f : α → Matrix l m ℂ}
    (hf : Measurable f) : Measurable (fun a => (f a)ᴴ) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  simp only [Matrix.conjTranspose_apply]
  exact continuous_star.measurable.comp (meas_entry hf k i)

theorem meas_trace {m : Type*} [Fintype m] {f : α → Matrix m m ℂ} (hf : Measurable f) :
    Measurable (fun a => (f a).trace) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.measurable_sum _ fun j _ => meas_entry hf j j

theorem meas_hsSandwich {W : ℕ} {f g : α → Matrix (Fin W) (Fin W) ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun a => hsSandwich (f a) (g a)) := by
  unfold hsSandwich
  exact Real.continuous_sqrt.measurable.comp (Complex.continuous_re.measurable.comp
    (meas_trace (meas_mul (meas_mul (meas_mul hf hg) hf) (meas_conjTranspose hg))))

variable {W : ℕ}

/-- Joint measurability of the augmented layer matrix in the old input and the layer. -/
theorem meas_layerMatrix_joint (E : ℝ) (z : ℂ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      layerMatrix .oneBlockOnePort E z (physEmbed p.1) p.2) := by
  have hcoordA : ∀ (a : Fin 1) (i j : Fin W),
      Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => p.2.1 a i j) :=
    fun a i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)))
  have hcoordB : ∀ (a : Fin 1) (k : Fin 1) (i j : Fin W),
      Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => p.2.2 a k i j) :=
    fun a k i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply k).comp ((measurable_pi_apply a).comp
        (measurable_snd.comp measurable_snd))))
  have hcoordX : ∀ i j : Fin W,
      Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => p.1 i j) :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  have hA : ∀ x y, Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      Internal.Contracts.Layers.blockDiag p.2.1 x y) := by
    intro x y
    unfold Internal.Contracts.Layers.blockDiag
    split_ifs
    · exact hcoordA _ _ _
    · exact measurable_const
  have hB : ∀ x y, Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      bondMatrix .oneBlockOnePort p.2.2 x y) := by
    intro x y
    unfold bondMatrix
    split_ifs
    · exact hcoordB _ _ _ _
    · exact measurable_const
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · simp only [layerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply, physEmbed,
      Matrix.of_apply]
    exact ((hA x y).sub measurable_const).sub (hcoordX _ _)
  · simp only [layerMatrix, Matrix.fromBlocks_apply₁₂]
    exact hB x y
  · simp only [layerMatrix, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    exact continuous_star.measurable.comp (hB y x)
  · simp only [layerMatrix, Matrix.fromBlocks_apply₂₂]
    exact measurable_const

theorem meas_freshLayer (b E : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => freshLayer b E p.1 p.2) :=
  BlockBand.Layers.measurable_matrix_inv.comp (meas_layerMatrix_joint E (boundaryZ b E))

theorem meas_freshG12 (b E : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => freshG12 b E p.1 p.2) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [freshG12, Matrix.of_apply]
  exact meas_entry (meas_freshLayer b E) _ _

theorem meas_freshC (b E : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => freshC b E p.1 p.2) :=
  meas_mul (meas_conjTranspose (meas_freshG12 b E)) (meas_freshG12 b E)

theorem meas_freshL (b E : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => freshL b E p.1 p.2) :=
  meas_mul (measurable_const.sub measurable_fst) (meas_freshG12 b E)

theorem meas_freshSchur (E : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W => freshSchur E p.1 p.2) := by
  have hBm : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      bondMatrix .oneBlockOnePort p.2.2) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    unfold bondMatrix
    split_ifs
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
          (measurable_snd.comp measurable_snd))))
    · exact measurable_const
  have hTop : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      (blockDiag p.2.1 - (E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort)
        (PhysSite W .oneBlockOnePort) ℂ) - physEmbed p.1)⁻¹) := by
    refine BlockBand.Layers.measurable_matrix_inv.comp ?_
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    simp only [Matrix.sub_apply, physEmbed, Matrix.of_apply]
    refine (Measurable.sub ?_ measurable_const).sub ?_
    · unfold Internal.Contracts.Layers.blockDiag
      split_ifs
      · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
          ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
      · exact measurable_const
    · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_fst)
  have hS : Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      layerSchur .oneBlockOnePort E (physEmbed p.1) p.2) :=
    meas_mul (meas_mul (meas_conjTranspose hBm) hTop) hBm
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [freshSchur, Matrix.of_apply]
  exact meas_entry hS _ _

theorem meas_passiveF (b E : ℝ) :
    Measurable (fun X : Matrix (Fin W) (Fin W) ℂ => passiveF b E X) := by
  unfold passiveF passiveResolvent
  exact (BlockBand.Layers.measurable_matrix_inv.comp (measurable_const.sub measurable_id)).sub
    measurable_const

theorem meas_freshTransportedF (b E : ℝ) :
    Measurable (fun p : Matrix (Fin W) (Fin W) ℂ × OneEndedLayer W =>
      freshTransportedF b E p.1 p.2) := by
  unfold freshTransportedF
  exact meas_mul (meas_mul (meas_freshL b E) ((meas_passiveF b E).comp (meas_freshSchur E)))
    (meas_conjTranspose (meas_freshL b E))

theorem meas_init (j : ℕ) {S : Type*} [MeasurableSpace S] :
    Measurable (fun ω : Fin (j + 1) → S => Fin.init ω) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem meas_last (j : ℕ) {S : Type*} [MeasurableSpace S] :
    Measurable (fun ω : Fin (j + 1) → S => ω (Fin.last j)) :=
  measurable_pi_apply _

theorem meas_X (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (oneEndedX E D j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have h : oneEndedX E D (j + 1) =
        fun ω => freshSchur E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := rfl
    have hp : Measurable (fun ω : Fin (j + 1) → OneEndedLayer W =>
        (oneEndedX E D j (Fin.init ω), ω (Fin.last j))) :=
      (ih.comp (meas_init j)).prodMk (meas_last j)
    rw [h]
    have h2 := (meas_freshSchur (W := W) E).comp hp
    simpa only [Function.comp_def] using h2

theorem meas_Y (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (oneEndedY b E q D j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hp : Measurable (fun ω : Fin (j + 1) → OneEndedLayer W =>
        (oneEndedX E D j (Fin.init ω), ω (Fin.last j))) :=
      ((meas_X E D j).comp (meas_init j)).prodMk (meas_last j)
    have hL := (meas_freshL b E).comp hp
    have h : oneEndedY b E q D (j + 1) = fun ω =>
        ((q (((j + 1 : ℕ) : ℝ) / W) : ℝ) : ℂ) •
            freshC b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) +
          (freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)))ᴴ *
            oneEndedY b E q D j (Fin.init ω) *
            freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) := rfl
    rw [h]
    exact (meas_smul _ ((meas_freshC b E).comp hp)).add
      (meas_mul (meas_mul (meas_conjTranspose hL) (ih.comp (meas_init j))) hL)

theorem meas_Q (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (oneEndedQ b E q D j) :=
  meas_smul _ (meas_Y b E q D j)

theorem meas_gamma (b E : ℝ) (q : ℝ → ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (oneEndedGamma b E q D j) :=
  Complex.continuous_re.measurable.comp (meas_trace (meas_Q b E q D j))

end Meas

/-!
## 2. The past and the fresh layer
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
      eLpNorm g p (Measure.pi fun _ : Fin j => ν) := by
  have hmp : MeasurePreserving (fun ω : Fin (j + 1) → S => Fin.init ω)
      (Measure.pi fun _ : Fin (j + 1) => ν) (Measure.pi fun _ : Fin j => ν) :=
    (measurePreserving_fst (μ := Measure.pi fun _ : Fin j => ν) (ν := ν)).comp
      (measurePreserving_initLast ν j)
  exact eLpNorm_comp_measurePreserving hg hmp

end Split

end ClockMixingProb

end BlockBand.Endpoints.Clock
