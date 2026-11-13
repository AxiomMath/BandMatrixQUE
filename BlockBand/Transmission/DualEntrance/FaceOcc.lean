module

public import BlockBand.Transmission.DualEntrance.Restart
public import BlockBand.Transmission.DualEntrance.FaceCalc
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main

/-!
# Generic 1D entrance lemma, part (i): zero occupation of the face

Setting: a filtered probability space `(Ω, Q, 𝓖)` (`Ω : Type`, raw filtration), a real
continuous semimartingale `z ≥ 0` (contract form in `ℝ¹`) with drift `β`, covariance `α`, every
path continuous, and a measurable random time `τ`. **`IsEntranceFace Q 𝓖 z β α τ c K M B`**
(`c > 0`, `K, M ≥ 0`): for `0 < u ≤ τ`,
`α ≤ 2z(β + Kz)` (i.e. `a/(2z) − b ≤ Kz`), `c − Mz ≤ β ≤ B`; after `τ`, `β = α = 0`.

* `itoDrift_le`: the Itô drift of `faceFun δ C T (t, z_t)`, `C = K + M + max B 0`, is
  `≤ −cδ/(z+δ)² 1{u ≤ τ}` (`occ`) at every `u > 0`.
* `lintegral_occ_le`: `∫_{z₀ ≤ m} ∫_{(0,T]} occ ≤ −log δ + m + 1 + CT` (restarted
  supermartingale bound at `s = 0`).
* **`lintegral_zeroInd`**: `E ∫_{(0,T]} 1{z_u = 0, u ≤ τ} du = 0` (take
  `δ = (j+1)^{-2}`: `δ log(1/δ) → 0`).
* **`exists_good_time`**: for every `ε > 0` there is `s ∈ (0, ε)` with `z_s > 0` a.s. on
  `{s ≤ τ}` (Tonelli).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The hypotheses of the generic 1D entrance lemma (`a/(2z) − b ≤ Kz`, `b ≥ c − Mz`). -/
structure IsEntranceFace (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (z β : ℝ≥0 → Ω → Fin 1 → ℝ) (α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ)
    (τ : Ω → WithTop ℝ≥0) (c K M B : ℝ) : Prop where
  csm : IsContinuousSemimartingale Q 𝓖 z β α
  cont : ∀ ω, Continuous fun u => z u ω 0
  nonneg : ∀ (u : ℝ≥0) (ω : Ω), 0 ≤ z u ω 0
  meas : Measurable τ
  c_pos : 0 < c
  K_nonneg : 0 ≤ K
  M_nonneg : 0 ≤ M
  inside : ∀ (u : ℝ≥0) (ω : Ω), 0 < u → (u : WithTop ℝ≥0) ≤ τ ω →
    α u ω 0 0 ≤ 2 * z u ω 0 * (β u ω 0 + K * z u ω 0) ∧ c - M * z u ω 0 ≤ β u ω 0 ∧
      β u ω 0 ≤ B
  outside : ∀ (u : ℝ≥0) (ω : Ω), ¬ (u : WithTop ℝ≥0) ≤ τ ω → β u ω 0 = 0 ∧ α u ω 0 0 = 0

/-- The time-correction constant. -/
def cst (K M B : ℝ) : ℝ := K + M + max B 0

/-- The occupation density `cδ/(z + δ)²` before `τ`. -/
def occ (z : ℝ≥0 → Ω → Fin 1 → ℝ) (τ : Ω → WithTop ℝ≥0) (c δ : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if (u : WithTop ℝ≥0) ≤ τ ω then c * δ / (z u ω 0 + δ) ^ 2 else 0

open scoped Classical in
/-- The indicator of `{z_u = 0, u ≤ τ}` (real time `u`). -/
def zeroInd (z : ℝ≥0 → Ω → Fin 1 → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) (u : ℝ) : ℝ≥0∞ :=
  if z u.toNNReal ω 0 = 0 ∧ (u.toNNReal : WithTop ℝ≥0) ≤ τ ω then 1 else 0

/-- `q ≤ E/(j+1)` for all `j` forces `q = 0`. -/
theorem eq_zero_of_le_div {q : ℝ≥0∞} {E : ℝ} (h : ∀ j : ℕ, q ≤ ENNReal.ofReal (E / (j + 1))) :
    q = 0 := by
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (E / (j + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul E
    simpa [div_eq_mul_inv] using this
  exact le_antisymm (ge_of_tendsto' ht h) bot_le

theorem le_ofReal_div {q : ℝ≥0∞} {x B : ℝ} (hx : 0 < x) (h : ENNReal.ofReal x * q ≤ ENNReal.ofReal B) :
    q ≤ ENNReal.ofReal (B / x) := by
  rw [ENNReal.ofReal_div_of_pos hx]
  refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hx).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2 ?_
  rwa [mul_comm]

namespace IsEntranceFace

variable {z β : ℝ≥0 → Ω → Fin 1 → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
  {τ : Ω → WithTop ℝ≥0} {c K M B : ℝ} (hF : IsEntranceFace Q 𝓖 z β α τ c K M B)
include hF

theorem cst_nonneg : 0 ≤ cst K M B := by
  unfold cst; linarith [hF.K_nonneg, hF.M_nonneg, le_max_right B 0]

theorem occ_nonneg {δ : ℝ} (hδ : 0 < δ) (u : ℝ≥0) (ω : Ω) : 0 ≤ occ z τ c δ u ω := by
  unfold occ; split_ifs
  · exact div_nonneg (mul_nonneg hF.c_pos.le hδ.le) (sq_nonneg _)
  · exact le_rfl

theorem pos_add {δ : ℝ} (hδ : 0 < δ) (u : ℝ≥0) (ω : Ω) : 0 < z u ω 0 + δ := by
  linarith [hF.nonneg u ω]

/-- **The drift of the face test function.** -/
theorem itoDrift_le {δ : ℝ} (hδ : 0 < δ) (T : ℝ) {u : ℝ≥0} (hu : 0 < u) (ω : Ω) :
    itoDrift (faceFun δ (cst K M B) T) (z u ω) u (β u ω) (α u ω) ≤ -occ z τ c δ u ω := by
  rw [itoDrift_faceFun (hF.pos_add hδ u ω)]
  unfold occ
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := hF.inside u ω hu h
    exact faceDrift_le (hF.nonneg u ω) hδ hF.K_nonneg hF.M_nonneg h1 h2 h3
  · obtain ⟨h1, h2⟩ := hF.outside u ω h
    rw [h1, h2]
    linarith [hF.cst_nonneg]

/-- Itô's formula for the face test function along `z`. -/
theorem isCSM_face [IsProbabilityMeasure Q] {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω (_ : Fin 1) => faceFun δ (cst K M B) T ((t : ℝ), z t ω))
      (fun t ω (_ : Fin 1) => itoDrift (faceFun δ (cst K M B) T) (z t ω) t (β t ω) (α t ω))
      (fun t ω => Matrix.of fun (_ _ : Fin 1) =>
        itoBracket (faceFun δ (cst K M B) T) (z t ω) t (α t ω)) :=
  SemimartingaleIto.semimartingaleItoFormula_holds 1 Ω Q 𝓖 z β α hF.csm (faceU δ)
    (isOpen_faceU δ) (Eventually.of_forall fun ω t => show -δ < z t ω 0 by
      linarith [hF.nonneg t ω]) _ (measurable_faceFun δ _ T) (contDiffOn_faceFun δ _ T)

theorem measurable_z0 : Measurable[𝓖 0] fun ω => z 0 ω 0 :=
  (continuous_apply 0).measurable.comp (hF.csm.adapted 0).measurable

/-- **Occupation bound** (restarted supermartingale bound at `s = 0`). -/
theorem lintegral_occ_le [IsProbabilityMeasure Q] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ) (T : ℝ≥0) :
    ∫⁻ ω in {ω | z 0 ω 0 ≤ m}, (∫⁻ u in Ioc (0 : ℝ) T,
      ENNReal.ofReal (occ z τ c δ u.toNNReal ω)) ∂Q ≤
      ENNReal.ofReal (-Real.log δ + m + 1 + cst K M B * T) := by
  have hA : MeasurableSet[𝓖 0] {ω | z 0 ω 0 ≤ (m : ℝ)} :=
    measurableSet_le hF.measurable_z0 measurable_const
  have hB : ∀ ω ∈ {ω | z 0 ω 0 ≤ (m : ℝ)}, faceFun δ (cst K M B) T
      (((0 : ℝ≥0) : ℝ), z 0 ω) ≤ -Real.log δ + m + 1 + cst K M B * T := by
    intro ω hω
    have hl : Real.log δ ≤ Real.log (z 0 ω 0 + δ) :=
      Real.log_le_log hδ (by linarith [hF.nonneg 0 ω])
    simp only [faceFun, NNReal.coe_zero, sub_zero]
    have : z 0 ω 0 ≤ m := hω
    linarith
  have H := lintegral_restart_le (hF.isCSM_face hδ T) (zero_le : (0 : ℝ≥0) ≤ T) hA hB (occ z τ c δ)
    (fun u ω => hF.occ_nonneg hδ u ω)
    (Eventually.of_forall fun ω _ u hu _ => hF.itoDrift_le hδ T hu ω)
    (Eventually.of_forall fun ω _ u hu => by
      have := faceFun_ge (δ := δ) (C := cst K M B) (T := T) (p := ((u : ℝ), z u ω))
        (hF.pos_add hδ u ω)
      have h2 : 0 ≤ cst K M B * ((T : ℝ) - u) :=
        mul_nonneg hF.cst_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hu))
      simp only at this ⊢
      linarith)
  calc _ ≤ ∫⁻ ω in {ω | z 0 ω 0 ≤ (m : ℝ)}, (ENNReal.ofReal (faceFun δ (cst K M B) T
          ((T : ℝ), z T ω)) + ∫⁻ u in Ioc ((0 : ℝ≥0) : ℝ) T,
            ENNReal.ofReal (occ z τ c δ u.toNNReal ω)) ∂Q :=
        lintegral_mono fun ω => by rw [NNReal.coe_zero]; exact le_add_self
    _ ≤ _ := H
    _ ≤ ∫⁻ _ in {ω | z 0 ω 0 ≤ (m : ℝ)},
          ENNReal.ofReal (-Real.log δ + m + 1 + cst K M B * T) ∂Q :=
        setLIntegral_mono_ae' (𝓖.le 0 _ hA) (Eventually.of_forall fun ω hω =>
          ENNReal.ofReal_le_ofReal (hB ω hω))
    _ ≤ _ := by
        rw [setLIntegral_const]
        exact mul_le_of_le_one_right' prob_le_one

theorem zeroInd_le {δ : ℝ} (hδ : 0 < δ) (ω : Ω) {u : ℝ} :
    zeroInd z τ ω u ≤ ENNReal.ofReal (δ / c) * ENNReal.ofReal (occ z τ c δ u.toNNReal ω) := by
  unfold zeroInd
  split_ifs with h
  · rw [← ENNReal.ofReal_mul (div_nonneg hδ.le hF.c_pos.le)]
    unfold occ
    rw [ite_eq_left h.2, h.1, zero_add]
    have : δ / c * (c * δ / δ ^ 2) = 1 := by
      field_simp [hδ.ne', hF.c_pos.ne']
    rw [this, ENNReal.ofReal_one]
  · exact bot_le

theorem lintegral_zeroInd_le [IsProbabilityMeasure Q] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (m : ℕ) (T : ℝ≥0) :
    ∫⁻ ω in {ω | z 0 ω 0 ≤ m}, (∫⁻ u in Ioc (0 : ℝ) T, zeroInd z τ ω u) ∂Q ≤
      ENNReal.ofReal (δ / c) * ENNReal.ofReal (-Real.log δ + m + 1 + cst K M B * T) := by
  calc _ ≤ ∫⁻ ω in {ω | z 0 ω 0 ≤ m}, ENNReal.ofReal (δ / c) * (∫⁻ u in Ioc (0 : ℝ) T,
        ENNReal.ofReal (occ z τ c δ u.toNNReal ω)) ∂Q :=
        lintegral_mono fun ω => (lintegral_mono fun u => hF.zeroInd_le hδ ω).trans_eq
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal (δ / c) * ∫⁻ ω in {ω | z 0 ω 0 ≤ m}, (∫⁻ u in Ioc (0 : ℝ) T,
        ENNReal.ofReal (occ z τ c δ u.toNNReal ω)) ∂Q :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (hF.lintegral_occ_le hδ hδ1 m T) _

/-- `E[∫_{(0,T]} 1{z_u = 0, u ≤ τ} du; z₀ ≤ m] = 0`. -/
theorem lintegral_zeroInd_restrict [IsProbabilityMeasure Q] (m : ℕ) (T : ℝ≥0) :
    ∫⁻ ω in {ω | z 0 ω 0 ≤ m}, (∫⁻ u in Ioc (0 : ℝ) T, zeroInd z τ ω u) ∂Q = 0 := by
  set D : ℝ := m + 1 + cst K M B * T with hD
  have hD0 : 0 ≤ D := by
    have := mul_nonneg hF.cst_nonneg T.coe_nonneg; positivity
  refine eq_zero_of_le_div (E := (2 + D) / c) fun j => ?_
  have hj : (1 : ℝ) ≤ j + 1 := by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith
  set δ : ℝ := 1 / ((j : ℝ) + 1) ^ 2 with hδdef
  have hj2 : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hj2]; nlinarith
  refine (hF.lintegral_zeroInd_le hδ hδ1 m T).trans ?_
  rw [← ENNReal.ofReal_mul (div_nonneg hδ.le hF.c_pos.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlog : -Real.log δ = 2 * Real.log ((j : ℝ) + 1) := by
    rw [hδdef, one_div, Real.log_inv, Real.log_pow, neg_neg]; push_cast; ring
  have hl : Real.log ((j : ℝ) + 1) ≤ j + 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < j + 1); linarith
  have key : δ * (-Real.log δ + D) ≤ (2 + D) / (j + 1) := by
    have h1 : δ * (-Real.log δ + D) ≤ δ * (2 * (j + 1) + D) :=
      mul_le_mul_of_nonneg_left (by rw [hlog]; linarith) hδ.le
    refine h1.trans ?_
    rw [hδdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hj2 (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hD0 (by linarith : (0 : ℝ) ≤ j + 1)) j.cast_nonneg]
  have hc := hF.c_pos
  rw [show -Real.log δ + m + 1 + cst K M B * T = -Real.log δ + D by rw [hD]; ring]
  calc δ / c * (-Real.log δ + D) = δ * (-Real.log δ + D) / c := by ring
    _ ≤ (2 + D) / (j + 1) / c := div_le_div_of_nonneg_right key hc.le
    _ = (2 + D) / c / (j + 1) := by ring

/-- **Zero occupation of the face**: `E ∫_{(0,T]} 1{z_u = 0, u ≤ τ} du = 0`. -/
theorem lintegral_zeroInd [IsProbabilityMeasure Q] (T : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Ioc (0 : ℝ) T, zeroInd z τ ω u) ∂Q = 0 := by
  have hU : (⋃ m : ℕ, {ω | z 0 ω 0 ≤ m}) = univ :=
    eq_univ_of_forall fun ω => by
      obtain ⟨n, hn⟩ := exists_nat_ge (z 0 ω 0)
      exact mem_iUnion.2 ⟨n, show z 0 ω 0 ≤ n by linarith⟩
  have hmono : Monotone fun m : ℕ => {ω | z 0 ω 0 ≤ (m : ℝ)} := fun m n hmn ω hω => by
    have h1 : z 0 ω 0 ≤ m := hω
    show z 0 ω 0 ≤ n
    exact h1.trans (Nat.cast_le.2 hmn)
  rw [← setLIntegral_univ, ← hU, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  simp only [hF.lintegral_zeroInd_restrict, iSup_const]

theorem measurable_zeroInd : Measurable (Function.uncurry (zeroInd z τ)) := by
  have hz : Measurable (Function.uncurry fun (u : ℝ≥0) ω => z u ω 0) :=
    measurable_uncurry_of_continuous_of_measurable hF.cont fun u =>
      (continuous_apply 0).measurable.comp ((hF.csm.adapted u).mono (𝓖.le u)).measurable
  have h1 : Measurable fun p : Ω × ℝ => z p.2.toNNReal p.1 0 :=
    hz.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hs : MeasurableSet {p : Ω × ℝ | z p.2.toNNReal p.1 0 = 0 ∧
      (p.2.toNNReal : WithTop ℝ≥0) ≤ τ p.1} :=
    (measurableSet_eq_fun h1 measurable_const).inter
      (measurableSet_le (by fun_prop) (hF.meas.comp measurable_fst))
  show Measurable fun p : Ω × ℝ => zeroInd z τ p.1 p.2
  unfold zeroInd
  exact Measurable.ite hs measurable_const measurable_const

/-- Tonelli: for a.e. time `u ∈ (0, T]`, a.s. `¬(z_u = 0 ∧ u ≤ τ)`. -/
theorem ae_zeroInd [IsProbabilityMeasure Q] (T : ℝ≥0) :
    ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) T)), ∀ᵐ ω ∂Q, zeroInd z τ ω u = 0 := by
  have h := hF.lintegral_zeroInd T
  rw [lintegral_lintegral_swap hF.measurable_zeroInd.aemeasurable] at h
  have hm : Measurable fun u => ∫⁻ ω, zeroInd z τ ω u ∂Q :=
    hF.measurable_zeroInd.lintegral_prod_left'
  filter_upwards [(lintegral_eq_zero_iff hm).1 h] with u hu
  exact (lintegral_eq_zero_iff (hF.measurable_zeroInd.comp
    (measurable_id.prodMk measurable_const))).1 hu

/-- **Good times near `0`**: for every `ε > 0` some `s ∈ (0, ε)` has `z_s > 0` a.s. on
`{s ≤ τ}`. -/
theorem exists_good_time [IsProbabilityMeasure Q] {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ) < ε ∧ ∀ᵐ ω ∂Q, (s : WithTop ℝ≥0) ≤ τ ω → 0 < z s ω 0 := by
  have hsub : Ioo (0 : ℝ) (min ε 1) ⊆ Ioc (0 : ℝ) ((1 : ℝ≥0) : ℝ) := fun u hu =>
    ⟨hu.1, by rw [NNReal.coe_one]; exact hu.2.le.trans (min_le_right _ _)⟩
  have h' := ae_restrict_of_ae_restrict_of_subset hsub (hF.ae_zeroInd 1)
  have hpos : volume (Ioo (0 : ℝ) (min ε 1)) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.2 (lt_min hε one_pos)).ne'
  obtain ⟨u, hu, hP⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos h'
  refine ⟨u.toNNReal, Real.toNNReal_pos.2 hu.1, ?_, ?_⟩
  · rw [Real.coe_toNNReal _ hu.1.le]; exact hu.2.trans_le (min_le_left _ _)
  · filter_upwards [hP] with ω hω hτ
    unfold zeroInd at hω
    rcases (hF.nonneg u.toNNReal ω).lt_or_eq with h | h
    · exact h
    · rw [ite_eq_left ⟨h.symm, hτ⟩] at hω; exact absurd hω one_ne_zero

end IsEntranceFace

end BlockBand.Transmission.DualEntrance
