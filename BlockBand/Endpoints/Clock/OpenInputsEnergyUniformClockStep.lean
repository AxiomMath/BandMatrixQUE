module

public import BlockBand.Endpoints.Clock.OpenInputsEnergyUniformStep

/-!
# The open-inputs lemma, energy-uniform: the conditional clock-moment step

`OpenInputsProof.ingredients`, `crude_bound`, `main_moment` and `clockStep_of` (`ClockStepBound`)
fix `E` first. Their inputs are already uniform:
* `OnePortWeighted` (proved from `WeightedLayerContract` by `onePortWeighted_of`) is uniform in
  `E ∈ bulkInterval κ` (the fixed-energy proof uses `κ = 2 - |E|`; here `κ` is the given one);
* `GaussianAbsorptionContract` is uniform in every real `E` and every `z` with `Im z ≥ η₀`,
  `|z| ≤ M`; we use `η₀ = etaLow b κ`, `M = 3`;
* the scalar step is `delta_next_unif`.

The proofs below are the fixed-energy ones with `E` introduced after the constants.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof

variable {b κ : ℝ}

/-- **The fresh ingredients at order `P`, uniformly on `bulkInterval κ`**
(`OpenInputsProof.ingredients`). -/
theorem ingredients_unif (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract)
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) {P : ℕ} (hP : 1 ≤ P) :
    ∃ (Cp CG : ℝ) (W₀ : ℕ), 0 ≤ Cp ∧ 0 ≤ CG ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef →
        eLpNorm (fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b)
            (P : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal (Cp * clockU Y / Real.sqrt W) ∧
        eLpNorm (clockT b E X Y) (P : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal (Cp * clockU Y) ∧
        eLpNorm (cInj b E X) (P : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal CG := by
  obtain ⟨-, hnoise⟩ := hW1 b hb0 hb1 κ hκ
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  obtain ⟨Cp, W₂, hCp⟩ := hnoise P hP1
  obtain ⟨ε₁, CG, hε₁, hCG, hGAb⟩ := hGA b hb0 hb1 (etaLow b κ) 3 (etaLow_pos hb1 hκ hκ4)
  refine ⟨max Cp 0, CG ^ 2, max W₂ ⌈2 * P / ε₁⌉₊, le_max_right _ _, by positivity, ?_⟩
  intro W hW hW₀ E hEκ X hX Y hY
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨h1, h2⟩ := hCp W hW ((le_max_left _ _).trans hW₀) X hX E hEκ Y hY
  have hu := clockU_nonneg hY
  rw [eLpNorm_nat_eq] at h1 h2
  refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), h2.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have : 0 ≤ clockU Y / Real.sqrt W := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu
  have hpW : (2 * P : ℝ) ≤ ε₁ * W := by
    have h := (Nat.le_ceil (2 * P / ε₁)).trans (by exact_mod_cast (le_max_right _ _).trans hW₀ :
      ((⌈2 * P / ε₁⌉₊ : ℕ) : ℝ) ≤ W)
    rw [div_le_iff₀ hε₁] at h; linarith
  have hG := (hGAb W hW .oneBlockOnePort (ClockMixingAlg.physEmbed X)
    (ClockMixingAlg.physEmbed_isHermitian hX) E (boundaryZ b E) (etaLow_le_im hb1 hκ hEκ)
    (norm_boundaryZ_le3 hb0 hb1 hκ hEκ)).2 (2 * P) (by linarith) hpW
  have hGm := (meas_freshLayer' (b := b) (E := E) X).aestronglyMeasurable (μ := freshLaw W b)
  have hG' : eLpNorm (fun ω => freshLayer b E X ω) (P * ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal CG := by
    have e : (P : ℝ≥0∞) * ENNReal.ofReal 2 = ENNReal.ofReal (2 * P) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, mul_comm]
    rw [e, ← eLpNorm_norm]
    exacts [hG, hGm]
  calc eLpNorm (cInj b E X) (P : ℝ≥0∞) (freshLaw W b)
      ≤ eLpNorm (fun ω => ‖freshLayer b E X ω‖ ^ (2 : ℝ)) (P : ℝ≥0∞) (freshLaw W b) := by
        refine eLpNorm_mono_real (meas_cInj X).aestronglyMeasurable fun ω => ?_
        rw [Real.norm_of_nonneg (cInj_nonneg X ω), Real.rpow_two]
        exact cInj_le hW X ω
    _ = eLpNorm (fun ω => freshLayer b E X ω) (P * ENNReal.ofReal 2) (freshLaw W b) ^ (2 : ℝ) :=
        eLpNorm_norm_rpow _ hGm (by norm_num)
    _ ≤ ENNReal.ofReal CG ^ (2 : ℝ) := ENNReal.rpow_le_rpow hG' (by norm_num)
    _ = ENNReal.ofReal (CG ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hCG.le (by norm_num), Real.rpow_two]

/-- **The crude clause, uniformly on `bulkInterval κ`** (`OpenInputsProof.crude_bound`):
`E u₊^P ≤ C(u^P + 1)` for every Hermitian past. -/
theorem crude_bound_unif (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract)
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) {Kq : ℝ} (hKq : 0 ≤ Kq)
    {P : ℕ} (hP : 1 ≤ P) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
          ENNReal.ofReal (C * (clockU Y ^ P + 1)) := by
  obtain ⟨Cp, CG, W₀, hCp, hCG, hing⟩ := ingredients_unif hW1 hGA hb0 hb1 hκ hκ4 hP
  refine ⟨2 ^ P * ((Kq * CG) ^ P + Cp ^ P), W₀, by positivity, ?_⟩
  intro W hW hW₀ E hEκ X hX Y hY w hw hwK
  obtain ⟨-, ht, hc⟩ := hing W hW hW₀ E hEκ X hX Y hY
  have hu := clockU_nonneg hY
  have hP1 : (1 : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast hP
  have hsum : eLpNorm (nextClockU b E w X Y) (P : ℝ≥0∞) (freshLaw W b) ≤
      ENNReal.ofReal (Kq * CG + Cp * clockU Y) := by
    have e : nextClockU b E w X Y = (fun ω => w * cInj b E X ω) + clockT b E X Y :=
      funext fun ω => nextClockU_eq w X Y ω
    rw [e]
    refine (eLpNorm_add_le hP1).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (eLpNorm_inj_le hw hwK hc) ht
  have h := lintegral_ofReal_pow_le hP (meas_nextClockU w X Y).aestronglyMeasurable
    (by positivity) hsum
  have e2 : ∀ ω, ‖nextClockU b E w X Y ω‖ = nextClockU b E w X Y ω := fun ω =>
    Real.norm_of_nonneg (nextClockU_nonneg hw X hY ω)
  simp only [e2] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 := add_pow_le_two_pow (by positivity : 0 ≤ Kq * CG) (by positivity : 0 ≤ Cp * clockU Y) P
  rw [mul_pow Cp] at h1
  have h2 : 2 ^ P * ((Kq * CG) ^ P + Cp ^ P * clockU Y ^ P) ≤
      2 ^ P * ((Kq * CG) ^ P + Cp ^ P) * (clockU Y ^ P + 1) := by
    have : 0 ≤ (Kq * CG) ^ P * clockU Y ^ P := by positivity
    have : 0 ≤ Cp ^ P := by positivity
    have : (0 : ℝ) ≤ 2 ^ P := by positivity
    nlinarith
  linarith

/-- **The main moment bound, uniformly on `bulkInterval κ`** (`OpenInputsProof.main_moment`):
on the scalar domain, `E u₊^{n+2} ≤ (1 + Aδ₀ + A/W) u^{n+2} + B(u^{n+1} + 1)`. -/
theorem main_moment_unif (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract)
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) {Kq : ℝ} (hKq : 0 ≤ Kq)
    (n : ℕ) :
    ∃ (dstar A B : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 ≤ A ∧ 0 ≤ B ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ dstar →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ (n + 2)) ∂freshLaw W b ≤
          ENNReal.ofReal ((1 + A * jetDistance0 b E X + A / W) * clockU Y ^ (n + 2) +
            B * (clockU Y ^ (n + 1) + 1)) := by
  obtain ⟨⟨dstar₀, C₁, W₁, hd₀, hmean⟩, -⟩ := hW1 b hb0 hb1 κ hκ
  obtain ⟨Cp, CG, W₂, hCp, hCG, hing⟩ := ingredients_unif hW1 hGA hb0 hb1 hκ hκ4
    (P := n + 2) (by omega)
  have hC₁0 : 0 ≤ max C₁ 0 := le_max_right _ _
  refine ⟨min dstar₀ (1 / (2 * max C₁ 0 + 1)),
    ((n : ℝ) + 2) * 2 ^ (n + 2) * max C₁ 0 +
      2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)),
    ((n : ℝ) + 2) * 2 ^ (n + 1) * (Kq * CG) +
      2 ^ (n + 2) * (2 ^ (n + 1) * (Kq * CG) ^ 2 + 2 ^ (n + 2) * (Kq * CG) ^ (n + 2)),
    max (max W₁ W₂) (⌈2 * max C₁ 0⌉₊ + 1), lt_min hd₀ (by positivity), by positivity,
    by positivity, ?_⟩
  intro W hW hW₀ E hEκ X hX hδ Y hY w hw hwK
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hW2' : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hW3 : 2 * max C₁ 0 + 1 ≤ (W : ℝ) := by
    have h := Nat.le_ceil (2 * max C₁ 0)
    have h2 : ((⌈2 * max C₁ 0⌉₊ + 1 : ℕ) : ℝ) ≤ W := by
      exact_mod_cast (le_max_right _ _).trans hW₀
    push_cast at h h2; linarith
  have hWr1 : (1 : ℝ) ≤ W := by linarith
  have hWr : (0 : ℝ) < W := by linarith
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδd : jetDistance0 b E X ≤ dstar₀ := hδ.trans (min_le_left _ _)
  have hδs : jetDistance0 b E X ≤ 1 / (2 * max C₁ 0 + 1) := hδ.trans (min_le_right _ _)
  obtain ⟨hint, hm⟩ := hmean W hW hW1' X hX E hEκ hδd Y hY
  obtain ⟨hξB, -, hιB⟩ := hing W hW hW2' E hEκ X hX Y hY
  have hu := clockU_nonneg hY
  have hm0 : 0 ≤ ∫ ω, clockT b E X Y ω ∂freshLaw W b :=
    integral_nonneg fun ω => clockT_nonneg X hY ω
  have hm' : ∫ ω, clockT b E X Y ω ∂freshLaw W b ≤
      (1 + max C₁ 0 * jetDistance0 b E X + max C₁ 0 / (W : ℝ) ^ 2) * clockU Y := by
    refine hm.trans (mul_le_mul_of_nonneg_right ?_ hu)
    have h1 : C₁ * jetDistance0 b E X ≤ max C₁ 0 * jetDistance0 b E X :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
    have h2 : C₁ / (W : ℝ) ^ 2 ≤ max C₁ 0 / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  have hsmall : max C₁ 0 * jetDistance0 b E X + max C₁ 0 / (W : ℝ) ^ 2 ≤ 1 := by
    have h1 : max C₁ 0 * jetDistance0 b E X ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hδs
      nlinarith
    have h2 : max C₁ 0 / (W : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hξ0 : ∫ ω, (clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b) ∂freshLaw W b
      = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]; simp
  have hmb := moment_bound n hm0
    (ξ := fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b)
    (ι := fun ω => w * cInj b E X ω) ((meas_clockT X Y).sub measurable_const).aestronglyMeasurable
    (measurable_const.mul (meas_cInj X)).aestronglyMeasurable hξ0
    (fun ω => by
      have := clockT_nonneg (b := b) (E := E) X hY ω
      have := mul_nonneg hw (cInj_nonneg (b := b) (E := E) X ω)
      linarith)
    (by positivity : 0 ≤ Cp * clockU Y / Real.sqrt W) (by positivity : 0 ≤ Kq * CG)
    hξB (eLpNorm_inj_le hw hwK hιB)
  have hpt : ∀ ω, (∫ ω', clockT b E X Y ω' ∂freshLaw W b) +
      ((clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b) + w * cInj b E X ω) =
        nextClockU b E w X Y ω := by
    intro ω; rw [nextClockU_eq]; ring
  simp only [hpt] at hmb
  refine hmb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact main_algebra n hu hm0 hm' hC₁0 hδ0 hWr1 hsmall hCp (by positivity)

/-- **The weighted clause of `ClockStepBound`, uniformly on `bulkInterval κ`**
(`OpenInputsProof.clockStep_of`, second clause). -/
theorem clockStep_weighted_unif (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4)
    {Kq : ℝ} (hKq : 0 ≤ Kq) {P : ℕ} (hP : 2 ≤ P) :
    ∃ (r₁ K C : ℝ) (W₀ : ℕ), 0 < r₁ ∧ 0 ≤ K ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ r₁ →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
            nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
          ENNReal.ofReal ((1 + C / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
            C * (clockU Y ^ (P - 1) + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 2 := ⟨P - 2, by omega⟩
  obtain ⟨r₀, q, C₂, Cn, Wd, hr₀, hq0, hq1, hC₂, hCn, hdel⟩ :=
    delta_next_unif hGA hTM hb0 hb1 hκ hκ4
  obtain ⟨dstar, A, B, Wm, hd, hA, hB, hmain⟩ := main_moment_unif hW1 hGA hb0 hb1 hκ hκ4 hKq n
  obtain ⟨Cc, Wc, hCc, hcrude⟩ :=
    crude_bound_unif hW1 hGA hb0 hb1 hκ hκ4 hKq (P := 2 * n + 4) (by omega)
  have h1q : 0 < 1 - q := by linarith
  set K := 2 * A / (1 - q) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : K = K * q + 2 * A := by rw [hKdef]; field_simp; ring
  refine ⟨min (min r₀ dstar) (min 1 (1 / (K + 1))), K,
    2 * A + K * C₂ * (1 + 2 * A) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B, max (max Wd Wm) Wc,
    lt_min (lt_min hr₀ hd) (lt_min one_pos (by positivity)), hK0, ?_⟩
  intro W hW hW₀ E hEκ X hX hδ Y hY w hw hwK
  have hWd : Wd ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hWm : Wm ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hWc : Wc ≤ W := (le_max_right _ _).trans hW₀
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set δ := jetDistance0 b E X with hδdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδr : δ ≤ r₀ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδd : δ ≤ dstar := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδK : δ ≤ 1 / (K + 1) := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKqδ : K * q * δ ≤ 1 := by
    have h1 : K * q * δ ≤ K * δ := by
      have := mul_le_mul_of_nonneg_left (by linarith : q ≤ 1) hK0
      exact mul_le_mul_of_nonneg_right (by linarith) hδ0
    rw [le_div_iff₀ (by positivity)] at hδK
    nlinarith
  obtain ⟨hstep, hN⟩ := hdel W hW hWd E hEκ X hX
  have hstep' := hstep hδr
  have hM := hmain W hW hWm E hEκ X hX hδd Y hY w hw hwK
  have hCr := hcrude W hW hWc E hEκ X hX Y hY w hw hwK
  have hu := clockU_nonneg hY
  set U := clockU Y ^ (n + 2) with hU
  have hU0 : 0 ≤ U := by positivity
  set lam := (W : ℝ) * (U + 1) with hlam
  have hlam0 : 0 < lam := by positivity
  set c₀ := 1 + K * q * δ + K * C₂ / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set c₁ := K * lam / 2 with hc₁
  set c₂ := K / (2 * lam) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set V : OneEndedLayer W → ℝ := fun ω => nextClockU b E w X Y ω ^ (n + 2) with hV
  have hV0 : ∀ ω, 0 ≤ V ω := fun ω => pow_nonneg (nextClockU_nonneg hw X hY ω) _
  have hV2 : ∀ ω, V ω ^ 2 = nextClockU b E w X Y ω ^ (2 * n + 4) := fun ω => by
    rw [hV, ← pow_mul]; ring_nf
  have hpt : ∀ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) * V ω) ≤
      ENNReal.ofReal c₀ * ENNReal.ofReal (V ω) +
        ENNReal.ofReal c₁ * ENNReal.ofReal (portNoise b E X ω ^ 2) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (nextClockU b E w X Y ω ^ (2 * n + 4)) := by
    intro ω
    rw [← ENNReal.ofReal_mul hc₀0, ← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
      ← ENNReal.ofReal_add (mul_nonneg hc₀0 (hV0 ω)) (mul_nonneg hc₁0 (sq_nonneg _)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hc₀0 (hV0 ω)) (mul_nonneg hc₁0 (sq_nonneg _)))
        (mul_nonneg hc₂0 (pow_nonneg (nextClockU_nonneg hw X hY ω) _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := hstep' ω
    have hN0 : 0 ≤ portNoise b E X ω := norm_nonneg _
    have h1 : (1 + K * jetDistance0 b E (freshSchur E X ω)) * V ω ≤
        (1 + K * (q * δ + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω)) * V ω := by
      refine mul_le_mul_of_nonneg_right ?_ (hV0 ω)
      have := mul_le_mul_of_nonneg_left hs hK0
      linarith
    have h2 := two_mul_le_weighted (N := portNoise b E X ω) (V := V ω) hlam0
    have h3 : K * (portNoise b E X ω * V ω) ≤
        K * (lam / 2 * portNoise b E X ω ^ 2 + 1 / (2 * lam) * V ω ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have e1 : (1 + K * (q * δ + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω)) * V ω =
        c₀ * V ω + K * (portNoise b E X ω * V ω) := by rw [hc₀]; ring
    have e2 : K * (lam / 2 * portNoise b E X ω ^ 2 + 1 / (2 * lam) * V ω ^ 2) =
        c₁ * portNoise b E X ω ^ 2 + c₂ * V ω ^ 2 := by rw [hc₁, hc₂]; ring
    rw [← hV2 ω]
    linarith
  have hmV : Measurable (fun ω => ENNReal.ofReal (V ω)) :=
    ENNReal.measurable_ofReal.comp ((meas_nextClockU w X Y).pow_const _)
  have hmN : Measurable (fun ω => ENNReal.ofReal (portNoise b E X ω ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((meas_portNoise b E X).pow_const _)
  calc ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
          nextClockU b E w X Y ω ^ (n + 2)) ∂freshLaw W b
      ≤ ∫⁻ ω, (ENNReal.ofReal c₀ * ENNReal.ofReal (V ω) +
          ENNReal.ofReal c₁ * ENNReal.ofReal (portNoise b E X ω ^ 2) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (nextClockU b E w X Y ω ^ (2 * n + 4)))
          ∂freshLaw W b := lintegral_mono hpt
    _ = ENNReal.ofReal c₀ * ∫⁻ ω, ENNReal.ofReal (V ω) ∂freshLaw W b +
          ENNReal.ofReal c₁ * ∫⁻ ω, ENNReal.ofReal (portNoise b E X ω ^ 2) ∂freshLaw W b +
          ENNReal.ofReal c₂ * ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ (2 * n + 4))
            ∂freshLaw W b := by
        have hm1 : Measurable (fun ω => ENNReal.ofReal c₀ * ENNReal.ofReal (V ω) +
            ENNReal.ofReal c₁ * ENNReal.ofReal (portNoise b E X ω ^ 2)) :=
          (hmV.const_mul _).add (hmN.const_mul _)
        have hm2 : Measurable (fun ω => ENNReal.ofReal c₀ * ENNReal.ofReal (V ω)) :=
          hmV.const_mul _
        rw [lintegral_add_left hm1, lintegral_add_left hm2, lintegral_const_mul _ hmV,
          lintegral_const_mul _ hmN, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c₀ * ENNReal.ofReal ((1 + A * δ + A / W) * U +
            B * (clockU Y ^ (n + 1) + 1)) +
          ENNReal.ofReal c₁ * ENNReal.ofReal (Cn / (W : ℝ) ^ 2) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (Cc * (clockU Y ^ (2 * n + 4) + 1)) := by
        gcongr
    _ = ENNReal.ofReal (c₀ * ((1 + A * δ + A / W) * U + B * (clockU Y ^ (n + 1) + 1)) +
          c₁ * (Cn / (W : ℝ) ^ 2) + c₂ * (Cc * (clockU Y ^ (2 * n + 4) + 1))) := by
        rw [← ENNReal.ofReal_mul hc₀0, ← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hU2 : clockU Y ^ (2 * n + 4) = U ^ 2 := by rw [hU, ← pow_mul]; ring_nf
        have hV1 : 1 ≤ clockU Y ^ (n + 1) + 1 := by have := pow_nonneg hu (n + 1); linarith
        have h := weighted_algebra (U2 := clockU Y ^ (2 * n + 4)) (Cn := Cn) (Cc := Cc) hU0 hV1
          hU2 hδ0 hδ1 hKqδ hq0 hK0 hK hA hB hW1r hC₂ hCn hCc
        rw [hc₀, hc₁, hc₂, hlam]
        exact h

end MovingEnergy

end BlockBand.Endpoints.Clock
