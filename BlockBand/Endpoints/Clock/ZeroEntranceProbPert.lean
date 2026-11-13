module

public import BlockBand.Endpoints.Clock.ZeroEntranceProbPertAlg

/-!
# The zero-entrance lemma: perturbation by a deterministic initial matrix

Law: `oneEndedLaw W b J`; the two chains `X_J^D` and `X_J^0` are driven by the same layers.
`QBound κ J`: for every domain `Im ζ ≥ η`, `|ζ| ≤ M` there are `K, W₀` with
`E ‖(ζ - X_J^D)⁻¹ - (ζ - X_J^0)⁻¹‖ ≤ K ‖D‖` for `W ≥ W₀`, `(b, e)` in the compact set, every
Hermitian `D` and `ζ` in the domain. Induction on `J`: by `resolvent_diff_step` (with the
intermediate port `ζ = i`) and conditioning on the past,
`E T_{J+1}(ζ') ≤ (sup_past E_layer[‖𝒢_X‖ a ‖𝒢_Y‖ a]) · E T_J(i)`, and the layer factor is bounded
by `‖𝒢_X‖⁴ + ‖𝒢_Y‖⁴ + 27(3⁴ + ‖A‖⁴ + ‖B‖⁴)`, whose mean is bounded by the b-uniform absorption
moments (`AbsorptionUniform`, `p = 4 ≤ ε₁ W`) and the Gaussian norm moments
(`gueBlock_lintegral_pow_le`, `bondBlock_lintegral_pow_le`). No real cavity inverse is
estimated. Consequence `pertBound_all`: `|E h_J^D(ζ) - E h_J^0(ζ)| ≤ C ‖D‖`.
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

variable {W : ℕ}

/-- `‖(ζ - X)⁻¹ - (ζ - Y)⁻¹‖`. -/
def tdiff (ζ : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖(ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ - (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - Y)⁻¹‖

theorem measurable_tdiff (ζ : ℂ) :
    Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × Matrix (Fin W) (Fin W) ℂ => tdiff ζ q.1 q.2) := by
  unfold tdiff
  refine Measurable.norm (Measurable.sub ?_ ?_)
  · exact BlockBand.Layers.measurable_matrix_inv.comp (measurable_const.sub measurable_fst)
  · exact BlockBand.Layers.measurable_matrix_inv.comp (measurable_const.sub measurable_snd)

/-- `‖(z - X)⁻¹‖ ≤ (Im z)⁻¹` for Hermitian `X`. -/
theorem norm_resolvent_le' {z : ℂ} (hz : 0 < z.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) : ‖(z • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹‖ ≤ z.im⁻¹ := by
  have h := BlockBand.Layers.lct_norm_shifted_inv_le (-X) hX.neg (fun _ => -z) hz
    (fun _ => by simp)
  have he : -X - diagonal (fun _ : Fin W => -z) = z • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
    rw [← smul_one_eq_diagonal, neg_smul]; abel
  rwa [he] at h

theorem isUnit_resolvent {z : ℂ} (hz : 0 < z.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det := by
  have h := BlockBand.Layers.cmp_det_ne_zero (-X) hX.neg (fun _ => -z) (fun _ => by simp [hz])
  have he : -X - diagonal (fun _ : Fin W => -z) = z • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
    rw [← smul_one_eq_diagonal, neg_smul]; abel
  rw [he] at h
  exact isUnit_iff_ne_zero.mpr h

theorem norm_nrt_sub_le (hW : 0 < W) (ζ : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    ‖normalizedResolventTrace X ζ - normalizedResolventTrace Y ζ‖ ≤ tdiff ζ X Y := by
  unfold normalizedResolventTrace tdiff
  rw [← mul_sub, ← Matrix.trace_sub]
  set N := (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ - (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - Y)⁻¹
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖N.trace‖ ≤ W * ‖N‖ := by
    unfold Matrix.trace
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖N.diag i‖ ≤ ∑ _i : Fin W, ‖N‖ :=
          Finset.sum_le_sum fun i _ => BlockBand.Layers.tfl_entry_le N i i
      _ = W * ‖N‖ := by simp
  calc (W : ℝ)⁻¹ * ‖N.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖N‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖N‖ := by field_simp

/-- The one-layer factor `‖𝒢_X(ζ')‖ a ‖𝒢_Y(ζ')‖ a`, `a = |i| + |e| + ‖A‖ + ‖B‖`. -/
def layerFactor (e : ℝ) (ζ' : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) (y : OneEndedLayer W) : ℝ :=
  (‖layerResolvent .oneBlockOnePort e ζ' (cavityLift X) y‖ *
      (‖Complex.I‖ + |e| + ‖y.1 0‖ + ‖y.2 0 0‖)) *
    (‖layerResolvent .oneBlockOnePort e ζ' (cavityLift Y) y‖ *
      (‖Complex.I‖ + |e| + ‖y.1 0‖ + ‖y.2 0 0‖))

/-- **Pathwise step**: for Hermitian old inputs and a layer with Hermitian block and invertible
top blocks, `T_{+}(ζ') ≤ layerFactor · T(i)`. -/
theorem tdiff_step (e : ℝ) {ζ' : ℂ} (hz : 0 < ζ'.im) {X Y : Matrix (Fin W) (Fin W) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) {y : OneEndedLayer W}
    (hA : ∀ j, (y.1 j).IsHermitian)
    (hPX : IsUnit (Internal.Contracts.Layers.blockDiag y.1 - (e : ℂ) • 1 - cavityLift X).det)
    (hPY : IsUnit (Internal.Contracts.Layers.blockDiag y.1 - (e : ℂ) • 1 - cavityLift Y).det) :
    tdiff ζ' (freshSchur e X y) (freshSchur e Y y) ≤ layerFactor e ζ' X Y y * tdiff Complex.I X Y := by
  rw [isUnit_top_iff] at hPX hPY
  have hHX := CavityMeanProb.freshSchur_isHermitian e hX y hA
  have hHY := CavityMeanProb.freshSchur_isHermitian e hY y hA
  have hSX := isUnit_resolvent hz hHX
  have hSY := isUnit_resolvent hz hHY
  rw [freshSchur_eq_plain] at hSX hSY
  have hRX := isUnit_resolvent (z := Complex.I) (by simp) hX
  have hRY := isUnit_resolvent (z := Complex.I) (by simp) hY
  have h := resolvent_diff_step (y.1 0) (y.2 0 0) X Y e Complex.I ζ' hPX hPY hSX hSY hRX hRY
  unfold tdiff layerFactor
  rw [freshSchur_eq_plain, freshSchur_eq_plain, layerResolvent_norm_eq, layerResolvent_norm_eq]
  unfold plainLayer topP
  calc _ ≤ _ := h
    _ = _ := by ring

theorem measurable_layerFactor (e : ℝ) (ζ' : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (layerFactor e ζ' X Y) := by
  have hG : ∀ Z : Matrix (Fin W) (Fin W) ℂ, Measurable (fun y : OneEndedLayer W =>
      ‖layerResolvent .oneBlockOnePort e ζ' (cavityLift Z) y‖) := fun Z =>
    (BlockBand.Layers.measurable_matrix_inv.comp
      (BlockBand.Layers.measurable_layerMatrix .oneBlockOnePort e ζ' (cavityLift Z))).norm
  have hA : Measurable (fun y : OneEndedLayer W => ‖y.1 0‖) :=
    ((measurable_pi_apply 0).comp measurable_fst).norm
  have hB : Measurable (fun y : OneEndedLayer W => ‖y.2 0 0‖) :=
    ((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd)).norm
  have ha : Measurable (fun y : OneEndedLayer W => ‖Complex.I‖ + |e| + ‖y.1 0‖ + ‖y.2 0 0‖) :=
    ((measurable_const.add hA).add hB)
  exact ((hG X).mul ha).mul ((hG Y).mul ha)

theorem real_amgm {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x * z) * (y * z) ≤ x ^ 4 + y ^ 4 + z ^ 4 := by
  have h1 : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith [sq_nonneg (x - y)]
  have h2 : (x * y) * z ^ 2 ≤ ((x * y) ^ 2 + (z ^ 2) ^ 2) / 2 := by
    nlinarith [sq_nonneg (x * y - z ^ 2)]
  have h3 : (x * y) ^ 2 ≤ (x ^ 4 + y ^ 4) / 2 := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have h4 : 0 ≤ x * y := mul_nonneg hx hy
  nlinarith [sq_nonneg z, pow_two_nonneg (z ^ 2), pow_two_nonneg x, pow_two_nonneg y]

theorem real_pow4_sum (u v w : ℝ) :
    (u + v + w) ^ 4 ≤ 27 * (u ^ 4 + v ^ 4 + w ^ 4) := by
  have h1 : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w)]
  have h2 : (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 ≤ 3 * (u ^ 4 + v ^ 4 + w ^ 4) := by
    nlinarith [sq_nonneg (u ^ 2 - v ^ 2), sq_nonneg (v ^ 2 - w ^ 2), sq_nonneg (u ^ 2 - w ^ 2)]
  have h0 : 0 ≤ (u + v + w) ^ 2 := sq_nonneg _
  calc (u + v + w) ^ 4 = ((u + v + w) ^ 2) ^ 2 := by ring
    _ ≤ (3 * (u ^ 2 + v ^ 2 + w ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 9 * (u ^ 2 + v ^ 2 + w ^ 2) ^ 2 := by ring
    _ ≤ 9 * (3 * (u ^ 4 + v ^ 4 + w ^ 4)) := by gcongr
    _ = 27 * (u ^ 4 + v ^ 4 + w ^ 4) := by ring

theorem layerFactor_le (e : ℝ) (he : |e| ≤ 2) (ζ' : ℂ) (X Y : Matrix (Fin W) (Fin W) ℂ)
    (y : OneEndedLayer W) :
    layerFactor e ζ' X Y y ≤ ‖layerResolvent .oneBlockOnePort e ζ' (cavityLift X) y‖ ^ 4 +
      ‖layerResolvent .oneBlockOnePort e ζ' (cavityLift Y) y‖ ^ 4 +
      27 * (3 ^ 4 + ‖y.1 0‖ ^ 4 + ‖y.2 0 0‖ ^ 4) := by
  unfold layerFactor
  refine (real_amgm (norm_nonneg _) (norm_nonneg _)).trans ?_
  have ha : ‖Complex.I‖ + |e| + ‖y.1 0‖ + ‖y.2 0 0‖ ≤ 3 + ‖y.1 0‖ + ‖y.2 0 0‖ := by
    rw [Complex.norm_I]; linarith
  have h0 : 0 ≤ ‖Complex.I‖ + |e| + ‖y.1 0‖ + ‖y.2 0 0‖ := by positivity
  have := real_pow4_sum 3 ‖y.1 0‖ ‖y.2 0 0‖
  have h4 := pow_le_pow_left₀ h0 ha 4
  linarith

theorem lintegral_rpow_four_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ) {C : ℝ}
    (h : eLpNorm g (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (g ω ^ 4) ∂μ ≤ ENNReal.ofReal (C ^ 4) := by
  have h4 : ENNReal.ofReal 4 ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h4 ENNReal.ofReal_ne_top hg,
    ENNReal.toReal_ofReal (by norm_num)] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 4)
  rw [← ENNReal.rpow_mul, show (1 / (4 : ℝ)) * 4 = 1 by norm_num, ENNReal.rpow_one] at h'
  have heq : ∀ ω, ENNReal.ofReal (g ω ^ 4) ≤ ‖g ω‖ₑ ^ (4 : ℝ) := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow]
    exact le_abs_self _
  refine (lintegral_mono heq).trans (h'.trans ?_)
  rcases le_or_gt 0 C with hC | hC
  · rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  · rw [ENNReal.ofReal_of_nonpos hC.le, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le

/-- The mean of the layer factor is bounded uniformly in the old inputs. -/
theorem layerFactor_lintegral (hAbs : AbsorptionUniform) {κ : ℝ} (hκ : 0 < κ) {η M : ℝ}
    (hη : 0 < η) : ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W → ∀ b : ℝ, κ ≤ b →
      κ ≤ 1 - 2 * b → ∀ e : ℝ, |e| ≤ 2 → ∀ X Y : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        Y.IsHermitian → ∀ ζ' : ℂ, η ≤ ζ'.im → ‖ζ'‖ ≤ M →
          ∫⁻ y, ENNReal.ofReal (layerFactor e ζ' X Y y) ∂freshLaw W b ≤ ENNReal.ofReal K := by
  obtain ⟨ε₁, CG, hε₁, hCG, habs⟩ := hAbs κ hκ η M hη
  obtain ⟨CA, WA, hCA, hgue⟩ := gueBlock_lintegral_pow_le 4
  obtain ⟨CB, WB, hCB, hbond⟩ := bondBlock_lintegral_pow_le 4
  refine ⟨CG ^ 4 + CG ^ 4 + 27 * 3 ^ 4 + 27 * CA + 27 * CB, max (max WA WB) ⌈4 / ε₁⌉₊,
    by positivity, ?_⟩
  intro W hW hW0 b hb hc e he X Y hX hY ζ' hz hzM
  have hWA : WA ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWB : WB ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW4 : (4 : ℝ) ≤ ε₁ * W := by
    have h1 : (⌈4 / ε₁⌉₊ : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW
    have h2 : 4 / ε₁ ≤ W := (Nat.le_ceil _).trans h1
    rw [div_le_iff₀ hε₁] at h2; linarith
  have hb0 : 0 ≤ b := hκ.le.trans hb
  have hb1 : b < 1 / 2 := by linarith
  set gX := fun y : OneEndedLayer W => ‖layerResolvent .oneBlockOnePort e ζ' (cavityLift X) y‖
  set gY := fun y : OneEndedLayer W => ‖layerResolvent .oneBlockOnePort e ζ' (cavityLift Y) y‖
  have hgm : ∀ Z : Matrix (Fin W) (Fin W) ℂ, Measurable (fun y : OneEndedLayer W =>
      ‖layerResolvent .oneBlockOnePort e ζ' (cavityLift Z) y‖) := fun Z =>
    (BlockBand.Layers.measurable_matrix_inv.comp
      (BlockBand.Layers.measurable_layerMatrix .oneBlockOnePort e ζ' (cavityLift Z))).norm
  have hG4 : ∀ Z : Matrix (Fin W) (Fin W) ℂ, Z.IsHermitian →
      ∫⁻ y, ENNReal.ofReal (‖layerResolvent .oneBlockOnePort e ζ' (cavityLift Z) y‖ ^ 4)
        ∂freshLaw W b ≤ ENNReal.ofReal (CG ^ 4) := by
    intro Z hZ
    have h := (habs b hb hc W hW0 (cavityLift Z) (CavityMeanProb.cavityLift_isHermitian hZ) e ζ'
      hz hzM).2 4 (by norm_num) hW4
    exact lintegral_rpow_four_le (hgm Z).aestronglyMeasurable h
  have hA4 : ∫⁻ y, ‖(y.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 ∂freshLaw W b ≤ ENNReal.ofReal CA :=
    hgue W hWA b hb0 hb1
  have hB4 : ∫⁻ y, ‖(y.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 ∂freshLaw W b ≤
      ENNReal.ofReal CB := hbond W hWB b (hκ.trans_le hb) hb1
  have hpt : ∀ y : OneEndedLayer W, ENNReal.ofReal (layerFactor e ζ' X Y y) ≤
      ENNReal.ofReal (gX y ^ 4) + ENNReal.ofReal (gY y ^ 4) + ENNReal.ofReal (27 * 3 ^ 4) +
        27 * ‖(y.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 +
        27 * ‖(y.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 := by
    intro y
    have h := layerFactor_le e he ζ' X Y y
    have hA : (27 : ℝ≥0∞) * ‖(y.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 =
        ENNReal.ofReal (27 * ‖y.1 0‖ ^ 4) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      norm_num
    have hB : (27 : ℝ≥0∞) * ‖(y.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 =
        ENNReal.ofReal (27 * ‖y.2 0 0‖ ^ 4) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      norm_num
    rw [hA, hB, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    ring
  have hmA' : Measurable (fun y : OneEndedLayer W =>
      ‖(y.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4) :=
    (((measurable_pi_apply 0).comp measurable_fst).enorm).pow_const 4
  have hmB' : Measurable (fun y : OneEndedLayer W =>
      ‖(y.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4) :=
    (((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp
      measurable_snd)).enorm).pow_const 4
  have hmA : Measurable (fun y : OneEndedLayer W =>
      (27 : ℝ≥0∞) * ‖(y.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4) := measurable_const.mul hmA'
  have hmB : Measurable (fun y : OneEndedLayer W =>
      (27 : ℝ≥0∞) * ‖(y.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4) := measurable_const.mul hmB'
  have hmX : Measurable (fun y => ENNReal.ofReal (gX y ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((hgm X).pow_const 4)
  have hmY : Measurable (fun y => ENNReal.ofReal (gY y ^ 4)) :=
    ENNReal.measurable_ofReal.comp ((hgm Y).pow_const 4)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_right _ hmB, lintegral_add_right _ hmA, lintegral_add_right _ measurable_const,
    lintegral_add_right _ hmY, lintegral_const, measure_univ, mul_one, lintegral_const_mul _ hmA',
    lintegral_const_mul _ hmB']
  have e1 := hG4 X hX
  have e2 := hG4 Y hY
  calc ∫⁻ y, ENNReal.ofReal (gX y ^ 4) ∂freshLaw W b + ∫⁻ y, ENNReal.ofReal (gY y ^ 4) ∂freshLaw W b +
        ENNReal.ofReal (27 * 3 ^ 4) +
        27 * ∫⁻ y, ‖(y.1 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 ∂freshLaw W b +
        27 * ∫⁻ y, ‖(y.2 0 0 : Matrix (Fin W) (Fin W) ℂ)‖ₑ ^ 4 ∂freshLaw W b
      ≤ ENNReal.ofReal (CG ^ 4) + ENNReal.ofReal (CG ^ 4) + ENNReal.ofReal (27 * 3 ^ 4) +
          27 * ENNReal.ofReal CA + 27 * ENNReal.ofReal CB := by gcongr
    _ = ENNReal.ofReal (CG ^ 4 + CG ^ 4 + 27 * 3 ^ 4 + 27 * CA + 27 * CB) := by
        have h27 : (27 : ℝ≥0∞) = ENNReal.ofReal 27 := by norm_num
        rw [h27, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The expected resolvent difference after `J` layers. -/
def QBound (κ : ℝ) (J : ℕ) : Prop :=
  ∀ η M : ℝ, 0 < η → ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W → ∀ b e : ℝ,
    zeParam κ b e → ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ∀ ζ : ℂ, η ≤ ζ.im →
      ‖ζ‖ ≤ M → ∫⁻ ω, ENNReal.ofReal (tdiff ζ (oneEndedX e D J ω) (oneEndedX e 0 J ω))
        ∂oneEndedLaw W b J ≤ ENNReal.ofReal (K * ‖D‖)

theorem qBound_zero (κ : ℝ) : QBound κ 0 := by
  intro η M hη
  refine ⟨1 / η ^ 2, 0, by positivity, ?_⟩
  intro W _ hW b e hbe D hD ζ hz hzM
  have hz0 : 0 < ζ.im := hη.trans_le hz
  have hpt : ∀ ω : Fin 0 → OneEndedLayer W,
      tdiff ζ (oneEndedX e D 0 ω) (oneEndedX e 0 0 ω) ≤ 1 / η ^ 2 * ‖D‖ := by
    intro ω
    show tdiff ζ D 0 ≤ _
    unfold tdiff
    have hR := isUnit_resolvent hz0 hD
    have hR0 := isUnit_resolvent hz0 (Matrix.isHermitian_zero (n := Fin W))
    rw [inv_sub_inv hR hR0, sub_sub_sub_cancel_left]
    simp only [sub_zero]
    have h1 := norm_resolvent_le' hz0 hD
    have h2 := norm_resolvent_le' hz0 (Matrix.isHermitian_zero (n := Fin W))
    rw [sub_zero] at h2
    have hi : ζ.im⁻¹ ≤ 1 / η := by rw [← one_div]; exact one_div_le_one_div_of_le hη hz
    calc ‖(ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - D)⁻¹ * D * (ζ • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹‖
        ≤ ‖(ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - D)⁻¹‖ * ‖D‖ *
            ‖(ζ • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹‖ :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
            (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1 / η) * ‖D‖ * (1 / η) := by gcongr <;> linarith
      _ = 1 / η ^ 2 * ‖D‖ := by ring
  refine (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)).trans ?_
  rw [lintegral_const, measure_univ, mul_one]

theorem qBound_succ (hAbs : AbsorptionUniform) {κ : ℝ} (hκ : 0 < κ) {J : ℕ} (ih : QBound κ J) :
    QBound κ (J + 1) := by
  intro η M hη
  obtain ⟨KL, WL, hKL, hLF⟩ := layerFactor_lintegral hAbs hκ (M := M) hη
  obtain ⟨KJ, WJ, hKJ, hJ⟩ := ih 1 1 one_pos
  refine ⟨KL * KJ, max WL WJ, by positivity, ?_⟩
  intro W hW hW0 b e hbe D hD ζ hz hzM
  obtain ⟨hb0, hb1, -, -, -, he2, -⟩ := zeParam_facts hκ hbe
  have hz0 : 0 < ζ.im := hη.trans_le hz
  set P := oneEndedLaw W b J
  have hD0 : (0 : Matrix (Fin W) (Fin W) ℂ).IsHermitian := Matrix.isHermitian_zero
  set F : (Fin J → OneEndedLayer W) × OneEndedLayer W → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (tdiff ζ (freshSchur e (oneEndedX e D J q.1) q.2)
      (freshSchur e (oneEndedX e 0 J q.1) q.2)) with hFdef
  have hFm : Measurable F := by
    have hp1 : Measurable (fun q : (Fin J → OneEndedLayer W) × OneEndedLayer W =>
        (oneEndedX e D J q.1, q.2)) :=
      ((measurable_X e D J).comp measurable_fst).prodMk measurable_snd
    have hp2 : Measurable (fun q : (Fin J → OneEndedLayer W) × OneEndedLayer W =>
        (oneEndedX e 0 J q.1, q.2)) :=
      ((measurable_X e 0 J).comp measurable_fst).prodMk measurable_snd
    have h1 := (measurable_freshSchur_joint (W := W) e).comp hp1
    have h2 := (measurable_freshSchur_joint (W := W) e).comp hp2
    have h3 := ENNReal.measurable_ofReal.comp ((measurable_tdiff (W := W) ζ).comp (h1.prodMk h2))
    rw [hFdef]
    exact h3
  have hsplit : ∫⁻ ω, ENNReal.ofReal (tdiff ζ (oneEndedX e D (J + 1) ω) (oneEndedX e 0 (J + 1) ω))
      ∂oneEndedLaw W b (J + 1) = ∫⁻ x, ∫⁻ y, F (x, y) ∂freshLaw W b ∂P := by
    have hmp : MeasurePreserving (fun ω : Fin (J + 1) → OneEndedLayer W =>
        (Fin.init ω, ω (Fin.last J))) (oneEndedLaw W b (J + 1)) (P.prod (freshLaw W b)) :=
      measurePreserving_initLast (freshLaw W b) J
    rw [← lintegral_prod _ hFm.aemeasurable, ← hmp.lintegral_comp hFm]
    rfl
  rw [hsplit]
  have hin : ∀ᵐ x ∂P, ∫⁻ y, F (x, y) ∂freshLaw W b ≤
      ENNReal.ofReal (tdiff Complex.I (oneEndedX e D J x) (oneEndedX e 0 J x)) *
        ENNReal.ofReal KL := by
    filter_upwards [ae_X_isHermitian b e hD J, ae_X_isHermitian b e hD0 J] with x hx1 hx2
    have hae : ∀ᵐ y ∂freshLaw W b, F (x, y) ≤
        ENNReal.ofReal (tdiff Complex.I (oneEndedX e D J x) (oneEndedX e 0 J x)) *
          ENNReal.ofReal (layerFactor e ζ (oneEndedX e D J x) (oneEndedX e 0 J x) y) := by
      filter_upwards [BlockBand.Layers.lct_ae_blocks_isHermitian W b .oneBlockOnePort,
        BlockBand.Layers.srec_ae_isUnit_top hb1 .oneBlockOnePort e (cavityLift (oneEndedX e D J x)),
        BlockBand.Layers.srec_ae_isUnit_top hb1 .oneBlockOnePort e (cavityLift (oneEndedX e 0 J x))]
        with y hA hP1 hP2
      have h := tdiff_step e hz0 hx1 hx2 hA hP1 hP2
      rw [hFdef, ← ENNReal.ofReal_mul (by unfold tdiff; positivity)]
      refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
      ring
    refine (lintegral_mono_ae hae).trans ?_
    rw [lintegral_const_mul _ (measurable_layerFactor e ζ _ _).ennreal_ofReal]
    gcongr
    exact hLF W ((le_max_left _ _).trans hW) hW0 b hbe.1 hbe.2.1 e he2 _ _ hx1 hx2 ζ hz hzM
  refine (lintegral_mono_ae hin).trans ?_
  have hmT : Measurable (fun x : Fin J → OneEndedLayer W =>
      ENNReal.ofReal (tdiff Complex.I (oneEndedX e D J x) (oneEndedX e 0 J x))) := by
    have h := ((measurable_tdiff (W := W) Complex.I).comp
      ((measurable_X e D J).prodMk (measurable_X e 0 J))).ennreal_ofReal
    exact h
  rw [lintegral_mul_const _ hmT]
  have h1 := hJ W ((le_max_right _ _).trans hW) hW0 b e hbe D hD Complex.I (by simp) (by simp)
  calc (∫⁻ x, ENNReal.ofReal (tdiff Complex.I (oneEndedX e D J x) (oneEndedX e 0 J x)) ∂P) *
        ENNReal.ofReal KL ≤ ENNReal.ofReal (KJ * ‖D‖) * ENNReal.ofReal KL := by gcongr
    _ = ENNReal.ofReal (KL * KJ * ‖D‖) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf

theorem qBound_all (hAbs : AbsorptionUniform) {κ : ℝ} (hκ : 0 < κ) (J : ℕ) : QBound κ J := by
  induction J with
  | zero => exact qBound_zero κ
  | succ J ih => exact qBound_succ hAbs hκ ih

/-- **Perturbation of the mean by the initial matrix** (the zero-entrance lemma):
`|E h_J^D(ζ) - E h_J^0(ζ)| ≤ C ‖D‖`, uniformly on the domain and the compact parameter set. -/
theorem pertBound_all (hAbs : AbsorptionUniform) {κ : ℝ} (hκ : 0 < κ) (J : ℕ) {η M : ℝ}
    (hη : 0 < η) : ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W → ∀ b e : ℝ,
      zeParam κ b e → ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ∀ ζ : ℂ, η ≤ ζ.im →
        ‖ζ‖ ≤ M → ‖meanTrace b e D J ζ - meanTrace b e (0 : Matrix (Fin W) (Fin W) ℂ) J ζ‖ ≤
          C * ‖D‖ := by
  obtain ⟨K, W₀, hK, hQ⟩ := qBound_all hAbs hκ J η M hη
  refine ⟨K, W₀, hK, ?_⟩
  intro W hW hW0 b e hbe D hD ζ hz hzM
  have hz0 : 0 < ζ.im := hη.trans_le hz
  have hD0 : (0 : Matrix (Fin W) (Fin W) ℂ).IsHermitian := Matrix.isHermitian_zero
  unfold meanTrace
  rw [← integral_sub (integrable_zeTrace hW0 b e hD J hz0) (integrable_zeTrace hW0 b e hD0 J hz0)]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_).trans
    (hQ W hW hW0 b e hbe D hD ζ hz hzM)
  exact norm_nrt_sub_le hW0 ζ _ _

end ZeroEntranceProb

end BlockBand.Endpoints.Clock
