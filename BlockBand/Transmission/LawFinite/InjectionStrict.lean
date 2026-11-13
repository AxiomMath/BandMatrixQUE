module

public import BlockBand.Transmission.LawFinite.InjectionAlg
public import BlockBand.Transmission.Generator.RefinedMean

/-!
# Injection mean at strictly passive inputs, bulk-uniform

**Hypothesis:** `PassiveBoundsStatement`, through its bulk forms `freshU_mean_bulk`
(`EU = s KM KM* + O(W⁻²)`), `dressedBlocks_bulk`, `scalarS1_bulk`, `mm_matched0_bulk`
(`‖KM - 1‖, |z - ζ|, |h - 1| ≤ C(δ₀ + W⁻²)` on the domain `δ₀ ≤ d₀`) and `rf_sre`.

**`injMean_strict_bulk`**: `b, κ` first; then `C, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ` and
strictly passive `X`: `|W⁻¹ Re Tr(R*R·E[LL*]) - d_*| ≤ C(δ₀ + q/W + W⁻¹)`.

Proof: `inj_trace_bound` with `N = R*R` reduces to `|Re s - 1|`, `‖KM KM* - 1‖`, `‖Δ‖` and
`|⟨R*R⟩ - d_*| ≤ (δ₀ + q/W)/η` (`normTrace_adjR_sub_dStar_le`); `rf_sre` + `inj_re_s` give
`|Re s - 1| ≤ C(δ₀ + q/W + W⁻²)` (the `u/W` term, `u ≤ ‖KM‖²q`, is where `q/W` enters).
Off the domain the bound is `‖EU‖‖R‖² + d_* ≤ C δ₀/d₁`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.Generator
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem re_normTrace (M : Matrix (Fin W) (Fin W) ℂ) :
    ((W : ℂ)⁻¹ * M.trace).re = (W : ℝ)⁻¹ * M.trace.re := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem normTrace_re_le (M : Matrix (Fin W) (Fin W) ℂ) :
    |(W : ℝ)⁻¹ * M.trace.re| ≤ ‖M‖ := by
  rw [← re_normTrace]
  exact (Complex.abs_re_le_norm _).trans (PathScalar.norm_normTrace_le M)

theorem norm_mul_adj_sub_one_le (KM : Matrix (Fin W) (Fin W) ℂ) {c : ℝ}
    (h : ‖KM - 1‖ ≤ c) (hK : ‖KM‖ ≤ 3 / 2) : ‖KM * KMᴴ - 1‖ ≤ 5 / 2 * c := by
  have e : KM * KMᴴ - 1 = (KM - 1) * KMᴴ + (KM - 1)ᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Matrix.l2_opNorm_conjTranspose]
  have := (Matrix.l2_opNorm_mul (KM - 1) KMᴴ)
  rw [Matrix.l2_opNorm_conjTranspose] at this
  have h0 : 0 ≤ c := (norm_nonneg _).trans h
  nlinarith [norm_nonneg (KM - 1), norm_nonneg KM]

/-- Scalar bookkeeping for `|Re s - 1|`. -/
theorem inj_s_final {sre ε₀ b η Li W e q Cm Z : ℝ} (hε0 : 0 ≤ ε₀) (hb0 : 0 < b) (hη : 0 < η)
    (hLi : η⁻¹ ≤ Li) (hCm : 0 ≤ Cm) (hZ : 0 ≤ Z) (hW2Z : (W : ℝ)⁻¹ ^ 2 ≤ Z)
    (heZ : e ≤ 2 * Z) (hqZ : q / W ≤ Z)
    (hs : |sre - 1| ≤ 2 * (ε₀ / W ^ 2 + 3 / 2 * b * (Cm * e) + 9 / 4 * (q / W)) / (b * η)) :
    |sre - 1| ≤ 2 * Li / b * (ε₀ + 3 * b * Cm + 9 / 4) * Z := by
  refine hs.trans ?_
  have a1 : ε₀ / W ^ 2 ≤ ε₀ * Z := by
    rw [div_eq_mul_inv, ← inv_pow]; exact mul_le_mul_of_nonneg_left hW2Z hε0
  have a2 : 3 / 2 * b * (Cm * e) ≤ 3 / 2 * b * Cm * (2 * Z) := by
    have := mul_le_mul_of_nonneg_left heZ (by positivity : 0 ≤ 3 / 2 * b * Cm)
    linarith only [this]
  have a3 : ε₀ / W ^ 2 + 3 / 2 * b * (Cm * e) + 9 / 4 * (q / W) ≤
      (ε₀ + 3 * b * Cm + 9 / 4) * Z := by linarith only [a1, a2, hqZ]
  rw [div_le_iff₀ (by positivity)]
  have hLe : 1 ≤ Li * η := by
    have := mul_le_mul_of_nonneg_right hLi hη.le
    rwa [inv_mul_cancel₀ hη.ne'] at this
  have e' : 2 * Li / b * (ε₀ + 3 * b * Cm + 9 / 4) * Z * (b * η) =
      2 * ((ε₀ + 3 * b * Cm + 9 / 4) * Z * (Li * η)) := by field_simp
  rw [e']
  have : (ε₀ + 3 * b * Cm + 9 / 4) * Z ≤ (ε₀ + 3 * b * Cm + 9 / 4) * Z * (Li * η) :=
    le_mul_of_one_le_right (by positivity) hLe
  linarith only [this, a3]

/-- **`|Re s - 1| ≤ C(δ₀ + q/W + W⁻¹)` on the domain** (all inputs explicit). -/
theorem inj_s_bound {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef)
    {Cf C2 CD Cm Li e Z : ℝ} (hCf : 0 ≤ Cf) (hC2 : 0 ≤ C2) (hCD : 0 ≤ CD) (hCm : 0 ≤ Cm)
    (hZ : 0 ≤ Z) (hLi : (etaZ b E)⁻¹ ≤ Li) (hz2 : ‖boundaryZ b E‖ ≤ 2)
    (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e)
    (hh1' : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e) (hCme : Cm * e ≤ 1 / 2)
    (hKMn' : ‖kmOf b E X‖ ≤ 3 / 2) (hsn : ‖sOne b E X‖ ≤ Cf)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤ C2 / (W : ℝ) ^ 2)
    (heZ : e ≤ 2 * Z) (hW2Z : (W : ℝ)⁻¹ ^ 2 ≤ Z) (hqZ : passiveMass b E X / W ≤ Z) :
    |(sOne b E X).re - 1| ≤ 2 * Li / b * ((3 * C2 + Cf * (2 * CD)) + 3 * b * Cm + 9 / 4) * Z := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hYs := hX.posSemidef
  have hq : 0 ≤ passiveMass b E X := passiveMass_nonneg b E hYs
  set z := boundaryZ b E
  set ζ := zetaX b E X
  set ω := z - ζ with hωdef
  have hιb : |ζ.im| ≤ 3 := by
    have h' : ‖ζ‖ ≤ ‖z‖ + ‖z - ζ‖ := by
      have := norm_sub_le z (z - ζ); rwa [sub_sub_cancel] at this
    have := Complex.abs_im_le_norm ζ
    have : Cm * e ≤ 1 / 2 := hCme
    linarith only [h', hz2, hzζ, this, Complex.abs_im_le_norm ζ]
  have hsre := rf_sre hW1 hb0 hb hG hB0 hB1 hzM hS hsn (hh1'.trans hCme) hιb
  have hι : ζ.im = etaZ b E - ω.im := by simp only [ω, etaZ, Complex.sub_im]; ring
  rw [hι] at hsre
  set h := Complex.normSq (vOf b E X)
  set M := mOf b E X
  set u := (Mᴴ * passiveY X * M).trace.re
  obtain ⟨-, hRz⟩ := nearPencil_inverse hb0 hb h1 h2 hYs
  have hKMeq : kmOf b E X = (z • 1 - X) * M := (blkAt_kHat_mul_zero b E X _).1
  have hRKM : passiveResolvent b E X * kmOf b E X = M := by
    rw [hKMeq, ← Matrix.mul_assoc, hRz, Matrix.one_mul]
  obtain ⟨hu0, -, huq, -⟩ := mm_trace_decomp (Q := passiveQ b E X) (U := 1) (sOne b E X) hYs rfl
    hRKM
  have huq' : u ≤ 9 / 4 * passiveMass b E X := by
    refine huq.trans (mul_le_mul_of_nonneg_right ?_ hq)
    have := mul_le_mul hKMn' hKMn' (norm_nonneg _) (by norm_num)
    rw [sq]; linarith only [this]
  have hhlo : 1 / 2 ≤ h := by have := neg_abs_le (h - 1); linarith only [this, hh1', hCme]
  have hhhi : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith only [this, hh1', hCme]
  have hc0 : 0 ≤ 1 - 2 * b := by linarith only [hb]
  have hk0 : 0 ≤ (1 - 2 * b) + b ^ 2 * h := by positivity
  have hk1 : (1 - 2 * b) + b ^ 2 * h ≤ 1 := by
    have h3 : b * h ≤ 2 := by nlinarith only [hhhi, hb, hb0, hhlo]
    have : b ^ 2 * h ≤ 2 * b := by nlinarith only [h3, hb0]
    linarith only [this]
  have hDlo : b * (1 / 2) * etaZ b E ≤
      b * h * etaZ b E + ((1 - 2 * b) + b ^ 2 * h) * (u / W) := by
    have : 0 ≤ ((1 - 2 * b) + b ^ 2 * h) * (u / W) := by positivity
    have : b * (1 / 2) * etaZ b E ≤ b * h * etaZ b E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhlo hb0.le) hη.le
    linarith
  have hωi : |ω.im| ≤ Cm * e := (Complex.abs_im_le_norm _).trans hzζ
  have hs1 := inj_re_s hb0 hη rfl hDlo hhhi hk0 hk1 hu0 huq' hWpos hsre hωi
    (by linarith only [hhlo])
  exact inj_s_final (by positivity) hb0 hη hLi hCm hZ hW2Z heZ hqZ hs1

/-- Assembly of the on-domain bound (pure). -/
theorem inj_assemble {N U KM : Matrix (Fin W) (Fin W) ℂ} (s : ℂ) (hN : N.PosSemidef)
    {Cf Ks Cm Li Z e d : ℝ} (hCf : 0 ≤ Cf) (hKs : 0 ≤ Ks) (hCm : 0 ≤ Cm)
    (hZ : 0 ≤ Z) (hW2Z : (W : ℝ)⁻¹ ^ 2 ≤ Z) (heZ : e ≤ 2 * Z)
    (hU : ‖U - s • (KM * KMᴴ)‖ ≤ Cf / (W : ℝ) ^ 2) (hs : |s.re - 1| ≤ Ks * Z)
    (hPn : ‖KM * KMᴴ‖ ≤ 9 / 4) (hP1 : ‖KM * KMᴴ - 1‖ ≤ 5 / 2 * (Cm * e))
    (ht₀ : (W : ℝ)⁻¹ * N.trace.re ≤ Li ^ 2) (ht₀0 : 0 ≤ (W : ℝ)⁻¹ * N.trace.re)
    (hdst : |(W : ℝ)⁻¹ * N.trace.re - d| ≤ Li * Z) :
    |(W : ℝ)⁻¹ * (N * U).trace.re - d| ≤ ((Cf + 9 / 4 * Ks + 5 * Cm) * Li ^ 2 + Li) * Z := by
  have hmain := inj_trace_bound (N := N) (U := U) (KM := KM) s hN
  have a1 : Cf / (W : ℝ) ^ 2 ≤ Cf * Z := by
    rw [div_eq_mul_inv, ← inv_pow]; exact mul_le_mul_of_nonneg_left hW2Z hCf
  have a2 : |s.re - 1| * ‖KM * KMᴴ‖ ≤ Ks * Z * (9 / 4) :=
    mul_le_mul hs hPn (norm_nonneg _) (by positivity)
  have a3 : 5 / 2 * (Cm * e) ≤ 5 * Cm * Z := by
    have := mul_le_mul_of_nonneg_left heZ hCm; linarith only [this]
  have hfac : ‖U - s • (KM * KMᴴ)‖ + |s.re - 1| * ‖KM * KMᴴ‖ + ‖KM * KMᴴ - 1‖ ≤
      (Cf + 9 / 4 * Ks + 5 * Cm) * Z := by linarith only [a1, a2, a3, hU, hP1]
  have hm2 := hmain.trans (mul_le_mul hfac ht₀ ht₀0 (by positivity))
  have := abs_sub_le ((W : ℝ)⁻¹ * (N * U).trace.re) ((W : ℝ)⁻¹ * N.trace.re) d
  have hfin : (Cf + 9 / 4 * Ks + 5 * Cm) * Z * Li ^ 2 + Li * Z =
      ((Cf + 9 / 4 * Ks + 5 * Cm) * Li ^ 2 + Li) * Z := by ring
  linarith only [this, hm2, hdst, hfin]

/-- Off-domain bookkeeping (pure). -/
theorem inj_off {a d C₁ Li d₁ δ Z : ℝ} (ha : |a| ≤ C₁ * Li ^ 2) (hd : |d| ≤ 2)
    (hC₁ : 0 ≤ C₁) (hd₁ : 0 < d₁) (hdom : d₁ < δ) (hδZ : δ ≤ Z) :
    |a - d| ≤ (C₁ * Li ^ 2 + 2) / d₁ * Z := by
  have h0 : 0 ≤ C₁ * Li ^ 2 + 2 := by positivity
  have hK0 : 0 ≤ (C₁ * Li ^ 2 + 2) / d₁ := div_nonneg h0 hd₁.le
  have hoff : C₁ * Li ^ 2 + 2 ≤ (C₁ * Li ^ 2 + 2) / d₁ * Z :=
    calc C₁ * Li ^ 2 + 2 = (C₁ * Li ^ 2 + 2) / d₁ * d₁ := by field_simp
      _ ≤ (C₁ * Li ^ 2 + 2) / d₁ * δ := mul_le_mul_of_nonneg_left hdom.le hK0
      _ ≤ _ := mul_le_mul_of_nonneg_left hδZ hK0
  have := abs_sub a d
  linarith only [this, ha, hd, hoff]

/-- **Injection mean, strictly passive inputs, bulk-uniform.** -/
theorem injMean_strict_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        |(W : ℝ)⁻¹ * ((passiveResolvent b E X)ᴴ * passiveResolvent b E X *
            matrixExpect (freshLaw W b) (freshU b E X)).trace.re - dStar b| ≤
          C * (jetDistance0 b E X + passiveMass b E X / W + (W : ℝ)⁻¹) := by
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨C2, W2, hC2, hS1⟩ := scalarS1_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hm0⟩ := mm_matched0_bulk hA hb0 hb hκ
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κ)⁻¹
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hηL).le
  set d₁ := min d₀ (1 / (4 * (Cm + 1)))
  have hd₁ : 0 < d₁ := lt_min hd₀ (by positivity)
  set C₁ := Cf * Cf * Cf + Cf
  set Ks := 2 * Li / b * ((3 * C2 + Cf * (2 * CD)) + 3 * b * Cm + 9 / 4)
  have hKs : 0 ≤ Ks := by positivity
  set Kon := (Cf + 9 / 4 * Ks + 5 * Cm) * Li ^ 2 + Li
  set Koff := (C₁ * Li ^ 2 + 2) / d₁
  have hKon : 0 ≤ Kon := by positivity
  have hKoff : 0 ≤ Koff := by positivity
  refine ⟨Kon + Koff, max (max (max Wf W2) (max WD Wm)) ⌈d₁⁻¹⌉₊, by positivity,
    fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hz2 : ‖boundaryZ b E‖ ≤ 2 := bulk_norm_z hb0 hb hκ hE
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWf, hW2⟩, hWD, hWm⟩, hWd⟩ := hW
  have hYs := hX.posSemidef
  obtain ⟨hKMn, hsn, hU⟩ := hF W hWf E hE X hX
  obtain ⟨hW1, -, -, -, -, -, hB0, hB1, hG, hzM, -⟩ := hD W hWD E hE X hX
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set R := passiveResolvent b E X
  set N := Rᴴ * R
  set q := passiveMass b E X
  set U := matrixExpect (freshLaw W b) (freshU b E X)
  set δ := jetDistance0 b E X
  set Z := δ + q / W + (W : ℝ)⁻¹
  have hq : 0 ≤ q := passiveMass_nonneg b E hYs
  have hδ : 0 ≤ δ := norm_nonneg _
  have hWi : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hWpos.le
  have hqW : 0 ≤ q / W := div_nonneg hq hWpos.le
  have hZ0 : 0 ≤ Z := by positivity
  have hδZ : δ ≤ Z := by simp only [Z]; linarith only [hqW, hWi]
  have hqZ : q / W ≤ Z := by simp only [Z]; linarith only [hδ, hWi]
  have hWZ : (W : ℝ)⁻¹ ≤ Z := by simp only [Z]; linarith only [hδ, hqW]
  have hW2Z : (W : ℝ)⁻¹ ^ 2 ≤ Z :=
    (pow_le_of_le_one hWi (inv_le_one_of_one_le₀ hW1r) two_ne_zero).trans hWZ
  have hN : N.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self R
  have hR : ‖R‖ ≤ Li := (norm_passiveResolvent_le hb0 hb h1 h2 hYs).trans hLi
  have hNn : ‖N‖ ≤ Li ^ 2 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, sq]
    exact mul_le_mul hR hR (norm_nonneg _) hLi0
  have ht₀ : (W : ℝ)⁻¹ * N.trace.re ≤ Li ^ 2 :=
    (le_abs_self _).trans ((normTrace_re_le N).trans hNn)
  have ht₀0 : 0 ≤ (W : ℝ)⁻¹ * N.trace.re := mul_nonneg hWi (mm_trace_posSemidef hN).1
  have hdst := normTrace_adjR_sub_dStar_le hb0 hb h1 h2 hYs (by omega : W ≠ 0)
  have hdst' : |(W : ℝ)⁻¹ * N.trace.re - dStar b| ≤ Li * Z := by
    refine hdst.trans ?_
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul hLi (by simp only [Z]; linarith only [hWi]) (by positivity) hLi0
  have hKZ : 0 ≤ Kon * Z := by positivity
  have hKZ' : 0 ≤ Koff * Z := by positivity
  rw [add_mul]
  by_cases hdom : δ ≤ d₁
  swap
  · push Not at hdom
    have hUn : ‖U‖ ≤ C₁ := by
      have h := norm_add_le (U - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
        (sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
      rw [sub_add_cancel] at h
      have h2' : ‖sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf * (Cf * Cf) := by
        refine (norm_smul_le _ _).trans (mul_le_mul hsn ?_ (norm_nonneg _) hCf)
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hKMn hKMn (norm_nonneg _) hCf
      have h3 : Cf / (W : ℝ) ^ 2 ≤ Cf := div_le_self hCf (one_le_pow₀ hW1r)
      simp only [C₁]; linarith only [h, h2', h3, hU]
    have hNU : |(W : ℝ)⁻¹ * (N * U).trace.re| ≤ C₁ * Li ^ 2 := by
      rw [abs_mul, abs_of_nonneg hWi, trace_mul_comm]
      have := (Complex.abs_re_le_norm _).trans (norm_trace_mul_posSemidef_le hN U)
      calc (W : ℝ)⁻¹ * |(U * N).trace.re| ≤ (W : ℝ)⁻¹ * (‖U‖ * N.trace.re) :=
            mul_le_mul_of_nonneg_left this hWi
        _ = ‖U‖ * ((W : ℝ)⁻¹ * N.trace.re) := by ring
        _ ≤ C₁ * Li ^ 2 := mul_le_mul hUn ht₀ ht₀0 (by positivity)
    have hds : |dStar b| ≤ 2 := by
      have hb1 : 0 < 1 - b := by linarith
      rw [dStar, abs_of_pos (by positivity)]
      rw [div_le_iff₀ hb1]; linarith only [hb]
    have := inj_off hNU hds (by positivity) hd₁ hdom hδZ
    linarith only [this, hKZ]
  -- on the domain
  have hWinv : (W : ℝ)⁻¹ ≤ d₁ := by
    rw [inv_le_comm₀ hWpos hd₁]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d₁ := Generator.rf_Wsq hW1r hWinv
  set e := δ + (W : ℝ)⁻¹ ^ 2
  have heZ : e ≤ 2 * Z := by simp only [e]; linarith only [hδZ, hW2Z]
  have hCme : Cm * e ≤ 1 / 2 := by
    have hd4 : d₁ ≤ 1 / (4 * (Cm + 1)) := min_le_right _ _
    have he2 : e ≤ 2 * (1 / (4 * (Cm + 1))) := by
      simp only [e]; linarith only [hd4, hdom, hWsq]
    have := mul_le_mul_of_nonneg_left he2 hCm
    have h' : Cm * (2 * (1 / (4 * (Cm + 1)))) ≤ 1 / 2 := by
      rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith only [hCm]
    linarith only [this, h']
  obtain ⟨hzζ, hKM1, hh1⟩ := hm0 W hWm E hE X hX (hdom.trans (min_le_left _ _))
  set KM := kmOf b E X
  have hKMn' : ‖KM‖ ≤ 3 / 2 := by
    have := norm_add_le (KM - 1) 1
    rw [sub_add_cancel] at this
    have h1' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
    linarith only [this, h1', hKM1, hCme]
  have hP1 : ‖KM * KMᴴ - 1‖ ≤ 5 / 2 * (Cm * e) := norm_mul_adj_sub_one_le KM hKM1 hKMn'
  have hPn : ‖KM * KMᴴ‖ ≤ 9 / 4 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    have := mul_le_mul hKMn' hKMn' (norm_nonneg _) (by norm_num)
    linarith only [this]
  have hheq : hOf b E X - 1 = ((Complex.normSq (vOf b E X) - 1 : ℝ) : ℂ) := by
    simp only [hOf, Complex.mul_conj]; push_cast; ring
  have hh1' : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e := by
    rw [hheq, Complex.norm_real, Real.norm_eq_abs] at hh1; exact hh1
  have hs := inj_s_bound hb0 hb h1 h2 hW1 hX hCf hC2 hCD hCm hZ0 hLi hz2 hzζ hh1' hCme hKMn'
    hsn hG hB0 hB1 hzM (hS1 W hW2 E hE X hX).2.2 heZ hW2Z hqZ
  have := inj_assemble (N := N) (U := U) (KM := KM) (sOne b E X) hN hCf hKs hCm hZ0 hW2Z
    heZ hU hs hPn hP1 ht₀ ht₀0 hdst'
  exact this.trans (le_add_of_nonneg_right hKZ')

end BlockBand.Transmission.LawFinite
