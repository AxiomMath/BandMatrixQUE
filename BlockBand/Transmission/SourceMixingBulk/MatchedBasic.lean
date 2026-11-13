module

public import BlockBand.Transmission.SourceMixingBulk.Scalars
public import BlockBand.Transmission.SourceMixing.MatchedBasic
public import BlockBand.Transmission.LengthUniform.BulkDressed
public import BlockBand.Transmission.LengthUniform.BulkMeanIdentify

/-!
# Matched values of the dressed quantities, uniformly on the bulk

The matched-value estimates of `matchedBasic` with constants uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Matched values of the dressed quantities.
The version of `matchedBasic` with constants uniform on `bulkInterval κ`. -/
theorem matchedBasic_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖mOf b E X‖ ≤ C ∧ ‖vOf b E X‖ ≤ C ∧ ‖passiveResolvent b E X‖ ≤ (etaZ b E)⁻¹ ∧
        ‖kmOf b E X - 1‖ ≤ C * epsOf b E s X ∧
        ‖mOf b E X - passiveResolvent b E X‖ ≤ C * epsOf b E s X ∧
        ‖vOf b E X - matchedA E‖ ≤ C * epsOf b E s X ∧
        ‖hOf b E X - 1‖ ≤ C * epsOf b E s X ∧
        ‖aOf b E X - dStar b‖ ≤ C * epsOf b E s X ∧
        ‖m2Of b E X + s‖ ≤ C * epsOf b E s X ∧
        ‖bOf b E X - jetB b E s‖ ≤ C * epsOf b E s X := by
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hmi⟩ := mean_identify_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨CR, WR, -, hres⟩ := mean_residuals_bulk hA hb0 hb hκ
  set ηi := (etaLow b κ)⁻¹
  have hηi : 0 ≤ ηi := inv_nonneg.mpr (etaLow_pos (by linarith) hκ).le
  set Cz := Cm
  set Cv := CD * b * Cz
  set CMR := Cz * CD * ηi
  set C := CD + Cz * CD + CMR + Cv + (CD + 1) * Cv + (CMR * (CD + ηi) + ηi) +
    (CMR * (CD + ηi) + 1) + (CMR * (CD * CD + CD * ηi + ηi * ηi) + constBL b κ)
  have hcB : 0 ≤ constBL b κ := constBL_nonneg hb hκ
  refine ⟨d₀, C, max (max Wm WD) (max WR 1), hd₀, by positivity, fun W hW E hEκ s X hX hd => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWD⟩, hWR, hW1⟩ := hW
  have hY := hX.posSemidef
  obtain ⟨hm1, hm2, -⟩ := hmi W hWm E hEκ X hX hd
  obtain ⟨-, -, hM, hv, -, -, -, -, -, hzM, hMz⟩ := hD W hWD E hEκ X hX
  obtain ⟨-, -, -, -, hβ, -⟩ := hres W hWR E hEκ X hX
  obtain ⟨e0, e1, eq, e01, eall⟩ := epsOf_ge (b := b) (E := E) s hY
  set e := epsOf b E s X
  have he : 0 ≤ e := by linarith
  have hW0 : W ≠ 0 := by omega
  set R := passiveResolvent b E X
  set M := mOf b E X
  set a := matchedA E
  set z := boundaryZ b E
  set ζ := zetaX b E X
  have hR0 : ‖R‖ ≤ (etaZ b E)⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hR : ‖R‖ ≤ ηi := hR0.trans (inv_etaZ_le_bulk hb hκ hEκ)
  obtain ⟨hzR, -⟩ := nearPencil_inverse hb0 hb h1 h2 hY
  have hCe : ∀ K : ℝ, 0 ≤ K → K ≤ C → K * e ≤ C * e := fun K _ hK =>
    mul_le_mul_of_nonneg_right hK he
  -- `|z - ζ| ≤ Cz e`
  have hz : ‖z - ζ‖ ≤ Cz * e := by
    have h := PathJet.zeta_sub_z b E h1 h2 (meanTr b E X 0) (meanTr b E X 3)
    change ‖boundaryZ b E - zetaOf b E (meanTr b E X 0) (meanTr b E X 3)‖ ≤ _
    rw [← norm_neg, neg_sub, h, norm_neg]
    have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, nc, nb]
    have hc : 0 ≤ 1 - 2 * b := by linarith
    calc (1 - 2 * b) * ‖meanTr b E X 0 - a‖ + b * ‖meanTr b E X 3 - a‖
        ≤ (1 - 2 * b) * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) +
          b * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) := by gcongr
      _ ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
          have : 0 ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by positivity
          nlinarith
      _ ≤ Cz * e := mul_le_mul_of_nonneg_left e01 hCm
  -- `KM = 1 + (z - ζ)M`
  have hKM : kmOf b E X - 1 = (z - ζ) • M := by
    have e' : kmOf b E X = (z • 1 - X) * M := (blkAt_kHat_mul_zero b E X _).1
    rw [e', show z • (1 : Matrix (Fin W) (Fin W) ℂ) - X = (z - ζ) • 1 + (ζ • 1 - X) by
      rw [sub_smul]; abel, Matrix.add_mul, hzM, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hKM' : ‖kmOf b E X - 1‖ ≤ Cz * CD * e := by
    rw [hKM]
    calc ‖(z - ζ) • M‖ ≤ ‖z - ζ‖ * ‖M‖ := norm_smul_le _ _
      _ ≤ Cz * e * CD := mul_le_mul hz hM (norm_nonneg _) (by positivity)
      _ = Cz * CD * e := by ring
  -- `M - R = (z - ζ)MR`
  have hMR : M - R = (z - ζ) • (M * R) := by
    calc M - R = M * ((z • 1 - X) * R) - (M * (ζ • 1 - X)) * R := by
          rw [hzR, hMz, Matrix.mul_one, Matrix.one_mul]
      _ = M * ((z • 1 - X) - (ζ • 1 - X)) * R := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (z - ζ) • (M * R) := by
          rw [show (z • 1 - X) - (ζ • 1 - X) = (z - ζ) • (1 : Matrix (Fin W) (Fin W) ℂ) by
            rw [sub_smul]; abel, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hMR' : ‖M - R‖ ≤ CMR * e := by
    rw [hMR]
    calc ‖(z - ζ) • (M * R)‖ ≤ ‖z - ζ‖ * (‖M‖ * ‖R‖) :=
          (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ Cz * e * (CD * ηi) := mul_le_mul hz (mul_le_mul hM hR (norm_nonneg _) hCD)
          (by positivity) (by positivity)
      _ = CMR * e := by ring
  -- `v - a = vab(m₁ - a)`
  have ha0 : a ≠ 0 := matchedA_ne_zero E h1 h2
  have hna : ‖a‖ = 1 := norm_matchedA E h1 h2
  have hva : vOf b E X - a = vOf b E X * a * (b : ℂ) * (meanTr b E X 0 - a) := by
    have hβ' : (a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0 ≠ 0 := hβ
    show ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0)⁻¹ - a =
      ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0)⁻¹ * a * (b : ℂ) * (meanTr b E X 0 - a)
    have hD2 : 1 - a * (b : ℂ) * meanTr b E X 0 + a ^ 2 * (b : ℂ) ≠ 0 := by
      have e' : 1 - a * (b : ℂ) * meanTr b E X 0 + a ^ 2 * (b : ℂ) =
          a * ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0) := by field_simp; ring
      rw [e']; exact mul_ne_zero ha0 hβ'
    have hinv := mul_inv_cancel₀ hD2
    field_simp
    linear_combination hinv
  have hva' : ‖vOf b E X - a‖ ≤ Cv * e := by
    rw [hva, norm_mul, norm_mul, norm_mul, hna, Complex.norm_real, Real.norm_of_nonneg hb0.le,
      mul_one]
    calc ‖vOf b E X‖ * b * ‖meanTr b E X 0 - a‖ ≤ CD * b * (Cm * (jetDistance0 b E X +
          (W : ℝ)⁻¹ ^ 2)) := by gcongr
      _ ≤ CD * b * (Cz * e) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e01 hCm)
          (by positivity)
      _ = Cv * e := by ring
  -- `h - 1`
  have hh' : ‖hOf b E X - 1‖ ≤ (CD + 1) * Cv * e := by
    have e' : hOf b E X - 1 = (vOf b E X - a) * conj (vOf b E X) + a * conj (vOf b E X - a) := by
      unfold hOf
      rw [map_sub]
      have : a * conj a = 1 := matchedA_mul_conj E h1 h2
      linear_combination this
    rw [e']
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hna]
    calc ‖vOf b E X - a‖ * ‖vOf b E X‖ + 1 * ‖vOf b E X - a‖ = (‖vOf b E X‖ + 1) *
          ‖vOf b E X - a‖ := by ring
      _ ≤ (CD + 1) * (Cv * e) := mul_le_mul (by linarith) hva' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- the three normalized traces
  have hMMs : ‖M * Mᴴ - R * Rᴴ‖ ≤ CMR * (CD + ηi) * e := by
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    rw [norm_conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    calc ‖M - R‖ * ‖M‖ + ‖R‖ * ‖M - R‖ = (‖M‖ + ‖R‖) * ‖M - R‖ := by ring
      _ ≤ (CD + ηi) * (CMR * e) := mul_le_mul (add_le_add hM hR) hMR' (norm_nonneg _)
          (by positivity)
      _ = _ := by ring
  have hMM : ‖M * M - R * R‖ ≤ CMR * (CD + ηi) * e := by
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    calc ‖M - R‖ * ‖M‖ + ‖R‖ * ‖M - R‖ = (‖M‖ + ‖R‖) * ‖M - R‖ := by ring
      _ ≤ (CD + ηi) * (CMR * e) := mul_le_mul (add_le_add hM hR) hMR' (norm_nonneg _)
          (by positivity)
      _ = _ := by ring
  have hMMM : ‖M * (M * Mᴴ) - R * (R * Rᴴ)‖ ≤ CMR * (CD * CD + CD * ηi + ηi * ηi) * e := by
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    have hn : ‖M * Mᴴ‖ ≤ CD * CD := (Matrix.l2_opNorm_mul _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hCD)
    calc ‖M - R‖ * ‖M * Mᴴ‖ + ‖R‖ * ‖M * Mᴴ - R * Rᴴ‖
        ≤ CMR * e * (CD * CD) + ηi * (CMR * (CD + ηi) * e) :=
          add_le_add (mul_le_mul hMR' hn (norm_nonneg _) (by positivity))
            (mul_le_mul hR hMMs (norm_nonneg _) hηi)
      _ = _ := by ring
  have hA' : ‖aOf b E X - dStar b‖ ≤ (CMR * (CD + ηi) + ηi) * e := by
    have h := normTrace_RRstar_sub_dStar_le hb0 hb h1 h2 hY hW0
    calc ‖aOf b E X - dStar b‖ ≤ ‖aOf b E X - (W : ℂ)⁻¹ * (R * Rᴴ).trace‖ +
          ‖(W : ℂ)⁻¹ * (R * Rᴴ).trace - dStar b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ CMR * (CD + ηi) * e + (jetDistance0 b E X + passiveMass b E X / W) / etaZ b E :=
          add_le_add ((norm_normTrace_sub_le _ _).trans hMMs) h
      _ ≤ CMR * (CD + ηi) * e + ηi * e := by
          refine add_le_add le_rfl ?_
          rw [div_eq_inv_mul]
          have hm0 := passiveMass_nonneg b E hY
          have hj0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
          exact mul_le_mul (inv_etaZ_le_bulk hb hκ hEκ) (by linarith) (by positivity) hηi
      _ = _ := by ring
  have hm2' : ‖m2Of b E X + s‖ ≤ (CMR * (CD + ηi) + 1) * e := by
    have h := normTrace_R2_add_s hb0 hb h1 h2 hY s
    calc ‖m2Of b E X + s‖ ≤ ‖m2Of b E X - (W : ℂ)⁻¹ * (R * R).trace‖ +
          ‖(W : ℂ)⁻¹ * (R * R).trace + s‖ := by
          rw [← norm_neg ((W : ℂ)⁻¹ * (R * R).trace + s)]
          refine (norm_sub_le _ _).trans_eq' ?_
          ring_nf
      _ ≤ CMR * (CD + ηi) * e + 1 * e := by
          rw [h]
          exact add_le_add ((norm_normTrace_sub_le _ _).trans hMM) (by linarith)
      _ = _ := by ring
  have hB' : ‖bOf b E X - jetB b E s‖ ≤
      (CMR * (CD * CD + CD * ηi + ηi * ηi) + constBL b κ) * e := by
    have h := normTrace_R2Rstar_sub_le hb0 hb h1 h2 hY hW0 s
    rw [Matrix.mul_assoc] at h
    calc ‖bOf b E X - jetB b E s‖ ≤ ‖bOf b E X - (W : ℂ)⁻¹ * (R * (R * Rᴴ)).trace‖ +
          ‖(W : ℂ)⁻¹ * (R * (R * Rᴴ)).trace - jetB b E s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ CMR * (CD * CD + CD * ηi + ηi * ηi) * e + constBL b κ * e :=
          add_le_add ((norm_normTrace_sub_le _ _).trans hMMM)
            ((h.trans (mul_le_mul_of_nonneg_left eall (constB_nonneg (hb0 := hb0) (hb := hb) (h1 := h1)
              (h2 := h2)))).trans (mul_le_mul_of_nonneg_right (constB_le_bulk hb hκ hEκ) he))
      _ = _ := by ring
  have p1 : 0 ≤ Cz * CD := by positivity
  have p2 : 0 ≤ CMR := by positivity
  have p3 : 0 ≤ Cv := by positivity
  have p4 : 0 ≤ (CD + 1) * Cv := by positivity
  have p5 : 0 ≤ CMR * (CD + ηi) + ηi := by positivity
  have p6 : 0 ≤ CMR * (CD + ηi) + 1 := by positivity
  have p7 : 0 ≤ CMR * (CD * CD + CD * ηi + ηi * ηi) + constBL b κ := by positivity
  refine ⟨hM.trans (by linarith), hv.trans (by linarith), hR0,
    hKM'.trans (hCe _ p1 (by linarith)), hMR'.trans (hCe _ p2 (by linarith)),
    hva'.trans (hCe _ p3 (by linarith)), hh'.trans (hCe _ p4 (by linarith)),
    hA'.trans (hCe _ p5 (by linarith)), hm2'.trans (hCe _ p6 (by linarith)),
    hB'.trans (hCe _ p7 (by linarith))⟩

end BlockBand.Transmission.SourceMixingBulk
