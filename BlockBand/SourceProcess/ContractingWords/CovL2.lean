module

public import BlockBand.SourceProcess.ContractingWords.LayerDriftProof

/-!
# `L²` sizes of the one-layer increment and of the injection

Second-moment bounds for the increment of one word over one layer and for the injection.

Measure `freshLaw W b`; deterministic Hermitian `𝕏`; Hermitian letters with `Tr|A_ℓ| ≤ K`; injections
`|c_ℓ| ≤ c₀/W²`; ordinary words `w`, `|w| ≤ d`; `e = layerErr`. The constants depend only on `b, κ, d, K, c₀`.

* `new_old_L2`: `E|new_c w - Tr w(𝕏)|² ≤ (C(W^{-1/2} + e))²` (`LayerFreshBound` at `r = 2`,
  `meanFactor [w] = 1`);
* `inj_L2`: `E|new_c w - new_0 w|² ≤ (C/W)²` (`newProd_sub_core_le` and the moments of
  `G = 1 + ‖N‖ + ‖D‖`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

/-- **The increment of one word in `L²`.** -/
theorem new_old_L2 (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (d : ℕ) {K c₀ : ℝ} (hK : 0 ≤ K)
    (hc₀ : 0 ≤ c₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (c : TraceLetter nT nI → ℝ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        (∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2) →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        Integrable (fun y => layerNew b E A c XX w y) (freshLaw W b) ∧
        Integrable (fun y => ‖layerNew b E A c XX w y - coreProd A (sepOf b E XX) [w]‖ ^ 2)
          (freshLaw W b) ∧
        ∫ y, ‖layerNew b E A c XX w y - coreProd A (sepOf b E XX) [w]‖ ^ 2 ∂freshLaw W b ≤
          (C * (1 / Real.sqrt W + layerErr b E s XX)) ^ 2 := by
  obtain ⟨CF, WF, hCF, hFr⟩ := layerFreshBound_holds hGA hLp b hb0 hb κ hκ d 2 K c₀
    (by norm_num) hK hc₀
  refine ⟨2 * CF, WF, by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A c hA hAK hc w hw hwd
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨hδ0, hδe, -, -, he0, -⟩ := layerErr_parts b E s XX hg (W := W)
  have hZ : IsAdmittedProduct [w] := fun v hv => by
    simp only [List.mem_singleton] at hv; rw [hv]; exact hw.1
  have hd : productDegree [w] ≤ d := by simpa [productDegree] using hwd
  obtain ⟨hI, hm, hf⟩ := hFr W hW E hE s hs XX hXX nT nI A c hA hAK hc [w] hZ hd
  have e0 : ∀ y, newProd A c (freshTransport b E XX y) (freshD b E XX y)
      (sepOf b E (freshTwoPortSchur E XX y)) [w] = layerNew b E A c XX w y := fun y => by
    simp [newProd, layerNew]
  simp only [e0, meanFactor_ord b E s hw, one_mul] at hI hm hf
  set Z := fun y => layerNew b E A c XX w y
  set old := coreProd A (sepOf b E XX) [w]
  set EZ := ∫ y, Z y ∂freshLaw W b
  refine ⟨hI, ?_⟩
  have hmeas : AEStronglyMeasurable (fun y => Z y - old) (freshLaw W b) :=
    (hI.sub (integrable_const old)).aestronglyMeasurable
  have hsplit : (fun y => Z y - old) = fun y => (EZ - old) + (Z y - EZ) := funext fun y => by ring
  have h2 : ENNReal.ofReal (2 : ℝ) = ((2 : ℕ) : ℝ≥0∞) := by simp
  rw [h2] at hf
  have hL : eLpNorm (fun y => Z y - old) ((2 : ℕ) : ℝ≥0∞) (freshLaw W b) ≤
      ENNReal.ofReal (2 * CF * (1 / Real.sqrt W + layerErr b E s XX)) := by
    rw [hsplit]
    refine (eLpNorm_add_le (f := fun _ => EZ - old) (by norm_num)).trans ?_
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one]
    have hsq : 0 ≤ 1 / Real.sqrt W := by positivity
    calc ‖EZ - old‖ₑ + eLpNorm (fun y => Z y - EZ) ((2 : ℕ) : ℝ≥0∞) (freshLaw W b) ≤
        ENNReal.ofReal (CF * layerErr b E s XX) +
          ENNReal.ofReal (CF * (1 / Real.sqrt W + jetDistance0 b E
            (nearSchur (boundaryZ b E) XX))) := by
          refine add_le_add ?_ hf
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hm
      _ ≤ _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_le_mul_of_nonneg_left hδe hCF]
  have hmom := moments_of_eLpNorm hmeas (by positivity) hL 2 (by norm_num) le_rfl
  exact ⟨hmom.1, by simpa [mul_assoc] using hmom.2⟩

theorem inj_pow_eq (d : ℕ) (W ρ : ℝ) :
    d * d / W * ρ ^ (d + 1) * ((3 + d) * ρ ^ (d + 1)) ^ d =
      d * d * (3 + d) ^ d * W⁻¹ * ρ ^ ((d + 1) ^ 2) := by
  rw [mul_pow, ← pow_mul, show (d + 1) ^ 2 = (d + 1) + (d + 1) * d by ring, pow_add]
  ring

/-- **The injection in `L²`.** -/
theorem inj_L2 (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (d : ℕ) {K c₀ : ℝ} (hK : 0 ≤ K) (hc₀ : 0 ≤ c₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (c : TraceLetter nT nI → ℝ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        (∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2) →
      ∀ w : TraceWord nT nI, w ≠ [] → w.length ≤ d →
        Integrable (fun y => layerNew b E A c XX w y) (freshLaw W b) →
        Integrable (fun y => layerNew b E A (fun _ => 0) XX w y) (freshLaw W b) →
        Integrable (fun y => ‖layerNew b E A c XX w y - layerNew b E A (fun _ => 0) XX w y‖ ^ 2)
          (freshLaw W b) ∧
        ∫ y, ‖layerNew b E A c XX w y - layerNew b E A (fun _ => 0) XX w y‖ ^ 2 ∂freshLaw W b ≤
          (C * (W : ℝ)⁻¹) ^ 2 := by
  obtain ⟨CG, WG, hCG, hG⟩ := fresh_G_moment hGA hb0 hb hκ (4 * (d + 1) ^ 2)
    (by have : 1 ≤ (d + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos d); omega)
  set Q : ℝ := d * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2)
  have hQ : 0 ≤ Q := by positivity
  refine ⟨Q * (1 + CG), max WG 1, by positivity, ?_⟩
  intro W hW E hE XX hXX nT nI A c hA hAK hc w hw hwd hic hi0
  simp only [max_le_iff] at hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hS := ae_sepOf_le hb0 hW.2 hη hXX
  obtain ⟨hGi, hGb⟩ := hG W hW.1 E hE XX hXX
  have hZ : IsAdmittedProduct [w] := fun v hv => by
    simp only [List.mem_singleton] at hv; rw [hv]; exact hw
  have hd : productDegree [w] ≤ d := by simpa [productDegree] using hwd
  set f := fun y => layerNew b E A c XX w y - layerNew b E A (fun _ => 0) XX w y
  have hpt : ∀ᵐ y ∂freshLaw W b, ‖f y‖ ^ 2 ≤
      (Q * (W : ℝ)⁻¹) ^ 2 * freshG b E XX y ^ (4 * (d + 1) ^ 2) := by
    filter_upwards [hS] with y hy
    have h := newProd_sub_core_le hW.2 A c (freshTransport b E XX y) (freshD b E XX y)
      (sepOf b E (freshTwoPortSchur E XX y)) hK hc₀ hA hAK hc hy [w] hZ hd
    have e1 : newProd A c (freshTransport b E XX y) (freshD b E XX y)
        (sepOf b E (freshTwoPortSchur E XX y)) [w] -
        coreProd A (fun σ => freshTransport b E XX y * sepOf b E (freshTwoPortSchur E XX y) σ *
          (freshTransport b E XX y)ᴴ) [w] = f y := by
      simp only [f, layerNew, newWord_zero, newProd, coreProd, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
    rw [e1, inj_pow_eq] at h
    have hG1 : 1 ≤ freshG b E XX y := by
      simp only [freshG]; linarith [norm_nonneg (freshTransport b E XX y),
        norm_nonneg (freshD b E XX y)]
    have e2 : (3 * (1 + K + c₀) * (1 + ‖freshTransport b E XX y‖ + ‖freshD b E XX y‖) ^ 2) ^
        ((d + 1) ^ 2) = (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) *
          freshG b E XX y ^ (2 * (d + 1) ^ 2) := by
      rw [mul_pow, ← pow_mul]
    rw [e2] at h
    have hf0 := norm_nonneg (f y)
    generalize freshG b E XX y = Gy at h ⊢
    calc ‖f y‖ ^ 2 ≤ (d * d * (3 + d) ^ d * (W : ℝ)⁻¹ * ((3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) *
          Gy ^ (2 * (d + 1) ^ 2))) ^ 2 := pow_le_pow_left₀ hf0 h 2
      _ = (Q * (W : ℝ)⁻¹) ^ 2 * (Gy ^ (2 * (d + 1) ^ 2)) ^ 2 := by simp only [Q]; ring
      _ = (Q * (W : ℝ)⁻¹) ^ 2 * Gy ^ (4 * (d + 1) ^ 2) := by
          rw [← pow_mul, show 2 * (d + 1) ^ 2 * 2 = 4 * (d + 1) ^ 2 by ring]
  have hmeas : AEStronglyMeasurable (fun y => ‖f y‖ ^ 2) (freshLaw W b) :=
    ((hic.sub hi0).aestronglyMeasurable.norm.pow 2)
  have hint : Integrable (fun y => ‖f y‖ ^ 2) (freshLaw W b) :=
    (hGi.const_mul ((Q * (W : ℝ)⁻¹) ^ 2)).mono' hmeas (by
      filter_upwards [hpt] with y hy
      rw [Real.norm_of_nonneg (by positivity)]; exact hy)
  refine ⟨hint, ?_⟩
  refine (integral_mono_ae hint (hGi.const_mul _) hpt).trans ?_
  rw [integral_const_mul]
  have hW0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
  calc (Q * (W : ℝ)⁻¹) ^ 2 * ∫ y, freshG b E XX y ^ (4 * (d + 1) ^ 2) ∂freshLaw W b ≤
        (Q * (W : ℝ)⁻¹) ^ 2 * CG := mul_le_mul_of_nonneg_left hGb (by positivity)
    _ ≤ (Q * (1 + CG) * (W : ℝ)⁻¹) ^ 2 := by
        have : CG ≤ (1 + CG) ^ 2 := by nlinarith
        calc (Q * (W : ℝ)⁻¹) ^ 2 * CG ≤ (Q * (W : ℝ)⁻¹) ^ 2 * (1 + CG) ^ 2 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := by ring

end BlockBand.SourceProcess.ContractingWords
