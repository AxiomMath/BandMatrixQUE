module

public import BlockBand.SourceProcess.ContractingWords.InjMean
public import BlockBand.SourceProcess.ProjSeparator.InjNearW2

/-!
# The mean injection, all ordinary words

Conditional on `ProjSeparator.InjNearMeanW2` (the near mean injection with the error
`C(δ₀ + g/W + W⁻²)`) and `InjFarTrace`. Measure `freshLaw W b`; `e = layerErr`.

`inj_mean hGA hLp hIn hIf`: `C, W₀` from `b, κ, d, K, c₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`,
stationary `s`, Hermitian `𝕏`, Hermitian letters `Tr|A_ℓ| ≤ K`, tests `|q_a| ≤ c₀`, every `j`
and every ordinary `w` with `|w| ≤ d`: `new_c w`, `new_0 w` are integrable and
`|E new_c w - E new_0 w - W⁻¹ inj_w((j+1)/W)| ≤ C e²`.
The extra `W⁻²` of `InjNearMeanW2` enters multiplied by `|q|/W`, i.e. as `O(W⁻³) ≤ O(e²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem lam_le {K c₀ G : ℝ} (hK : 0 ≤ K) (hc₀ : 0 ≤ c₀) (hG : 1 ≤ G) {m M : ℕ} (hm : m ≤ M) :
    (1 + 3 * ((1 + K + c₀) * G ^ 2)) ^ m ≤ (1 + 3 * (1 + K + c₀)) ^ M * G ^ (2 * M) := by
  have hG2 : 1 ≤ G ^ 2 := one_le_pow₀ hG
  have h1 : 1 + 3 * ((1 + K + c₀) * G ^ 2) ≤ (1 + 3 * (1 + K + c₀)) * G ^ 2 := by nlinarith
  have h2 : 1 ≤ (1 + 3 * (1 + K + c₀)) * G ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith) hG2
  calc (1 + 3 * ((1 + K + c₀) * G ^ 2)) ^ m ≤ ((1 + 3 * (1 + K + c₀)) * G ^ 2) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
    _ ≤ ((1 + 3 * (1 + K + c₀)) * G ^ 2) ^ M := pow_le_pow_right₀ h2 hm
    _ = (1 + 3 * (1 + K + c₀)) ^ M * G ^ (2 * M) := by rw [mul_pow, ← pow_mul, mul_comm 2 M]

/-- **Long words**: the injected mean is `O(W⁻²)`. -/
theorem inj_long_mean {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hW : 1 ≤ W)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) {K c₀ CG : ℝ} (hK : 0 ≤ K) (hc₀ : 0 ≤ c₀)
    (hA : ∀ ℓ, (A ℓ).IsHermitian) (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K)
    (hc : ∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2)
    (hS : ∀ᵐ y ∂freshLaw W b, ∀ σ, ‖sepOf b E (freshTwoPortSchur E XX y) σ‖ ≤ 1) {M : ℕ}
    (hGM : Integrable (fun y => freshG b E XX y ^ (2 * M)) (freshLaw W b))
    (hCG : ∫ y, freshG b E XX y ^ (2 * M) ∂freshLaw W b ≤ CG)
    (x₀ x₁ : TraceLetter nT nI × Separator) (u : TraceWord nT nI) (hu : u.length + 5 ≤ M)
    (hic : Integrable (fun y => layerNew b E A c XX (x₀ :: x₁ :: u) y) (freshLaw W b))
    (hi0 : Integrable (fun y => layerNew b E A (fun _ => 0) XX (x₀ :: x₁ :: u) y) (freshLaw W b)) :
    ‖∫ y, layerNew b E A c XX (x₀ :: x₁ :: u) y ∂freshLaw W b -
        ∫ y, layerNew b E A (fun _ => 0) XX (x₀ :: x₁ :: u) y ∂freshLaw W b‖ ≤
      (M + 4) * (1 + 3 * (1 + K + c₀)) ^ M * CG / (W : ℝ) ^ 2 := by
  rw [← integral_sub hic hi0]
  set κ₀ := (M + 4) * (1 + 3 * (1 + K + c₀)) ^ M / (W : ℝ) ^ 2
  have hκ0 : 0 ≤ κ₀ := by positivity
  have hb : ∀ᵐ y ∂freshLaw W b, ‖layerNew b E A c XX (x₀ :: x₁ :: u) y -
      layerNew b E A (fun _ => 0) XX (x₀ :: x₁ :: u) y‖ ≤ κ₀ * freshG b E XX y ^ (2 * M) := by
    filter_upwards [hS] with y hy
    refine (newWord_long_sub_le hW A c _ _ _ hK hc₀ hA hAK hc hy x₀ x₁ u).trans ?_
    have hG1 : 1 ≤ freshG b E XX y := by
      simp only [freshG]; linarith [norm_nonneg (freshTransport b E XX y),
        norm_nonneg (freshD b E XX y)]
    have hl := lam_le hK hc₀ hG1 (m := u.length + 5) (M := M) hu
    have hul : (u.length : ℝ) + 4 ≤ M + 4 := by
      have : (u.length : ℝ) + 5 ≤ M := by exact_mod_cast hu
      linarith
    simp only [κ₀, div_eq_mul_inv]
    have hW2 : 0 ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
    calc (u.length + 4 : ℝ) * (1 + 3 * ((1 + K + c₀) * freshG b E XX y ^ 2)) ^ (u.length + 5) *
          ((W : ℝ) ^ 2)⁻¹ ≤ (M + 4) * ((1 + 3 * (1 + K + c₀)) ^ M * freshG b E XX y ^ (2 * M)) *
            ((W : ℝ) ^ 2)⁻¹ := by gcongr
      _ = _ := by ring
  refine (norm_integral_le_of_norm_le (hGM.const_mul κ₀) hb).trans ?_
  rw [integral_const_mul]
  calc κ₀ * ∫ y, freshG b E XX y ^ (2 * M) ∂freshLaw W b ≤ κ₀ * CG :=
        mul_le_mul_of_nonneg_left hCG hκ0
    _ = _ := by simp only [κ₀]; ring

/-- **The mean injection of one fresh layer.** -/
theorem inj_mean (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hIn : BlockBand.SourceProcess.ProjSeparator.InjNearMeanW2) (hIf : InjFarTrace) {b : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (d : ℕ) {K c₀ : ℝ} (hK : 0 ≤ K)
    (hc₀ : 0 ≤ c₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (q : Fin nI → ℝ → ℝ) (j : ℕ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        (∀ a x, |q a x| ≤ c₀) →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        Integrable (fun y => layerNew b E A (injCoef q W j) XX w y) (freshLaw W b) ∧
        Integrable (fun y => layerNew b E A (fun _ => 0) XX w y) (freshLaw W b) ∧
        ‖∫ y, layerNew b E A (injCoef q W j) XX w y ∂freshLaw W b -
            ∫ y, layerNew b E A (fun _ => 0) XX w y ∂freshLaw W b -
            (W : ℂ)⁻¹ * wordInjection b q (stepTime W j) w‖ ≤ C * layerErr b E s XX ^ 2 := by
  obtain ⟨CF, WF, -, hFr⟩ := layerFreshBound_holds hGA hLp b hb0 hb κ hκ d 1 K c₀ le_rfl hK hc₀
  obtain ⟨Cn, Wn, hCn, hn⟩ := hIn b hb0 hb κ hκ
  obtain ⟨Cf, Wf, hCf, hf⟩ := hIf b hb0 hb κ hκ
  obtain ⟨C2, W2, -, hG2⟩ := fresh_G_moment hGA hb0 hb hκ 2 (by norm_num)
  obtain ⟨CM, WM, hCM, hGM⟩ := fresh_G_moment hGA hb0 hb hκ (2 * (d + 3)) (by omega)
  refine ⟨c₀ * (Cn + Cf) + (((d + 3 : ℕ) : ℝ) + 4) * (1 + 3 * (1 + K + c₀)) ^ (d + 3) * CM,
    max (max (max WF Wn) (max Wf W2)) (max WM 1), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX nT nI A q j hA hAK hq w hw hwd
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWF, hWn⟩, hWf, hW2⟩, hWM, hW1⟩ := hW
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hg := FullSourceCovariance.conductance_nonneg b E hη.le
    (FullSource.nearSchur_passive hη hXX)
  obtain ⟨hδ0, -, hge, hWe, he0, hsum⟩ := layerErr_parts b E s XX hg (W := W)
  have hc := fun ℓ => injCoef_le (nT := nT) (W := W) hc₀ hq j ℓ
  have hc0 : ∀ ℓ : TraceLetter nT nI, |(fun _ => (0 : ℝ)) ℓ| ≤ c₀ / (W : ℝ) ^ 2 := fun _ => by
    simp only [abs_zero]; positivity
  have hZ : IsAdmittedProduct [w] := fun v hv => by
    simp only [List.mem_singleton] at hv; rw [hv]; exact hw.1
  have hd : productDegree [w] ≤ d := by simpa [productDegree] using hwd
  have hic : Integrable (fun y => layerNew b E A (injCoef q W j) XX w y) (freshLaw W b) :=
    (hFr W hWF E hE s hs XX hXX nT nI A (injCoef q W j) hA hAK hc [w] hZ hd).1.congr
      (Filter.Eventually.of_forall fun y => by simp [newProd, layerNew])
  have hi0 : Integrable (fun y => layerNew b E A (fun _ => 0) XX w y) (freshLaw W b) :=
    (hFr W hWF E hE s hs XX hXX nT nI A (fun _ => 0) hA hAK hc0 [w] hZ hd).1.congr
      (Filter.Eventually.of_forall fun y => by simp [newProd, layerNew])
  refine ⟨hic, hi0, ?_⟩
  have hR1 : 0 ≤ c₀ * (Cn + Cf) * layerErr b E s XX ^ 2 := by positivity
  have hR2 : 0 ≤ (((d + 3 : ℕ) : ℝ) + 4) * (1 + 3 * (1 + K + c₀)) ^ (d + 3) * CM *
      layerErr b E s XX ^ 2 := by positivity
  have hsplit : (c₀ * (Cn + Cf) + (((d + 3 : ℕ) : ℝ) + 4) * (1 + 3 * (1 + K + c₀)) ^ (d + 3) * CM) *
      layerErr b E s XX ^ 2 = c₀ * (Cn + Cf) * layerErr b E s XX ^ 2 +
        (((d + 3 : ℕ) : ℝ) + 4) * (1 + 3 * (1 + K + c₀)) ^ (d + 3) * CM *
          layerErr b E s XX ^ 2 := by ring
  rw [hsplit]
  rcases w with _ | ⟨⟨ℓ, s'⟩, _ | ⟨x₁, u⟩⟩
  · exact absurd rfl hw.1
  · have hs' := hw.2 _ (List.mem_singleton_self _)
    have hnb := hn W hWn E hE XX hXX
    simp only at hnb
    have hW2e : ((W : ℝ)⁻¹) ^ 2 ≤ (W : ℝ)⁻¹ := by
      have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
      nlinarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) W)]
    have hnb' : ‖(W : ℂ)⁻¹ * ∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * nearProjection W).trace
        ∂freshLaw W b - (dStar b : ℂ)‖ ≤ Cn * ((jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
          ((W : ℝ)⁻¹) ^ 2) + conductanceOf (passiveTransmission b E
            (nearSchur (boundaryZ b E) XX)) / W) := by
      refine hnb.trans_eq ?_; ring
    have hδe : jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2 +
        conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W ≤
          layerErr b E s XX := by linarith
    have h := inj_single_mean hW1 A q j hc₀ hq hCn hCf hg hδe hge hWe (hG2 W hW2 E hE XX hXX).1
      hnb' (hf W hWf E hE XX hXX) ℓ hs' hic hi0
    linarith
  · have hwi : wordInjection b q (stepTime W j) ((ℓ, s') :: x₁ :: u) = 0 := by
      cases ℓ <;> simp [wordInjection]
    rw [hwi, mul_zero, sub_zero]
    have hS := ae_sepOf_le hb0 hW1 hη hXX
    obtain ⟨hGMi, hGMb⟩ := hGM W hWM E hE XX hXX
    have hu : u.length + 5 ≤ d + 3 := by simp at hwd; omega
    have h := inj_long_mean hW1 A (injCoef q W j) hK hc₀ hA hAK hc hS hGMi hGMb (ℓ, s') x₁ u hu
      hic hi0
    refine h.trans ?_
    have hWe2 : ((W : ℝ) ^ 2)⁻¹ ≤ layerErr b E s XX ^ 2 := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hWe 2
    rw [div_eq_mul_inv]
    have : 0 ≤ (((d + 3 : ℕ) : ℝ) + 4) * (1 + 3 * (1 + K + c₀)) ^ (d + 3) * CM := by positivity
    have := mul_le_mul_of_nonneg_left hWe2 this
    linarith

end BlockBand.SourceProcess.ContractingWords
