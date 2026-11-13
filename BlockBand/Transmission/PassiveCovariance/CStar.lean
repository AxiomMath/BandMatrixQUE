module

public import BlockBand.Transmission.PassiveCovariance.VTrace

/-!
# `⟨RR*RR*⟩ = C_* + O(δ)` and `⟨MMᴴMMᴴ⟩ = C_* + O(ε)`

Deterministic part: for strictly passive `X` (`Y ⪰ 0`), `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, `W ≠ 0`,
every `s`; then, under `PassiveBoundsStatement` (law `layerLaw W b .oneBlockOnePort`), the dressed
matrix `M`.

* **`normTrace_RRsRRs_sub_le`**: `|⟨RR*RR*⟩ - C_*| ≤ (K_C + 2/η³)(δ₀ + δ₁ + q/W)`. Proof: Ward's
  identity `RR* = c₀(R* - R) - Q̃/η` (`resolvent_mul_adj`) applied to the first factor of `RR*·RR*`
  and to the middle factor of `R·RR*·R*` gives the same `c₀`-terms (cyclicity), so
  `⟨RR*RR*⟩ - ⟨R²R*²⟩ = η⁻¹(⟨RQ̃R*⟩ - ⟨Q̃RR*⟩)`, `|·| ≤ 2η⁻³q/W`; then
  `normTrace_R2Rstar2_sub_le`. (`⟨RR*RR*⟩` and `⟨R²R*²⟩` differ when `X` is not normal; only their
  difference is small.)
* `norm_mul4_sub_le`; **`cq_matched`**: `|⟨MMᴴMMᴴ⟩ - C_*| ≤ C·epsOf` (`matchedBasic`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **`⟨RR*RR*⟩ = C_* + O(δ₀ + δ₁ + q/W)`.** -/
theorem normTrace_RRsRRs_sub_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) (hW : W ≠ 0) (s : ℂ) :
    ‖(W : ℂ)⁻¹ * (passiveResolvent b E X * (passiveResolvent b E X)ᴴ *
        (passiveResolvent b E X * (passiveResolvent b E X)ᴴ)).trace - jetC b E s‖ ≤
      (constC b E + 2 / etaZ b E ^ 3) *
        (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W) := by
  have hηpos := etaZ_pos b E (by linarith) h1 h2
  have hRR := resolvent_mul_adj hb0 hb h1 h2 hY
  have hQtr0 := trace_tildeQ hb0 hb h1 h2 hY
  have hC := normTrace_R2Rstar2_sub_le hb0 hb h1 h2 hY hW s
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hQt : (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ).PosSemidef :=
    hY.mul_mul_conjTranspose_same _
  set R := passiveResolvent b E X
  set Qt := R * passiveY X * Rᴴ
  have hQtr : Qt.trace.re = passiveMass b E X := by rw [hQtr0]; rfl
  have hq := passiveMass_nonneg b E hY
  have e1 : R * Rᴴ * (R * Rᴴ) = cZero b E • (Rᴴ * (R * Rᴴ)) - cZero b E • (R * (R * Rᴴ)) -
      (etaZ b E : ℂ)⁻¹ • (Qt * (R * Rᴴ)) := by
    calc R * Rᴴ * (R * Rᴴ) = (cZero b E • (Rᴴ - R) - (etaZ b E : ℂ)⁻¹ • Qt) * (R * Rᴴ) := by
          rw [← hRR]
      _ = _ := by simp only [Matrix.sub_mul, Matrix.smul_mul, smul_sub]
  have e2 : R * R * Rᴴ * Rᴴ = cZero b E • (R * Rᴴ * Rᴴ) - cZero b E • (R * R * Rᴴ) -
      (etaZ b E : ℂ)⁻¹ • (R * Qt * Rᴴ) := by
    conv_lhs => rw [Matrix.mul_assoc R R, hRR]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
      smul_sub]
  have c1 : (Rᴴ * (R * Rᴴ)).trace = (R * Rᴴ * Rᴴ).trace := by rw [Matrix.trace_mul_comm]
  have c2 : (R * (R * Rᴴ)).trace = (R * R * Rᴴ).trace := by rw [Matrix.mul_assoc]
  have key : (W : ℂ)⁻¹ * (R * Rᴴ * (R * Rᴴ)).trace - jetC b E s =
      ((W : ℂ)⁻¹ * (R * R * Rᴴ * Rᴴ).trace - jetC b E s) +
        (etaZ b E : ℂ)⁻¹ * ((W : ℂ)⁻¹ * (R * Qt * Rᴴ).trace - (W : ℂ)⁻¹ * (Qt * (R * Rᴴ)).trace) := by
    rw [e1, e2, trace_sub, trace_sub, trace_sub, trace_sub, trace_smul, trace_smul, trace_smul,
      trace_smul, trace_smul, trace_smul, c1, c2]
    simp only [smul_eq_mul]; ring
  have hRR2 : ‖R‖ * ‖R‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
    rw [pow_two]; exact mul_le_mul hR hR (norm_nonneg _) (by positivity)
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  have tr_le : ∀ A : Matrix (Fin W) (Fin W) ℂ, ‖A‖ ≤ (etaZ b E)⁻¹ ^ 2 →
      ‖(W : ℂ)⁻¹ * (A * Qt).trace‖ ≤ (etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W) := fun A hA => by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h := norm_trace_mul_posSemidef_le hQt A
    rw [hQtr] at h
    calc (W : ℝ)⁻¹ * ‖(A * Qt).trace‖ ≤ (W : ℝ)⁻¹ * ((etaZ b E)⁻¹ ^ 2 * passiveMass b E X) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hA hq)) (by positivity)
      _ = _ := by ring
  have t1 : ‖(W : ℂ)⁻¹ * (R * Qt * Rᴴ).trace‖ ≤ (etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W) := by
    rw [show (R * Qt * Rᴴ).trace = (Rᴴ * R * Qt).trace by rw [trace_mul_comm, ← Matrix.mul_assoc]]
    refine tr_le _ ?_
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]; exact hRR2
  have t2 : ‖(W : ℂ)⁻¹ * (Qt * (R * Rᴴ)).trace‖ ≤ (etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W) := by
    rw [trace_mul_comm]
    refine tr_le _ ((Matrix.l2_opNorm_mul _ _).trans ?_)
    rw [Matrix.l2_opNorm_conjTranspose]; exact hRR2
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W
  have hd0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hd1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hqW : passiveMass b E X / W ≤ δ := by simp only [δ]; linarith
  have n2 : ‖(etaZ b E : ℂ)⁻¹ * ((W : ℂ)⁻¹ * (R * Qt * Rᴴ).trace -
      (W : ℂ)⁻¹ * (Qt * (R * Rᴴ)).trace)‖ ≤ 2 / etaZ b E ^ 3 * δ := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    have h := (norm_sub_le _ _).trans (add_le_add t1 t2)
    have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hηpos.le)
    have e : (etaZ b E)⁻¹ * ((etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W) +
        (etaZ b E)⁻¹ ^ 2 * (passiveMass b E X / W)) = 2 / etaZ b E ^ 3 * (passiveMass b E X / W) := by
      field_simp; ring
    rw [e] at h'
    exact h'.trans (mul_le_mul_of_nonneg_left hqW (by positivity))
  rw [key, add_mul]
  exact (norm_add_le _ _).trans (add_le_add hC n2)

theorem norm_mul4_sub_le (A B C D A' B' C' D' : Matrix (Fin W) (Fin W) ℂ) {Λ ε : ℝ}
    (hB : ‖B‖ ≤ Λ) (hC : ‖C‖ ≤ Λ) (hD : ‖D‖ ≤ Λ) (hA' : ‖A'‖ ≤ Λ) (hB' : ‖B'‖ ≤ Λ) (hC' : ‖C'‖ ≤ Λ)
    (h₁ : ‖A - A'‖ ≤ ε) (h₂ : ‖B - B'‖ ≤ ε) (h₃ : ‖C - C'‖ ≤ ε) (h₄ : ‖D - D'‖ ≤ ε) :
    ‖A * B * C * D - A' * B' * C' * D'‖ ≤ 4 * Λ ^ 3 * ε := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hB
  have hε : 0 ≤ ε := (norm_nonneg _).trans h₁
  have e : A * B * C * D - A' * B' * C' * D' = (A - A') * B * C * D + A' * (B - B') * C * D +
      A' * B' * (C - C') * D + A' * B' * C' * (D - D') := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  have m : ∀ (P Q S T : Matrix (Fin W) (Fin W) ℂ) (p q r t : ℝ), ‖P‖ ≤ p → ‖Q‖ ≤ q → ‖S‖ ≤ r →
      ‖T‖ ≤ t → 0 ≤ q → 0 ≤ r → 0 ≤ t → ‖P * Q * S * T‖ ≤ p * q * r * t :=
    fun P Q S T p q r t hP hQ hS hT hq hr ht => by
      have hp : 0 ≤ p := (norm_nonneg _).trans hP
      refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hP hQ (norm_nonneg _) hp))
          hS (norm_nonneg _) (by positivity))) hT (norm_nonneg _) (by positivity))
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (m _ _ _ _ _ _ _ _ h₁ hB hC hD hΛ hΛ hΛ) (m _ _ _ _ _ _ _ _ hA' h₂ hC hD hε hΛ hΛ)))
    (m _ _ _ _ _ _ _ _ hA' hB' h₃ hD hΛ hε hΛ))) (m _ _ _ _ _ _ _ _ hA' hB' hC' h₄ hΛ hΛ hε)).trans
    (le_of_eq (by ring))

/-- **`⟨MMᴴMMᴴ⟩ ↦ C_*`.** -/
theorem cq_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖(W : ℂ)⁻¹ * (SourceMixing.mOf b E X * ((SourceMixing.mOf b E X)ᴴ *
          (SourceMixing.mOf b E X * (SourceMixing.mOf b E X)ᴴ))).trace - jetC b E s‖ ≤
          C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  set Λ := Cb + (etaZ b E)⁻¹
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨d₀, 4 * Λ ^ 3 * Cb + (constC b E + 2 / etaZ b E ^ 3), max Wb 1, hd₀, ?_,
    fun W hW X hX hd => ?_⟩
  · have := constB_nonneg (b := b) (E := E) hb0 hb h1 h2
    have : 0 ≤ constC b E := by unfold constC; positivity
    positivity
  obtain ⟨hM, -, hR, -, hMR, -⟩ := hmb W (le_trans (le_max_left _ _) hW) X hX hd
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hC := normTrace_RRsRRs_sub_le hb0 hb h1 h2 hX.posSemidef (by omega) s
  obtain ⟨-, -, -, -, he⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
  set e := SourceMixing.epsOf b E s X
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  have hM' : ‖M‖ ≤ Λ := hM.trans (by simp only [Λ]; linarith [inv_nonneg.mpr hη.le])
  have hR' : ‖R‖ ≤ Λ := hR.trans (by simp only [Λ]; linarith)
  have hMh : ‖Mᴴ‖ ≤ Λ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM'
  have hRh : ‖Rᴴ‖ ≤ Λ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hR'
  have hMRh : ‖Mᴴ - Rᴴ‖ ≤ Cb * e := by rw [SourceMixing.norm_conjTranspose_sub]; exact hMR
  have h4 := norm_mul4_sub_le M Mᴴ M Mᴴ R Rᴴ R Rᴴ hMh hM' hMh hR' hRh hR' hMR hMRh hMR hMRh
  have eM : M * (Mᴴ * (M * Mᴴ)) = M * Mᴴ * M * Mᴴ := by simp only [Matrix.mul_assoc]
  have eR : R * Rᴴ * (R * Rᴴ) = R * Rᴴ * R * Rᴴ := by simp only [Matrix.mul_assoc]
  rw [eR] at hC
  have hd : ‖(W : ℂ)⁻¹ * (M * Mᴴ * M * Mᴴ).trace - (W : ℂ)⁻¹ * (R * Rᴴ * R * Rᴴ).trace‖ ≤
      4 * Λ ^ 3 * (Cb * e) := by
    rw [← mul_sub, ← trace_sub]; exact (norm_normTrace_le _).trans h4
  have hC0 : 0 ≤ constC b E + 2 / etaZ b E ^ 3 := by
    have := constB_nonneg (b := b) (E := E) hb0 hb h1 h2
    have : 0 ≤ constC b E := by unfold constC; positivity
    positivity
  rw [eM]
  calc _ ≤ ‖(W : ℂ)⁻¹ * (M * Mᴴ * M * Mᴴ).trace - (W : ℂ)⁻¹ * (R * Rᴴ * R * Rᴴ).trace‖ +
        ‖(W : ℂ)⁻¹ * (R * Rᴴ * R * Rᴴ).trace - jetC b E s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * Λ ^ 3 * (Cb * e) + (constC b E + 2 / etaZ b E ^ 3) * e :=
        add_le_add hd (hC.trans (mul_le_mul_of_nonneg_left he hC0))
    _ = _ := by ring

end BlockBand.Transmission.PassiveCovariance
