module

public import BlockBand.Transmission.LawFinite.DriftScalar
public import BlockBand.Transmission.LawFinite.InjectionMean

/-!
# One-step reciprocal drift at an unabsorbed passive input

Hypothesis `PassiveBoundsStatement`, through the two-sided refined mass mean
`Generator.massMeanRefined_bulk` and `ml_fresh_bulk` (the identity `E q₊ = Re Tr(Q E[LL*])` and
the `L^n` fluctuation `‖q₊ - Eq₊‖_n ≤ C_n q/√W`).

**`reciprocal_core`**: `b, κ` first; then the domain radius `d > 0` and `C ≥ 0`; then `K, A > 0`;
then `C_{A,K}`, `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`, every passive `Z` with `δ₀(Z) ≤ d` and
`q = q(Z) > 0`: `E r_K(q(Z₊)) ≤ q⁻¹ + C(W⁻¹ + δ₀/q + (Wq)⁻¹) + C_{A,K}W^{-A}`.

Proof: `μ = E q₊` satisfies `|μ - q/(1+αq/W)| ≤ C(δ₀ + W⁻²)q` (`refinedErr_le_bulk`), so on the
domain `μ ≥ c₁q/2` and `μ⁻¹ ≤ q⁻¹ + C/W + C(δ₀ + W⁻²)/q`; `integral_recipK_le` with
`σ₂ = C₂q/√W`, `σ_N = C_Nq/√W`, `N = ⌈2A⌉ + 1`. The lower bound `q ≥ K` of the paper is not
needed here (only `q > 0`).
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
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `r_K(q₊) = r_K(qc₊)` almost surely (`X₊` is passive). -/
theorem integral_recipK_qc (b E K : ℝ) {Z : Matrix (Fin W) (Fin W) ℂ}
    (hZ : (passiveY Z).PosSemidef) :
    ∫ ω, recipK K (passiveMass b E (freshSchur E Z ω)) ∂freshLaw W b =
      ∫ ω, recipK K (qc b E (freshSchur E Z ω)) ∂freshLaw W b := by
  refine integral_congr_ae ?_
  filter_upwards [ae_layer_herm (W := W) b] with ω hA
  rw [qc_eq (PathScalar.passiveY_freshSchur E hZ ω hA)]

/-- `0 ≤ α ≤ Li/b` and `q ≤ WLi/4` (`η⁻¹ ≤ Li`). -/
theorem drift_bulk_aux {b E Li : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hLi : (etaZ b E)⁻¹ ≤ Li) (Z : Matrix (Fin W) (Fin W) ℂ) :
    0 ≤ alphaCoef b E ∧ alphaCoef b E ≤ Li / b ∧ passiveMass b E Z ≤ W * Li / 4 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hLe : 1 ≤ Li * etaZ b E := by
    have := mul_le_mul_of_nonneg_right hLi hη.le
    rwa [inv_mul_cancel₀ hη.ne'] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  · rw [alphaCoef, div_le_div_iff₀ (mul_pos hb0 hη) hb0]
    have hb1 : (1 - b) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · refine (passiveMass_le_width (by linarith) h1 h2 Z).trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : (W : ℝ) * 1 ≤ W * (Li * etaZ b E) :=
      mul_le_mul_of_nonneg_left hLe (Nat.cast_nonneg _)
    nlinarith

/-- The refined error on the bulk: `refinedErr ≤ (2Li + 3)(δ₀ + W⁻²)q` when `δ₀ + W⁻² ≤ 2`. -/
theorem refinedErr_le_bulk {b E Li : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hLi : (etaZ b E)⁻¹ ≤ Li) (hW : 1 ≤ W) (he : jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 ≤ 2) :
    refinedErr b E X ≤ (4 * Li + 6) * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) *
      passiveMass b E X := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hq := passiveMass_nonneg b E hY
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hτ : ‖(passiveQ b E X * passiveF b E X).trace‖ ≤ 3 / 2 * Li * passiveMass b E X := by
    have hf := PassiveCovariance.norm_passiveF_le hb0 hb h1 h2 hY
    have h3 : ‖(passiveQ b E X * passiveF b E X).trace‖ ≤ ‖passiveF b E X‖ * passiveMass b E X := by
      rw [trace_mul_comm]
      exact PassiveCovariance.norm_trace_mul_posSemidef_le (hY.conjTranspose_mul_mul_same _) _
    have h4 : 3 / (2 * etaZ b E) ≤ 3 / 2 * Li := by
      rw [show 3 / (2 * etaZ b E) = 3 / 2 * (etaZ b E)⁻¹ by field_simp]
      exact mul_le_mul_of_nonneg_left hLi (by norm_num)
    exact h3.trans (mul_le_mul_of_nonneg_right (hf.trans h4) hq)
  have hqW := (drift_bulk_aux hb0 hb h1 h2 hLi X).2.2
  have he0 : 0 ≤ jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 := add_nonneg (norm_nonneg _) (by positivity)
  have := drift_err_le he0 he hq hW1 hτ hqW (norm_nonneg _)
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have h5 : (2 * Li + 3) * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ ^ 2) *
      passiveMass b E X ≤ (4 * Li + 6) * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) *
      passiveMass b E X := by
    have h6 : jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ ^ 2 ≤
        2 * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
      have := norm_nonneg ((W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E)
      unfold jetDistance0; linarith
    have := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 2 * Li + 3)
    have := mul_le_mul_of_nonneg_right this hq
    linarith
  unfold refinedErr
  linarith

/-- Final scalar step of `reciprocal_core` (pure). -/
theorem core_scalar {m q W δ e Li b Kr c₁ C₂ CN K A : ℝ} {N : ℕ} (hq : 0 < q) (hW : 1 ≤ W)
    (hc₁ : 0 < c₁) (hK : 0 < K) (hKr : 0 ≤ Kr) (hCN : 0 ≤ CN) (hLib : 0 ≤ Li / b)
    (hδ : 0 ≤ δ) (he : e = δ + W⁻¹ ^ 2) (hmlo : c₁ * q / 2 ≤ m) (hAN : A ≤ N / 2)
    (hinv : m⁻¹ ≤ q⁻¹ + Li / b * W⁻¹ + 2 * Kr / c₁ ^ 2 * (e / q)) :
    m⁻¹ + 2 * (C₂ * q / Real.sqrt W) ^ 2 / m ^ 3 + K⁻¹ * (2 * (CN * q / Real.sqrt W) / m) ^ N ≤
      q⁻¹ + (Li / b + 2 * Kr / c₁ ^ 2 + 16 * C₂ ^ 2 / c₁ ^ 3) *
        (W⁻¹ + δ / q + (W * q)⁻¹) + K⁻¹ * (4 * CN / c₁) ^ N * W ^ (-A) := by
  have hW0 : 0 < W := by linarith
  have hv := drift_var_le (C₂ := C₂) hq hW0 hc₁ hmlo
  have ht := drift_tail_le (CN := CN) hq hW hc₁ hCN hmlo hAN
  have hK0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hK.le
  have ht' : K⁻¹ * (2 * (CN * q / Real.sqrt W) / m) ^ N ≤ K⁻¹ * (4 * CN / c₁) ^ N * W ^ (-A) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ht hK0
  have heq : e / q ≤ δ / q + (W * q)⁻¹ := by
    rw [he, add_div]
    have : W⁻¹ ^ 2 / q ≤ (W * q)⁻¹ := by
      rw [mul_inv, sq, div_eq_mul_inv]
      have : W⁻¹ * W⁻¹ ≤ W⁻¹ := mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hW)
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  have hC2 : 2 * Kr / c₁ ^ 2 * (e / q) ≤ 2 * Kr / c₁ ^ 2 * (δ / q + (W * q)⁻¹) :=
    mul_le_mul_of_nonneg_left heq (by positivity)
  have hδq : 0 ≤ δ / q := div_nonneg hδ hq.le
  have hWq : 0 ≤ (W * q)⁻¹ := by positivity
  have hWi : 0 ≤ W⁻¹ := by positivity
  have a' : 0 ≤ 2 * Kr / c₁ ^ 2 := by positivity
  have a'' : 0 ≤ 16 * C₂ ^ 2 / c₁ ^ 3 := by positivity
  have hfin : Li / b * W⁻¹ + 2 * Kr / c₁ ^ 2 * (δ / q + (W * q)⁻¹) +
      16 * C₂ ^ 2 / c₁ ^ 3 * (W * q)⁻¹ ≤
      (Li / b + 2 * Kr / c₁ ^ 2 + 16 * C₂ ^ 2 / c₁ ^ 3) * (W⁻¹ + δ / q + (W * q)⁻¹) := by
    nlinarith
  linarith

/-- **One-step reciprocal drift, unabsorbed passive input, bulk-uniform.** -/
theorem reciprocal_core (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧ ∀ K A : ℝ, 0 < K → 0 < A →
      ∃ (CA : ℝ) (W₀ : ℕ), 0 ≤ CA ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ Z : Matrix (Fin W) (Fin W) ℂ, (passiveY Z).PosSemidef →
          jetDistance0 b E Z ≤ d → 0 < passiveMass b E Z →
            ∫ ω, recipK K (passiveMass b E (freshSchur E Z ω)) ∂freshLaw W b ≤
              (passiveMass b E Z)⁻¹ + C * ((W : ℝ)⁻¹ + jetDistance0 b E Z / passiveMass b E Z +
                ((W : ℝ) * passiveMass b E Z)⁻¹) + CA * (W : ℝ) ^ (-A) := by
  obtain ⟨Cr, Wr, hCr, hMR⟩ := massMeanRefined_bulk hA hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, hF2⟩ := ml_fresh_bulk hA hb0 hb hκ 2 (by norm_num)
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κ)⁻¹
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hηL).le
  set c₁ := (1 + Li ^ 2 / (4 * b))⁻¹
  have hc₁ : 0 < c₁ := by positivity
  set Kr := Cr * (4 * Li + 6)
  have hKr : 0 ≤ Kr := by positivity
  set d := min (c₁ / (4 * (Kr + 1))) 1
  have hd : 0 < d := lt_min (by positivity) one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hKd : Kr * (2 * d) ≤ c₁ / 2 := by
    have hd4 : d ≤ c₁ / (4 * (Kr + 1)) := min_le_left _ _
    have : Kr * (2 * d) ≤ Kr * (2 * (c₁ / (4 * (Kr + 1)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hKr
    refine this.trans ?_
    rw [show Kr * (2 * (c₁ / (4 * (Kr + 1)))) = c₁ / 2 * (Kr / (Kr + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr (by linarith))
  refine ⟨d, Li / b + 2 * Kr / c₁ ^ 2 + 16 * C₂ ^ 2 / c₁ ^ 3, hd, by positivity,
    fun K A hK hA0 => ?_⟩
  set N : ℕ := ⌈2 * A⌉₊ + 1
  have hN : 1 ≤ N := by omega
  have hAN : A ≤ (N : ℝ) / 2 := by
    have := Nat.le_ceil (2 * A)
    have : ((⌈2 * A⌉₊ + 1 : ℕ) : ℝ) = (⌈2 * A⌉₊ : ℝ) + 1 := by push_cast; ring
    simp only [N]; linarith
  obtain ⟨CN, WN, hCN, hFN⟩ := ml_fresh_bulk hA hb0 hb hκ N hN
  have hCN0 : 0 ≤ CN := by linarith
  refine ⟨K⁻¹ * (4 * CN / c₁) ^ N, max (max Wr W₂) (max WN ⌈d⁻¹⌉₊),
    by positivity, fun W hW E hE Z hZ hδ hq => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWr, hW₂⟩, hWN, hWd⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hdinv : 1 ≤ d⁻¹ := (one_le_inv₀ hd).mpr hd1
  have hW1r : (1 : ℝ) ≤ W := hdinv.trans ((Nat.le_ceil _).trans (by exact_mod_cast hWd))
  have hW1 : 1 ≤ W := by exact_mod_cast hW1r
  have hWpos : (0 : ℝ) < W := by linarith
  have hWinv : (W : ℝ)⁻¹ ≤ d := by
    rw [inv_le_comm₀ hWpos hd]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d := Generator.rf_Wsq hW1r hWinv
  have hδ0 : 0 ≤ jetDistance0 b E Z := norm_nonneg _
  have he2 : jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2 ≤ 2 * d := by linarith
  have hKe : Kr * (jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2) ≤ c₁ / 2 :=
    (mul_le_mul_of_nonneg_left he2 hKr).trans hKd
  -- the mean
  obtain ⟨hmean2, hfl2⟩ := hF2 W hW₂ E hE Z hZ
  obtain ⟨-, hflN⟩ := hFN W hWN E hE Z hZ
  have hMRb := hMR W hWr E hE Z hZ
  rw [← hmean2] at hMRb
  have hErr := refinedErr_le_bulk hb0 hb h1 h2 hZ hLi hW1 (by linarith)
  have hm' : |(∫ ω, qc b E (freshSchur E Z ω) ∂freshLaw W b) - passiveMass b E Z /
      (1 + alphaCoef b E * passiveMass b E Z / W)| ≤
      Kr * (jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2) * passiveMass b E Z := by
    refine hMRb.trans ?_
    calc Cr * refinedErr b E Z ≤ Cr * ((4 * Li + 6) * (jetDistance0 b E Z + (W : ℝ)⁻¹ ^ 2) *
          passiveMass b E Z) := mul_le_mul_of_nonneg_left hErr hCr
      _ = _ := by ring
  obtain ⟨hα0, hα, hqW⟩ := drift_bulk_aux hb0 hb h1 h2 hLi Z
  obtain ⟨hmlo, hm0⟩ := drift_mean_lower hq hWpos hb0 hα0 hα hqW hm' hKe
  have hmpos : 0 < ∫ ω, qc b E (freshSchur E Z ω) ∂freshLaw W b :=
    lt_of_lt_of_le (by positivity) hmlo
  have hinv := drift_inv_mean_le hq hWpos hc₁ hα0 hα hm' hmlo hm0
  -- the probabilistic bound
  rw [integral_recipK_qc b E K hZ]
  have hσ₂ : 0 ≤ C₂ / Real.sqrt W * passiveMass b E Z := by
    have : 0 ≤ C₂ := by linarith
    positivity
  have hσN : 0 ≤ CN / Real.sqrt W * passiveMass b E Z := by positivity
  have hfl2' : eLpNorm (fun ω => qc b E (freshSchur E Z ω) -
      ∫ ω', qc b E (freshSchur E Z ω') ∂freshLaw W b) 2 (freshLaw W b) ≤
      ENNReal.ofReal (C₂ / Real.sqrt W * passiveMass b E Z) := by
    simpa only [Nat.cast_ofNat] using hfl2
  have hP := integral_recipK_le (μ := freshLaw W b) (measurable_qc_fresh b E Z)
    (fun ω => qc_nonneg b E _) hN hK hmpos hσ₂ hσN rfl hfl2' hflN
  refine hP.trans ?_
  have e1 : C₂ / Real.sqrt W * passiveMass b E Z = C₂ * passiveMass b E Z / Real.sqrt W := by
    ring
  have e2 : CN / Real.sqrt W * passiveMass b E Z = CN * passiveMass b E Z / Real.sqrt W := by
    ring
  rw [e1, e2]
  exact core_scalar hq hW1r hc₁ hK hKr hCN0 (by positivity) hδ0 rfl hmlo hAN hinv

end BlockBand.Transmission.LawFinite
