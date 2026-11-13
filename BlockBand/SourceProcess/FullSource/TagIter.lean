module

public import BlockBand.SourceProcess.FullSource.TagStep

/-!
# Iterating the tag recursion; crude growth; removing the stops

Iteration gives the stopped tag bounds; crude unconditional fresh product moments grow at most as
`C_p^{j+1}`; Hölder and the superexponential exit probability remove every stop.

* `stopped_tag_iter`: `E[1_{G_{k+1+m}}Z_{k+1+m}] ≤ (1 + α/W)^m E[1_{G_{k+1}}Z_{k+1}]`;
* `crude_tag_step`: `E t_{j+1}^q ≤ C_N^{2q} E t_j^q` (no stopping); it is iterated to
  `E t_{k+1+m}^q ≤ (C_N^{2q})^m E t_{k+1}^q` in the sibling module (`crude_tag_iter`), where the stops
  are also removed (`stop_removal`: `E t_j^n ≤ E[1_{G_j}Z_j] + (E t_j^{2n})^{1/2} μ(G_jᶜ)^{1/2}`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

theorem measurable_tagMass (b E : ℝ) (j k : ℕ) : Measurable (tagMass b E W j k) := by
  have hS := (measurable_pastS (W := W) b E j k).comp (measurable_pastCoords W j)
  have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
  have e : tagMass b E W j k = fun ω => (W : ℝ)⁻¹ * ((pastS b E W j k (pastCoords W j ω))ᴴ *
      pastS b E W j k (pastCoords W j ω)).trace.re := by
    funext ω; exact tagMass_eq_past b E j k ω
  rw [e]
  refine measurable_const.mul (Complex.measurable_re.comp ?_)
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.measurable_sum _ fun i _ => hT.eval_matrix

/-- **Iteration of the stopped step.** -/
theorem stopped_tag_iter {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {n k : ℕ} (hW : 1 ≤ W) (hn : 2 ≤ n)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W n Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lcoef Ca n ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lcoef Ca n * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (m : ℕ) :
    ∫⁻ ω, (stopEv b E W k d (k + 1 + m)).indicator (tagWeight b E W k n K (k + 1 + m)) ω
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) ^ m *
        ∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (tagWeight b E W k n K (k + 1)) ω
          ∂growthPathLaw W b := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := stopped_tag_step hb0 hb hE1 hE2 (k := k) (j := k + 1 + m) hW hn (by omega) hL hCa hC₂ hCn hCN
      hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hdd₀
    rw [show k + 1 + (m + 1) = k + 1 + m + 1 by omega]
    refine h.trans ?_
    rw [pow_succ, mul_comm (ENNReal.ofReal _ ^ m), mul_assoc]
    exact mul_le_mul_of_nonneg_left ih (zero_le)

/-- **One crude step**: `E t_{j+1}^q ≤ C_N^{2q} E t_j^q` from `‖‖N‖‖_{2q} ≤ C_N`. -/
theorem crude_tag_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {q k j : ℕ} (hW : 1 ≤ W) (hq : 1 ≤ q) (hkj : k + 1 ≤ j) {CN : ℝ} (hCN : 0 ≤ CN)
    (hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal ((2 * q : ℕ) : ℝ))
        (freshLaw W b) ≤ ENNReal.ofReal CN) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W (j + 1) k ω ^ q) ∂growthPathLaw W b ≤
      ENNReal.ofReal (CN ^ (2 * q)) *
        ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ q) ∂growthPathLaw W b := by
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun q' =>
    ENNReal.ofReal (tagPlus b E (pastXX E W j q'.1) (pastS b E W j k q'.1) q'.2 ^ q)
  set Ψ : PastSample W j → ℝ≥0∞ := fun p => ENNReal.ofReal (CN ^ (2 * q)) *
    ENNReal.ofReal (((W : ℝ)⁻¹ * ((pastS b E W j k p)ᴴ * pastS b E W j k p).trace.re) ^ q)
  have hmΦ : Measurable Φ := by
    have hXX : Measurable fun q' : PastSample W j × LayerSample W .oneBlockOnePort =>
        pastXX E W j q'.1 := (measurable_pastXX E j).comp measurable_fst
    have hN' := measurable_freshTransport_comp b E hXX measurable_snd
    have hSN := measurable_matrix_mul' ((measurable_pastS b E j k).comp measurable_fst) hN'
    have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hSN) hSN
    refine ((measurable_const.mul ?_).pow_const q).ennreal_ofReal
    simp only [Matrix.trace, Matrix.diag]
    exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hT.eval_matrix)
  have hmΨ : Measurable Ψ := by
    have hS := measurable_pastS (W := W) b E j k
    have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
    refine measurable_const.mul (((measurable_const.mul ?_).pow_const q).ennreal_ofReal)
    simp only [Matrix.trace, Matrix.diag]
    exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hT.eval_matrix)
  have hZ : ∀ᵐ ω ∂growthPathLaw W b, pastCoords W j ω ∈ (Set.univ : Set (PastSample W j)) →
      ENNReal.ofReal (tagMass b E W (j + 1) k ω ^ q) ≤ Φ (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_tagResponse_succ_full hb0 hb hE1 hE2 hW] with ω h1 _
    refine le_of_eq ?_
    simp only [Φ]
    congr 2
    rw [tagMass, h1 j (by omega) k (by omega), tagResponse_eq_factor, transportN, pastXX_eq,
      tagPlus, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ (Set.univ : Set (PastSample W j)) →
      ∫⁻ f, Φ (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with p hp _
    obtain ⟨hi, hb'⟩ := tagStep_crude_moment (pastXX E W j p) (pastS b E W j k p) hq hCN
      (hN _ (pastXX_isHermitian E hp))
    simp only [Φ, Ψ]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun f =>
      pow_nonneg (tagPlus_nonneg _ _ _ _ _) q), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hb'
  have h := lintegral_indicator_step (μ := growthPathLaw W b) (μP := pastLaw W j b)
    (ν := freshLaw W b) (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) MeasurableSet.univ hmΦ hmΨ hZ hstep
  simp only [Set.preimage_univ, Set.indicator_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_const_mul]
  · congr 1; funext ω; simp only [Ψ, tagMass_eq_past]
  · exact ((measurable_tagMass b E j k).pow_const q).ennreal_ofReal

end BlockBand.SourceProcess.FullSource
