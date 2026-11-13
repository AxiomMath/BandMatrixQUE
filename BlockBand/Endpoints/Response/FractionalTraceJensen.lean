module

public import BlockBand.Endpoints.Response.FractionalTraceJensenMatrix
public import BlockBand.Endpoints.Response.ClockEntranceOnePort

/-!
# The fractional-trace Jensen gap

This file proves `FractionalTraceJensenGap` (`fractionalTraceJensenGap_holds`) with no hypotheses:
for `0 < p < 1`, a PSD random matrix `B` dominated by `V diag(q) V*` on an event `G` and in mean,
the strict concavity of `Tr(·)^p` gives
`E Tr B^p + c ∫_G Σ_{ij} |(V*(B - EB)V)_ij|² ∫_0^∞ s^{p-1}ds/((q_i+s)(q_j+s)) ≤ Tr (EB)^p`,
with `c = p / (16 K_p)`, `K_p = ∫_0^∞ s^{p-1}/(1+s) ds`. The proof first proves a regularized gap
with the kernel at `q + ε` (`ftj_regularized`) and then lets `ε ↓ 0` (`ftj_main`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The regularized gap (fixed `ε > 0`), with constant `p/(4K_p)`, kernel at `q + ε`, and the
right side `Tr(EB)^p + nε^p`. -/
theorem ftj_regularized {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → Matrix ι ι ℂ) (V : Matrix ι ι ℂ) (q : ι → ℝ) (G : Set Ω)
    (hB : ∀ ω, (B ω).PosSemidef) (hBint : ∀ a b, Integrable (fun ω => B ω a b) μ)
    (hG : MeasurableSet G) (hV : V ∈ unitaryGroup ι ℂ) (hq : ∀ i, 0 ≤ q i)
    (hMQ : (ftj_spec V q - matrixExpect μ B).PosSemidef)
    (hBQ : ∀ ω ∈ G, (ftj_spec V q - B ω).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω, ENNReal.ofReal (fracTrace p (B ω)) ∂μ +
        ENNReal.ofReal (p / (4 * ftj_resolventConst p)) * ∫⁻ ω in G, ENNReal.ofReal (∑ i, ∑ j,
          ‖(star V * (B ω - matrixExpect μ B) * V) i j‖ ^ 2 *
            ∫ s in Ioi (0 : ℝ), concavityKernel p (q i + ε) (q j + ε) s) ∂μ ≤
      ENNReal.ofReal (fracTrace p (matrixExpect μ B) + Fintype.card ι * ε ^ p) := by
  set M := matrixExpect μ B with hMdef
  have hK : 0 < ftj_resolventConst p := ftj_resolventConst_pos hp0 hp1
  set c₀ := p / (4 * ftj_resolventConst p) with hc₀def
  have hc₀ : 0 ≤ c₀ := by positivity
  have hMpsd : M.PosSemidef := opg_matrixExpect_posSemidef μ hB hBint
  have hMh := hMpsd.isHermitian
  set U : Matrix ι ι ℂ := (hMh.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : U ∈ unitaryGroup ι ℂ := (hMh.eigenvectorUnitary).2
  set lam := hMh.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := fun i => hMpsd.eigenvalues_nonneg i
  set x : ι → ℝ := fun i => lam i + ε with hxdef
  have hx : ∀ i, 0 < x i := fun i => by have := hlam i; simp only [hxdef]; linarith
  have hX : ftj_spec U x = M + (ε : ℂ) • 1 := by
    rw [hxdef, ftj_spec_add_const hU, ← ftj_spec_eigen hMh]
  set D := ftj_grad p U x
  have hqε : ∀ i, 0 < q i + ε := fun i => by linarith [hq i]
  have hQ' : ftj_spec V (fun i => q i + ε) = ftj_spec V q + (ε : ℂ) • 1 :=
    ftj_spec_add_const hV q ε
  have hXQ : (ftj_spec V (fun i => q i + ε) - ftj_spec U x).PosSemidef := by
    rw [hQ', hX]; convert hMQ using 1; abel
  set gap : Ω → ℝ := fun ω => ∑ i, ∑ j, ‖(star V * (B ω - M) * V) i j‖ ^ 2 *
      ∫ s in Ioi (0 : ℝ), concavityKernel p (q i + ε) (q j + ε) s with hgapdef
  set g : Ω → ℝ := fun ω => ∑ i, x i ^ p + (D * (B ω - M)).trace.re with hgdef
  have hgap0 : ∀ ω, 0 ≤ gap ω := fun ω =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Ioi fun s hs =>
        concavityKernel_nonneg (hqε i).le (hqε j).le (le_of_lt hs))
  -- pathwise bound
  have hpath : ∀ ω, fracTrace p (B ω) + G.indicator (fun ω => c₀ * gap ω) ω ≤ g ω := by
    intro ω
    have hBh := (hB ω).isHermitian
    set W : Matrix ι ι ℂ := (hBh.eigenvectorUnitary : Matrix ι ι ℂ)
    have hW : W ∈ unitaryGroup ι ℂ := (hBh.eigenvectorUnitary).2
    set β := hBh.eigenvalues
    have hβ : ∀ j, 0 ≤ β j := fun j => (hB ω).eigenvalues_nonneg j
    set y : ι → ℝ := fun j => β j + ε with hydef
    have hy : ∀ j, 0 ≤ y j := fun j => by have := hβ j; simp only [hydef]; linarith
    have hY : ftj_spec W y = B ω + (ε : ℂ) • 1 := by
      rw [hydef, ftj_spec_add_const hW, ← ftj_spec_eigen hBh]
    have hYX : ftj_spec W y - ftj_spec U x = B ω - M := by rw [hY, hX]; abel
    have hfr : fracTrace p (B ω) ≤ ∑ j, y j ^ p := by
      rw [fracTrace_eq_sum_eigenvalues_of_posSemidef (hB ω)]
      exact Finset.sum_le_sum fun j _ =>
        Real.rpow_le_rpow (hβ j) (by simp only [hydef]; linarith) hp0.le
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω]
      have hYQ : (ftj_spec V (fun i => q i + ε) - ftj_spec W y).PosSemidef := by
        rw [hQ', hY]; convert hBQ ω hω using 1; abel
      have hcore := ftj_core_gap hp0 hp1 hU hW hV x y (fun i => q i + ε) hx hy hqε hXQ hYQ
      rw [hYX] at hcore
      simp only [hgdef, hgapdef]
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hk := ftj_klein hp0.le hp1.le hU hW x y hx hy
      rw [hYX] at hk
      exact hfr.trans hk
  -- the first-order term has mean zero
  have htr : ∀ ω, (D * (B ω - M)).trace = ∑ a, ∑ b, D a b * (B ω b a - M b a) := by
    intro ω; simp only [trace, diag_apply, mul_apply, Matrix.sub_apply]
  have hint_ab : ∀ a b, Integrable (fun ω => D a b * (B ω b a - M b a)) μ := fun a b =>
    ((hBint b a).sub (integrable_const _)).const_mul _
  have hint_tr : Integrable (fun ω => (D * (B ω - M)).trace) μ := by
    simp_rw [htr]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint_ab a b
  have hint0 : ∫ ω, (D * (B ω - M)).trace ∂μ = 0 := by
    simp_rw [htr]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint_ab a b]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint_ab a b]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_const_mul, integral_sub (hBint b a) (integrable_const _), integral_const]
    simp [hMdef, matrixExpect]
  have hint_re : Integrable (fun ω => (D * (B ω - M)).trace.re) μ := hint_tr.re
  have hg_int : Integrable g μ := (integrable_const _).add hint_re
  have hg_integral : ∫ ω, g ω ∂μ = ∑ i, x i ^ p := by
    rw [hgdef, integral_add (integrable_const _) hint_re, integral_const]
    have : ∫ ω, (D * (B ω - M)).trace.re ∂μ = 0 := by
      have h := integral_re hint_tr
      simp only [RCLike.re_to_complex] at h
      rw [h, hint0, Complex.zero_re]
    rw [this]
    simp
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by
    have h1 := hpath ω
    have h2 := fracTrace_nonneg p (B ω)
    have h3 : 0 ≤ G.indicator (fun ω => c₀ * gap ω) ω :=
      Set.indicator_nonneg (fun ω _ => mul_nonneg hc₀ (hgap0 ω)) ω
    linarith
  calc ∫⁻ ω, ENNReal.ofReal (fracTrace p (B ω)) ∂μ +
        ENNReal.ofReal c₀ * ∫⁻ ω in G, ENNReal.ofReal (gap ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (fracTrace p (B ω)) ∂μ +
          ∫⁻ ω, G.indicator (fun ω => ENNReal.ofReal (c₀ * gap ω)) ω ∂μ := by
        congr 1
        rw [lintegral_indicator hG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_mul hc₀]
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (fracTrace p (B ω)) +
          G.indicator (fun ω => ENNReal.ofReal (c₀ * gap ω)) ω) ∂μ := le_lintegral_add _ _
    _ ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
        refine lintegral_mono fun ω => ?_
        have h := hpath ω
        by_cases hω : ω ∈ G
        · rw [Set.indicator_of_mem hω] at h ⊢
          rw [← ENNReal.ofReal_add (fracTrace_nonneg _ _) (mul_nonneg hc₀ (hgap0 ω))]
          exact ENNReal.ofReal_le_ofReal h
        · rw [Set.indicator_of_notMem hω] at h ⊢
          rw [add_zero] at h ⊢
          exact ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (∫ ω, g ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg0)).symm
    _ = ENNReal.ofReal (∑ i, x i ^ p) := by rw [hg_integral]
    _ ≤ ENNReal.ofReal (fracTrace p M + Fintype.card ι * ε ^ p) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hMpsd]
        calc ∑ i, x i ^ p ≤ ∑ i, (lam i ^ p + ε ^ p) := Finset.sum_le_sum fun i _ =>
              Real.rpow_add_le_add_rpow (hlam i) hε.le hp0.le hp1.le
          _ = ∑ i, lam i ^ p + Fintype.card ι * ε ^ p := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The Jensen gap for a general finite index type, with constant `p / (16 K_p)`. -/
theorem ftj_main {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → Matrix ι ι ℂ) (V : Matrix ι ι ℂ) (q : ι → ℝ) (G : Set Ω)
    (hB : ∀ ω, (B ω).PosSemidef) (hBint : ∀ a b, Integrable (fun ω => B ω a b) μ)
    (hG : MeasurableSet G) (hV : V ∈ unitaryGroup ι ℂ) (hq : ∀ i, 0 ≤ q i)
    (hMQ : (V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V - matrixExpect μ B).PosSemidef)
    (hBQ : ∀ ω ∈ G, (V * diagonal (fun i => ((q i : ℝ) : ℂ)) * star V - B ω).PosSemidef) :
    ∫⁻ ω, ENNReal.ofReal (fracTrace p (B ω)) ∂μ +
        ENNReal.ofReal (p / (16 * ftj_resolventConst p)) * ∫⁻ ω in G, ENNReal.ofReal (∑ i, ∑ j,
          ‖(star V * (B ω - matrixExpect μ B) * V) i j‖ ^ 2 *
            ∫ s in Ioi (0 : ℝ), concavityKernel p (q i) (q j) s) ∂μ ≤
      ENNReal.ofReal (fracTrace p (matrixExpect μ B)) := by
  have hK : 0 < ftj_resolventConst p := ftj_resolventConst_pos hp0 hp1
  -- a regularization scale below every positive `q_i`
  set f : ι → ℝ := fun i => if 0 < q i then q i else 1 with hfdef
  have hf : ∀ i, 0 < f i := fun i => by
    simp only [hfdef]; split_ifs with h
    · exact h
    · exact one_pos
  set ε0 : ℝ := (1 + ∑ i, (f i)⁻¹)⁻¹ with hε0def
  have hε0 : 0 < ε0 :=
    inv_pos.mpr (add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hf i)).le))
  have hε0q : ∀ i, 0 < q i → ε0 ≤ q i := by
    intro i hi
    have hfi : f i = q i := by simp [hfdef, hi]
    rw [← hfi]
    have h1 : (f i)⁻¹ ≤ 1 + ∑ j, (f j)⁻¹ := by
      have := Finset.single_le_sum (f := fun j => (f j)⁻¹)
        (fun j _ => (inv_pos.mpr (hf j)).le) (Finset.mem_univ i)
      linarith
    calc ε0 = (1 + ∑ j, (f j)⁻¹)⁻¹ := rfl
      _ ≤ ((f i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr (hf i)) h1
      _ = f i := inv_inv _
  -- comparison with the regularized gap for every `0 < ε ≤ ε0`
  have hstep : ∀ ε, 0 < ε → ε ≤ ε0 →
      ∫⁻ ω, ENNReal.ofReal (fracTrace p (B ω)) ∂μ +
        ENNReal.ofReal (p / (16 * ftj_resolventConst p)) * ∫⁻ ω in G, ENNReal.ofReal (∑ i, ∑ j,
          ‖(star V * (B ω - matrixExpect μ B) * V) i j‖ ^ 2 *
            ∫ s in Ioi (0 : ℝ), concavityKernel p (q i) (q j) s) ∂μ ≤
      ENNReal.ofReal (fracTrace p (matrixExpect μ B) + Fintype.card ι * ε ^ p) := by
    intro ε hε hεle
    refine le_trans (add_le_add_right ?_ _)
      (ftj_regularized hp0 hp1 μ B V q G hB hBint hG hV hq hMQ hBQ hε)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc : p / (16 * ftj_resolventConst p) = p / (4 * ftj_resolventConst p) * (1 / 4) := by
      field_simp; ring
    rw [hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hkε : 0 ≤ ∫ s in Ioi (0 : ℝ), concavityKernel p (q i + ε) (q j + ε) s :=
      setIntegral_nonneg measurableSet_Ioi fun s hs =>
        concavityKernel_nonneg (by linarith [hq i]) (by linarith [hq j]) (le_of_lt hs)
    have hkk : ∫ s in Ioi (0 : ℝ), concavityKernel p (q i) (q j) s ≤
        4 * ∫ s in Ioi (0 : ℝ), concavityKernel p (q i + ε) (q j + ε) s := by
      by_cases hi : 0 < q i
      · by_cases hj : 0 < q j
        · exact ftj_integral_concavityKernel_shift_ge hp0 hp1 hi hj hε.le
            (hεle.trans (hε0q i hi)) (hεle.trans (hε0q j hj))
        · have h0 : q j = 0 := le_antisymm (not_lt.mp hj) (hq j)
          rw [h0] at hkε ⊢
          rw [ftj_integral_concavityKernel_zero_right hp1 (hq i)]
          linarith
      · have h0 : q i = 0 := le_antisymm (not_lt.mp hi) (hq i)
        rw [h0] at hkε ⊢
        rw [ftj_integral_concavityKernel_zero_left hp1 (hq j)]
        linarith
    have hn : 0 ≤ ‖(star V * (B ω - matrixExpect μ B) * V) i j‖ ^ 2 := by positivity
    nlinarith
  -- `ε ↓ 0`
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδr : (0 : ℝ) < δ := NNReal.coe_pos.mpr hδ
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set ε : ℝ := min ε0 (((δ : ℝ) / (N + 1)) ^ p⁻¹) with hεdef
  have hε : 0 < ε := lt_min hε0 (Real.rpow_pos_of_pos (div_pos hδr (by linarith)) _)
  refine (hstep ε hε (min_le_left _ _)).trans ?_
  have hεp : ε ^ p ≤ (δ : ℝ) / (N + 1) := by
    calc ε ^ p ≤ ((((δ : ℝ) / (N + 1)) ^ p⁻¹)) ^ p :=
          Real.rpow_le_rpow hε.le (min_le_right _ _) hp0.le
      _ = (δ : ℝ) / (N + 1) := Real.rpow_inv_rpow (div_pos hδr (by linarith)).le hp0.ne'
  have hNε : N * ε ^ p ≤ δ := by
    calc N * ε ^ p ≤ N * ((δ : ℝ) / (N + 1)) := mul_le_mul_of_nonneg_left hεp hN
      _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  rw [ENNReal.ofReal_add (fracTrace_nonneg _ _) (mul_nonneg hN (Real.rpow_nonneg hε.le _))]
  gcongr
  calc ENNReal.ofReal (N * ε ^ p) ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hNε
    _ = δ := ENNReal.ofReal_coe_nnreal

/-- `FractionalTraceJensenGap` holds, with `c = p / (16 K_p)`, `K_p = ∫_0^∞ s^{p-1}/(1+s) ds`. -/
theorem fractionalTraceJensenGap_holds : FractionalTraceJensenGap := by
  intro p hp0 hp1
  have hK : 0 < ftj_resolventConst p := ftj_resolventConst_pos hp0 hp1
  refine ⟨p / (16 * ftj_resolventConst p), by positivity, ?_⟩
  intro n Ω _ μ hμ B V q G hB hBint hG hV hq hMQ hBQ
  exact ftj_main hp0 hp1 μ B V q G hB hBint hG hV hq hMQ hBQ

open BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Inputs
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws in

/-- `clockFractionalEntrance_of_onePortProps` with `FractionalTraceJensenGap` discharged by
`fractionalTraceJensenGap_holds`.
-/
theorem clockFractionalEntrance_of_onePortProps' (hECM : EdgeClockMomentsContract)
    (hTLU : BlockBand.Internal.Contracts.TransmissionUniform.TransmissionLengthUniformContract)
    (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hMean : OnePortPassiveMean) (hOp : OnePortOperatorMoments)
    (hJet : OnePortJetContraction) :
    ClockFractionalEntranceContract :=
  clockFractionalEntrance_of_onePortProps hECM hTLU hCount hTL hPC hPSM
    fractionalTraceJensenGap_holds hMean hOp hJet

open BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Inputs
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.LayersOnePort in

/-- `clockFractionalEntrance_of_onePort` with `FractionalTraceJensenGap` discharged. -/
theorem clockFractionalEntrance_of_onePort' (hECM : EdgeClockMomentsContract)
    (hTLU : BlockBand.Internal.Contracts.TransmissionUniform.TransmissionLengthUniformContract)
    (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hPM : OnePortPassiveMeanContract) (hOM : OnePortOperatorMomentsContract)
    (hJet : OnePortJetContraction) :
    ClockFractionalEntranceContract :=
  clockFractionalEntrance_of_onePort hECM hTLU hCount hTL hPC hPSM hPM hOM hJet
    fractionalTraceJensenGap_holds

end BlockBand.Endpoints
