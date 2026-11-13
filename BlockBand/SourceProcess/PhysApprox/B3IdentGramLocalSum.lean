module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMstep

/-!
# The stopped sum through the discrete jumps; the special cells

Measure: `closedLaw b W np`.
* **`pStopSum_eq`**: for `R > R_χ + C_T` (`C_T` bounding the traces of the jump values) and
  `a, t` off the birth lengths, `pStopSum = Σ_j ∫ 1_{A_j} ψ Dh_j` (the endpoint corrections
  telescope to `0` pointwise: `alive_tele`, `corrF_eq_zero_of_trace`);
* `integrable_D_Dh`: the tested increments are integrable on the alive sets;
* **`crudeStep`**: on any cell, `‖∫ 1_{A_j} ψ Dh_j‖ₑ ≤ ∫⁻ 1_{A_j} ‖φ‖ (ε + K₀ eDist + C_L/W)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2 BlockBand.SourceProcess.PhysApprox.B3.Modul
open scoped NNReal ENNReal

variable {K np : ℕ}

section Sum

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} {a t : ℝ≥0} {R : ℝ}
  {r : ℕ} {i : Fin r → LIdx K np} {u : Fin r → ℝ≥0}
  {φ : BoundedContinuousFunction (Fin r → ℂ) ℝ}

/-- **The stopped sum through the discrete jumps.** -/
theorem pStopSum_eq (hs : 0 ≤ s) (hτ : ∀ i, s < τ i) (hW : 1 ≤ W) (hat : a ≤ t)
    (hnbp : ¬ IsBirthStep τ W (limLenAll s W a)) (hnbq : ¬ IsBirthStep τ W (limLenAll s W t))
    {Rχ : ℝ} (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ) {CT : ℝ}
    (hCT : ∀ J ∈ jSet (K := K) b m, trRe J ≤ CT) (hRR : Rχ + CT < R)
    (hi1 : ∀ j, Integrable ((b3Alive b E s h τ m R W j V).indicator fun y =>
      pTest b E s h τ m W V i u φ y • (pM χ b E s h τ m W V F Λ (cellT s W a t (j + 1)) y -
        pM χ b E s h τ m W V F Λ (cellT s W a t j) y)) (closedLaw b W np))
    (hi2 : ∀ j, Integrable ((b3Alive b E s h τ m R W j V).indicator fun y =>
      (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y)
      (closedLaw b W np)) :
    pStopSum χ b E s h τ m W V F Λ R i u φ a t =
      ∑ j ∈ Finset.Ico (limLenAll s W a) (limLenAll s W t + 1),
        ∫ y, (b3Alive b E s h τ m R W j V).indicator (fun y =>
          (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y) y
          ∂closedLaw b W np := by
  classical
  unfold pStopSum
  rw [← integral_finsetSum _ fun j _ => hi1 j, ← integral_finsetSum _ fun j _ => hi2 j]
  congr 1
  funext y
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℂ, f = fun j => (pTest b E s h τ m W V i u φ y : ℂ) *
      corrF χ b E s h τ m W V F (cellT s W a t j) y := ⟨_, rfl⟩
  have hdiff : ∀ j, (b3Alive b E s h τ m R W j V).indicator (fun y =>
      pTest b E s h τ m W V i u φ y • (pM χ b E s h τ m W V F Λ (cellT s W a t (j + 1)) y -
        pM χ b E s h τ m W V F Λ (cellT s W a t j) y)) y -
      (b3Alive b E s h τ m R W j V).indicator (fun y =>
        (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y) y =
      if y ∈ b3Alive b E s h τ m R W j V then f (j + 1) - f j else 0 := fun j => by
    by_cases hA : y ∈ b3Alive b E s h τ m R W j V
    · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, ite_eq_left_of_eq_true _ _ (eq_true hA),
        hf, Complex.real_smul]
      unfold Dh
      ring
    · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA,
        ite_eq_right_of_eq_false _ _ (eq_false hA), sub_zero]
  have hp0 : f (limLenAll s W a) = 0 := by
    rw [hf]; dsimp only
    rw [cellT_first hs hW, corrF_eq_zero_of_nb hτ hW hnbp, mul_zero]
  have hq0 : f (limLenAll s W t + 1) = 0 := by
    rw [hf]; dsimp only
    rw [cellT_last hW hat, corrF_eq_zero_of_nb hτ hW hnbq, mul_zero]
  have hst : ∀ n, limLenAll s W a < n → n ≤ limLenAll s W t →
      y ∈ b3Alive b E s h τ m R W (n - 1) V → y ∉ b3Alive b E s h τ m R W n V → f n = 0 := by
    intro n hpn hnq hA hnA
    have hLn : limLenAll s W (cellT s W a t n) = n := limLenAll_cellT hs hW hpn.le hnq
    have htr : R ≤ trRe (b3ClosedGramAt b E s h τ m W n V y) := by
      by_contra hlt
      refine hnA ⟨hA.1, fun i hi hin => ?_⟩
      rcases eq_or_lt_of_le hin with h | h
      · rw [h]; exact not_le.1 hlt
      · exact hA.2 i hi (by omega)
    have htr' : R ≤ trRe (b3ClosedGramAt b E s h τ m W (limLenAll s W (cellT s W a t n)) V y) := by
      rw [hLn]; exact htr
    have h0 : corrF χ b E s h τ m W V F (cellT s W a t n) y = 0 :=
      corrF_eq_zero_of_trace (χ := χ) (b := b) (E := E) (h := h) (τ := τ) (m := m) (V := V) hFv
        hCT hRR (cellT s W a t n) y htr'
    rw [hf]; dsimp only
    rw [h0, mul_zero]
  have htele := alive_tele f (fun j => y ∈ b3Alive b E s h τ m R W j V)
    (fun j hj => b3Alive_succ_subset j hj) hp0 hq0 hst
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hdiff j]
  exact htele

theorem sm_corrF (hVg : Measurable[growthSigma W (closeLen s W)] V) (hχ : Continuous χ)
    (hF : Continuous F) (v : ℝ≥0) :
    StronglyMeasurable (corrF χ b E s h τ m W V F v) := by
  have hV : Measurable V := hVg.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hG : StronglyMeasurable (Function.uncurry (pG b E s h τ m W V)) := sm_pG hV
  have h1 := (sm_stZ (b := b) (E := E) (s := s) (τ := τ) (m := m) hG hχ).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable fun y : ProbedPath W np × ℝ => (v, y))
  rw [Function.comp_def] at h1
  have h2 : StronglyMeasurable (zHat χ b E s h τ m W V v) :=
    (sm_zHat_past hVg hχ (j := limLenAll s W v) le_rfl).mono (gen_sigma_le W _ np)
  exact (hF.comp_stronglyMeasurable h1).sub (hF.comp_stronglyMeasurable h2)

/-- **Integrability of the tested increments on the alive sets.** -/
theorem integrable_D_Dh (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hVg : Measurable[growthSigma W (closeLen s W)] V) (hχ : Continuous χ) (hF : Continuous F)
    (hΛ : Continuous Λ) (hat : a ≤ t) {CH CF : ℝ}
    (hCH : ∀ y, FeasPath b E s h τ m W V y → ∀ v ≤ t, ‖pM χ b E s h τ m W V F Λ v y‖ ≤ CH)
    (hCF : ∀ y, FeasPath b E s h τ m W V y → ∀ v ≤ t,
      ‖F (stZ χ b E s τ m (pG b E s h τ m W V) v y)‖ ≤ CF ∧
        ‖F (zHat χ b E s h τ m W V v y)‖ ≤ CF)
    (hfe : ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W →
      FeasPath b E s h τ m W V y) (j : ℕ) :
    Integrable ((b3Alive b E s h τ m R W j V).indicator fun y =>
      pTest b E s h τ m W V i u φ y • (pM χ b E s h τ m W V F Λ (cellT s W a t (j + 1)) y -
        pM χ b E s h τ m W V F Λ (cellT s W a t j) y)) (closedLaw b W np) ∧
    Integrable ((b3Alive b E s h τ m R W j V).indicator
      (Dh χ b E s h τ m W V F Λ a t j)) (closedLaw b W np) ∧
    Integrable ((b3Alive b E s h τ m R W j V).indicator fun y =>
      (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y)
      (closedLaw b W np) := by
  have hV : Measurable V := hVg.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hA' := measurableSet_b3AliveM b E s h τ m R W j hV
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j V
  have hMm : ∀ v, StronglyMeasurable (pM χ b E s h τ m W V F Λ v) :=
    sm_pM (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m) hV hχ hF hΛ
  have hψm : StronglyMeasurable fun y => ((pTest b E s h τ m W V i u φ y : ℝ) : ℂ) :=
    (Complex.measurable_ofReal.comp (measurable_pTest (b := b) (E := E) (s := s) (h := h)
      (τ := τ) (m := m) hV i u φ)).stronglyMeasurable
  have hDh : StronglyMeasurable (Dh χ b E s h τ m W V F Λ a t j) :=
    ((hMm _).sub (hMm _)).sub ((sm_corrF hVg hχ hF _).sub (sm_corrF hVg hχ hF _))
  have hb1 : ∀ y, FeasPath b E s h τ m W V y →
      ‖Dh χ b E s h τ m W V F Λ a t j y‖ ≤ (CH + CH) + ((CF + CF) + (CF + CF)) := fun y hy => by
    have h1 := hCH y hy _ (cellT_le s W hat (j + 1))
    have h2 := hCH y hy _ (cellT_le s W hat j)
    have h3 := hCF y hy _ (cellT_le s W hat (j + 1))
    have h4 := hCF y hy _ (cellT_le s W hat j)
    unfold Dh corrF
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2))
      ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h3.1 h3.2))
        ((norm_sub_le _ _).trans (add_le_add h4.1 h4.2)))))
  have hψ : ∀ y, ‖((pTest b E s h τ m W V i u φ y : ℝ) : ℂ)‖ ≤ ‖φ‖ := fun y => by
    rw [Complex.norm_real]; exact φ.norm_coe_le_norm _
  refine ⟨integrable_indicator_of_bound hA' hAA ?_ (C := ‖φ‖ * (CH + CH)) ?_,
    integrable_indicator_of_bound hA' hAA hDh.aestronglyMeasurable
      (C := (CH + CH) + ((CF + CF) + (CF + CF))) ?_,
    integrable_indicator_of_bound hA' hAA (hψm.mul hDh).aestronglyMeasurable
      (C := ‖φ‖ * ((CH + CH) + ((CF + CF) + (CF + CF)))) ?_⟩
  · simp only [Complex.real_smul]
    exact (hψm.mul ((hMm _).sub (hMm _))).aestronglyMeasurable
  · filter_upwards [hfe] with y hy hA
    rw [norm_smul]
    exact mul_le_mul (φ.norm_coe_le_norm _) ((norm_sub_le _ _).trans (add_le_add
      (hCH y (hy hA.1) _ (cellT_le s W hat _)) (hCH y (hy hA.1) _ (cellT_le s W hat _))))
      (norm_nonneg _) (norm_nonneg _)
  · filter_upwards [hfe] with y hy hA using hb1 y (hy hA.1)
  · filter_upwards [hfe] with y hy hA
    rw [norm_mul]
    exact mul_le_mul (hψ y) (hb1 y (hy hA.1)) (norm_nonneg _) (norm_nonneg _)

/-- **The crude step under the closed law.** -/
theorem crudeStep (j : ℕ) {X : ProbedPath W np × ℝ → ℝ}
    (hX : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j V →
      ‖Dh χ b E s h τ m W V F Λ a t j y‖ ≤ X y) :
    ‖∫ y, (b3Alive b E s h τ m R W j V).indicator (fun y =>
        (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y) y
      ∂closedLaw b W np‖ₑ ≤
      ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
        (fun y => ENNReal.ofReal (‖φ‖ * X y)) y ∂closedLaw b W np := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hX] with y hy
  by_cases hA : y ∈ b3Alive b E s h τ m R W j V
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, ← ofReal_norm, norm_mul]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ (hy hA) (norm_nonneg _) (norm_nonneg _))
    rw [Complex.norm_real]; exact φ.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA, enorm_zero]

end Sum

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
