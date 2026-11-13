module

public import BlockBand.Endpoints.Clock.BUniformDeterministic

/-!
# `b`-uniform deterministic step of the open-inputs lemma

The constants `r₀, q, C` of `MovingEnergy.step_consts_unif` and `step_bound_unif` are chosen after
`b`. Here they are chosen after `(β, κ)` only and hold for every `b ∈ Icc β (1/2-β)` and every
`E ∈ bulkInterval κ` (`0 < β`, `0 < κ ≤ 1`):
* `step_consts_unifB`: the worst-case constants for a stability constant `Cs`, from the
  `(β, κ)` bounds `gapLowB`, `etaLowB`, `dStarB ≤ 2`, `‖kMinus‖ ≤ 1`, `b ≤ 1/2`, `mC > b ≥ β`,
  each factor bounded separately;
* `cavity_stability_bandB`: one stability constant for all `b ∈ Icc β (1/2-β)`, `c = 1-2b`, at
  `(η, M, a_*) = (etaLowB β κ, 3, 1)`;
* `step_bound_unifB`: the deterministic one-step bounds of `OpenInputsProof.step_bound`, using
  `step_scalar_jet` at each `(b, E)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof CavityMeanProb ZeroEntranceProb

/-- **The worst-case constants of `step_bound`, uniformly in `b ∈ Icc β (1/2-β)` and
`E ∈ bulkInterval κ`**, for a given stability constant `Cs`: the statement of
`step_consts_unif` with `r₀, q, C` chosen before `b`. -/
theorem step_consts_unifB (β κ : ℝ) (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1) {Cs : ℝ}
    (hCs : 0 < Cs) :
    ∃ r₀ q C : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ E ∈ bulkInterval κ,
      (b + gapC b E / 4) / mC b E ≤ q ∧ b ^ 2 / (mC b E * dZero b E) ≤ q ∧
      3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 + 2 * Cs / iotaC b E ^ 3 ≤ C ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ r₀ → δ ≤ 1 ∧ Cs * δ ≤ 1 ∧ Cs * δ ≤ yA E / 2 ∧
        4 * lamC b E Cs * δ ≤ gapC b E ∧ 4 * b * Cs * δ ≤ gapC b E ∧ muC b E Cs * δ ≤ 1 := by
  have hκ4 : κ < 4 := by linarith
  have hy0 := yLow_pos hκ hκ4
  have hg0 := gapLowB_pos hβ hκ
  have hη0 := etaLowB_pos hβ hκ hκ4
  set g₀ := gapLowB β κ with hg₀
  set y := yLow κ with hy
  set μ₀ := 2 * Cs / ((1 / 2) ^ 2 * y) + 1 / ((1 / 2) * y) with hμ₀
  have hμ₀0 : 0 ≤ μ₀ := by rw [hμ₀]; positivity
  set Λ₀ := μ₀ + 3 * Cs * 2 + 3 * Cs * μ₀ with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := by rw [hΛ₀]; positivity
  set ι₀ := etaLowB β κ / 2 with hι₀
  have hι₀0 : 0 < ι₀ := by rw [hι₀]; positivity
  set qs := (1 / 2 + g₀ / 4) / (1 / 2 + 3 * g₀ / 4) with hqs
  set q₁ := (1 / 2) / (1 / 2 + 3 * g₀ / 4) with hq₁
  have hqs0 : 0 ≤ qs := by rw [hqs]; positivity
  have hqs1 : qs < 1 := by rw [hqs, div_lt_one (by positivity)]; linarith
  have hq₁1 : q₁ < 1 := by rw [hq₁, div_lt_one (by positivity)]; linarith
  refine ⟨min (min 1 (1 / Cs)) (min (y / (2 * Cs))
    (min (g₀ / (4 * Λ₀ + 1)) (min (g₀ / (4 * Cs + 1)) (1 / (μ₀ + 1))))),
    max qs q₁, 3 * (2 + 2) ^ 2 * Cs / β ^ 2 + 2 * Cs / ι₀ ^ 3,
    lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))),
    le_max_of_le_left hqs0, max_lt hqs1 hq₁1, by positivity, ?_⟩
  intro b hb E hEκ
  obtain ⟨hb0, hb1, hβb, -, -, h1b2, -⟩ := mem_IccB_facts hβ hb
  have h1b : 0 < 1 - b := by linarith
  have hb12 : b ≤ 1 / 2 := hb1.le
  have hbone : b ≤ 1 := by linarith
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  obtain ⟨hy0E, -, hgap, hmb, hmD, hD₀b, hι0⟩ := consts_facts hb0 hb1 hE0 hE1
  have hyy : y ≤ yA E := yLow_le_yA hEκ
  have hgg : g₀ ≤ gapC b E := gapLowB_le_gapC hβ hκ hκ1 hb hEκ
  have hkk : ‖kMinus b E‖ ≤ 1 := norm_kMinus_le_one hβ hκ hκ1 hb hEκ
  obtain ⟨hdS1, hdSB, hdB2⟩ := dStar_le_B hβ hb
  have hdS2 : dStar b ≤ 2 := hdSB.trans hdB2
  have hm0 : 0 < mC b E := hb0.trans hmb
  have hb2 : b ^ 2 ≤ 1 := pow_le_one₀ hb0.le hbone
  have hμE : muC b E Cs ≤ μ₀ := by
    unfold muC; rw [hμ₀]
    have hh : (1 / 2 : ℝ) ≤ 1 - b := by linarith
    have h1 : 2 * b * Cs / ((1 - b) ^ 2 * yA E) ≤ 2 * Cs / ((1 / 2) ^ 2 * y) := by
      refine div_le_div₀ (by positivity) ?_ (by positivity)
        (mul_le_mul (pow_le_pow_left₀ (by norm_num) hh 2) hyy hy0.le (by positivity))
      have := mul_le_mul_of_nonneg_right hbone hCs.le
      linarith
    have h2 : 1 / ((1 - b) * yA E) ≤ 1 / ((1 / 2) * y) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul hh hyy hy0.le h1b.le)
    linarith
  have hμ0 : 0 ≤ muC b E Cs := by unfold muC; positivity
  have hΛE : lamC b E Cs ≤ Λ₀ := by
    unfold lamC; rw [hΛ₀]
    have h1 : ‖kMinus b E‖ * muC b E Cs ≤ 1 * μ₀ := mul_le_mul hkk hμE hμ0 zero_le_one
    have h2 : 3 * b ^ 2 * Cs * dStar b ≤ 3 * 1 * Cs * 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by norm_num))
        hCs.le) hdS2 (by linarith) (by positivity)
    have h3 : 3 * b ^ 2 * Cs * muC b E Cs ≤ 3 * 1 * Cs * μ₀ :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by norm_num))
        hCs.le) hμE hμ0 (by positivity)
    linarith
  have emC : mC b E = b + 3 * gapC b E / 4 := by unfold mC gapC; ring
  have hDE : b + g₀ ≤ dZero b E := by unfold gapC at hgg; linarith
  have hιE : ι₀ ≤ iotaC b E := by rw [hι₀]; exact iotaC_ge_B hβ hκ hκ4 hb hEκ
  have hbg : b * g₀ ≤ 1 / 2 * g₀ := mul_le_mul_of_nonneg_right hb12 hg0.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ (le_max_left _ _)
    rw [hqs, emC, div_le_div_iff₀ (by positivity) (by positivity)]
    have e1 : (b + gapC b E / 4) * (1 / 2 + 3 * g₀ / 4) =
        b / 2 + 3 / 4 * (b * g₀) + gapC b E / 8 + 3 / 16 * (gapC b E * g₀) := by ring
    have e2 : (1 / 2 + g₀ / 4) * (b + 3 * gapC b E / 4) =
        b / 2 + 3 / 8 * gapC b E + 1 / 4 * (b * g₀) + 3 / 16 * (gapC b E * g₀) := by ring
    rw [e1, e2]
    linarith
  · refine le_trans ?_ (le_max_right _ _)
    have hbm : b / mC b E ≤ q₁ := by
      rw [hq₁, emC, div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : b * (1 / 2 + 3 * g₀ / 4) = b / 2 + 3 / 4 * (b * g₀) := by ring
      have e2 : 1 / 2 * (b + 3 * gapC b E / 4) = b / 2 + 3 / 8 * gapC b E := by ring
      rw [e1, e2]
      linarith
    refine le_trans ?_ hbm
    have hD0 : 0 < dZero b E := hb0.trans hD₀b
    rw [div_le_div_iff₀ (mul_pos hm0 hD0) hm0]
    have := mul_le_mul_of_nonneg_left hD₀b.le (mul_nonneg hb0.le hm0.le)
    have e1 : b ^ 2 * mC b E = b * mC b E * b := by ring
    have e2 : b * (mC b E * dZero b E) = b * mC b E * dZero b E := by ring
    rw [e1, e2]
    exact this
  · have h1 : 3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 ≤ 3 * (2 + 2) ^ 2 * Cs / β ^ 2 := by
      refine div_le_div₀ (by positivity) ?_ (by positivity)
        (pow_le_pow_left₀ hβ.le (hβb.trans hmb.le) 2)
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hCs.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : 2 * Cs / iotaC b E ^ 3 ≤ 2 * Cs / ι₀ ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hι₀0.le hιE 3)
    linarith
  intro δ hδ0 hδ
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδCs : δ ≤ 1 / Cs := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδy : δ ≤ y / (2 * Cs) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδΛ : δ ≤ g₀ / (4 * Λ₀ + 1) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδb : δ ≤ g₀ / (4 * Cs + 1) := hδ.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδμ : δ ≤ 1 / (μ₀ + 1) := hδ.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  rw [le_div_iff₀ hCs] at hδCs
  rw [le_div_iff₀ (by positivity)] at hδy hδΛ hδb hδμ
  have e1 : 4 * lamC b E Cs * δ ≤ 4 * Λ₀ * δ := by
    have := mul_le_mul_of_nonneg_right hΛE hδ0; linarith
  have e2 : muC b E Cs * δ ≤ μ₀ * δ := mul_le_mul_of_nonneg_right hμE hδ0
  have e3 : 4 * b * Cs * δ ≤ 4 * Cs * δ := by
    have := mul_le_mul_of_nonneg_right hbone (by positivity : (0 : ℝ) ≤ 4 * Cs * δ)
    linarith
  refine ⟨hδ1, by linarith, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- **One stability constant on the band** `b ∈ Icc β (1/2-β)`, `c = 1-2b`, at
`(η, M, a_*) = (η, 3, 1)` (the instantiation of `cavity_stability` in `step_bound`). -/
theorem cavity_stability_bandB {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ (ι : Type) [Fintype ι] (p x : ι → ℝ) (e : ℝ) (z' v u vbar ubar : ℂ) (ε : ℝ),
      IsCavityWeights p → η ≤ z'.im → ‖z'‖ ≤ 3 →
      IsCavitySolution p x b (1 - 2 * b) e z' v u → vbar.im ≤ 0 → 1 ≤ ‖ubar‖ →
      η * ‖ubar‖ ^ 2 ≤ -ubar.im →
      ‖vbar - cavityStieltjes p x (-e - ((1 - 2 * b : ℝ) : ℂ) * vbar - b * ubar)‖ ≤ ε →
      ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε →
      ‖vbar - v‖ + ‖ubar - u‖ ≤ C * ε := by
  obtain ⟨C, hC, h⟩ := cavity_stability_unifB (c₀ := 2 * β) (M := 3) (astar := 1) hβ
    (by linarith) hη (by norm_num) one_pos
  refine ⟨C, hC, fun b hb => ?_⟩
  obtain ⟨hb0, -, hβb, -, hc, -, -⟩ := mem_IccB_facts hβ hb
  exact h b (1 - 2 * b) hβb (by linarith) hc (by linarith)

/-- **The deterministic one-step bounds of the open-inputs lemma, uniformly in `b ∈ Icc β (1/2-β)`
and `E ∈ bulkInterval κ`**: the bounds of `OpenInputsProof.step_bound` with `r₀, q, C` depending
only on `(β, κ)`. -/
theorem step_bound_unifB (β κ : ℝ) (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ r₀ q C : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ E ∈ bulkInterval κ,
      ∀ {W : ℕ}, 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        jetDistance0 b E X ≤ r₀ →
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ ≤ q * jetDistance0 b E X ∧
        ∀ s : ℂ, IsStationaryJet b E s →
          ‖deriv (cavityU X b E) (boundaryZ b E) - s‖ ≤
            q * jetDistance1 b E s X + C * jetDistance0 b E X := by
  have hκ4 : κ < 4 := by linarith
  have hη0 := etaLowB_pos hβ hκ hκ4
  obtain ⟨Cs, hCs, hstab⟩ := cavity_stability_bandB hβ hη0
  obtain ⟨r₀, q, C, hr₀, hq0, hq1, hC0, hcons⟩ := step_consts_unifB β κ hβ hκ hκ1 hCs
  refine ⟨r₀, q, C, hr₀, hq0, hq1, hC0, ?_⟩
  intro b hb E hEκ W hW X hX hδ
  obtain ⟨hb0, hb1, -, -, -, -, hβ4⟩ := mem_IccB_facts hβ hb
  obtain ⟨hqsE, hq₁E, hCE, hsmall⟩ := hcons b hb E hEκ
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hyy := yLow_le_yA hEκ
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have ha1 : ‖matchedA E‖ = 1 := BlockBand.Layers.norm_matchedA hE
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E =
      boundaryZ b E := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; push_cast; ring
  have hza' : boundaryZ b E - (b : ℂ) * matchedA E = (matchedA E)⁻¹ := by
    unfold boundaryZ; ring
  have hc : 0 < 1 - 2 * b := by linarith
  have p_def : ∃ p : Fin W → ℝ, p = fun _ => (W : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ := p_def
  have hp : IsCavityWeights p := hpdef ▸ isCavityWeights_uniform hW
  have hfX : normalizedResolventTrace X (boundaryZ b E) =
      cavityStieltjes p hX.eigenvalues (boundaryZ b E) := by
    rw [hpdef]; exact normalizedResolventTrace_eq hX hzpos.ne'
  have hδeq : jetDistance0 b E X =
      ‖cavityStieltjes p hX.eigenvalues (boundaryZ b E) - matchedA E‖ := by
    rw [jetDistance0_eq, hfX]
  have hsol : IsCavitySolution p hX.eigenvalues b (1 - 2 * b) E (boundaryZ b E)
      (cavityV X b E (boundaryZ b E)) (cavityU X b E (boundaryZ b E)) := by
    rw [hpdef]
    exact (isCavityMatrixSolution_iff hX hb0 hc).mp (cavitySol_spec hW hX hb0 hb1 E hzpos)
  rw [hδeq] at hδ ⊢
  generalize hδg : ‖cavityStieltjes p hX.eigenvalues (boundaryZ b E) - matchedA E‖ = δ at hδ
  have hδ0 : 0 ≤ δ := by rw [← hδg]; exact norm_nonneg _
  have hport : etaLowB β κ * ‖matchedA E‖ ^ 2 ≤ -(matchedA E).im := by
    rw [ha1, one_pow, mul_one]
    have e : -(matchedA E).im = yA E := rfl
    rw [e]
    exact (etaLowB_le_yLow hβ4 hκ hκ4).trans hyy
  have hst : ‖cavityV X b E (boundaryZ b E) - matchedA E‖ +
      ‖cavityU X b E (boundaryZ b E) - matchedA E‖ ≤ Cs * δ := by
    have h := hstab b hb (Fin W) p hX.eigenvalues E (boundaryZ b E) _ _ (matchedA E)
      (matchedA E) δ hp (etaLowB_le_im hβ hκ hκ4 hb hEκ) (norm_boundaryZ_le3 hb0 hb1 hκ hEκ)
      hsol ?_ ?_ hport ?_ ?_
    · rw [norm_sub_rev (cavityV _ _ _ _), norm_sub_rev (cavityU _ _ _ _)]; exact h
    · have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩); linarith
    · rw [ha1]
    · rw [hzeq, norm_sub_rev, hδg]
    · rw [hza', inv_inv, sub_self, norm_zero]; exact hδ0
  obtain ⟨hδ1, hCsδ1, hCsδy, hΛδ, hbCsδ, hμδ⟩ := hsmall δ hδ0 hδ
  rw [← hδg] at hst hδ1 hCsδ1 hCsδy hΛδ hbCsδ hμδ
  obtain ⟨hsc, hjet⟩ := step_scalar_jet hb0 hb1 hE0 hE1 hCs hp hsol hst hδ1 hCsδ1 hCsδy hΛδ
    hbCsδ hμδ
  rw [hδg] at hsc hjet
  refine ⟨hsc.trans (mul_le_mul_of_nonneg_right hqsE hδ0), ?_⟩
  intro s hs
  have hd1 : jetDistance1 b E s X =
      ‖-kerK p hX.eigenvalues (boundaryZ b E) (boundaryZ b E) - s‖ := by
    rw [jetDistance1_eq, hpdef, (hasDerivAt_normalizedResolventTrace hX hzpos).deriv]
  rw [hd1, hpdef, deriv_cavityU_eq hW hX hb0 hb1 hzpos]
  rw [hpdef] at hjet
  refine (hjet s hs).trans ?_
  have h1 := mul_le_mul_of_nonneg_right hq₁E
    (norm_nonneg (-kerK (fun _ : Fin W => (W : ℝ)⁻¹) hX.eigenvalues (boundaryZ b E)
      (boundaryZ b E) - s))
  have h2 := mul_le_mul_of_nonneg_right hCE hδ0
  linarith

end MovingEnergy

end BlockBand.Endpoints.Clock
