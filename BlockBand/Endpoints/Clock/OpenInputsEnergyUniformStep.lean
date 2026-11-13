module

public import BlockBand.Endpoints.Clock.OpenInputsProof

/-!
# The open-inputs lemma, energy-uniform: the deterministic step and one fresh layer

Here `b` is fixed and `E` ranges over `bulkInterval κ = [-2+κ, 2-κ]`, `0 < κ < 4`.
`OpenInputsProof.step_bound`, `one_step` and `delta_next` fix `E` before their constants. Their
constants are explicit functions of `E` through `y = -Im a` (`yA`), `|k| = |c + b²a²|`
(`kMinus`), `Im z` and `|z|`, and of the stability constant of `CavityMean.cavity_stability` at
`(Im z, |z|)`. On `bulkInterval κ`:
* `y ≥ y_κ = √(4-(2-κ)²)/2` (`matchedA_im_le_of_mem_bulkInterval`);
* `|k| ≤ r_κ = √((1-b)⁴ - 2(1-2b)b²κ) < (1-b)²` (`norm_contraction_le_of_mem_bulkInterval`,
  `contractionRadius_lt`), so the gap `D₀ - b` is at least `g_κ = 1 - r_κ d_* - b > 0`;
* `Im z ≥ (1-b) y_κ` and `|z| ≤ 3` (`boundaryZ_im_ge_of_mem_bulkInterval`, `norm_boundaryZ_le`).

`cavity_stability` is uniform in `z` with `Im z ≥ η`, `|z| ≤ M`, and `CavityMeanStatement` is
uniform in every real energy and every `z` with `Im z ≥ η₀`, `|z| ≤ M`. Each `E`-dependent constant
of `step_bound` is monotone in these quantities, so it is dominated by its value at the worst case
(`step_bound_unif`); `step_scalar_jet` is reused at each `E`.

* `step_bound_unif`: the deterministic one-step bounds (Steps 2–4 of the paper's proof),
  `r₀, q, C` uniform on `bulkInterval κ`.
* `oneStepFacts_unif`: the conclusion `OneStepFacts` of `one_step` with one set of constants for
  every `E ∈ bulkInterval κ`.
* `delta_next_unif`: the scalar step of `delta_next` with uniform constants.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof CavityMeanProb ZeroEntranceProb

variable {b κ E : ℝ}

/-- `y_κ = √(4-(2-κ)²)/2`, the uniform lower bound of `y = -Im a` on `bulkInterval κ`. -/
def yLow (κ : ℝ) : ℝ := Real.sqrt (4 - (2 - κ) ^ 2) / 2

/-- `r_κ = √((1-b)⁴ - 2(1-2b)b²κ)`, the uniform upper bound of `|k|` on `bulkInterval κ`. -/
def kHigh (b κ : ℝ) : ℝ := Real.sqrt ((1 - b) ^ 4 - 2 * (1 - 2 * b) * b ^ 2 * κ)

/-- `g_κ = 1 - r_κ d_* - b`, the uniform lower bound of the gap `D₀ - b`. -/
def gapLow (b κ : ℝ) : ℝ := 1 - kHigh b κ * dStar b - b

/-- `η_κ = (1-b) y_κ`, the uniform lower bound of `Im z`. -/
def etaLow (b κ : ℝ) : ℝ := (1 - b) * yLow κ

theorem mem_bulk_lt (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : -2 < E ∧ E < 2 := by
  have h := BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ hE
  exact ⟨(abs_lt.mp h).1, (abs_lt.mp h).2⟩

theorem yLow_pos (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < yLow κ := by
  unfold yLow
  have := Real.sqrt_pos.mpr (BlockBand.Layers.four_sub_sq_pos hκ hκ4)
  positivity

theorem yLow_le_yA (hE : E ∈ bulkInterval κ) : yLow κ ≤ yA E := by
  have := BlockBand.Layers.matchedA_im_le_of_mem_bulkInterval hE
  unfold yLow yA; linarith

theorem norm_kMinus_le_kHigh (hb1 : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖kMinus b E‖ ≤ kHigh b κ :=
  BlockBand.Layers.norm_contraction_le_of_mem_bulkInterval hb1.le hκ.le hE

theorem gapLow_pos (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) : 0 < gapLow b κ := by
  have hr := BlockBand.Layers.contractionRadius_lt hb0 hb1 hκ
  have h1b : 0 < 1 - b := by linarith
  have hr0 : 0 ≤ kHigh b κ := Real.sqrt_nonneg _
  have : kHigh b κ * dStar b < 1 - b := by
    unfold dStar; rw [mul_one_div, div_lt_iff₀ h1b]; unfold kHigh; nlinarith
  unfold gapLow; linarith

theorem gapLow_le_gapC (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    gapLow b κ ≤ gapC b E := by
  have hk := norm_kMinus_le_kHigh hb1 hκ hE
  have hdS : 0 ≤ dStar b := by unfold dStar; have : 0 < 1 - b := by linarith
                               positivity
  have := mul_le_mul_of_nonneg_right hk hdS
  unfold gapC dZero gapLow; linarith

theorem etaLow_pos (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < etaLow b κ := by
  unfold etaLow; have := yLow_pos hκ hκ4; have : 0 < 1 - b := by linarith
  positivity

theorem etaLow_le_im (hb1 : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    etaLow b κ ≤ (boundaryZ b E).im := by
  have h := BlockBand.Layers.boundaryZ_im_ge_of_mem_bulkInterval (b := b) (by linarith) hκ hE
  unfold etaLow yLow; linarith

theorem norm_boundaryZ_le3 (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) : ‖boundaryZ b E‖ ≤ 3 :=
  BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith)
    (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ hE).le

theorem im_pos_of_bulk (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) (hE : E ∈ bulkInterval κ) :
    0 < (boundaryZ b E).im :=
  (etaLow_pos hb1 hκ hκ4).trans_le (etaLow_le_im hb1 hκ hE)

/-- The worst-case constants of `step_bound` on `bulkInterval κ`, for a given stability
constant `Cs`: every smallness condition of `step_scalar_jet` at `E` follows from `δ ≤ r₀`, and
the `E`-dependent contraction factors and slope are dominated by `q < 1` and `C`. -/
theorem step_consts_unif (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) {Cs : ℝ}
    (hCs : 0 < Cs) :
    ∃ r₀ q C : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ ∀ E ∈ bulkInterval κ,
      (b + gapC b E / 4) / mC b E ≤ q ∧ b ^ 2 / (mC b E * dZero b E) ≤ q ∧
      3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 + 2 * Cs / iotaC b E ^ 3 ≤ C ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ r₀ → δ ≤ 1 ∧ Cs * δ ≤ 1 ∧ Cs * δ ≤ yA E / 2 ∧
        4 * lamC b E Cs * δ ≤ gapC b E ∧ 4 * b * Cs * δ ≤ gapC b E ∧ muC b E Cs * δ ≤ 1 := by
  have h1b : 0 < 1 - b := by linarith
  have hy0 := yLow_pos hκ hκ4
  have hg0 := gapLow_pos hb0 hb1 hκ
  have hdS1 : 1 ≤ dStar b := by unfold dStar; rw [le_div_iff₀ h1b]; linarith
  have hdS0 : 0 ≤ dStar b := by linarith
  have hkH0 : 0 ≤ kHigh b κ := Real.sqrt_nonneg _
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : ℝ, μ₀ = 2 * b * Cs / ((1 - b) ^ 2 * yLow κ) + 1 / ((1 - b) * yLow κ) :=
    ⟨_, rfl⟩
  have hμ₀0 : 0 ≤ μ₀ := by rw [hμ₀]; positivity
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = kHigh b κ * μ₀ + 3 * b ^ 2 * Cs * dStar b +
      3 * b ^ 2 * Cs * μ₀ := ⟨_, rfl⟩
  have hΛ₀0 : 0 ≤ Λ₀ := by rw [hΛ₀]; positivity
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ℝ, g₀ = gapLow b κ := ⟨_, rfl⟩
  rw [← hg₀] at hg0
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = b + 3 * g₀ / 4 := ⟨_, rfl⟩
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  obtain ⟨ι₀, hι₀⟩ : ∃ ι₀ : ℝ, ι₀ = (1 - b) * yLow κ / 2 := ⟨_, rfl⟩
  have hι₀0 : 0 < ι₀ := by rw [hι₀]; positivity
  obtain ⟨qs, hqs⟩ : ∃ qs : ℝ, qs = (b + g₀ / 4) / m₀ := ⟨_, rfl⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : ℝ, q₁ = b ^ 2 / (m₀ * (b + g₀)) := ⟨_, rfl⟩
  have hqs0 : 0 ≤ qs := by rw [hqs]; positivity
  have hqs1 : qs < 1 := by rw [hqs, div_lt_one hm₀0, hm₀]; linarith
  have hq₁1 : q₁ < 1 := by
    rw [hq₁, div_lt_one (by positivity)]
    have h1 : b < m₀ := by rw [hm₀]; linarith
    have h2 : b < b + g₀ := by linarith
    rw [sq]; exact mul_lt_mul'' h1 h2 hb0.le hb0.le
  refine ⟨min (min 1 (1 / Cs)) (min (yLow κ / (2 * Cs))
    (min (g₀ / (4 * Λ₀ + 1)) (min (g₀ / (4 * b * Cs + 1)) (1 / (μ₀ + 1))))),
    max qs q₁, 3 * (2 + dStar b) ^ 2 * Cs / m₀ ^ 2 + 2 * Cs / ι₀ ^ 3,
    lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))),
    le_max_of_le_left hqs0, max_lt hqs1 hq₁1, by positivity, ?_⟩
  intro E hEκ
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  obtain ⟨hy0E, -, hgap, hmb, hmD, hD₀b, hι0⟩ := consts_facts hb0 hb1 hE0 hE1
  have hyy := yLow_le_yA hEκ
  have hgg : g₀ ≤ gapC b E := hg₀ ▸ gapLow_le_gapC hb0 hb1 hκ hEκ
  have hkk := norm_kMinus_le_kHigh hb1 hκ hEκ
  have hm0 : 0 < mC b E := hb0.trans hmb
  have hμE : muC b E Cs ≤ μ₀ := by
    unfold muC; rw [hμ₀]
    have h1 : 2 * b * Cs / ((1 - b) ^ 2 * yA E) ≤ 2 * b * Cs / ((1 - b) ^ 2 * yLow κ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hyy (by positivity))
    have h2 : 1 / ((1 - b) * yA E) ≤ 1 / ((1 - b) * yLow κ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hyy h1b.le)
    linarith
  have hμ0 : 0 ≤ muC b E Cs := by unfold muC; positivity
  have hΛE : lamC b E Cs ≤ Λ₀ := by
    unfold lamC; rw [hΛ₀]
    have h1 : ‖kMinus b E‖ * muC b E Cs ≤ kHigh b κ * μ₀ :=
      mul_le_mul hkk hμE hμ0 hkH0
    have h2 : 3 * b ^ 2 * Cs * muC b E Cs ≤ 3 * b ^ 2 * Cs * μ₀ :=
      mul_le_mul_of_nonneg_left hμE (by positivity)
    linarith
  have emC : mC b E = b + 3 * gapC b E / 4 := by unfold mC gapC; ring
  have hmE : m₀ ≤ mC b E := by rw [emC, hm₀]; linarith
  have hDE : b + g₀ ≤ dZero b E := by unfold gapC at hgg; linarith
  have hιE : ι₀ ≤ iotaC b E := by
    unfold iotaC; rw [hι₀]
    have := mul_le_mul_of_nonneg_left hyy h1b.le
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ (le_max_left _ _)
    rw [hqs, emC, hm₀, div_le_div_iff₀ (by positivity) (by positivity)]
    have : b * g₀ ≤ b * gapC b E := mul_le_mul_of_nonneg_left hgg hb0.le
    linarith
  · refine le_trans ?_ (le_max_right _ _)
    rw [hq₁]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hmE hDE (by positivity) hm0.le)
  · have h1 : 3 * (2 + dStar b) ^ 2 * Cs / mC b E ^ 2 ≤ 3 * (2 + dStar b) ^ 2 * Cs / m₀ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hm₀0.le hmE 2)
    have h2 : 2 * Cs / iotaC b E ^ 3 ≤ 2 * Cs / ι₀ ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hι₀0.le hιE 3)
    linarith
  intro δ hδ0 hδ
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδCs : δ ≤ 1 / Cs := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδy : δ ≤ yLow κ / (2 * Cs) := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδΛ : δ ≤ g₀ / (4 * Λ₀ + 1) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδb : δ ≤ g₀ / (4 * b * Cs + 1) := hδ.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδμ : δ ≤ 1 / (μ₀ + 1) := hδ.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  rw [le_div_iff₀ hCs] at hδCs
  rw [le_div_iff₀ (by positivity)] at hδy hδΛ hδb hδμ
  have e1 : 4 * lamC b E Cs * δ ≤ 4 * Λ₀ * δ := by
    have := mul_le_mul_of_nonneg_right hΛE hδ0; linarith
  have e2 : muC b E Cs * δ ≤ μ₀ * δ := mul_le_mul_of_nonneg_right hμE hδ0
  refine ⟨hδ1, by linarith, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-- **The deterministic step of the open-inputs lemma, uniformly on `bulkInterval κ`**: the deterministic
one-step bounds of `OpenInputsProof.step_bound` with `r₀, q, C` depending only on `(b, κ)`. -/
theorem step_bound_unif (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ r₀ q C : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧ ∀ E ∈ bulkInterval κ,
      ∀ {W : ℕ}, 0 < W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        jetDistance0 b E X ≤ r₀ →
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ ≤ q * jetDistance0 b E X ∧
        ∀ s : ℂ, IsStationaryJet b E s →
          ‖deriv (cavityU X b E) (boundaryZ b E) - s‖ ≤
            q * jetDistance1 b E s X + C * jetDistance0 b E X := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hη0 := etaLow_pos hb1 hκ hκ4
  obtain ⟨Cs, hCs, hstab⟩ := cavity_stability (b := b) (c := 1 - 2 * b) (η := etaLow b κ)
    (M := 3) (astar := 1) hb0 hc hη0 (by norm_num) one_pos
  obtain ⟨r₀, q, C, hr₀, hq0, hq1, hC0, hcons⟩ := step_consts_unif hb0 hb1 hκ hκ4 hCs
  refine ⟨r₀, q, C, hr₀, hq0, hq1, hC0, ?_⟩
  intro E hEκ W hW X hX hδ
  obtain ⟨hqsE, hq₁E, hCE, hsmall⟩ := hcons E hEκ
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hyy := yLow_le_yA hEκ
  have h1b : 0 < 1 - b := by linarith
  have hy0 := yLow_pos hκ hκ4
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have ha1 : ‖matchedA E‖ = 1 := BlockBand.Layers.norm_matchedA hE
  have hzeq : -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E - (b : ℂ) * matchedA E =
      boundaryZ b E := by
    rw [BlockBand.Layers.boundaryZ_eq hE]; push_cast; ring
  have hza' : boundaryZ b E - (b : ℂ) * matchedA E = (matchedA E)⁻¹ := by
    unfold boundaryZ; ring
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
  have hport : etaLow b κ * ‖matchedA E‖ ^ 2 ≤ -(matchedA E).im := by
    rw [ha1, one_pow, mul_one]; unfold etaLow
    have e : -(matchedA E).im = yA E := rfl
    rw [e]
    have : (1 - b) * yLow κ ≤ 1 * yLow κ := mul_le_mul_of_nonneg_right (by linarith) hy0.le
    linarith
  have hst : ‖cavityV X b E (boundaryZ b E) - matchedA E‖ +
      ‖cavityU X b E (boundaryZ b E) - matchedA E‖ ≤ Cs * δ := by
    have h := hstab (Fin W) p hX.eigenvalues E (boundaryZ b E) _ _ (matchedA E) (matchedA E) δ hp
      (etaLow_le_im hb1 hκ hEκ) (norm_boundaryZ_le3 hb0 hb1 hκ hEκ) hsol ?_ ?_ hport ?_ ?_
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

/-- **One fresh layer, uniformly on `bulkInterval κ`** (at a deterministic Hermitian past): the conclusion `OneStepFacts` of `OpenInputsProof.one_step` with one set of
constants `r₀, q, Cst, C₀, a₀` for every `E ∈ bulkInterval κ`. -/
theorem oneStepFacts_unif (hQ : CavityMeanStatement) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ r₀ q Cst C₀ a₀ : ℝ, ∀ E ∈ bulkInterval κ, OneStepFacts b E r₀ q Cst C₀ a₀ := by
  obtain ⟨r₀, q, Cst, hr₀, hq0, hq1, hCst, hstep⟩ := step_bound_unif hb0 hb1 hκ hκ4
  obtain ⟨⟨a₀, C₀, ha₀, hC₀, h0⟩, h1⟩ := hQ b hb0 hb1 (etaLow b κ) 3 (etaLow_pos hb1 hκ hκ4)
  obtain ⟨a₁, C₁, ha₁, h1⟩ := h1 1
  refine ⟨r₀, q, Cst, max C₀ (max C₁ 0), min a₀ a₁, fun E hEκ => ?_⟩
  have hCm0 : 0 ≤ max C₀ (max C₁ 0) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hr₀, hq0, hq1, hCst, hCm0, lt_min ha₀ ha₁, ?_⟩
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have hzη := etaLow_le_im hb1 hκ hEκ
  have hz3 := norm_boundaryZ_le3 hb0 hb1 hκ hEκ
  intro W hW X hX
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, -, hmean0, hfl0⟩ := h0 W hW X hX E (boundaryZ b E) hzη hz3
  obtain ⟨hmean1, hfl1⟩ := h1 W hW X hX E (boundaryZ b E) hzη hz3
  simp only [iteratedDeriv_one] at hmean1 hfl1
  have hmono : ∀ c : ℝ, c ≤ max C₀ (max C₁ 0) → ∀ p : ℝ, 0 ≤ p →
      ENNReal.ofReal (c * Real.sqrt p / W) ≤
        ENNReal.ofReal (max C₀ (max C₁ 0) * Real.sqrt p / W) := by
    intro c hc p _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  refine ⟨fun p hp2 hpa => ⟨?_, ?_⟩, fun hδ y => ⟨?_, fun s hs => ?_⟩⟩
  · have hpa0 : p ≤ a₀ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
    refine (eLpNorm_mono (measurable_freshNoise0 b E X).aestronglyMeasurable
      fun y => (norm_norm _).le).trans ?_
    exact (hfl0 p hp2 hpa0).trans (hmono C₀ (le_max_left _ _) p (by linarith))
  · have hpa1 : p ≤ a₁ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
    refine (eLpNorm_mono (aesm_freshNoise1 b E hX hzpos) fun y => (norm_norm _).le).trans ?_
    exact (hfl1 p hp2 hpa1).trans
      (hmono C₁ ((le_max_left _ _).trans (le_max_right _ _)) p (by linarith))
  · obtain ⟨hsc, -⟩ := hstep E hEκ hW X hX hδ
    rw [jetDistance0_freshSchur]
    have htri := norm_sub_le_norm_sub_add_norm_sub (cavityHplus E X (boundaryZ b E) y)
      (∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b) (matchedA E)
    have htri2 := norm_sub_le_norm_sub_add_norm_sub
      (∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b) (cavityU X b E (boundaryZ b E))
      (matchedA E)
    have hm : ‖(∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b) -
        cavityU X b E (boundaryZ b E)‖ ≤ max C₀ (max C₁ 0) / (W : ℝ) ^ 2 :=
      hmean0.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have : freshNoise0 b E X y = ‖cavityHplus E X (boundaryZ b E) y -
        ∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b‖ := rfl
    linarith
  · obtain ⟨-, hj⟩ := hstep E hEκ hW X hX hδ
    rw [jetDistance1_freshSchur]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E))
      (∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b) s
    have htri2 := norm_sub_le_norm_sub_add_norm_sub
      (∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b)
      (deriv (cavityU X b E) (boundaryZ b E)) s
    have hm : ‖(∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b) -
        deriv (cavityU X b E) (boundaryZ b E)‖ ≤ max C₀ (max C₁ 0) / (W : ℝ) ^ 2 :=
      hmean1.trans (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
        (by positivity))
    have : freshNoise1 b E X y = ‖deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E) -
        ∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b‖ := rfl
    have := hj s hs
    linarith

/-- **The scalar step at the next layer, uniformly on `bulkInterval κ`**
(`OpenInputsProof.delta_next` with constants depending only on `(b, κ)`). -/
theorem delta_next_unif (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract)
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ (r₀ q C₂ Cn : ℝ) (W₀ : ℕ), 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C₂ ∧ 0 ≤ Cn ∧
      ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        (jetDistance0 b E X ≤ r₀ → ∀ ω, jetDistance0 b E (freshSchur E X ω) ≤
          q * jetDistance0 b E X + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω) ∧
        ∫⁻ ω, ENNReal.ofReal (portNoise b E X ω ^ 2) ∂freshLaw W b ≤
          ENNReal.ofReal (Cn / (W : ℝ) ^ 2) := by
  obtain ⟨r₀, q, Cs, hr₀, hq0, hq1, -, hstep⟩ := step_bound_unif hb0 hb1 hκ hκ4
  obtain ⟨⟨a₀, C, ha₀, hC, hcm⟩, -⟩ := cavityMean_of hGA hTM b hb0 hb1 (etaLow b κ) 3
    (etaLow_pos hb1 hκ hκ4)
  refine ⟨r₀, q, C, 2 * C ^ 2, ⌈2 / a₀⌉₊, hr₀, hq0, hq1, hC.le, by positivity, ?_⟩
  intro W hW hW₀ E hEκ X hX
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, -, hmean, hfl⟩ := hcm W hW X hX E (boundaryZ b E) (etaLow_le_im hb1 hκ hEκ)
    (norm_boundaryZ_le3 hb0 hb1 hκ hEκ)
  refine ⟨fun hδ ω => ?_, ?_⟩
  · have hsc := (hstep E hEκ hW X hX hδ).1
    have e : jetDistance0 b E (freshSchur E X ω) =
        ‖cavityHplus E X (boundaryZ b E) ω - matchedA E‖ := rfl
    rw [e]
    have htri : ‖cavityHplus E X (boundaryZ b E) ω - matchedA E‖ ≤ portNoise b E X ω +
        ‖(∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) -
          cavityU X b E (boundaryZ b E)‖ +
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ := by
      unfold portNoise
      refine (norm_sub_le_norm_sub_add_norm_sub _
        (∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) _).trans ?_
      have := norm_sub_le_norm_sub_add_norm_sub
        (∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) (cavityU X b E (boundaryZ b E))
        (matchedA E)
      linarith
    have : ‖(∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) -
        cavityU X b E (boundaryZ b E)‖ ≤ C / (W : ℝ) ^ 2 := hmean
    linarith
  · have h2W : (2 : ℝ) ≤ a₀ * W := by
      have h := (Nat.le_ceil (2 / a₀)).trans (by exact_mod_cast hW₀ : ((⌈2 / a₀⌉₊ : ℕ) : ℝ) ≤ W)
      rw [div_le_iff₀ ha₀] at h; linarith
    have h2 := hfl 2 le_rfl h2W
    rw [ENNReal.ofReal_ofNat] at h2
    have h2' : eLpNorm (fun ω => cavityHplus E X (boundaryZ b E) ω -
        ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) ((2 : ℕ) : ℝ≥0∞) (freshLaw W b) ≤
        ENNReal.ofReal (C * Real.sqrt 2 / W) := by
      simpa using h2
    have hm : AEStronglyMeasurable (fun ω => cavityHplus E X (boundaryZ b E) ω -
        ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) (freshLaw W b) :=
      ((meas_cavityHplus (E := E) X (boundaryZ b E)).sub measurable_const).aestronglyMeasurable
    have h := lintegral_ofReal_pow_le (by norm_num) hm (by positivity) h2'
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring

end MovingEnergy

end BlockBand.Endpoints.Clock
