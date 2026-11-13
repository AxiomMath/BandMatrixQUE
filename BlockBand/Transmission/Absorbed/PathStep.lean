module

public import BlockBand.Transmission.Absorbed.LayerStep
public import BlockBand.Transmission.SourceMixing.MassMoment

/-!
# One path step of the absorbed mass-moment recursion

Along the path with profile `κ`, almost surely `X_{j+1} = freshSchur E (X_j - iε'_j) fresh_j`
for `j ≥ 1` (`ae_pathNearSchur_succ_abs`), and `X_j - iε'_j = stepInput κ j (past_j)`.
* `abs_integral_path_le`: Fubini over `pastLaw ⊗ freshLaw` for any measurable input map `S` of
  the past (`mp_integral_path_le`, with `stepInput 0` replaced by `S`);
* `abs_integrable_qc`, `abs_integrable_delta`: integrability along the absorbed path;
* **`abs_path_step`**: a one-layer bound at every absorbed input gives
  `x_{j+1} ≤ x_j(1 - cl/W) + (clⁿ⁺¹ + D₁ + D₂C_δⁿ⁺¹)/W`, `x_j = E qc(X^κ_j)ⁿ`, given
  `E δ₀(X^κ_j)ⁿ⁺¹ ≤ (C_δ/W)ⁿ⁺¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LawFinite
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- **Fubini over one fresh layer, for any measurable input map of the past.** -/
theorem abs_integral_path_le {b : ℝ} {j : ℕ} {S : PastSample W j → Matrix (Fin W) (Fin W) ℂ}
    (hS : Measurable S)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {M : ℝ} (hΨM : ∀ x, ‖Ψ x‖ ≤ M) {g : PastSample W j → ℝ} (hg : Measurable g)
    (hgi : Integrable (fun ω => g (pastCoords W j ω)) (growthPathLaw W b))
    (hbd : ∀ p ∈ hermPast W j, ∫ ω, Ψ (S p, ω) ∂freshLaw W b ≤ g p) :
    ∫ ω, Ψ (S (pastCoords W j ω), freshSample W j ω) ∂growthPathLaw W b ≤
      ∫ ω, g (pastCoords W j ω) ∂growthPathLaw W b := by
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ := fun x => Ψ (S x.1, x.2)
  have hΦ : Measurable Φ := hΨ.comp ((hS.comp measurable_fst).prodMk measurable_snd)
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have hgS : Integrable g (pastLaw W j b) := by
    have := (integrable_map_measure hg.aestronglyMeasurable
      (measurable_pastCoords W j).aemeasurable).2 hgi
    rwa [growthPathLaw_map_pastCoords] at this
  have hΦi : Integrable Φ ((pastLaw W j b).prod (freshLaw W b)) :=
    Integrable.of_bound hΦ.aestronglyMeasurable M (ae_of_all _ fun x => hΨM _)
  have m1 : ∫ ω, Φ (pastCoords W j ω, freshSample W j ω) ∂growthPathLaw W b =
      ∫ x, Φ x ∂((pastLaw W j b).prod (freshLaw W b)) := by
    rw [← growthPathLaw_map_past_fresh]
    exact (integral_map hT.aemeasurable hΦ.aestronglyMeasurable).symm
  have m2 : ∫ ω, g (pastCoords W j ω) ∂growthPathLaw W b = ∫ x, g x ∂pastLaw W j b := by
    rw [← growthPathLaw_map_pastCoords]
    exact (integral_map (measurable_pastCoords W j).aemeasurable hg.aestronglyMeasurable).symm
  change ∫ ω, Φ (pastCoords W j ω, freshSample W j ω) ∂growthPathLaw W b ≤ _
  rw [m1, m2, integral_prod Φ hΦi]
  refine integral_mono_ae hΦi.integral_prod_left hgS ?_
  filter_upwards [ae_pastLaw_hermitian W j b] with x hx
  exact hbd x hx

theorem abs_integrable_qc {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (κ : ℝ → ℝ)
    (n r : ℕ) :
    Integrable (fun ω => qc b E (pathNearSchur b E κ W r ω) ^ n) (growthPathLaw W b) := by
  have hm : Measurable fun ω => pathNearSchur b E κ W r ω := by
    have e : (fun ω => pathNearSchur b E κ W r ω) = pastX b E κ W r ∘ pastCoords W r := by
      funext ω; simp only [Function.comp, pathNearSchur_eq_past]
    rw [e]; exact (measurable_pastX b E κ r).comp (measurable_pastCoords W r)
  exact Integrable.of_bound (((measurable_qc b E).comp hm).pow_const n).aestronglyMeasurable
    ((W / (4 * etaZ b E)) ^ n) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (pow_nonneg (qc_nonneg b E _) n)]
      exact pow_le_pow_left₀ (qc_nonneg b E _) (qc_le hb h1 h2 _) n)

theorem abs_integrable_delta {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (k r : ℕ) :
    Integrable (fun ω => absorbedDelta b E κ W r ω ^ k) (growthPathLaw W b) := by
  refine Integrable.of_bound ((measurable_absorbedDelta b E κ r).pow_const k).aestronglyMeasurable
    (((etaZ b E)⁻¹ + 1) ^ k) ?_
  filter_upwards [ae_passiveSample W hκ (by linarith) h1 h2] with ω hP
  have h0 := absorbedDelta_nonneg b E κ r ω
  rw [Real.norm_of_nonneg (pow_nonneg h0 k)]
  exact pow_le_pow_left₀ h0 (jetDistance0_le_bound hb0 hb h1 h2 (pathNearSchur_passive hP r)) k

/-- **One path step of the absorbed mass-moment recursion.** -/
theorem abs_path_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) {K : ℝ} (hκK : ∀ s, κ s ≤ K)
    {n : ℕ} {c D₁ D₂ l Cδ : ℝ} (hD₂ : 0 ≤ D₂) (hW : 1 ≤ W)
    (hstep : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ K / (W : ℝ) ^ 2 →
      ∫ ω, qc b E (freshSchur E (absorbedInput X ε) ω) ^ n ∂freshLaw W b ≤
        qc b E X ^ n * (1 - c * l / W) +
          (c * l ^ (n + 1) + D₁ + D₂ * (W * jetDistance0 b E X) ^ (n + 1)) / W)
    {j : ℕ} (hj : 1 ≤ j)
    (hδ : ∫ ω, absorbedDelta b E κ W j ω ^ (n + 1) ∂growthPathLaw W b ≤ (Cδ / W) ^ (n + 1)) :
    ∫ ω, qc b E (pathNearSchur b E κ W (j + 1) ω) ^ n ∂growthPathLaw W b ≤
      (∫ ω, qc b E (pathNearSchur b E κ W j ω) ^ n ∂growthPathLaw W b) * (1 - c * l / W) +
        (c * l ^ (n + 1) + (D₁ + D₂ * Cδ ^ (n + 1))) / W := by
  set P := growthPathLaw W b
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hb1 : b < 1 := by linarith
  set a := 1 - c * l / W
  set β := (c * l ^ (n + 1) + D₁) / W
  set γ := D₂ * (W : ℝ) ^ (n + 1) / W
  have hγ : 0 ≤ γ := by positivity
  set X₀ : PastSample W j → Matrix (Fin W) (Fin W) ℂ := pastX b E κ W j
  set g : PastSample W j → ℝ := fun p =>
    a * qc b E (X₀ p) ^ n + (β + γ * jetDistance0 b E (X₀ p) ^ (n + 1))
  have hX₀ : Measurable X₀ := measurable_pastX b E κ j
  have hg : Measurable g := ((((measurable_qc b E).comp hX₀).pow_const n).const_mul a).add
    (measurable_const.add ((((measurable_jetDistance0 b E).comp hX₀).pow_const
      (n + 1)).const_mul γ))
  have hgX : ∀ ω, g (pastCoords W j ω) = a * qc b E (pathNearSchur b E κ W j ω) ^ n +
      (β + γ * absorbedDelta b E κ W j ω ^ (n + 1)) := fun ω => by
    simp only [g, X₀, absorbedDelta, pathNearSchur_eq_past]
  have hqi := abs_integrable_qc (W := W) hb1 h1 h2 κ n j
  have hδi := abs_integrable_delta (W := W) hb0 hb h1 h2 hκ (n + 1) j
  have hgi : Integrable (fun ω => g (pastCoords W j ω)) P := by
    simp only [hgX]
    exact (hqi.const_mul a).add ((integrable_const β).add (hδi.const_mul γ))
  set S := stepInput b E κ W j
  set Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ :=
    fun q => qc b E (freshSchur E q.1 q.2) ^ n
  have hΨ : Measurable Ψ := ((measurable_qc b E).comp (measurable_freshSchur_prod E)).pow_const n
  have hΨM : ∀ x, ‖Ψ x‖ ≤ (W / (4 * etaZ b E)) ^ n := fun x => by
    rw [Real.norm_of_nonneg (pow_nonneg (qc_nonneg b E _) n)]
    exact pow_le_pow_left₀ (qc_nonneg b E _) (qc_le hb1 h1 h2 _) n
  have hbd : ∀ p ∈ hermPast W j, ∫ ω, Ψ (S p, ω) ∂freshLaw W b ≤ g p := fun p hp => by
    have hY := passiveY_pastX hb1 h1 h2 hκ hp
    have hε0 : 0 ≤ layerAbsorption W κ (j + 1) 0 := div_nonneg (hκ _) (sq_nonneg _)
    have hεK : layerAbsorption W κ (j + 1) 0 ≤ K / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (hκK _) (sq_nonneg _)
    refine (hstep (X₀ p) hY _ hε0 hεK).trans_eq ?_
    simp only [g, a, β, γ, mul_pow]
    field_simp
  have hsucc : ∫ ω, qc b E (pathNearSchur b E κ W (j + 1) ω) ^ n ∂P =
      ∫ ω, Ψ (S (pastCoords W j ω), freshSample W j ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_pathNearSchur_succ_abs (W := W) (b := b) hb h1 h2 hW hκ] with ω hω
    simp only [Ψ, S, hω j hj, stepInput, pathNearSchur_eq_past]
  have hmain := abs_integral_path_le (b := b) (measurable_stepInput b E κ j) hΨ hΨM hg hgi hbd
  have hint : ∫ ω, g (pastCoords W j ω) ∂P = a * ∫ ω, qc b E (pathNearSchur b E κ W j ω) ^ n ∂P +
      (β + γ * ∫ ω, absorbedDelta b E κ W j ω ^ (n + 1) ∂P) := by
    have i1 : Integrable (fun ω => a * qc b E (pathNearSchur b E κ W j ω) ^ n) P := hqi.const_mul a
    have i3 : Integrable (fun ω => γ * absorbedDelta b E κ W j ω ^ (n + 1)) P := hδi.const_mul γ
    have i2 : Integrable (fun ω => β + γ * absorbedDelta b E κ W j ω ^ (n + 1)) P :=
      (integrable_const β).add i3
    simp only [hgX]
    rw [integral_add i1 i2, integral_const_mul, integral_add (integrable_const β) i3,
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have hγδ : γ * ∫ ω, absorbedDelta b E κ W j ω ^ (n + 1) ∂P ≤ D₂ * Cδ ^ (n + 1) / W := by
    calc γ * ∫ ω, absorbedDelta b E κ W j ω ^ (n + 1) ∂P ≤ γ * (Cδ / W) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hδ hγ
      _ = D₂ * Cδ ^ (n + 1) / W := by
          simp only [γ, div_pow]; field_simp
  rw [hsucc]
  refine hmain.trans ?_
  rw [hint]
  have e : (c * l ^ (n + 1) + (D₁ + D₂ * Cδ ^ (n + 1))) / W = β + D₂ * Cδ ^ (n + 1) / W := by
    simp only [β]; ring
  rw [e]
  linarith

end BlockBand.Transmission.Absorbed
