module

public import BlockBand.SourceProcess.LengthCont.OneLayer.Window
public import BlockBand.SourceProcess.RawTag.FrameMoments
public import BlockBand.SourceProcess.RawTag.StepScalar
public import BlockBand.Transmission.LengthUniform.DeltaZero
public import BlockBand.Transmission.SourceMixing.Conductance
public import BlockBand.Transmission.EnergyUniform.Holds

/-!
# Moments of the past quantities on the probed path

* `δ₀ = jetDistance0 (pathX n)`: `∫ δ₀^q ≤ (C_q/W)^q` (`delta_moment`, from
  `LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp`);
* unit frames: `∫ ‖f‖^r ≤ A_r^r` (`frame_moment`, from `RawTag.momBd_frame` and
  `EnergyUniform.fullSourceMomentsEnergyUniform_holds hGA hLp hSR`);
* `H = 1 + hsA ℝ + hsB ℝ = 1 + g/(2η²)` a.s. (`hs_eq_conductance`), so
  `∫ H^p ≤ 2^p (1 + (2η²)^{-p} C_p (1 + W^p/(n+1)^p))` (`hFun_moment`, from
  `SourceMixing.conductanceMomentBound_holds hMT hGA hLp`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.RawTag BlockBand.SourceProcess.ComplexSourceLaw
open scoped Matrix ComplexOrder ComplexConjugate ENNReal

variable {W : ℕ}

/-- `(a + b)^k ≤ 2^k (a^k + b^k)` for `a, b ≥ 0`. -/
theorem add_pow_le_two_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (a + b) ^ k ≤ 2 ^ k * (a ^ k + b ^ k) := by
  have hm : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hmk : max a b ^ k ≤ a ^ k + b ^ k := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha k]
    · rw [max_eq_left h]; linarith [pow_nonneg hb k]
  calc (a + b) ^ k ≤ (2 * max a b) ^ k := pow_le_pow_left₀ (by positivity) hm k
    _ = 2 ^ k * max a b ^ k := by rw [mul_pow]
    _ ≤ 2 ^ k * (a ^ k + b ^ k) := by gcongr

/-- A function of the path coordinate integrates against `probedPathLaw` as against the
path law. -/
theorem lintegral_fst_probed {np : ℕ} (b : ℝ) (F : GrowthPath W → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x.1 ∂probedPathLaw W np b = ∫⁻ ω, F ω ∂growthPathLaw W b := by
  have h : (probedPathLaw W np b).map Prod.fst = growthPathLaw W b := by
    rw [probedPathLaw, Measure.map_fst_prod, measure_univ, one_smul]
  rw [← h, lintegral_map hF measurable_fst]

theorem measurable_delta (b E : ℝ) (n : ℕ) :
    Measurable fun ω : GrowthPath W => jetDistance0 b E (pathX b E W n ω) :=
  (measurable_jetDistance0 b E).comp (BlockBand.Transmission.PathJet.measurable_pathX b E n)

theorem measurable_hFun (b E : ℝ) (n : ℕ) : Measurable fun ω : GrowthPath W => hFun b E W n ω := by
  have hR : Measurable fun ω : GrowthPath W => boundaryResolvent b E W n ω :=
    Measurable.of_eval_matrix _ fun _ _ =>
      (BlockBand.SourceProcess.FullSourceStops.measurable_fullInverse b E n).eval_matrix
  have h1 : ∀ x y : Fin 2 × Fin W, Measurable fun ω => boundaryResolvent b E W n ω x y :=
    fun x y => hR.eval_matrix
  unfold hFun hsA hsB
  fun_prop

/-- **`δ₀` moments.** -/
theorem delta_moment (hδ : BlockBand.Transmission.LengthUniform.DeltaZeroLengthUniform)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T' : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ T' * W → ∀ np : ℕ,
        ∫⁻ x, ENNReal.ofReal (jetDistance0 b E (pathX b E W n x.1) ^ q)
          ∂probedPathLaw W np b ≤ ENNReal.ofReal ((C / W) ^ q) := by
  obtain ⟨C, hC, hT⟩ := hδ b hb0 hb κ q hκ (by exact_mod_cast hq)
  refine ⟨C, hC, fun T' => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hT T'
  refine ⟨W₀, fun W hW E hE n hn hnT np => ?_⟩
  have hm : MomBd (growthPathLaw W b) (fun ω => jetDistance0 b E (pathX b E W n ω)) q (C / W) :=
    ⟨(measurable_delta b E n).aestronglyMeasurable, hW₀ W hW E hE n hn hnT⟩
  have h := lintegral_pow_le_of_momBd' hq hm (by positivity) (fun _ => norm_nonneg _)
  rw [lintegral_fst_probed b (fun ω => ENNReal.ofReal (jetDistance0 b E (pathX b E W n ω) ^ q))
    ((measurable_delta b E n).pow_const q).ennreal_ofReal]
  exact h

/-- **Frame moments.** -/
theorem frame_moment (hFS : FullSourceMomentsEnergyUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (T' : ℝ) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (A : ℝ) (W₀ : ℕ), 0 ≤ A ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ l β : ℕ, β < l →
      (l : ℝ) ≤ T' * W → ∀ (np : ℕ) (j : Fin np),
        ∫⁻ x, ENNReal.ofReal (vecNorm (frame b E W l β x.1 (x.2 j)) ^ r)
          ∂probedPathLaw W np b ≤ ENNReal.ofReal (A ^ r) := by
  obtain ⟨A, W₀, hA, h⟩ := momBd_frame hFS hb0 hb hκ T' (r := r) (by exact_mod_cast hr)
  refine ⟨A, W₀, hA, fun W hW E hE l β hβ hl np j => ?_⟩
  have hmap : (Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)).map
      (fun t : Fin np → Fin W → ℂ => t j) = circularVectorLaw (Fin W) := by
    classical
    rw [show (fun t : Fin np → Fin W → ℂ => t j) = Function.eval j from rfl, Measure.pi_map_eval]
    simp
  have hm := h W hW E hE l β hβ hl (Fin np → Fin W → ℂ)
    (Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)) (fun t => t j)
    (measurable_pi_apply j) hmap
  exact lintegral_pow_le_of_momBd' (by omega) hm hA (fun _ => vecNorm_nonneg _)

/-- `H = 1 + g/(2η²)` a.s. -/
theorem ae_hFun_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (n : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b,
      hFun b E W n ω = 1 + pathConductance b E W n ω / (2 * etaZ b E ^ 2) := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hη' : 0 < etaZ b E := hη
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E] with ω hA hF
  obtain ⟨h1, h2⟩ := hs_eq_conductance b E n ω hA hη (hF n)
  have e1 : hsA (boundaryResolvent b E W n ω) = hs01 b E W n ω := rfl
  have e2 : hsB (boundaryResolvent b E W n ω) = hs10 b E W n ω := rfl
  rw [hFun, e1, e2, h1, h2]
  field_simp
  ring

/-- **Moments of `H`** (from the conductance moments). -/
theorem hFun_moment (hCM : ConductanceMomentBound) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (T' : ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W → ∀ n : ℕ, (n : ℝ) ≤ T' * W → ∀ np : ℕ,
      ∫⁻ x, ENNReal.ofReal (hFun b E W n x.1 ^ p) ∂probedPathLaw W np b ≤
        ENNReal.ofReal (2 ^ p * (1 + ((2 * etaZ b E ^ 2) ^ p)⁻¹ * C *
          (1 + (W : ℝ) ^ p / ((n : ℝ) + 1) ^ p))) := by
  obtain ⟨C, hC⟩ := hCM b hb0 hb E hE1 hE2 T' p (by exact_mod_cast hp)
  have hη' : 0 < etaZ b E := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  set c : ℝ := ((2 * etaZ b E ^ 2) ^ p)⁻¹
  have hc : 0 ≤ c := by positivity
  refine ⟨max C 0, le_max_right _ _, fun W hW n hn np => ?_⟩
  rw [lintegral_fst_probed b (fun ω => ENNReal.ofReal (hFun b E W n ω ^ p))
    ((measurable_hFun b E n).pow_const p).ennreal_ofReal]
  have hg := hC W (by omega) n hn
  simp only [Real.rpow_natCast] at hg
  set g := pathConductance b E W n
  have hpt : ∀ᵐ ω ∂growthPathLaw W b, ENNReal.ofReal (hFun b E W n ω ^ p) ≤
      ENNReal.ofReal (2 ^ p) + ENNReal.ofReal (2 ^ p * c) * ‖g ω‖ₑ ^ (p : ℝ) := by
    filter_upwards [ae_hFun_eq hb0 hb hE1 hE2 hW n] with ω hω
    have hH0 : 0 ≤ hFun b E W n ω := by
      unfold hFun; linarith [hsA_nonneg (boundaryResolvent b E W n ω),
        hsB_nonneg (boundaryResolvent b E W n ω)]
    have hle : hFun b E W n ω ≤ 1 + |g ω| / (2 * etaZ b E ^ 2) := by
      rw [hω]; gcongr; exact le_abs_self _
    have h1 : hFun b E W n ω ^ p ≤ 2 ^ p * (1 + c * |g ω| ^ p) := by
      calc hFun b E W n ω ^ p ≤ (1 + |g ω| / (2 * etaZ b E ^ 2)) ^ p :=
            pow_le_pow_left₀ hH0 hle p
        _ ≤ 2 ^ p * (1 ^ p + (|g ω| / (2 * etaZ b E ^ 2)) ^ p) :=
            add_pow_le_two_pow zero_le_one (by positivity) p
        _ = 2 ^ p * (1 + c * |g ω| ^ p) := by rw [one_pow, div_pow]; simp only [c]; ring
    have e : ‖g ω‖ₑ ^ (p : ℝ) = ENNReal.ofReal (|g ω| ^ p) := by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow (abs_nonneg _), ENNReal.rpow_natCast]
    rw [e, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [h1]
  calc ∫⁻ ω, ENNReal.ofReal (hFun b E W n ω ^ p) ∂growthPathLaw W b
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 ^ p) + ENNReal.ofReal (2 ^ p * c) * ‖g ω‖ₑ ^ (p : ℝ))
          ∂growthPathLaw W b := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 ^ p) + ENNReal.ofReal (2 ^ p * c) *
          ∫⁻ ω, ‖g ω‖ₑ ^ (p : ℝ) ∂growthPathLaw W b := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 ^ p) + ENNReal.ofReal (2 ^ p * c) *
          ENNReal.ofReal (max C 0 * (1 + (W : ℝ) ^ p / ((n : ℝ) + 1) ^ p)) := by
        gcongr
        refine hg.trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = ENNReal.ofReal (2 ^ p * (1 + c * max C 0 * (1 + (W : ℝ) ^ p / ((n : ℝ) + 1) ^ p))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1; ring

end BlockBand.SourceProcess.LengthCont.OneLayer
