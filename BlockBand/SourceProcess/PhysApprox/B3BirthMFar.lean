module

public import BlockBand.SourceProcess.PhysApprox.B3BirthMAlg
public import BlockBand.SourceProcess.SmallLeak.LeakHolds
public import BlockBand.SourceProcess.SmallLeak.FluxStart
public import BlockBand.Transmission.LengthUniform.ConductanceUniform
public import BlockBand.GaussianCalculus.LpGradient

/-!
# The far birth mass of a newborn tag

Measure `growthPathLaw W b`; domain `0 < b < 1/2`, `-2 < E < 2`; the newborn tag of birth index
`j` read at its birth length `j + 1`, `⌊Ws⌋ ≤ j < ⌊WT⌋`, `s > 0`.

* `fluxAt_one_le`: at a Hermitian two-port the whole far-to-near flux `Re Tr(FP'F)`, `F = 1 − P`,
  is at most `Tr T^{1/2}` (`start_flux_le` at the cutoff `h = 1`, where the omitted
  projection is `1` because the far transmission is `≤ 1`).
* `lintegral_newbornFar_le` (one width, no contract): almost surely
  `Y_{j+1;j} = D₊ᴴD₊` (`Bridge.ae_tagResponse_succ_new_full`), and `birth_leak_le` with
  `A = 1`, `birthFactor_norm_le` and the fresh moment `E(1 + ‖Δ‖/η)² ≤ B` give
  `E Re Tr((1−P)Y_{j+1;j}) ≤ B/(4η²) · E Tr T_j^{1/2}`.
* `fracTrace_half_le`: `Tr T^{1/2} ≤ (Wε + Tr T/ε)/2`; with `ε = W^{-1/2}`,
  `W⁻¹ Tr T^{1/2} ≤ W^{-1/2}(1 + g)/2`, `g = Tr T` the conductance.
* **`newbornFarMass_holds`**: with the length-uniform conductance moment
  (`lengthUniform_conductance_holds`, `E g_r ≤ C` for `(s/2)W ≤ r ≤ TW`) and `delta_moments`,
  `E[W⁻¹ Re Tr((1−P)Y_{j+1;j})] → 0` (rate `W^{-1/2}`), uniformly over `⌊Ws⌋ ≤ j < ⌊WT⌋`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthM

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.FractionalBulk
open BlockBand.SourceProcess.SmallLeak BlockBand.SourceProcess.TagBirth
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.Generator
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- `1 − P = farEmbed 1` for the path's near projection. -/
theorem one_sub_nearProjection_eq_farEmbed :
    1 - nearProjection W = farEmbed (1 : Matrix (Fin W) (Fin W) ℂ) :=
  one_sub_nearPortProj_eq_farEmbed

/-- **The whole far flux is at most `Tr T^{1/2}`** at a Hermitian two-port. -/
theorem fluxAt_one_le {b E : ℝ} (hη : 0 < etaZ b E) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) :
    fluxAt b E XX 1 ≤
      fracTrace (1 / 2) (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) := by
  have h := start_flux_le hη hXX (h := 1) zero_le_one
  simp only at h
  set d := portBlock (twoPortScattering b E XX) 1 1
  have hsp : ∀ t ∈ spectrum ℝ (1 - dᴴ * d), t ≤ 1 := by
    intro t ht
    rw [show (1 : Matrix (Fin W) (Fin W) ℂ) - dᴴ * d = algebraMap ℝ _ 1 - dᴴ * d by simp,
      ← spectrum.singleton_sub_eq] at ht
    obtain ⟨a, ha, u, hu, rfl⟩ := ht
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hD := Matrix.posSemidef_conjTranspose_mul_self d
    rw [hD.1.spectrum_real_eq_range_eigenvalues] at hu
    obtain ⟨i, rfl⟩ := hu
    have := hD.eigenvalues_nonneg i
    linarith
  have hA : cfc (omitIndicator 1) (1 - dᴴ * d) = 1 := by
    have hsa : IsSelfAdjoint (1 - dᴴ * d) :=
      Matrix.isHermitian_one.sub (Matrix.posSemidef_conjTranspose_mul_self d).1
    rw [cfc_congr (g := fun _ => (1 : ℝ)) (fun t ht => by
      simp only [omitIndicator, one_pow, ite_eq_left_iff, not_le]
      intro h1; exact absurd (hsp t ht) (not_le.mpr h1)), cfc_const_one (R := ℝ) _ hsa]
  rw [hA, one_mul] at h
  exact h

theorem fluxAt_one_nonneg (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    0 ≤ fluxAt b E XX 1 :=
  fluxAt_nonneg b E XX conjTranspose_one

/-- **The far birth mass of the newborn tag at one width.** -/
theorem lintegral_newbornFar_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {j : ℕ} (hj : 1 ≤ j) {B : ℝ}
    (hBb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Integrable (fun f => (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2) (freshLaw W b) ∧
        ∫ f, (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2 ∂freshLaw W b ≤ B) :
    ∫⁻ ω, ENNReal.ofReal (((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re)
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (B / (4 * etaZ b E ^ 2)) * ∫⁻ ω, ENNReal.ofReal
        (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W j ω)) ∂growthPathLaw W b := by
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  set μ := growthPathLaw W b
  set c := B / (4 * etaZ b E ^ 2)
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((farEmbed (1 : Matrix (Fin W) (Fin W) ℂ) *
      ((freshD b E (pastXX E W j x.1) x.2)ᴴ * freshD b E (pastXX E W j x.1) x.2)).trace.re)
  set Ψ : PastSample W j → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (c * fluxAt b E (pastXX E W j p) 1)
  have hmΦ : Measurable Φ := by
    have hXX : Measurable fun x : PastSample W j × LayerSample W .oneBlockOnePort =>
        pastXX E W j x.1 := (measurable_pastXX E j).comp measurable_fst
    have hDm := measurable_freshD_comp b E hXX measurable_snd
    exact (measurable_trace_re (measurable_matrix_mul' measurable_const
      (measurable_matrix_mul' (measurable_matrix_conjTranspose' hDm) hDm))).ennreal_ofReal
  have hmΨ : Measurable Ψ :=
    (measurable_const.mul (measurable_fluxAt_comp b E (measurable_pastXX E j)
      measurable_const)).ennreal_ofReal
  have hZ : ∀ᵐ ω ∂μ, pastCoords W j ω ∈ (Set.univ : Set (PastSample W j)) →
      ENNReal.ofReal (((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re) ≤
        Φ (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_tagResponse_succ_new_full hb0 hb hE1 hE2 hW] with ω hnew _
    rw [hnew j hj, pastXX_eq, one_sub_nearProjection_eq_farEmbed]
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ (Set.univ : Set (PastSample W j)) →
      ∫⁻ f, Φ (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with p hp _
    set XX := pastXX E W j p
    have hXp : (passiveY (nearSchur (boundaryZ b E) XX)).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    obtain ⟨hBi, hB⟩ := hBb _ hXp
    have hg0 := fluxAt_one_nonneg b E XX
    have hpt : ∀ f, Φ (p, f) ≤ ENNReal.ofReal ((1 + ‖freshDelta b E
        (nearSchur (boundaryZ b E) XX) f‖ / etaZ b E) ^ 2 / (4 * etaZ b E ^ 2) *
          fluxAt b E XX 1) := by
      intro f
      refine ENNReal.ofReal_le_ofReal ?_
      refine (birth_leak_le hη XX f conjTranspose_one (Matrix.mul_one 1)).trans
        (mul_le_mul_of_nonneg_right ?_ hg0)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) (birthFactor_norm_le hb0 hb hE1 hE2 hXp f) 2
    refine (lintegral_mono hpt).trans ?_
    have hI : Integrable (fun f => (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ /
        etaZ b E) ^ 2 / (4 * etaZ b E ^ 2) * fluxAt b E XX 1) (freshLaw W b) :=
      (hBi.div_const _).mul_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun f => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_mul_const, integral_div]
    have h4 : 0 < 4 * etaZ b E ^ 2 := by positivity
    calc (∫ f, (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ / etaZ b E) ^ 2
          ∂freshLaw W b) / (4 * etaZ b E ^ 2) * fluxAt b E XX 1
        ≤ B / (4 * etaZ b E ^ 2) * fluxAt b E XX 1 :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hB h4.le) hg0
      _ = c * fluxAt b E XX 1 := rfl
  have hI := lintegral_indicator_step (μ := μ) (μP := pastLaw W j b) (ν := freshLaw W b)
    (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) MeasurableSet.univ hmΦ hmΨ hZ hstep
  simp only [Set.preimage_univ, Set.indicator_univ] at hI
  refine hI.trans ?_
  have hcg : ∀ g : ℝ, 0 ≤ g → ENNReal.ofReal (c * g) ≤ ENNReal.ofReal c * ENNReal.ofReal g := by
    intro g hg
    by_cases hc : 0 ≤ c
    · rw [ENNReal.ofReal_mul hc]
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hc).le hg)]
      exact zero_le
  calc ∫⁻ ω, Ψ (pastCoords W j ω) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal c *
          ENNReal.ofReal (fluxAt b E (pastXX E W j (pastCoords W j ω)) 1) ∂μ :=
        lintegral_mono fun ω => hcg _ (fluxAt_one_nonneg b E _)
    _ = ENNReal.ofReal c *
          ∫⁻ ω, ENNReal.ofReal (fluxAt b E (pastXX E W j (pastCoords W j ω)) 1) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        refine mul_le_mul_right (lintegral_mono_ae ?_) _
        filter_upwards [ae_growth_isHermitian W b] with ω hA
        rw [← pastXX_eq]
        refine ENNReal.ofReal_le_ofReal ((fluxAt_one_le hη (pathSchur_isHermitian E j ω hA)).trans
          (le_of_eq ?_))
        rw [pathTransmission, ← pathX, pathX_eq]

/-- `Tr T^{1/2} ≤ (nε + Re Tr T/ε)/2` for `T ⪰ 0`, `ε > 0` (`√t ≤ (ε + t/ε)/2`). -/
theorem fracTrace_half_le {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι ℂ}
    (hT : T.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    fracTrace (1 / 2) T ≤ (Fintype.card ι * ε + T.trace.re / ε) / 2 := by
  rw [fracTrace_eq_sum_eigenvalues_psd hT, hT.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  have hpt : ∀ i, hT.1.eigenvalues i ^ (1 / 2 : ℝ) ≤ ε / 2 + hT.1.eigenvalues i / (2 * ε) := by
    intro i
    have ht := hT.eigenvalues_nonneg i
    rw [← Real.sqrt_eq_rpow, show ε / 2 + hT.1.eigenvalues i / (2 * ε) =
      (ε ^ 2 + hT.1.eigenvalues i) / (2 * ε) by field_simp, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (ε - Real.sqrt (hT.1.eigenvalues i)), Real.sq_sqrt ht]
  refine (Finset.sum_le_sum fun i _ => hpt i).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  field_simp
  rfl

/-- **The far birth mass of a newborn tag tends to `0`** (rate `W^{-1/2}`), uniformly over the
birth indices `⌊Ws⌋ ≤ j < ⌊WT⌋`:
`E[W⁻¹ Re Tr((1−P)Y_{j+1;j})] ≤ θ` eventually.
Inputs: `MatchedTracesContract`, `GaussianAbsorptionContract` (length-uniform conductance, `Δ`
moments) and `gaussianLpGradient_holds`.
-/
theorem newbornFarMass_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s →
      ∀ θ : ℝ, 0 < θ → ∀ᶠ W : ℕ in atTop, ∀ j : ℕ, ⌊(W : ℝ) * s⌋₊ ≤ j →
        j < ⌊(W : ℝ) * T⌋₊ →
        ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ *
            ((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re)
          ∂growthPathLaw W b ≤ ENNReal.ofReal θ := by
  intro b hb0 hb E hE1 hE2 s T hs θ hθ
  obtain ⟨hκ, hEκ⟩ := mem_bulkInterval_self hE1 hE2
  set κ := min (E + 2) (2 - E)
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  obtain ⟨CD, W₃, hCD, hΔ2⟩ := delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨Cg, hCg⟩ := lengthUniform_conductance_holds hMT hGA
    BlockBand.GaussianCalculus.gaussianLpGradient_holds b hb0 hb κ
    (s / 2) 1 hκ (by positivity) le_rfl
  obtain ⟨W₀, hW₀⟩ := hCg T
  set B := (1 + CD / etaZ b E) ^ 2
  set c := B / (4 * etaZ b E ^ 2)
  set Cg' := max Cg 0
  set K := c * (1 + Cg') / 2
  have hK : 0 ≤ K := by positivity
  filter_upwards [eventually_ge_atTop (max (max W₀ W₃) (max (⌈2 / s⌉₊ + 1)
    (⌈(K / θ) ^ 2⌉₊ + 1)))] with W hW j hj1 hj2
  have hW0' : W₀ ≤ W := le_trans (by simp) hW
  have hW3 : W₃ ≤ W := le_trans (by simp) hW
  have hWs' : ⌈2 / s⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hWK : ⌈(K / θ) ^ 2⌉₊ + 1 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW1
  have hWs : 2 ≤ (W : ℝ) * s := by
    have : 2 / s ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 / s⌉₊ ≤ W))
    rw [div_le_iff₀ hs] at this; linarith
  have hns : (W : ℝ) * s - 1 < ⌊(W : ℝ) * s⌋₊ := Nat.sub_one_lt_floor _
  have hj1' : 1 ≤ j := le_trans (Nat.le_floor (by push_cast; linarith)) hj1
  have hjε : s / 2 * W ≤ j := by
    have : ((⌊(W : ℝ) * s⌋₊ : ℕ) : ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith
  have hjT : (j : ℝ) ≤ T * W := by
    have hpos : 0 < ⌊(W : ℝ) * T⌋₊ := by omega
    have h1 : (1 : ℝ) ≤ W * T := Nat.floor_pos.mp hpos
    have h2 : ((⌊(W : ℝ) * T⌋₊ : ℕ) : ℝ) ≤ W * T := Nat.floor_le (by linarith)
    have h3 : (j : ℝ) < ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hj2
    linarith [mul_comm (W : ℝ) T]
  have hBb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Integrable (fun f => (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2) (freshLaw W b) ∧
        ∫ f, (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2 ∂freshLaw W b ≤ B := fun X hX =>
    delta_sq hCD hη (fun f => norm_nonneg _) (by exact_mod_cast hΔ2 W hW3 E hEκ X hX)
  have hfar := lintegral_newbornFar_le hb0 hb hE1 hE2 hW1 hj1' hBb
  have hg := hW₀ W hW0' E hEκ j hjε hjT
  -- the conductance bound
  have hfrac : ∫⁻ ω, ENNReal.ofReal (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W j ω))
      ∂growthPathLaw W b ≤ ENNReal.ofReal (Real.sqrt W * (1 + Cg') / 2) := by
    have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWr
    have hpt : ∀ᵐ ω ∂growthPathLaw W b,
        ENNReal.ofReal (fracTrace (1 / 2) (pathTransmission b E (fun _ => 0) W j ω)) ≤
          ENNReal.ofReal (Real.sqrt W / 2) +
            ENNReal.ofReal (Real.sqrt W / 2) * ‖pathConductance b E W j ω‖ₑ ^ (1 : ℝ) := by
      filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith : b < 1)
        hE1 hE2] with ω hP
      have hTp := pathTransmission_posSemidef hP j
      have h1 := fracTrace_half_le hTp (ε := (Real.sqrt W)⁻¹) (by positivity)
      have hg0 : 0 ≤ pathConductance b E W j ω := by
        have := hTp.trace_nonneg
        simp only [pathConductance, conductanceOf]
        exact (Complex.nonneg_iff.mp this).1
      rw [ENNReal.rpow_one, ← ofReal_norm, Real.norm_of_nonneg hg0,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
      refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
      simp only [Fintype.card_fin, pathConductance, conductanceOf]
      rw [← div_eq_mul_inv, Real.div_sqrt, div_inv_eq_mul]
      ring
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Real.sqrt W / 2) + ENNReal.ofReal (Real.sqrt W / 2) *
          ∫⁻ ω, ‖pathConductance b E W j ω‖ₑ ^ (1 : ℝ) ∂growthPathLaw W b
        ≤ ENNReal.ofReal (Real.sqrt W / 2) + ENNReal.ofReal (Real.sqrt W / 2) *
            ENNReal.ofReal Cg' := by
          gcongr; exact hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1; ring
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWr
  have hKW : K / θ ≤ Real.sqrt W := by
    rw [Real.le_sqrt (by positivity) hWr.le]
    have : (K / θ) ^ 2 ≤ ⌈(K / θ) ^ 2⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(K / θ) ^ 2⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈(K / θ) ^ 2⌉₊ ≤ W)
    linarith
  have hfin : (W : ℝ)⁻¹ * (c * (Real.sqrt W * (1 + Cg') / 2)) ≤ θ := by
    have e : (W : ℝ)⁻¹ * (c * (Real.sqrt W * (1 + Cg') / 2)) = K / Real.sqrt W := by
      rw [show (W : ℝ)⁻¹ * (c * (Real.sqrt W * (1 + Cg') / 2)) = K * (Real.sqrt W / W) by
        simp only [K]; ring, Real.sqrt_div_self', mul_one_div]
    rw [e, div_le_iff₀ hsW]
    rw [div_le_iff₀ hθ] at hKW
    linarith
  calc ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ *
          ((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (W : ℝ)⁻¹ *
          ENNReal.ofReal (((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re)
          ∂growthPathLaw W b :=
        lintegral_mono fun ω => by rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (W : ℝ)⁻¹ * ∫⁻ ω, ENNReal.ofReal
          (((1 - nearProjection W) * tagResponse b E W (j + 1) j ω).trace.re) ∂growthPathLaw W b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (W : ℝ)⁻¹ * (ENNReal.ofReal c *
          ENNReal.ofReal (Real.sqrt W * (1 + Cg') / 2)) := by
        gcongr
        exact hfar.trans (mul_le_mul_right hfrac _)
    _ ≤ ENNReal.ofReal θ := by
        by_cases hc : 0 ≤ c
        · rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal hfin
        · rw [ENNReal.ofReal_of_nonpos (not_le.mp hc).le, zero_mul, mul_zero]
          exact zero_le

end BlockBand.SourceProcess.PhysApprox.B3.BirthM
