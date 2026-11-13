module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreInitial
public import BlockBand.Endpoints.Response.TaggedConvexOrderFlat
public import BlockBand.Internal.Contracts.TransmissionUniform2

/-!
# Energy-uniform tagged convex order: moments and the initial value along moving energies

Fixed `0 < b < 1/2`, a base bulk energy `-2 < E < 2`, `s > 0`, and a tagged sequence `σ` with
moving energies `e_j → E` (`TcoTagSequence`); path law `growthPathLaw W b`, probe
`circularVectorLaw`. Eventually `e_j ∈ bulkInterval κ` with `κ = (2 - |E|)/2`
(`tcu_eventually_bulk`), where the energy-uniform contracts are applied.

* `tcu_momentsAlong`: `TccMomentsAlong b σ` (the full tag clock moments along `σ`) from
  `FullSourceMomentsEnergyUniformContract` (the moving-energy analogue of
  `tcc_momentsAlong_fixed`).
* `tcu_birth_sq`: `E(Z_{k+1;k} - d)² → 0` along `σ` from `TagBirthValueEnergyUniformContract`
  (`trace` at `p = 2`, `square`), as `tcc_birth_sq_fixed`.
* `tcu_birthAlong`: the initial value `TccBirthAlong b σ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.TransmissionUniform2
open scoped ENNReal NNReal ComplexOrder

/-- An energy in `bulkInterval κ`, `κ > 0`, lies in the open bulk `(-2, 2)`. -/
theorem tcu_bulk_bounds {κ e : ℝ} (hκ : 0 < κ) (he : e ∈ bulkInterval κ) : -2 < e ∧ e < 2 := by
  unfold bulkInterval at he
  obtain ⟨h1, h2⟩ := he
  constructor <;> linarith

/-- Along a tagged sequence with moving energies `e_j → E ∈ (-2, 2)`, there is a bulk margin
`κ > 0` with `e_j ∈ bulkInterval κ` eventually. -/
theorem tcu_eventually_bulk {s τ E : ℝ} (σ : TcoTagSequence s τ E) (hE1 : -2 < E) (hE2 : E < 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ j in atTop, σ.energy j ∈ bulkInterval κ := by
  obtain ⟨κ, hκ, hN⟩ := tco_bulk_margin hE1 hE2
  exact ⟨κ, hκ, σ.energy_tendsto.eventually_mem hN⟩

/-- **`TccMomentsAlong` along moving energies** from
`FullSourceMomentsEnergyUniformContract` (through `tco_tag_pow_bound` on `bulkInterval κ`).
-/
theorem tcu_momentsAlong (hMom : FullSourceMomentsEnergyUniformContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ}
    (σ : TcoTagSequence s τ E) : TccMomentsAlong b σ := by
  obtain ⟨κ, hκ, hbulk⟩ := tcu_eventually_bulk σ hE1 hE2
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, Eventually.of_forall fun j l _ _ => ?_⟩
    have := tcc_law_prob b (σ.energy j) (σ.W j) l (σ.k j)
    simp
  obtain ⟨C, W₀, -, hC⟩ := tco_tag_pow_bound hMom hb hb' hκ (τ + 1) (m := 2 * m) (by omega)
  refine ⟨C, ?_⟩
  filter_upwards [tcc_eventually_len σ W₀, hbulk] with j ⟨hW, hn⟩ he l hkl hln
  unfold tcc_law
  rw [lintegral_map (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (2 * m)))
    (tco_measurable_tagClock _ _ _ _ _)]
  exact hC (σ.W j) hW (σ.energy j) he l (le_trans (by exact_mod_cast hln) hn) (σ.k j) hkl

/-- **`E(Z_{k+1;k} - d)² → 0` along moving energies**, from
`TagBirthValueEnergyUniformContract` (`trace` at `p = 2`, `square`, on `bulkInterval κ`) and
`E_h(h*Qh - d)² = (Tr Q - d)² + Tr Q²`.
Moving-energy analogue of `tcc_birth_sq_fixed`.
-/
theorem tcu_birth_sq (hBirth : TagBirthValueEnergyUniformContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ} (hs : 0 < s)
    (σ : TcoTagSequence s τ E) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ j in atTop, ∫⁻ x, ENNReal.ofReal ((x - dStar b) ^ 2)
      ∂tcc_law b (σ.energy j) (σ.W j) (σ.k j + 1) (σ.k j) ≤ ENNReal.ofReal θ := by
  obtain ⟨κ, hκ, hbulk⟩ := tcu_eventually_bulk σ hE1 hE2
  have hsτ := tco_tagSequence_s_le σ
  set ε := s / 2
  set T := τ + 1
  have hε : 0 < ε := by positivity
  have hεT : ε < T := by simp only [ε, T]; linarith
  set θ' := Real.sqrt (θ / 2)
  have hθ' : 0 < θ' := Real.sqrt_pos.2 (by positivity)
  obtain ⟨W₁, hW₁⟩ := hBirth.trace b hb hb' κ hκ ε T 2 hε hεT (by norm_num) θ' hθ'
  obtain ⟨C, W₂, hW₂⟩ := hBirth.square b hb hb' κ hκ ε T hε hεT
  have hCW : Tendsto (fun j => C / (σ.W j : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp σ.width_tendsto
  have hk := σ.tag_tendsto.eventually (lt_mem_nhds (show ε < s by simp only [ε]; linarith))
  filter_upwards [tcc_eventually_len σ (max W₁ W₂), hk,
    hCW.eventually (gt_mem_nhds (show (0 : ℝ) < θ / 2 by positivity)), hbulk]
    with j ⟨hWj, hn⟩ hkj hCj he
  set W := σ.W j
  set k := σ.k j
  set e := σ.energy j
  have hW0 : (0 : ℝ) < W := by exact_mod_cast σ.W_pos j
  have hεk : ε * W ≤ k := by rw [lt_div_iff₀ hW0] at hkj; exact hkj.le
  have hkT : ((k + 1 : ℕ) : ℝ) ≤ T * W :=
    le_trans (by exact_mod_cast σ.tag_lt j) hn
  have htr := hW₁ W (le_trans (le_max_left _ _) hWj) e he k hεk hkT
  have hsqr := hW₂ W (le_trans (le_max_right _ _) hWj) e he k hεk hkT
  set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ * (tagResponse b e W (k + 1) k ω).trace -
    (dStar b : ℂ)
  set g : GrowthPath W → ℂ := fun ω => (((W : ℂ)⁻¹ • tagResponse b e W (k + 1) k ω) ^ 2).trace
  have hQ : ∀ ω, (W : ℂ)⁻¹ • tagResponse b e W (k + 1) k ω = tco_tagQ b e W (k + 1) k ω := by
    intro ω; unfold tco_tagQ; ext x y; simp [Complex.real_smul]
  have hpt : ∀ ω, ∫⁻ h, ENNReal.ofReal ((lmf_tagResponseClock b e W (k + 1) k (ω, h) -
      dStar b) ^ 2) ∂circularVectorLaw (Fin 2 × Fin W) ≤ ‖f ω‖ₑ ^ 2 + ‖g ω‖ₑ := by
    intro ω
    set B := tco_tagQ b e W (k + 1) k ω
    have hB : B.IsHermitian := (tco_posSemidef_tagQ b e W (k + 1) k ω).isHermitian
    obtain ⟨-, -, i2, e2⟩ := tcc_quadForm_centered hB (dStar b)
    simp_rw [tco_tagClock_eq_quadForm]
    rw [← ofReal_integral_eq_lintegral_ofReal i2 (ae_of_all _ fun _ => sq_nonneg _), e2,
      ← rvG_trace_re_eq hB]
    have e3 : ∑ i, hB.eigenvalues i ^ 2 = (g ω).re := by
      rw [← rvG_hsSq_eq hB, ← trace_conjTranspose_mul_self_re_eq_hsSq, hB.eq]
      simp only [g, hQ, pow_two]
      rfl
    have e4 : B.trace.re - dStar b = (f ω).re := by
      simp only [f, ← hQ ω, B, trace_smul, smul_eq_mul, Complex.sub_re]
      simp
    rw [e3, e4]
    calc ENNReal.ofReal ((f ω).re ^ 2 + (g ω).re)
        ≤ ENNReal.ofReal (‖f ω‖ ^ 2 + ‖g ω‖) := by
          refine ENNReal.ofReal_le_ofReal (add_le_add ?_ (Complex.re_le_norm _))
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
      _ = ‖f ω‖ₑ ^ 2 + ‖g ω‖ₑ := by
          rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _), ENNReal.ofReal_pow
            (norm_nonneg _), ofReal_norm, ofReal_norm]
  have hfm : Measurable f := by
    refine Measurable.sub ?_ measurable_const
    exact measurable_const.mul (Continuous.measurable (continuous_id.matrix_trace) |>.comp
      (tco_measurable_tagResponse b e W (k + 1) k))
  have hL2 : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b ≤ ENNReal.ofReal (θ / 2) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    have e : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b = ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂growthPathLaw W b := by
      simp_rw [← ENNReal.rpow_natCast]; norm_num
    rw [e, lintegral_rpow_enorm_eq_rpow_eLpNorm' h2]
    have h1 : eLpNorm f (ENNReal.ofReal 2) (growthPathLaw W b) =
        eLpNorm' f 2 (growthPathLaw W b) := by
      rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 h2).ne' ENNReal.ofReal_ne_top
        hfm.aestronglyMeasurable, ENNReal.toReal_ofReal h2.le]
    rw [← h1]
    calc eLpNorm f (ENNReal.ofReal 2) (growthPathLaw W b) ^ (2 : ℝ)
        ≤ ENNReal.ofReal θ' ^ (2 : ℝ) := ENNReal.rpow_le_rpow htr h2.le
      _ = ENNReal.ofReal (θ / 2) := by
          rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hθ'.le, Real.sq_sqrt (by positivity)]
  rw [tcc_lintegral_law _ _ _ _ _ (by fun_prop)]
  calc ∫⁻ ω, ∫⁻ h, ENNReal.ofReal ((lmf_tagResponseClock b e W (k + 1) k (ω, h) - dStar b) ^ 2)
        ∂circularVectorLaw (Fin 2 × Fin W) ∂growthPathLaw W b
      ≤ ∫⁻ ω, (‖f ω‖ₑ ^ 2 + ‖g ω‖ₑ) ∂growthPathLaw W b := lintegral_mono hpt
    _ = ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b + ∫⁻ ω, ‖g ω‖ₑ ∂growthPathLaw W b :=
        lintegral_add_left (hfm.enorm.pow_const 2) _
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (C / W) := add_le_add hL2 hsqr
    _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (max (C / W) 0) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (θ / 2 + max (C / W) 0) :=
        (ENNReal.ofReal_add (by positivity) (le_max_right _ _)).symm
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := max_lt hCj (show (0 : ℝ) < θ / 2 by positivity)
        linarith

/-- **Step 5 along moving energies**: the initial value `TccBirthAlong`, from
the `TagBirthValueEnergyUniformContract` and `FullSourceMomentsEnergyUniformContract`.
-/
theorem tcu_birthAlong (hMom : FullSourceMomentsEnergyUniformContract)
    (hBirth : TagBirthValueEnergyUniformContract) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ} (hs : 0 < s) (σ : TcoTagSequence s τ E) :
    TccBirthAlong b σ := by
  have hM := tcu_momentsAlong hMom hb hb' hE1 hE2 σ
  refine tcc_moment_tendsto_of_sq (fun j => tcc_law_prob _ _ _ _ _) (dStar b) (fun m => ?_)
    (tcu_birth_sq hBirth hb hb' hE1 hE2 hs σ)
  obtain ⟨C, hC⟩ := hM m
  exact ⟨C, hC.mono fun j hj => hj _ (Nat.lt_succ_self _) (σ.tag_lt j)⟩

end BlockBand.Endpoints
