module

public import BlockBand.SourceProcess.FullSourceCovariance.OffDomain
public import BlockBand.SourceProcess.FullSource.DeltaMeanHolds
public import BlockBand.Transmission.PassiveCovariance.Continuity

/-!
# Strict passivity suffices for the two on-domain `Δ`-covariance statements

The on-domain statements `DeltaCovarianceSameOnDomain`, `DeltaCovarianceOppositeOnDomain` quantify
over every passive `X` (`Y ⪰ 0`). The Gaussian integration by parts needs `Y ≻ 0` (a.s.
invertibility at every Hermitian sample). This file reduces both statements to their strictly
passive versions on a jet domain of twice the radius, by passing to the limit along
`X_n = X - i(n+1)⁻¹` (`PassiveCovariance.regX`), exactly as
`PassiveCovariance.passiveCovarianceOnDomain_of_strict` does for `U = LL*`.

* `tendsto_covs_of_ae`: Vitali for `bilinearCovariance` and `bilinearCrossCovariance` from a.s.
  convergence and a uniform `L⁴` bound on `‖U‖` (any probability space).
* `tendsto_jetDist_regX`: `δ₀ + δ₁ + g/W` is continuous along `regX`.
* `DeltaCovarianceSameOnDomainStrict`, `DeltaCovarianceOppositeOnDomainStrict`: the on-domain
  statements with `(passiveY X).PosDef`.
* **`deltaCovarianceSameOnDomain_of_strict hGA`**, **`deltaCovarianceOppositeOnDomain_of_strict hGA`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSource BlockBand.Transmission
open BlockBand.Transmission.PassiveLayer
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

section Vitali
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Entries of `U` are in `L²` with norm `≤ C` when `‖U‖ ∈ L⁴` with norm `≤ C`. -/
theorem eLpNorm_entry_le {U : Ω → Matrix (Fin W) (Fin W) ℂ} (hm : Measurable U) {C : ℝ}
    (hb : MomBd μ (fun ω => ‖U ω‖) 4 C) (i j : Fin W) :
    eLpNorm (fun ω => U ω i j) 2 μ ≤ ENNReal.ofReal C := by
  refine (eLpNorm_mono_ae_real hm.eval_matrix.aestronglyMeasurable
    (ae_of_all _ fun ω => PassiveCovariance.norm_entry_le (U ω) i j)).trans ?_
  refine (eLpNorm_le_eLpNorm_of_exponent_le (q := ENNReal.ofReal 4) ?_).trans hb.2
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- `‖E U‖ ≤ C` when `‖U‖ ∈ L⁴` with norm `≤ C`. -/
theorem norm_matrixExpect_le_of_momBd {U : Ω → Matrix (Fin W) (Fin W) ℂ} (hm : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : MomBd μ (fun ω => ‖U ω‖) 4 C) :
    ‖matrixExpect μ U‖ ≤ C := by
  have hb1 : MomBd μ (fun ω => ‖U ω‖) ((1 : ℕ) : ℝ) C := hb.exponent_mono (by norm_num)
  obtain ⟨hi, hle⟩ := integral_abs_pow_le (ν := μ) (n := 1) le_rfl hC hb1
  simp only [pow_one, abs_norm] at hi hle
  have hent : ∀ i j, Integrable (fun ω => U ω i j) μ := fun i j =>
    (MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_entry_le hm hb i j)
      ENNReal.ofReal_lt_top : MemLp _ 2 μ))
  exact (PassiveCovariance.norm_matrixExpect_le U hent hi).trans hle

/-- **Vitali for both bilinear covariances**: a.s. convergence of `U n` and a uniform `L⁴` bound
on `‖U n‖`, `‖U₀‖` give convergence of `Cov(x,y;x',y')` and `CrossCov(x,y;x',y')`. -/
theorem tendsto_covs_of_ae {U : ℕ → Ω → Matrix (Fin W) (Fin W) ℂ}
    {U₀ : Ω → Matrix (Fin W) (Fin W) ℂ} (hm : ∀ n, Measurable (U n)) (hm₀ : Measurable U₀)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, MomBd μ (fun ω => ‖U n ω‖) 4 C)
    (hb₀ : MomBd μ (fun ω => ‖U₀ ω‖) 4 C)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => U n ω) atTop (𝓝 (U₀ ω))) (x y x' y' : Fin W → ℂ) :
    Tendsto (fun n => bilinearCovariance μ (U n) x y x' y') atTop
        (𝓝 (bilinearCovariance μ U₀ x y x' y')) ∧
      Tendsto (fun n => bilinearCrossCovariance μ (U n) x y x' y') atTop
        (𝓝 (bilinearCrossCovariance μ U₀ x y x' y')) := by
  -- the means converge
  have hM : Tendsto (fun n => matrixExpect μ (U n)) atTop (𝓝 (matrixExpect μ U₀)) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two
      (fun n => (hm n).eval_matrix) ENNReal.ofReal_ne_top
      (fun n => eLpNorm_entry_le (hm n) (hb n) i j) (eLpNorm_entry_le hm₀ hb₀ i j) ?_
    filter_upwards [hae] with ω hω
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hω i) j
  have hMb : ∀ n, ‖matrixExpect μ (U n)‖ ≤ C := fun n =>
    norm_matrixExpect_le_of_momBd (hm n) hC (hb n)
  have hMb₀ : ‖matrixExpect μ U₀‖ ≤ C := norm_matrixExpect_le_of_momBd hm₀ hC hb₀
  -- the dominating function `∏‖v‖ (‖U‖ + C)²`
  set F := fourNorm x y x' y'
  have hF : 0 ≤ F := fourNorm_nonneg x y x' y'
  have dom : ∀ (V : Ω → Matrix (Fin W) (Fin W) ℂ), Measurable V →
      MomBd μ (fun ω => ‖V ω‖) 4 C →
      eLpNorm (fun ω => F * (‖V ω‖ + C) ^ 2) 2 μ ≤ ENNReal.ofReal (F * (C + C) ^ 2) := by
    intro V hV hVb
    have h1 : MomBd μ (fun ω => ‖V ω‖ + C) 4 (C + C) := by
      have := hVb.add (by norm_num) (MomBd.const (μ := μ) C 4 (by norm_num)) hC (abs_nonneg C)
      simpa [abs_of_nonneg hC] using this
    have h2 := PassiveCovariance.eLpNorm_pow_le (μ := μ) (g := fun ω => ‖V ω‖ + C) (C := C + C)
      (fun ω => by positivity) h1.1 2 (by norm_num)
      (by rw [show ENNReal.ofReal (2 * ((2 : ℕ) : ℝ)) = ENNReal.ofReal 4 by norm_num]; exact h1.2)
    have h3 : MomBd μ (fun ω => (‖V ω‖ + C) ^ 2) 2 ((C + C) ^ 2) := by
      refine ⟨h1.1.pow 2, ?_⟩
      rw [show ENNReal.ofReal 2 = 2 by simp, ENNReal.ofReal_pow (by positivity)]
      exact h2
    have h4 := h3.const_mul hF
    simpa [show ENNReal.ofReal 2 = 2 by simp] using h4.2
  have hKfin : ENNReal.ofReal (F * (C + C) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have pt : ∀ (V : Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin W) (Fin W) ℂ), ‖M‖ ≤ C →
      ‖bilinear x (V - M) y‖ * ‖bilinear x' (V - M) y'‖ ≤ F * (‖V‖ + C) ^ 2 := by
    intro V M hMC
    have h1 := PassiveCovariance.norm_bilinear_le x (V - M) y
    have h2 := PassiveCovariance.norm_bilinear_le x' (V - M) y'
    have hVM : ‖V - M‖ ≤ ‖V‖ + C := (norm_sub_le _ _).trans (by linarith)
    have := PassiveCovariance.vecNorm_nonneg x; have := PassiveCovariance.vecNorm_nonneg y
    have := PassiveCovariance.vecNorm_nonneg x'; have := PassiveCovariance.vecNorm_nonneg y'
    calc ‖bilinear x (V - M) y‖ * ‖bilinear x' (V - M) y'‖
        ≤ (vecNorm x * (‖V‖ + C) * vecNorm y) * (vecNorm x' * (‖V‖ + C) * vecNorm y') := by
          gcongr
          · exact h1.trans (by gcongr)
          · exact h2.trans (by gcongr)
      _ = F * (‖V‖ + C) ^ 2 := by simp only [F, fourNorm]; ring
  have cb : ∀ u v : Fin W → ℂ, Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u M v :=
    PassiveCovariance.continuous_bilinear
  have hmeasB : ∀ (u v : Fin W → ℂ) (V : Ω → Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin W) (Fin W) ℂ),
      Measurable V → Measurable fun ω => bilinear u (V ω - M) v := fun u v V M hV =>
    (cb u v).measurable.comp (hV.sub measurable_const)
  have haeT : ∀ᵐ ω ∂μ, Tendsto (fun n => U n ω - matrixExpect μ (U n)) atTop
      (𝓝 (U₀ ω - matrixExpect μ U₀)) := by
    filter_upwards [hae] with ω hω using hω.sub hM
  constructor
  · refine PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two
      (fun n => (hmeasB x y _ _ (hm n)).mul (hmeasB x' y' _ _ (hm n))) hKfin (fun n => ?_) ?_ ?_
    · refine (eLpNorm_mono_ae_real ((hmeasB x y _ _ (hm n)).mul
        (hmeasB x' y' _ _ (hm n))).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)).trans (dom _ (hm n) (hb n))
      rw [Pi.mul_apply, norm_mul]; exact pt _ _ (hMb n)
    · refine (eLpNorm_mono_ae_real ((hmeasB x y _ _ hm₀).mul
        (hmeasB x' y' _ _ hm₀)).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)).trans (dom _ hm₀ hb₀)
      rw [Pi.mul_apply, norm_mul]; exact pt _ _ hMb₀
    · filter_upwards [haeT] with ω hω
      exact (((cb x y).tendsto _).comp hω).mul (((cb x' y').tendsto _).comp hω)
  · have hms : ∀ (V : Ω → Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin W) (Fin W) ℂ),
        Measurable V → Measurable fun ω =>
          bilinear x (V ω - M) y * star (bilinear x' (V ω - M) y') := fun V M hV =>
      (hmeasB x y V M hV).mul (continuous_star.measurable.comp (hmeasB x' y' V M hV))
    refine PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two
      (fun n => hms _ _ (hm n)) hKfin (fun n => ?_) ?_ ?_
    · refine (eLpNorm_mono_ae_real (hms _ _ (hm n)).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)).trans (dom _ (hm n) (hb n))
      rw [norm_mul, norm_star]; exact pt _ _ (hMb n)
    · refine (eLpNorm_mono_ae_real (hms _ _ hm₀).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)).trans (dom _ hm₀ hb₀)
      rw [norm_mul, norm_star]; exact pt _ _ hMb₀
    · filter_upwards [haeT] with ω hω
      exact (((cb x y).tendsto _).comp hω).mul
        ((continuous_star.tendsto _).comp (((cb x' y').tendsto _).comp hω))

end Vitali

/-- `δ₀ + δ₁ + g/W` along `X_n = X - i(n+1)⁻¹`. -/
theorem tendsto_jetDist_regX {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) (s : ℂ) :
    Tendsto (fun n => jetDist b E s (PassiveCovariance.regX X n)) atTop
      (𝓝 (jetDist b E s X)) := by
  have hT : Tendsto (fun n => passiveTransmission b E (PassiveCovariance.regX X n)) atTop
      (𝓝 (passiveTransmission b E X)) :=
    (PassiveCovariance.tendsto_Q_regX hb0 hb h1 h2 hY).const_smul _
  have hg : Tendsto (fun n => conductanceOf (passiveTransmission b E (PassiveCovariance.regX X n)))
      atTop (𝓝 (conductanceOf (passiveTransmission b E X))) :=
    Complex.continuous_re.tendsto _ |>.comp ((continuous_id.matrix_trace.tendsto _).comp hT)
  exact ((PassiveCovariance.tendsto_jet0_regX hb0 hb h1 h2 hY).add
    (PassiveCovariance.tendsto_jet1_regX hb0 hb h1 h2 hY s)).add (hg.div_const _)

/-- `DeltaCovarianceSameOnDomain` for strictly passive `X` (`Y ≻ 0`). -/
def DeltaCovarianceSameOnDomainStrict : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
            sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- `DeltaCovarianceOppositeOnDomain` for strictly passive `X` (`Y ≻ 0`). -/
def DeltaCovarianceOppositeOnDomainStrict : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
            ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- The regularization limit of both `Δ`-covariances, `W₀` uniform on `bulkInterval κ`. -/
theorem tendsto_deltaCovs_regX (hGA : GaussianAbsorptionContract) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ x y x' y' : Fin W → ℂ,
      Tendsto (fun n => bilinearCovariance (freshLaw W b)
          (freshDelta b E (PassiveCovariance.regX X n)) x y x' y') atTop
          (𝓝 (bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y')) ∧
        Tendsto (fun n => bilinearCrossCovariance (freshLaw W b)
          (freshDelta b E (PassiveCovariance.regX X n)) x y x' y') atTop
          (𝓝 (bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y')) := by
  obtain ⟨C4, W₄, hC4, hmom⟩ := delta_moments hGA b hb0 hb κ hκ 4 (by norm_num)
  obtain ⟨_, W₃, hdet⟩ := PassiveLayer.moments_holds hGA b hb0 hb κ hκ 1 le_rfl
  refine ⟨max W₄ W₃, fun W hW E hE X hY x y x' y' => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hmeas : ∀ (Y : Matrix (Fin W) (Fin W) ℂ), Measurable fun ω => freshDelta b E Y ω :=
    fun Y => measurable_freshDelta_comp b E (X := fun _ => Y) measurable_const measurable_id
  have hdetX := (hdet W (le_of_max_le_right hW) E hE (boundaryZ b E)
    (PassiveLayer.boundaryZ_mem_paramDisk (by linarith) h1 h2) X hY).1
  have hae : ∀ᵐ ω ∂freshLaw W b, Tendsto (fun n => freshDelta b E (PassiveCovariance.regX X n) ω)
      atTop (𝓝 (freshDelta b E X ω)) := by
    filter_upwards [hdetX] with ω hω using tendsto_freshDelta_regX b E X ω hω
  exact tendsto_covs_of_ae (fun n => hmeas _) (hmeas X) hC4
    (fun n => hmom W (le_of_max_le_left hW) E hE _
      (PassiveCovariance.passiveY_regX_posSemidef hY n))
    (hmom W (le_of_max_le_left hW) E hE X hY) hae x y x' y'

/-- **Strict passivity suffices** for the equal-sign statement (radius `d/2`). -/
theorem deltaCovarianceSameOnDomain_of_strict (hGA : GaussianAbsorptionContract)
    (h : DeltaCovarianceSameOnDomainStrict) : DeltaCovarianceSameOnDomain := by
  intro b hb0 hb κ hκ
  obtain ⟨d, hd, C, W₀, hC⟩ := h b hb0 hb κ hκ
  obtain ⟨W₁, hW₁⟩ := tendsto_deltaCovs_regX hGA hb0 hb hκ
  refine ⟨d / 2, by positivity, C, max W₀ W₁, fun W hW E hE s hs X hY hX x y x' y' => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have tδ := tendsto_jetDist_regX hb0 hb h1 h2 hY s
  have hev : ∀ᶠ n in atTop, jetDist b E s (PassiveCovariance.regX X n) ≤ d :=
    tδ.eventually (ge_mem_nhds (by linarith))
  have tL := ((hW₁ W (le_of_max_le_right hW) E hE X hY x y x' y').1.sub
    (tendsto_const_nhds (x := sigmaMinus b E s / W * crossedTensor x y x' y' 1 1))).norm
  have tR : Tendsto (fun n => C * covErr b E s (PassiveCovariance.regX X n) *
      fourNorm x y x' y') atTop (𝓝 (C * covErr b E s X * fourNorm x y x' y')) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tδ)).const_mul _).mul_const _
  exact le_of_tendsto_of_tendsto tL tR (hev.mono fun n hn =>
    hC W (le_of_max_le_left hW) E hE s hs _ (PassiveCovariance.passiveY_regX_posDef hY n) hn
      x y x' y')

/-- **Strict passivity suffices** for the opposite-sign statement (radius `d/2`). -/
theorem deltaCovarianceOppositeOnDomain_of_strict (hGA : GaussianAbsorptionContract)
    (h : DeltaCovarianceOppositeOnDomainStrict) : DeltaCovarianceOppositeOnDomain := by
  intro b hb0 hb κ hκ
  obtain ⟨d, hd, C, W₀, hC⟩ := h b hb0 hb κ hκ
  obtain ⟨W₁, hW₁⟩ := tendsto_deltaCovs_regX hGA hb0 hb hκ
  refine ⟨d / 2, by positivity, C, max W₀ W₁, fun W hW E hE s hs X hY hX x y x' y' => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have tδ := tendsto_jetDist_regX hb0 hb h1 h2 hY s
  have hev : ∀ᶠ n in atTop, jetDist b E s (PassiveCovariance.regX X n) ≤ d :=
    tδ.eventually (ge_mem_nhds (by linarith))
  have tL := ((hW₁ W (le_of_max_le_right hW) E hE X hY x y x' y').2.sub
    (tendsto_const_nhds (x := ((sigmaPlus b : ℝ) : ℂ) / W *
      (bilinear x 1 x' * bilinear y' 1 y)))).norm
  have tR : Tendsto (fun n => C * covErr b E s (PassiveCovariance.regX X n) *
      fourNorm x y x' y') atTop (𝓝 (C * covErr b E s X * fourNorm x y x' y')) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tδ)).const_mul _).mul_const _
  exact le_of_tendsto_of_tendsto tL tR (hev.mono fun n hn =>
    hC W (le_of_max_le_left hW) E hE s hs _ (PassiveCovariance.passiveY_regX_posDef hY n) hn
      x y x' y')

end BlockBand.SourceProcess.FullSourceCovariance
