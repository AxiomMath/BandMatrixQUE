module

public import BlockBand.Transmission.PassiveCovarianceBulk.Props
public import BlockBand.Transmission.PassiveCovarianceBulk.Scalars
public import BlockBand.Transmission.LengthUniform.BulkMeanField
public import BlockBand.Transmission.PassiveCovariance.Regularization
public import BlockBand.Transmission.PassiveCovariance.Continuity
public import BlockBand.Transmission.PassiveCovariance.Assembly

/-!
# Bulk-uniform regularization and strict-passivity reduction

The regularization limit along `X_n = X - i(n+1)⁻¹` and the reduction of the near-domain bound to
strictly passive inputs, with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds bulk_eta_le_one bulk_norm_z)
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Regularization limit**: along `X_n = X - i(n+1)⁻¹`, the bilinear covariance of the
fresh transport converges to that at `X`, for every passive `X` and `W ≥ W₀`. Input:
`PassiveBoundsStatement.moments` (`p = 4, 8`, at `w = z_∂`), which gives a.s. invertibility at
`X` and uniform moments of `L` over passive inputs.
Bulk-uniform copy of `tendsto_bilinearCovariance_regX` (constants uniform on `bulkInterval κ`). -/
theorem tendsto_bilinearCovariance_regX_bulk (hA : BlockBand.Transmission.PassiveLayer.PassiveBoundsStatement)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        Tendsto (fun n => bilinearCovariance (freshLaw W b) (freshU b E (PassiveCovariance.regX X n)) v₁ v₂ v₃ v₄)
          atTop (𝓝 (bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄)) := by
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb κ hκ 4 (by norm_num)
  obtain ⟨C8, W8, h8⟩ := hA.moments b hb0 hb κ hκ 8 (by norm_num)
  refine ⟨max W4 W8, fun W hW E hEκ X hX v₁ v₂ v₃ v₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hz := BlockBand.Transmission.PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  set μ := freshLaw W b
  -- moment bounds, uniform over passive inputs
  have m4 : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (fun ω => ‖freshL b E X' ω‖) (ENNReal.ofReal (2 * (2 : ℕ))) μ ≤ ENNReal.ofReal C4 :=
    fun X' hX' => by
      have := (h4 W (le_trans (le_max_left _ _) hW) E hEκ _ hz X' hX').2.2.2
      norm_num at this ⊢; exact this
  have m8 : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (fun ω => ‖freshL b E X' ω‖) (ENNReal.ofReal (2 * (4 : ℕ))) μ ≤ ENNReal.ofReal C8 :=
    fun X' hX' => by
      have := (h8 W (le_trans (le_max_right _ _) hW) E hEκ _ hz X' hX').2.2.2
      norm_num at this ⊢; exact this
  have hinv := (h4 W (le_trans (le_max_left _ _) hW) E hEκ _ hz X hX).1
  -- the three integrands and their bounds
  have hg0 : ∀ X' (ω : LayerSample W .oneBlockOnePort), 0 ≤ ‖freshL b E X' ω‖ := fun _ _ => norm_nonneg _
  have bnd2 : ∀ (u v : Fin W → ℂ) X', (passiveY X').PosSemidef →
      eLpNorm (fun ω => bilinear u (freshU b E X' ω) v) 2 μ ≤
        ENNReal.ofReal (vecNorm u * vecNorm v) * ENNReal.ofReal C4 ^ 2 := fun u v X' hX' =>
    eLpNorm_two_le_of_pow_bound (measurable_bilinear_freshU b E X' u v).aestronglyMeasurable
      (hg0 X') (measurable_norm_freshL b E X').aestronglyMeasurable
      (mul_nonneg (vecNorm_nonneg u) (vecNorm_nonneg v)) 2 (by norm_num) (fun ω => by
        refine (norm_bilinear_le _ _ _).trans ?_
        have := norm_freshU_le b E X' ω
        have := vecNorm_nonneg u; have := vecNorm_nonneg v
        calc vecNorm u * ‖freshU b E X' ω‖ * vecNorm v ≤ vecNorm u * ‖freshL b E X' ω‖ ^ 2 * vecNorm v := by gcongr
          _ = _ := by ring) (m4 X' hX')
  have bnd4 : ∀ X', (passiveY X').PosSemidef →
      eLpNorm (fun ω => bilinear v₁ (freshU b E X' ω) v₂ * bilinear v₃ (freshU b E X' ω) v₄) 2 μ ≤
        ENNReal.ofReal (fourNorm v₁ v₂ v₃ v₄) * ENNReal.ofReal C8 ^ 4 := fun X' hX' =>
    eLpNorm_two_le_of_pow_bound ((measurable_bilinear_freshU b E X' v₁ v₂).mul
      (measurable_bilinear_freshU b E X' v₃ v₄)).aestronglyMeasurable
      (hg0 X') (measurable_norm_freshL b E X').aestronglyMeasurable
      (fourNorm_nonneg v₁ v₂ v₃ v₄) 4 (by norm_num) (fun ω => by
        show ‖bilinear v₁ (freshU b E X' ω) v₂ * bilinear v₃ (freshU b E X' ω) v₄‖ ≤ _
        rw [norm_mul]
        have a1 := norm_bilinear_le v₁ (freshU b E X' ω) v₂
        have a2 := norm_bilinear_le v₃ (freshU b E X' ω) v₄
        have hu := norm_freshU_le b E X' ω
        have := vecNorm_nonneg v₁; have := vecNorm_nonneg v₂; have := vecNorm_nonneg v₃
        have := vecNorm_nonneg v₄
        calc ‖bilinear v₁ (freshU b E X' ω) v₂‖ * ‖bilinear v₃ (freshU b E X' ω) v₄‖
            ≤ (vecNorm v₁ * ‖freshL b E X' ω‖ ^ 2 * vecNorm v₂) *
                (vecNorm v₃ * ‖freshL b E X' ω‖ ^ 2 * vecNorm v₄) := by
              gcongr
              · exact a1.trans (by gcongr)
              · exact a2.trans (by gcongr)
          _ = _ := by rw [fourNorm]; ring) (m8 X' hX')
  have bndE : ∀ X', (passiveY X').PosSemidef → ∀ i j,
      eLpNorm (fun ω => freshU b E X' ω i j) 2 μ ≤ ENNReal.ofReal 1 * ENNReal.ofReal C4 ^ 2 :=
    fun X' hX' i j =>
    eLpNorm_two_le_of_pow_bound ((measurable_freshU b E X').eval_matrix).aestronglyMeasurable
      (hg0 X') (measurable_norm_freshL b E X').aestronglyMeasurable zero_le_one 2 (by norm_num)
      (fun ω => by rw [one_mul]; exact (norm_entry_le _ i j).trans (norm_freshU_le b E X' ω))
      (m4 X' hX')
  have fin : ∀ (c C : ℝ) (k : ℕ), ENNReal.ofReal c * ENNReal.ofReal C ^ k ≠ ∞ := fun c C k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have integ : ∀ {f : LayerSample W .oneBlockOnePort → ℂ} {K : ℝ≥0∞}, K ≠ ∞ →
      eLpNorm f 2 μ ≤ K → Integrable f μ := fun hK hf =>
    MemLp.integrable one_le_two (lt_of_le_of_lt hf hK.lt_top : MemLp _ 2 μ)
  have covEq : ∀ X', (passiveY X').PosSemidef →
      bilinearCovariance μ (freshU b E X') v₁ v₂ v₃ v₄ =
        (∫ ω, bilinear v₁ (freshU b E X' ω) v₂ * bilinear v₃ (freshU b E X' ω) v₄ ∂μ) -
          (∫ ω, bilinear v₁ (freshU b E X' ω) v₂ ∂μ) * ∫ ω, bilinear v₃ (freshU b E X' ω) v₄ ∂μ :=
    fun X' hX' => bilinearCovariance_eq _ _ _ _ _
      (fun i j => integ (fin _ _ _) (bndE X' hX' i j)) (integ (fin _ _ _) (bnd2 v₁ v₂ X' hX'))
      (integ (fin _ _ _) (bnd2 v₃ v₄ X' hX')) (integ (fin _ _ _) (bnd4 X' hX'))
  have hXn := fun n => passiveY_regX_posSemidef hX n
  simp only [covEq _ (hXn _), covEq X hX]
  -- a.s. convergence of the transport
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => freshU b E (PassiveCovariance.regX X n) ω) atTop (𝓝 (freshU b E X ω)) := by
    filter_upwards [hinv] with ω hω using tendsto_freshU_regX b E X ω hω
  have cb : ∀ u v : Fin W → ℂ, Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u M v :=
    fun u v => by unfold bilinear; fun_prop
  have t12 := tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => measurable_bilinear_freshU b E (PassiveCovariance.regX X n) v₁ v₂) (fin _ _ 2)
    (fun n => bnd2 v₁ v₂ _ (hXn n)) (bnd2 v₁ v₂ X hX)
    (by filter_upwards [hae] with ω hω using ((cb v₁ v₂).tendsto _).comp hω)
  have t34 := tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => measurable_bilinear_freshU b E (PassiveCovariance.regX X n) v₃ v₄) (fin _ _ 2)
    (fun n => bnd2 v₃ v₄ _ (hXn n)) (bnd2 v₃ v₄ X hX)
    (by filter_upwards [hae] with ω hω using ((cb v₃ v₄).tendsto _).comp hω)
  have tp := tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => (measurable_bilinear_freshU b E (PassiveCovariance.regX X n) v₁ v₂).mul
      (measurable_bilinear_freshU b E (PassiveCovariance.regX X n) v₃ v₄)) (fin _ _ 4)
    (fun n => bnd4 _ (hXn n)) (bnd4 X hX)
    (by filter_upwards [hae] with ω hω using
      (((cb v₁ v₂).tendsto _).comp hω).mul (((cb v₃ v₄).tendsto _).comp hω))
  exact tp.sub (t12.mul t34)

/-- **Strict passivity suffices**: with `PassiveBoundsStatement`, the near-domain bound for
strictly passive inputs implies it for all passive inputs (at half the radius), by passing to
the limit along `PassiveCovariance.regX`.
Bulk-uniform copy of `passiveCovarianceOnDomain_of_strict` (constants uniform on
`bulkInterval κ`). -/
theorem passiveCovarianceOnDomain_of_strict_bulk
    (hA : BlockBand.Transmission.PassiveLayer.PassiveBoundsStatement)
    (h : PassiveCovarianceOnDomainStrictBulk) : PassiveCovarianceOnDomainBulk := by
  intro b hb0 hb κ hκ
  obtain ⟨d, C, W₀, hd, hC⟩ := h b hb0 hb κ hκ
  obtain ⟨W₁, hW₁⟩ := tendsto_bilinearCovariance_regX_bulk hA hb0 hb hκ
  refine ⟨d / 2, C, max W₀ W₁, by positivity, fun W hW E hEκ s hs X hX hδ v₁ v₂ v₃ v₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  set δ : Matrix (Fin W) (Fin W) ℂ → ℝ := fun X' =>
    jetDistance0 b E X' + jetDistance1 b E s X' + passiveMass b E X' / W
  have tδ : Tendsto (fun n => δ (PassiveCovariance.regX X n)) atTop (𝓝 (δ X)) :=
    ((tendsto_jet0_regX hb0 hb h1 h2 hX).add (tendsto_jet1_regX hb0 hb h1 h2 hX s)).add
      ((tendsto_mass_regX hb0 hb h1 h2 hX).div_const _)
  have hev : ∀ᶠ n in atTop, δ (PassiveCovariance.regX X n) ≤ d :=
    tδ.eventually (ge_mem_nhds (by show δ X < d; simp only [δ]; linarith))
  have tL := ((hW₁ W (le_trans (le_max_right _ _) hW) E hEκ X hX v₁ v₂ v₃ v₄).sub
    (tendsto_mainTensor_regX hb0 hb h1 h2 hX s v₁ v₂ v₃ v₄)).norm
  have tR : Tendsto (fun n => C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ (PassiveCovariance.regX X n)) * fourNorm v₁ v₂ v₃ v₄)
      atTop (𝓝 (C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ X) * fourNorm v₁ v₂ v₃ v₄)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tδ)).const_mul _).mul_const _
  exact le_of_tendsto_of_tendsto tL tR (hev.mono fun n hn =>
    hC W (le_trans (le_max_left _ _) hW) E hEκ s hs _ (passiveY_regX_posDef hX n) hn v₁ v₂ v₃ v₄)

/-- **Homogeneity**: the normalized bound implies the strict near-domain bound.
Bulk-uniform copy of `strict_of_normalized` (constants uniform on `bulkInterval κ`). -/
theorem strict_of_normalized_bulk (hN : PassiveCovarianceNormalizedBulk) :
    PassiveCovarianceOnDomainStrictBulk := by
  intro b hb0 hb κ hκ
  obtain ⟨ρ, d, C, W₀, hρ, hd, hC⟩ := hN b hb0 hb κ hκ
  refine ⟨d, max C 0 / ρ, W₀, hd, fun W hW E hEκ s hs X hX hδ v₁ v₂ v₃ v₄ => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  set δ := jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W
  have hδ0 : 0 ≤ δ := by
    have := passiveMass_nonneg b E hX.posSemidef
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    positivity
  set B := (W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ
  have hB : 0 ≤ B := by positivity
  have hF := fourNorm_nonneg v₁ v₂ v₃ v₄
  have hC0 : 0 ≤ max C 0 / ρ := by positivity
  by_cases h0 : vecNorm v₁ = 0 ∨ vecNorm v₂ = 0 ∨ vecNorm v₃ = 0 ∨ vecNorm v₄ = 0
  · rw [cov_sub_main_zero b E s X v₁ v₂ v₃ v₄ h0, norm_zero]; positivity
  push Not at h0
  obtain ⟨n1, n2, n3, n4⟩ := h0
  have p1 := lt_of_le_of_ne (vecNorm_nonneg v₁) (Ne.symm n1)
  have p2 := lt_of_le_of_ne (vecNorm_nonneg v₂) (Ne.symm n2)
  have p3 := lt_of_le_of_ne (vecNorm_nonneg v₃) (Ne.symm n3)
  have p4 := lt_of_le_of_ne (vecNorm_nonneg v₄) (Ne.symm n4)
  set r₁ := vecNorm v₁ / ρ
  have q1 : 0 < r₁ := div_pos p1 hρ
  set w₁ := ((r₁⁻¹ : ℝ) : ℂ) • v₁
  set w₂ := (((vecNorm v₂)⁻¹ : ℝ) : ℂ) • v₂
  set w₃ := (((vecNorm v₃)⁻¹ : ℝ) : ℂ) • v₃
  set w₄ := (((vecNorm v₄)⁻¹ : ℝ) : ℂ) • v₄
  have m1 : vecNorm w₁ ≤ ρ := by
    rw [vecNorm_smul_real, abs_of_pos (inv_pos.mpr q1)]
    simp only [r₁]; field_simp; rfl
  have mj : ∀ v : Fin W → ℂ, 0 < vecNorm v → vecNorm ((((vecNorm v)⁻¹ : ℝ) : ℂ) • v) ≤ 1 :=
    fun v hv => by rw [vecNorm_smul_real, abs_of_pos (inv_pos.mpr hv), inv_mul_cancel₀ hv.ne']
  have hw := hC W hW E hEκ s hs X hX hδ w₁ w₂ w₃ w₄ m1 (mj v₂ p2) (mj v₃ p3) (mj v₄ p4)
  have e : bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
      mainTensor b E s X v₁ v₂ v₃ v₄ = ((r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ : ℝ) : ℂ) *
      (bilinearCovariance (freshLaw W b) (freshU b E X) w₁ w₂ w₃ w₄ -
        mainTensor b E s X w₁ w₂ w₃ w₄) := by
    conv_lhs => rw [smul_inv_smul_real r₁ q1.ne' v₁, smul_inv_smul_real _ p2.ne' v₂,
      smul_inv_smul_real _ p3.ne' v₃, smul_inv_smul_real _ p4.ne' v₄]
    rw [bilinearCovariance_smul, mainTensor_smul, mul_sub]
  have hr : 0 ≤ r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ := by positivity
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  calc r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ * ‖bilinearCovariance (freshLaw W b) (freshU b E X)
        w₁ w₂ w₃ w₄ - mainTensor b E s X w₁ w₂ w₃ w₄‖
      ≤ r₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄ * (max C 0 * B) :=
        mul_le_mul_of_nonneg_left (hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)) hr
    _ = max C 0 / ρ * B * fourNorm v₁ v₂ v₃ v₄ := by
        simp only [r₁, fourNorm]; field_simp

end BlockBand.Transmission.CovarianceBulk
