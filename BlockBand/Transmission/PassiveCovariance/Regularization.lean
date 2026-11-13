module

public import BlockBand.Transmission.PassiveCovariance.VitaliL2
public import BlockBand.Transmission.PassiveCovariance.LayerIBP
public import BlockBand.Transmission.PassiveLayer.Consistency

/-!
# ε-regularization of the passive input

* `tendsto_freshU_regX`: `U(X_n)(ω) → U(X)(ω)` whenever the layer matrix at `X` is invertible
  (continuity of the inverse, `tendsto_matrix_inv`).
* `tendsto_bilinearCovariance_regX`: for `W ≥ W₀`, every passive `X` and all vectors,
  `Cov(X_n) → Cov(X)`. **Hypothesis:** `PassiveLayer.PassiveBoundsStatement`; only
  `moments` (`p = 4, 8`, `w = z_∂`) is used, for a.s. invertibility at `X` and the uniform `L²`
  bounds. The proof is Vitali (`VitaliL2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

section RegPart
variable {W : ℕ}

/-- `X_n = X - i(n+1)⁻¹`, strictly passive when `X` is passive. -/
def regX (X : Matrix (Fin W) (Fin W) ℂ) (n : ℕ) : Matrix (Fin W) (Fin W) ℂ :=
  X - (Complex.I * (((n : ℝ) + 1)⁻¹ : ℝ)) • (1 : Matrix (Fin W) (Fin W) ℂ)

theorem passiveY_regX (X : Matrix (Fin W) (Fin W) ℂ) (n : ℕ) :
    passiveY (regX X n) = passiveY X + (((n : ℝ) + 1)⁻¹) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  have h := BlockBand.Transmission.matrixImaginaryPart_portPencil (0 : Matrix (Fin W) (Fin W) ℂ)
    Matrix.isHermitian_zero (Complex.I * (((n : ℝ) + 1)⁻¹ : ℝ))
  simp only [BlockBand.Transmission.portPencil, sub_zero] at h
  rw [passiveY, regX, BlockBand.Transmission.matrixImaginaryPart_sub, h, passiveY]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul]
  abel_nf

theorem passiveY_regX_posSemidef {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (n : ℕ) : (passiveY (regX X n)).PosSemidef := by
  rw [passiveY_regX]
  exact hY.add (Matrix.PosSemidef.one.smul (by positivity))

theorem tendsto_regX (X : Matrix (Fin W) (Fin W) ℂ) :
    Tendsto (regX X) atTop (𝓝 X) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 : Tendsto (fun n : ℕ => (Complex.I * (((n : ℝ) + 1)⁻¹ : ℝ)) •
      (1 : Matrix (Fin W) (Fin W) ℂ)) atTop (𝓝 ((Complex.I * ((0 : ℝ) : ℂ)) • 1)) :=
    ((tendsto_const_nhds.mul (Complex.continuous_ofReal.tendsto 0 |>.comp h)).smul_const _)
  have h3 := (tendsto_const_nhds (x := X)).sub h2
  simp only [Complex.ofReal_zero, mul_zero, zero_smul, sub_zero] at h3
  exact h3

theorem tendsto_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] {M : ℕ → Matrix n n ℂ}
    {M₀ : Matrix n n ℂ} (hM : Tendsto M atTop (𝓝 M₀)) (h0 : IsUnit M₀.det) :
    Tendsto (fun k => (M k)⁻¹) atTop (𝓝 M₀⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  have hd : Tendsto (fun k => (M k).det) atTop (𝓝 M₀.det) :=
    ((continuous_id.matrix_det).tendsto M₀).comp hM
  have ha : Tendsto (fun k => (M k).adjugate) atTop (𝓝 M₀.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto M₀).comp hM
  exact (hd.inv₀ h0.ne_zero).smul ha

theorem continuous_layerMatrix_X (E : ℝ) (z : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Continuous fun X : Matrix (Fin W) (Fin W) ℂ => layerMatrix .oneBlockOnePort E z
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω := by
  unfold layerMatrix
  refine Continuous.matrix_fromBlocks ?_ continuous_const continuous_const continuous_const
  refine continuous_const.sub ?_
  exact continuous_pi fun u => continuous_pi fun v => (continuous_apply_apply _ _)

theorem tendsto_freshL_regX (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    Tendsto (fun n => freshL b E (regX X n) ω) atTop (𝓝 (freshL b E X ω)) := by
  have hM := ((continuous_layerMatrix_X E (boundaryZ b E) ω).tendsto X).comp (tendsto_regX X)
  have hG := tendsto_matrix_inv hM hω
  have hG12 : Tendsto (fun n => Matrix.of fun x y =>
      freshLayer b E (regX X n) ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))) atTop
      (𝓝 (Matrix.of fun x y => freshLayer b E X ω (Sum.inl ((0 : Fin 1), x))
        (Sum.inr ((0 : Fin 1), y)))) := by
    have hc : Continuous fun G : Matrix (LayerSite W .oneBlockOnePort)
        (LayerSite W .oneBlockOnePort) ℂ => (Matrix.of fun x y =>
          G (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y)) : Matrix (Fin W) (Fin W) ℂ) :=
      continuous_pi fun x => continuous_pi fun y => continuous_apply_apply _ _
    exact (hc.tendsto _).comp hG
  have hK : Tendsto (fun n => boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - regX X n) atTop
      (𝓝 (boundaryZ b E • 1 - X)) := tendsto_const_nhds.sub (tendsto_regX X)
  exact hK.mul hG12

theorem tendsto_freshU_regX (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hω : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω).det) :
    Tendsto (fun n => freshU b E (regX X n) ω) atTop (𝓝 (freshU b E X ω)) := by
  have h := tendsto_freshL_regX b E X ω hω
  exact h.mul ((continuous_id.matrix_conjTranspose.tendsto _).comp h)

end RegPart

section Main
variable {W : ℕ}

theorem measurable_norm_freshL (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable fun ω => ‖freshL b E X ω‖ :=
  continuous_norm.measurable.comp (measurable_freshL b E X)

theorem measurable_bilinear_freshU (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (u v : Fin W → ℂ) :
    Measurable fun ω => bilinear u (freshU b E X ω) v := by
  have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u M v := by
    unfold bilinear; fun_prop
  exact hc.measurable.comp (measurable_freshU b E X)

/-- **Regularization limit**: along `X_n = X - i(n+1)⁻¹`, the bilinear covariance of the
fresh transport converges to that at `X`, for every passive `X` and `W ≥ W₀`. Input:
`PassiveBoundsStatement.moments` (`p = 4, 8`, at `w = z_∂`), which gives a.s. invertibility at
`X` and uniform moments of `L` over passive inputs. -/
theorem tendsto_bilinearCovariance_regX (hA : BlockBand.Transmission.PassiveLayer.PassiveBoundsStatement)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        Tendsto (fun n => bilinearCovariance (freshLaw W b) (freshU b E (regX X n)) v₁ v₂ v₃ v₄)
          atTop (𝓝 (bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄)) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C4, W4, h4⟩ := hA.moments b hb0 hb _ hκ 4 (by norm_num)
  obtain ⟨C8, W8, h8⟩ := hA.moments b hb0 hb _ hκ 8 (by norm_num)
  refine ⟨max W4 W8, fun W hW X hX v₁ v₂ v₃ v₄ => ?_⟩
  have hE := BlockBand.Transmission.PassiveLayer.mem_bulkInterval_min E
  have hz := BlockBand.Transmission.PassiveLayer.boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  set μ := freshLaw W b
  -- moment bounds, uniform over passive inputs
  have m4 : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (fun ω => ‖freshL b E X' ω‖) (ENNReal.ofReal (2 * (2 : ℕ))) μ ≤ ENNReal.ofReal C4 :=
    fun X' hX' => by
      have := (h4 W (le_trans (le_max_left _ _) hW) E hE _ hz X' hX').2.2.2
      norm_num at this ⊢; exact this
  have m8 : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      eLpNorm (fun ω => ‖freshL b E X' ω‖) (ENNReal.ofReal (2 * (4 : ℕ))) μ ≤ ENNReal.ofReal C8 :=
    fun X' hX' => by
      have := (h8 W (le_trans (le_max_right _ _) hW) E hE _ hz X' hX').2.2.2
      norm_num at this ⊢; exact this
  have hinv := (h4 W (le_trans (le_max_left _ _) hW) E hE _ hz X hX).1
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
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun n => freshU b E (regX X n) ω) atTop (𝓝 (freshU b E X ω)) := by
    filter_upwards [hinv] with ω hω using tendsto_freshU_regX b E X ω hω
  have cb : ∀ u v : Fin W → ℂ, Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u M v :=
    fun u v => by unfold bilinear; fun_prop
  have t12 := tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => measurable_bilinear_freshU b E (regX X n) v₁ v₂) (fin _ _ 2)
    (fun n => bnd2 v₁ v₂ _ (hXn n)) (bnd2 v₁ v₂ X hX)
    (by filter_upwards [hae] with ω hω using ((cb v₁ v₂).tendsto _).comp hω)
  have t34 := tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => measurable_bilinear_freshU b E (regX X n) v₃ v₄) (fin _ _ 2)
    (fun n => bnd2 v₃ v₄ _ (hXn n)) (bnd2 v₃ v₄ X hX)
    (by filter_upwards [hae] with ω hω using ((cb v₃ v₄).tendsto _).comp hω)
  have tp := tendsto_integral_of_ae_of_eLpNorm_two
    (fun n => (measurable_bilinear_freshU b E (regX X n) v₁ v₂).mul
      (measurable_bilinear_freshU b E (regX X n) v₃ v₄)) (fin _ _ 4)
    (fun n => bnd4 _ (hXn n)) (bnd4 X hX)
    (by filter_upwards [hae] with ω hω using
      (((cb v₁ v₂).tendsto _).comp hω).mul (((cb v₃ v₄).tendsto _).comp hω))
  exact tp.sub (t12.mul t34)

end Main

end BlockBand.Transmission.PassiveCovariance
