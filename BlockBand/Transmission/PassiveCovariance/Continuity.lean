module

public import BlockBand.Transmission.PassiveCovariance.Regularization
public import BlockBand.Transmission.PassiveCovariance.Step3

/-!
# Continuity along `regX` and the reduction to strictly passive inputs

* `tendsto_res_regX`, `tendsto_Q_regX`: `R_n → R` and `Q_n → Q` (continuity of the inverse
  at the invertible `z - X`);
* `tendsto_jet0_regX`, `tendsto_jet1_regX`, `tendsto_mass_regX`: `δ₀, δ₁, q` converge
  (`δ₁ = |⟨R²⟩ + s|` by `normTrace_R2_add_s`);
* `tendsto_mainTensor_regX`: the leading tensor converges.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission
open scoped NNReal ENNReal ComplexOrder ComplexConjugate

variable {W : ℕ}

theorem continuous_passiveY : Continuous (passiveY (W := W)) := by
  have h : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => M - Mᴴ :=
    continuous_id.sub continuous_id.matrix_conjTranspose
  exact (h.const_smul (-Complex.I / 2)).neg

theorem continuous_bilinear (u v : Fin W → ℂ) :
    Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u M v := by
  unfold bilinear; fun_prop

section
variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

theorem tendsto_res_regX :
    Tendsto (fun n => passiveResolvent b E (regX X n)) atTop (𝓝 (passiveResolvent b E X)) := by
  have hK := (passive_inverse_constructed _ _ (etaZ_pos b E (by linarith) h1 h2) hY
    (matrixImaginaryPart_nearPencil b E X)).1
  exact tendsto_matrix_inv (tendsto_const_nhds.sub (tendsto_regX X))
    ((Matrix.isUnit_iff_isUnit_det _).mp hK)

theorem tendsto_jet0_regX :
    Tendsto (fun n => jetDistance0 b E (regX X n)) atTop (𝓝 (jetDistance0 b E X)) := by
  have h := tendsto_res_regX hb0 hb h1 h2 hY
  unfold jetDistance0
  exact (((continuous_id.matrix_trace.tendsto _).comp h).const_mul _ |>.sub_const _).norm

theorem tendsto_jet1_regX (s : ℂ) :
    Tendsto (fun n => jetDistance1 b E s (regX X n)) atTop (𝓝 (jetDistance1 b E s X)) := by
  have h := tendsto_res_regX hb0 hb h1 h2 hY
  have e : ∀ n, jetDistance1 b E s (regX X n) = ‖(W : ℂ)⁻¹ *
      (passiveResolvent b E (regX X n) * passiveResolvent b E (regX X n)).trace + s‖ :=
    fun n => (normTrace_R2_add_s hb0 hb h1 h2 (passiveY_regX_posSemidef hY n) s).symm
  simp only [e, ← normTrace_R2_add_s hb0 hb h1 h2 hY s]
  exact ((((continuous_id.matrix_trace.tendsto _).comp (h.mul h)).const_mul _).add_const _).norm

theorem tendsto_Q_regX :
    Tendsto (fun n => passiveQ b E (regX X n)) atTop (𝓝 (passiveQ b E X)) := by
  have h := tendsto_res_regX hb0 hb h1 h2 hY
  have hy := (continuous_passiveY.tendsto X).comp (tendsto_regX X)
  exact (((continuous_id.matrix_conjTranspose.tendsto _).comp h).mul hy).mul h

theorem tendsto_mass_regX :
    Tendsto (fun n => passiveMass b E (regX X n)) atTop (𝓝 (passiveMass b E X)) := by
  unfold passiveMass
  exact Complex.continuous_re.tendsto _ |>.comp
    ((continuous_id.matrix_trace.tendsto _).comp (tendsto_Q_regX hb0 hb h1 h2 hY))

theorem tendsto_mainTensor_regX (s : ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    Tendsto (fun n => mainTensor b E s (regX X n) v₁ v₂ v₃ v₄) atTop
      (𝓝 (mainTensor b E s X v₁ v₂ v₃ v₄)) := by
  have hT : Tendsto (fun n => passiveTransmission b E (regX X n)) atTop
      (𝓝 (passiveTransmission b E X)) := (tendsto_Q_regX hb0 hb h1 h2 hY).const_smul _
  have hf : Tendsto (fun n => passiveF b E (regX X n)) atTop (𝓝 (passiveF b E X)) :=
    (tendsto_res_regX hb0 hb h1 h2 hY).sub_const _
  have hfH := (continuous_id.matrix_conjTranspose.tendsto _).comp hf
  have ct : ∀ {A B : ℕ → Matrix (Fin W) (Fin W) ℂ} {A₀ B₀}, Tendsto A atTop (𝓝 A₀) →
      Tendsto B atTop (𝓝 B₀) → Tendsto (fun n => crossedTensor v₁ v₂ v₃ v₄ (A n) (B n)) atTop
        (𝓝 (crossedTensor v₁ v₂ v₃ v₄ A₀ B₀)) := fun hA hB =>
    (((continuous_bilinear v₁ v₄).tendsto _).comp hA).mul (((continuous_bilinear v₃ v₂).tendsto _).comp hB)
  have h1T := (tendsto_const_nhds (x := (1 : Matrix (Fin W) (Fin W) ℂ))).sub hT
  unfold mainTensor
  exact ((tendsto_const_nhds.mul ((ct tendsto_const_nhds h1T).add (ct h1T tendsto_const_nhds))).add
    (tendsto_const_nhds.mul (ct hf hf))).add (tendsto_const_nhds.mul (ct hfH hfH))
end

/-- `PassiveCovarianceOnDomain` restricted to strictly passive inputs (`Y ≻ 0`). -/
def PassiveCovarianceOnDomainStrict : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (d C : ℝ) (W₀ : ℕ), 0 < d ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
      jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W ≤ d →
      ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

theorem passiveY_regX_posDef {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (n : ℕ) : (passiveY (regX X n)).PosDef := by
  rw [passiveY_regX]
  exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul (by positivity))

/-- **Strict passivity suffices**: with `PassiveBoundsStatement`, the near-domain bound for
strictly passive inputs implies it for all passive inputs (at half the radius), by passing to
the limit along `regX`. -/
theorem passiveCovarianceOnDomain_of_strict
    (hA : BlockBand.Transmission.PassiveLayer.PassiveBoundsStatement)
    (h : PassiveCovarianceOnDomainStrict) : PassiveCovarianceOnDomain := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨d, C, W₀, hd, hC⟩ := h b hb0 hb E h1 h2 s hs
  obtain ⟨W₁, hW₁⟩ := tendsto_bilinearCovariance_regX hA hb0 hb h1 h2
  refine ⟨d / 2, C, max W₀ W₁, by positivity, fun W hW X hX hδ v₁ v₂ v₃ v₄ => ?_⟩
  set δ : Matrix (Fin W) (Fin W) ℂ → ℝ := fun X' =>
    jetDistance0 b E X' + jetDistance1 b E s X' + passiveMass b E X' / W
  have tδ : Tendsto (fun n => δ (regX X n)) atTop (𝓝 (δ X)) :=
    ((tendsto_jet0_regX hb0 hb h1 h2 hX).add (tendsto_jet1_regX hb0 hb h1 h2 hX s)).add
      ((tendsto_mass_regX hb0 hb h1 h2 hX).div_const _)
  have hev : ∀ᶠ n in atTop, δ (regX X n) ≤ d :=
    tδ.eventually (ge_mem_nhds (by show δ X < d; simp only [δ]; linarith))
  have tL := ((hW₁ W (le_trans (le_max_right _ _) hW) X hX v₁ v₂ v₃ v₄).sub
    (tendsto_mainTensor_regX hb0 hb h1 h2 hX s v₁ v₂ v₃ v₄)).norm
  have tR : Tendsto (fun n => C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ (regX X n)) * fourNorm v₁ v₂ v₃ v₄)
      atTop (𝓝 (C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * δ X) * fourNorm v₁ v₂ v₃ v₄)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tδ)).const_mul _).mul_const _
  exact le_of_tendsto_of_tendsto tL tR (hev.mono fun n hn =>
    hC W (le_trans (le_max_left _ _) hW) _ (passiveY_regX_posDef hX n) hn v₁ v₂ v₃ v₄)

end BlockBand.Transmission.PassiveCovariance
