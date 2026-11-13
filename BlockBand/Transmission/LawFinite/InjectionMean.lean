module

public import BlockBand.Transmission.LawFinite.InjectionStrict
public import BlockBand.Transmission.SourceMixing.MassLayer
public import BlockBand.Transmission.LengthUniform.BulkMassLayer

/-!
# The injection mean

The normalized trace of the injection `C = 𝒢₁₂*𝒢₁₂` has mean `d_* + O(δ₀ + q/W + W⁻¹)`,
uniformly in the passive input (`injectionMean_holds`). Hypothesis `PassiveBoundsStatement`.

* `injMean_passive_bulk`: the strict bound `injMean_strict_bulk` at every passive input, by the
  `regX` limit (`mm_tendsto_EU_bulk`, continuity of `R, δ₀, q`), as in `massMeanRefined_bulk`;
* `passiveMass_absorb_le`: `q(X - iε) ≤ (1 + ε/η)²q + εW/η²` (`R' = R(1 - iεR')`);
* `integral_trace_injection`: `∫ Re Tr C = Re Tr(R'*R'·E[L'L'*])`, `X' = X - iε`;
* **`injectionMean_holds hA : InjectionMean`**: the bound at `X'`, then `δ₀(X') ≤ δ₀ + ε/η²`
  (`PathScalar.jetDistance0_absorb_le`) and the mass perturbation, with `ε ≤ Kε/W²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Injection mean, every passive input, bulk-uniform.** -/
theorem injMean_passive_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        |(W : ℝ)⁻¹ * ((passiveResolvent b E X)ᴴ * passiveResolvent b E X *
            matrixExpect (freshLaw W b) (freshU b E X)).trace.re - dStar b| ≤
          C * (jetDistance0 b E X + passiveMass b E X / W + (W : ℝ)⁻¹) := by
  obtain ⟨C, W₀, hC, hS⟩ := injMean_strict_bulk hA hb0 hb hκ
  obtain ⟨W₁, hT⟩ := mm_tendsto_EU_bulk hA hb0 hb hκ
  refine ⟨C, max W₀ W₁, hC, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  set Xn := PassiveCovariance.regX X
  have tq := tendsto_mass_regX hb0 hb h1 h2 hX
  have tR := tendsto_res_regX hb0 hb h1 h2 hX
  have tδ := tendsto_jet0_regX hb0 hb h1 h2 hX
  have tU := hT W (le_trans (le_max_right _ _) hW) E hE X hX
  have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => Mᴴ := continuous_id.matrix_conjTranspose
  have tN := (((hc.tendsto _).comp tR).mul tR).mul tU
  have hL : Tendsto (fun n => |(W : ℝ)⁻¹ * ((passiveResolvent b E (Xn n))ᴴ *
      passiveResolvent b E (Xn n) * matrixExpect (freshLaw W b) (freshU b E (Xn n))).trace.re -
        dStar b|) atTop
      (𝓝 |(W : ℝ)⁻¹ * ((passiveResolvent b E X)ᴴ * passiveResolvent b E X *
        matrixExpect (freshLaw W b) (freshU b E X)).trace.re - dStar b|) :=
    ((((Complex.continuous_re.tendsto _).comp ((continuous_id.matrix_trace.tendsto _).comp
      tN)).const_mul _).sub_const _).abs
  have hR : Tendsto (fun n => C * (jetDistance0 b E (Xn n) + passiveMass b E (Xn n) / W +
      (W : ℝ)⁻¹)) atTop
      (𝓝 (C * (jetDistance0 b E X + passiveMass b E X / W + (W : ℝ)⁻¹))) :=
    (((tδ.add (tq.div_const _)).add_const _)).const_mul _
  exact le_of_tendsto_of_tendsto' hL hR fun n =>
    hS W (le_trans (le_max_left _ _) hW) E hE (Xn n) (passiveY_regX_posDef hX n)

section Absorb

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- `R' = R(1 - iεR')`. -/
theorem resolvent_absorb_eq {ε : ℝ} (hε : 0 ≤ ε) :
    passiveResolvent b E (absorbedInput X ε) = passiveResolvent b E X *
      (1 - (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε)) := by
  have hR := (nearPencil_inverse hb0 hb h1 h2 hY).2
  have hR' := (nearPencil_inverse hb0 hb h1 h2 (passiveY_absorbedInput hY hε)).1
  set R := passiveResolvent b E X
  set R' := passiveResolvent b E (absorbedInput X ε)
  have hK : boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X =
      (boundaryZ b E • 1 - absorbedInput X ε) - (((ε : ℝ) : ℂ) * Complex.I) • 1 := by
    simp only [absorbedInput]; abel
  calc R' = R * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * R' := by
        rw [hR, Matrix.one_mul]
    _ = R * (1 - (((ε : ℝ) : ℂ) * Complex.I) • R') := by
        rw [hK, Matrix.mul_assoc, Matrix.sub_mul, hR', Matrix.smul_mul, Matrix.one_mul]

/-- **Mass under input absorption**: `q(X - iε) ≤ (1 + ε/η)²q + εW/η²`. -/
theorem passiveMass_absorb_le {ε : ℝ} (hε : 0 ≤ ε) :
    passiveMass b E (absorbedInput X ε) ≤
      (1 + ε / etaZ b E) ^ 2 * passiveMass b E X + ε * W / etaZ b E ^ 2 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY' := passiveY_absorbedInput hY hε
  set R := passiveResolvent b E X
  set R' := passiveResolvent b E (absorbedInput X ε)
  set A := 1 - (((ε : ℝ) : ℂ) * Complex.I) • R'
  have hR'n : ‖R'‖ ≤ (etaZ b E)⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY'
  have hAn : ‖A‖ ≤ 1 + ε / etaZ b E := by
    refine (norm_sub_le _ _).trans (add_le_add PassiveLayer.norm_one_le' ?_)
    refine (norm_smul_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε,
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hR'n hε
  have hQ : (passiveQ b E X).PosSemidef := hY.conjTranspose_mul_mul_same _
  have hYe : passiveY (absorbedInput X ε) = passiveY X + (ε : ℂ) • 1 :=
    PathScalar.passiveY_absorb_eq X ε
  have hsplit : passiveQ b E (absorbedInput X ε) =
      Aᴴ * passiveQ b E X * A + (ε : ℂ) • (R'ᴴ * R') := by
    rw [passiveQ, hYe]
    conv_lhs => rw [show passiveResolvent b E (absorbedInput X ε) = R * A from
      resolvent_absorb_eq hb0 hb h1 h2 hY hε]
    rw [passiveQ, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
    congr 1
    · simp only [Matrix.mul_assoc, R]
    · congr 1
      rw [← conjTranspose_mul, ← resolvent_absorb_eq hb0 hb h1 h2 hY hε]
  have h1' : (Aᴴ * passiveQ b E X * A).trace.re ≤ (1 + ε / etaZ b E) ^ 2 * passiveMass b E X := by
    have e : (Aᴴ * passiveQ b E X * A).trace = ((A * Aᴴ) * passiveQ b E X).trace := by
      rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]; exact trace_mul_comm _ _
    rw [e]
    refine (Complex.re_le_norm _).trans ((norm_trace_mul_posSemidef_le hQ _).trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (passiveMass_nonneg b E hY)
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, sq]
    exact mul_le_mul hAn hAn (norm_nonneg _) (by positivity)
  have h2' : ((ε : ℂ) • (R'ᴴ * R')).trace.re ≤ ε * W / etaZ b E ^ 2 := by
    rw [trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have hn : ‖R'ᴴ * R'‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose, sq]
      exact mul_le_mul hR'n hR'n (norm_nonneg _) (by positivity)
    have ht : (R'ᴴ * R').trace.re ≤ W * (etaZ b E)⁻¹ ^ 2 :=
      (Complex.re_le_norm _).trans ((norm_trace_le_mul _).trans
        (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)))
    calc ε * (R'ᴴ * R').trace.re ≤ ε * (W * (etaZ b E)⁻¹ ^ 2) := mul_le_mul_of_nonneg_left ht hε
      _ = ε * W / etaZ b E ^ 2 := by rw [inv_pow]; ring
  rw [passiveMass, hsplit, trace_add, Complex.add_re]
  linarith

end Absorb

theorem integrable_trace_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (N : Matrix (Fin W) (Fin W) ℂ) {U : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hU : ∀ i j, Integrable (fun ω => U ω i j) μ) :
    Integrable (fun ω => (N * U ω).trace) μ := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hU j i).const_mul _

/-- `∫ Re Tr C = Re Tr(R'*R'·E[L'L'*])` at `X' = X - iε`. -/
theorem integral_trace_injection {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hU : ∀ i j, Integrable (fun ω => freshU b E (absorbedInput X ε) ω i j) (freshLaw W b)) :
    ∫ ω, (injection b E X ε ω).trace.re ∂freshLaw W b =
      ((passiveResolvent b E (absorbedInput X ε))ᴴ * passiveResolvent b E (absorbedInput X ε) *
        matrixExpect (freshLaw W b) (freshU b E (absorbedInput X ε))).trace.re := by
  simp_rw [trace_injection_eq hb0 hb h1 h2 hY hε]
  have hI := integrable_trace_mul ((passiveResolvent b E (absorbedInput X ε))ᴴ *
    passiveResolvent b E (absorbedInput X ε)) hU
  have := integral_re hI
  simp only [RCLike.re_to_complex] at this
  rw [this, ml_trace_matrixExpect _ _ hU]

/-- Scalar bookkeeping for `injectionMean_holds`. -/
theorem inj_absorb_scalar {δ δ' q q' W ε η Li Kε : ℝ} (hW : 1 ≤ W) (hη : 0 < η) (hLi : η⁻¹ ≤ Li)
    (hε : 0 ≤ ε) (hεK : ε ≤ Kε / W ^ 2) (hδ : 0 ≤ δ) (hq : 0 ≤ q)
    (hδ' : δ' ≤ δ + ε / η ^ 2) (hq' : q' ≤ (1 + ε / η) ^ 2 * q + ε * W / η ^ 2) :
    δ' + q' / W + W⁻¹ ≤
      ((1 + Kε * Li) ^ 2 + 2 * Kε * Li ^ 2 + 1) * (δ + q / W + W⁻¹) := by
  have hW0 : 0 < W := by linarith
  have hKε : 0 ≤ Kε := by
    have : 0 ≤ Kε / W ^ 2 := hε.trans hεK
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => by nlinarith [h.2, sq_pos_of_pos hW0]
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have hεW : ε ≤ Kε / W := hεK.trans (div_le_div_of_nonneg_left hKε hW0 (by nlinarith))
  have hεK1 : ε ≤ Kε := hεW.trans (div_le_self hKε hW)
  have hηi : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  have a1 : ε / η ≤ Kε * Li := by
    rw [div_eq_mul_inv]; exact mul_le_mul hεK1 hLi hηi hKε
  have a2 : ε / η ^ 2 ≤ Kε * Li ^ 2 * W⁻¹ := by
    rw [div_eq_mul_inv, ← inv_pow]
    have h3 : ε ≤ Kε * W⁻¹ := by rw [← div_eq_mul_inv]; exact hεW
    have h4 : η⁻¹ ^ 2 ≤ Li ^ 2 := pow_le_pow_left₀ hηi hLi 2
    calc ε * η⁻¹ ^ 2 ≤ Kε * W⁻¹ * Li ^ 2 := mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = _ := by ring
  have a3 : q' / W ≤ (1 + Kε * Li) ^ 2 * (q / W) + Kε * Li ^ 2 * W⁻¹ := by
    have h5 : (1 + ε / η) ^ 2 ≤ (1 + Kε * Li) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [a1]) 2
    have h6 : q' / W ≤ (1 + ε / η) ^ 2 * (q / W) + ε / η ^ 2 := by
      rw [div_le_iff₀ hW0]
      have : ((1 + ε / η) ^ 2 * (q / W) + ε / η ^ 2) * W =
          (1 + ε / η) ^ 2 * q + ε * W / η ^ 2 := by field_simp
      rw [this]; exact hq'
    have h7 : (1 + ε / η) ^ 2 * (q / W) ≤ (1 + Kε * Li) ^ 2 * (q / W) :=
      mul_le_mul_of_nonneg_right h5 (div_nonneg hq hW0.le)
    linarith only [h6, h7, a2]
  have hqW : 0 ≤ q / W := div_nonneg hq hW0.le
  have hWi : 0 ≤ W⁻¹ := inv_nonneg.mpr hW0.le
  have hA : 0 ≤ (1 + Kε * Li) ^ 2 := sq_nonneg _
  have hB : 0 ≤ Kε * Li ^ 2 := by positivity
  nlinarith only [hδ', a2, a3, hδ, hqW, hWi, hA, hB]

/-- **`InjectionMean`**. -/
theorem injectionMean_holds (hA : PassiveBoundsStatement) : InjectionMean := by
  intro b hb0 hb κI Kε hκ hKε
  obtain ⟨C₀, W₀, hC₀, hM⟩ := injMean_passive_bulk hA hb0 hb hκ
  obtain ⟨Wi, hI⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  have hηL : 0 < etaLow b κI := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κI)⁻¹
  refine ⟨C₀ * ((1 + Kε * Li) ^ 2 + 2 * Kε * Li ^ 2 + 1), max (max W₀ Wi) 1,
    fun W hW E hE X hY ε hε hεK => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hWi⟩, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hY' := passiveY_absorbedInput hY hε
  rw [integral_trace_injection hb0 hb h1 h2 hY hε (hI W hWi E hE _ hY')]
  have hb1 := hM W hW0 E hE _ hY'
  have hδ' : jetDistance0 b E (absorbedInput X ε) ≤ jetDistance0 b E X + ε / etaZ b E ^ 2 :=
    jetDistance0_absorb_le hb0 hb h1 h2 hY hε
  have hq' := passiveMass_absorb_le hb0 hb h1 h2 hY hε
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hs := inj_absorb_scalar hW1r hη hLi hε hεK (norm_nonneg _) (passiveMass_nonneg b E hY)
    hδ' hq'
  refine hb1.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hs hC₀

end BlockBand.Transmission.LawFinite
