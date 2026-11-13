module

public import BlockBand.Transmission.LawFinite.Ward
public import BlockBand.Transmission.PassiveLayer.Statement
public import BlockBand.Transmission.PassiveLayer.Moments
public import BlockBand.Transmission.PassiveLayer.Consistency

/-!
# Injection norms

Hypothesis `PassiveBoundsStatement`, only its `moments` clause, at the passive absorbed input
`X' = X - iε`.

`C = 𝒢₁₂*𝒢₁₂` with `𝒢₁₂` a submatrix of `𝒢`, so `‖C‖ ≤ ‖𝒢‖²` and `|Tr C| ≤ W‖𝒢‖²`.
With `ε ≤ Kε/W²` and `‖‖𝒢‖‖_{2p} ≤ C'`: `‖ε‖C‖‖_p ≤ KεC'²/W²`, `‖ε Tr C‖_p ≤ KεC'²/W`.

* `norm_freshG12_le`, `norm_injection_le`, `abs_trace_injection_le`, `measurable_injection`;
* `eLpNorm_le_of_sq`: `|f| ≤ c g²`, `‖g‖_{2p} ≤ C` ⇒ `‖f‖_p ≤ cC²`;
* **`injectionNorms_holds hA : InjectionNorms`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveLayer
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `𝒢₁₂` is the physical × port block of `layerAt` at `w = z_∂`. -/
theorem freshG12_eq_submatrix (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshG12 b E X ω = (layerAt E (boundaryZ b E) X ω).submatrix
      (fun x : Fin W => Sum.inl ((0 : Fin 1), x)) (fun y : Fin W => Sum.inr ((0 : Fin 1), y)) :=
  rfl

theorem norm_freshG12_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖freshG12 b E X ω‖ ≤ ‖layerAt E (boundaryZ b E) X ω‖ := by
  rw [freshG12_eq_submatrix]
  refine norm_submatrix_le _ ?_ ?_
  · intro x y h
    have := Sum.inl_injective h
    exact (Prod.mk.inj this).2
  · intro x y h
    have := Sum.inr_injective h
    exact (Prod.mk.inj this).2

/-- `‖C‖ ≤ ‖𝒢(X')‖²`. -/
theorem norm_injection_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖injection b E X ε ω‖ ≤ ‖layerAt E (boundaryZ b E) (absorbedInput X ε) ω‖ ^ 2 := by
  rw [injection]
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  rw [Matrix.l2_opNorm_conjTranspose, sq]
  have h := norm_freshG12_le b E (absorbedInput X ε) ω
  exact mul_le_mul h h (norm_nonneg _) (norm_nonneg _)

/-- `‖Tr M‖ ≤ W‖M‖`. -/
theorem norm_trace_le_mul (M : Matrix (Fin W) (Fin W) ℂ) : ‖M.trace‖ ≤ W * ‖M‖ := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp [Matrix.trace]
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have h := PathScalar.norm_normTrace_le M
  have e : M.trace = (W : ℂ) * ((W : ℂ)⁻¹ * M.trace) := by field_simp
  rw [e, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

/-- `|Re Tr C| ≤ W‖𝒢(X')‖²`. -/
theorem abs_trace_injection_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) :
    |(injection b E X ε ω).trace.re| ≤
      W * ‖layerAt E (boundaryZ b E) (absorbedInput X ε) ω‖ ^ 2 :=
  (Complex.abs_re_le_norm _).trans ((norm_trace_le_mul _).trans
    (mul_le_mul_of_nonneg_left (norm_injection_le b E X ε ω) (Nat.cast_nonneg _)))

theorem measurable_freshG12 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshG12 b E X) :=
  measurable_g12 E (boundaryZ b E) X

theorem measurable_injection (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) :
    Measurable (injection b E X ε) :=
  Bridge.measurable_matrix_mul'
    (Bridge.measurable_matrix_conjTranspose' (measurable_freshG12 b E _))
    (measurable_freshG12 b E _)

/-- `|f| ≤ c g²` and `‖g‖_{2p} ≤ C` give `‖f‖_p ≤ cC²`. -/
theorem eLpNorm_le_of_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {g f : Ω → ℝ}
    (hgm : AEStronglyMeasurable g μ) (hfm : AEStronglyMeasurable f μ)
    {p c C : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hC0 : 0 ≤ C)
    (hC : eLpNorm g (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal C)
    (hf : ∀ ω, |f ω| ≤ c * g ω ^ 2) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (c * C ^ 2) := by
  have e1 : (fun ω => c * g ω ^ 2) = c • fun ω => ‖g ω‖ ^ (2 : ℝ) := by
    funext ω; simp
  have hmono : eLpNorm f (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => c * g ω ^ 2) (ENNReal.ofReal p) μ :=
    eLpNorm_mono_real hfm fun ω => by rw [Real.norm_eq_abs]; exact hf ω
  have e2 : ENNReal.ofReal p * ENNReal.ofReal 2 = ENNReal.ofReal (2 * p) := by
    rw [← ENNReal.ofReal_mul hp, mul_comm]
  refine hmono.trans ?_
  rw [e1, eLpNorm_const_smul, eLpNorm_norm_rpow _ hgm (by norm_num : (0 : ℝ) < 2), e2,
    Real.enorm_eq_ofReal hc, ENNReal.ofReal_mul hc, ENNReal.ofReal_pow hC0]
  gcongr
  rw [← ENNReal.rpow_natCast]
  exact ENNReal.rpow_le_rpow hC (by norm_num)

/-- **`InjectionNorms`**, from the `moments` clause of `PassiveBoundsStatement`. -/
theorem injectionNorms_holds (hA : PassiveBoundsStatement) : InjectionNorms := by
  intro b hb0 hb κI Kε p hκ hKε hp
  obtain ⟨C', W₀, hm⟩ := hA.moments b hb0 hb κI hκ (2 * p) (by linarith)
  set Cm := max C' 0
  refine ⟨Kε * Cm ^ 2, max W₀ 1, fun W hW E hE X hY ε hε hεK => ?_⟩
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 ≤ W := (le_max_right _ _).trans hW
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hz := boundaryZ_mem_paramDisk (b := b) (by linarith) h1 h2
  have hY' := passiveY_absorbedInput hY hε
  set g : LayerSample W .oneBlockOnePort → ℝ :=
    fun ω => ‖layerAt E (boundaryZ b E) (absorbedInput X ε) ω‖
  have hgm : AEStronglyMeasurable g (freshLaw W b) :=
    (measurable_layerAt E _ _).norm.aestronglyMeasurable
  have hg := (hm W hW0 E hE _ hz _ hY').2.1
  have hg' : eLpNorm g (ENNReal.ofReal (2 * p)) (freshLaw W b) ≤ ENNReal.ofReal Cm :=
    hg.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hCm : 0 ≤ Cm := le_max_right _ _
  have hp0 : 0 ≤ p := by linarith
  have hεW : ε * W ≤ Kε / W := by
    have := mul_le_mul_of_nonneg_right hεK hWpos.le
    calc ε * W ≤ Kε / (W : ℝ) ^ 2 * W := this
      _ = Kε / W := by field_simp
  constructor
  · refine (eLpNorm_le_of_sq hgm
      (((measurable_injection b E X ε).norm.const_mul ε).aestronglyMeasurable)
      hp0 hε hCm hg' fun ω => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · rw [abs_of_nonneg (mul_nonneg hε (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (norm_injection_le b E X ε ω) hε
    · calc ε * Cm ^ 2 ≤ Kε / (W : ℝ) ^ 2 * Cm ^ 2 :=
            mul_le_mul_of_nonneg_right hεK (by positivity)
        _ = Kε * Cm ^ 2 / (W : ℝ) ^ 2 := by ring
  · have hmeas : Measurable fun ω => ε * (injection b E X ε ω).trace.re :=
      measurable_const.mul (Complex.measurable_re.comp
        (continuous_id.matrix_trace.measurable.comp (measurable_injection b E X ε)))
    refine (eLpNorm_le_of_sq hgm hmeas.aestronglyMeasurable
      hp0 (mul_nonneg hε hWpos.le) hCm hg' fun ω => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · rw [abs_mul, abs_of_nonneg hε, mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_trace_injection_le b E X ε ω) hε
    · calc ε * W * Cm ^ 2 ≤ Kε / W * Cm ^ 2 := mul_le_mul_of_nonneg_right hεW (by positivity)
        _ = Kε * Cm ^ 2 / W := by ring

end BlockBand.Transmission.LawFinite
