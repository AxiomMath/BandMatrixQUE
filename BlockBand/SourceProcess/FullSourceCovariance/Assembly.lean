module

public import BlockBand.SourceProcess.FullSourceCovariance.MainMatch
public import BlockBand.SourceProcess.FullSource.DeltaMoments

/-!
# `FullSourceCovarianceEnergyUniformContract` from the two `Δ`-covariance Props

**`fullSourceCovarianceEnergyUniform_of_delta hGA hS hO`**: `GaussianAbsorptionContract` (only
for `L²` moments of `Δ`, via `delta_moments`, `delta_integrable`) and the two open one-port Props
`DeltaCovarianceSame`, `DeltaCovarianceOpposite` give the additive covariance statement.

Proof: `cov_wardOf` (four `Δ`-covariances, from the a.s. Ward identity `ward_ae`), `main_match`
(the four main terms sum to the contract tensor), and `‖ι*v‖ ≤ ‖v‖`,
`‖Fv‖ ≤ (η₀⁻¹ + (2η₀)⁻¹)‖v‖` with `η₀ = (1-b)κI/4 ≤ η` on `bulkInterval κI`. Constant:
`C = 2(|C_S| + |C_O|)K_F²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

theorem fourNorm_le {n : Type*} [Fintype n] {a₁ a₂ a₃ a₄ : n → ℂ} {r₁ r₂ r₃ r₄ : ℝ}
    (h₁ : vecNorm a₁ ≤ r₁) (h₂ : vecNorm a₂ ≤ r₂) (h₃ : vecNorm a₃ ≤ r₃) (h₄ : vecNorm a₄ ≤ r₄) :
    fourNorm a₁ a₂ a₃ a₄ ≤ r₁ * r₂ * r₃ * r₄ := by
  have h1 := vecNorm_nonneg a₁; have h2 := vecNorm_nonneg a₂
  have h3 := vecNorm_nonneg a₃; have h4 := vecNorm_nonneg a₄
  rw [fourNorm]
  exact mul_le_mul (mul_le_mul (mul_le_mul h₁ h₂ h2 (h1.trans h₁)) h₃ h3
    (mul_nonneg (h1.trans h₁) (h2.trans h₂))) h₄ h4
    (mul_nonneg (mul_nonneg (h1.trans h₁) (h2.trans h₂)) (h3.trans h₃))

theorem fourNorm_nonneg {n : Type*} [Fintype n] (a₁ a₂ a₃ a₄ : n → ℂ) :
    0 ≤ fourNorm a₁ a₂ a₃ a₄ := by
  have := vecNorm_nonneg a₁; have := vecNorm_nonneg a₂
  have := vecNorm_nonneg a₃; have := vecNorm_nonneg a₄
  rw [fourNorm]; positivity

/-- `g = 4η q ≥ 0` for passive `X`. -/
theorem conductance_nonneg (b E : ℝ) (hη : 0 ≤ etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) : 0 ≤ conductanceOf (passiveTransmission b E X) := by
  have h : conductanceOf (passiveTransmission b E X) = 4 * etaZ b E * passiveMass b E X := by
    simp [conductanceOf, passiveTransmission, passiveMass, Matrix.trace_smul]
  rw [h]
  have := passiveMass_nonneg b E hY
  positivity

theorem covErr_nonneg (b E : ℝ) (s : ℂ) (hη : 0 ≤ etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) : 0 ≤ covErr b E s X := by
  have := conductance_nonneg b E hη hY
  have h0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have h1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  rw [covErr]; positivity

/-- `L²` centered bilinear forms of `Δ` from an `L²` bound on `‖Δ‖`. -/
theorem memLp_bilinear_centered {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (D : Ω → Matrix (Fin W) (Fin W) ℂ) (hm : Measurable D)
    (h2 : MemLp (fun ω => ‖D ω‖) 2 μ) (D₀ : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    MemLp (fun ω => bilinear x (D ω - D₀) y) 2 μ := by
  have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear x (M - D₀) y := by
    unfold bilinear; fun_prop
  have hg : MemLp (fun ω => vecNorm x * vecNorm y * (‖D ω‖ + ‖D₀‖)) 2 μ :=
    (h2.add (memLp_const _)).const_mul _
  refine hg.of_le (hc.measurable.comp hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hx := vecNorm_nonneg x; have hy := vecNorm_nonneg y
  have hb := norm_bilinear_le x (D ω - D₀) y
  have hs := norm_sub_le (D ω) D₀
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖bilinear x (D ω - D₀) y‖ ≤ vecNorm x * ‖D ω - D₀‖ * vecNorm y := hb
    _ ≤ vecNorm x * (‖D ω‖ + ‖D₀‖) * vecNorm y := by gcongr
    _ = _ := by ring

/-- **The additive covariance statement `FullSourceCovarianceEnergyUniformContract`**, from
`GaussianAbsorptionContract` and the two open `Δ`-covariance Props. -/
theorem fullSourceCovarianceEnergyUniform_of_delta (hGA : GaussianAbsorptionContract)
    (hS : DeltaCovarianceSame) (hO : DeltaCovarianceOpposite) :
    FullSourceCovarianceEnergyUniformContract := by
  intro b hb0 hb κI hκ
  obtain ⟨CS, WS, hCS⟩ := hS b hb0 hb κI hκ
  obtain ⟨CO, WO, hCO⟩ := hO b hb0 hb κI hκ
  obtain ⟨CΔ, WΔ, hCΔ, hΔ2⟩ := delta_moments hGA b hb0 hb κI hκ 2 one_le_two
  obtain ⟨Ci, Wi, -, hInt⟩ := delta_integrable hGA b hb0 hb κI hκ
  set η₀ := (1 - b) * κI / 4 with hη₀def
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  set KF := η₀⁻¹ + (2 * η₀)⁻¹ with hKF
  have hKF0 : 0 ≤ KF := by positivity
  refine ⟨2 * (|CS| + |CO|) * KF ^ 2, max (max WS WO) (max (max WΔ Wi) 1),
    fun W hW E hE s hs XX hXX v₁ v₂ v₃ v₄ => ?_⟩
  have hWS : WS ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWO : WO ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWΔ : WΔ ≤ W := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hW
  have hWi : Wi ≤ W := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hE' := hE
  obtain ⟨hE1, hE2⟩ := hE'
  have hEl : -2 < E := by linarith
  have hEr : E < 2 := by linarith
  have hηge : η₀ ≤ etaZ b E := etaZ_ge hb0 hb hκ hE
  have hη : 0 < etaZ b E := lt_of_lt_of_le hη₀ hηge
  set X := nearSchur (boundaryZ b E) XX with hX
  have hY : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  set μ := freshLaw W b
  set D := fun ω => freshDelta b E X ω
  set F := wardF b E XX
  have hm : Measurable D := measurable_freshDelta_comp b E (X := fun _ => X) measurable_const
    measurable_id
  have hD2 : MemLp (fun ω => ‖D ω‖) 2 μ := by
    obtain ⟨-, hle⟩ := hΔ2 W hWΔ E hE X hY
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := CΔ))
    simpa [ENNReal.ofReal_ofNat] using hle
  have hexp := cov_wardOf (μ := μ) (wardNoise b E XX) D F (ward_ae hb0 hXX hη hW1)
    (hInt W hWi E hE X hY).1 (fun x y => memLp_bilinear_centered D hm hD2 _ x y) v₁ v₂ v₃ v₄
  have hmain := main_match b E hb0 hb hEl hEr (by omega) s XX v₁ v₂ v₃ v₄
  simp only at hexp hmain ⊢
  rw [hexp, hmain]
  -- vector bounds
  set x := fun v : Fin 2 × Fin W → ℂ => nearSel W *ᵥ v
  set y := fun v : Fin 2 × Fin W → ℂ => F *ᵥ v
  have hF : ‖F‖ ≤ KF := (norm_wardF_le b E hXX hη).trans (add_le_add
    (inv_anti₀ hη₀ hηge) (inv_anti₀ (by positivity) (by linarith)))
  have hx : ∀ v, vecNorm (x v) ≤ vecNorm v := fun v => vecNorm_nearSel_mulVec_le v
  have hy : ∀ v, vecNorm (y v) ≤ KF * vecNorm v := fun v =>
    (vecNorm_mulVec_le' F v).trans (mul_le_mul_of_nonneg_right hF (vecNorm_nonneg v))
  set e := covErr b E s X
  have he : 0 ≤ e := covErr_nonneg b E s hη.le hY
  set fn := fourNorm v₁ v₂ v₃ v₄
  have hfn0 : 0 ≤ fn := fourNorm_nonneg _ _ _ _
  have b1 : fourNorm (x v₁) (y v₂) (x v₃) (y v₄) ≤ KF ^ 2 * fn :=
    (fourNorm_le (hx v₁) (hy v₂) (hx v₃) (hy v₄)).trans_eq (by simp only [fn, fourNorm]; ring)
  have b2 : fourNorm (x v₁) (y v₂) (x v₄) (y v₃) ≤ KF ^ 2 * fn :=
    (fourNorm_le (hx v₁) (hy v₂) (hx v₄) (hy v₃)).trans_eq (by simp only [fn, fourNorm]; ring)
  have b3 : fourNorm (x v₃) (y v₄) (x v₂) (y v₁) ≤ KF ^ 2 * fn :=
    (fourNorm_le (hx v₃) (hy v₄) (hx v₂) (hy v₁)).trans_eq (by simp only [fn, fourNorm]; ring)
  have b4 : fourNorm (x v₂) (y v₁) (x v₄) (y v₃) ≤ KF ^ 2 * fn :=
    (fourNorm_le (hx v₂) (hy v₁) (hx v₄) (hy v₃)).trans_eq (by simp only [fn, fourNorm]; ring)
  have t1 := hCS W hWS E hE s hs X hY (x v₁) (y v₂) (x v₃) (y v₄)
  have t2 := hCO W hWO E hE s hs X hY (x v₁) (y v₂) (x v₄) (y v₃)
  have t3 := hCO W hWO E hE s hs X hY (x v₃) (y v₄) (x v₂) (y v₁)
  have t4 := hCS W hWS E hE s hs X hY (x v₂) (y v₁) (x v₄) (y v₃)
  have up : ∀ (c f : ℝ), 0 ≤ f → f ≤ KF ^ 2 * fn → c * e * f ≤ |c| * e * (KF ^ 2 * fn) :=
    fun c f hf0 hf => by
      have h1 : c * e * f ≤ |c| * e * f := by gcongr; exact le_abs_self c
      exact h1.trans (by gcongr)
  have f1 := up CS _ (fourNorm_nonneg _ _ _ _) b1
  have f2 := up CO _ (fourNorm_nonneg _ _ _ _) b2
  have f3 := up CO _ (fourNorm_nonneg _ _ _ _) b3
  have f4 := up CS _ (fourNorm_nonneg _ _ _ _) b4
  have hsplit : ∀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : ℂ,
      A₁ + A₂ + A₃ + star A₄ - (B₁ + B₂ + B₃ + star B₄) =
        (A₁ - B₁) + (A₂ - B₂) + (A₃ - B₃) + star (A₄ - B₄) := by
    intro A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄; rw [star_sub]; ring
  have n4 : ∀ a b c d : ℂ, ‖a + b + c + star d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    calc ‖a + b + c + star d‖ ≤ ‖a + b + c‖ + ‖star d‖ := norm_add_le _ _
      _ ≤ ‖a + b‖ + ‖c‖ + ‖star d‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖star d‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_star]
  rw [hsplit]
  refine (n4 _ _ _ _).trans ?_
  show _ ≤ 2 * (|CS| + |CO|) * KF ^ 2 * e * fn
  nlinarith [t1, t2, t3, t4, f1, f2, f3, f4]

end BlockBand.SourceProcess.FullSourceCovariance
