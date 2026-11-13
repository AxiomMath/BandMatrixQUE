module

public import BlockBand.SourceProcess.FullSourceCovariance.PhiSameIBP
public import BlockBand.SourceProcess.FullSourceCovariance.TauCrossed

/-!
# The exact mean identity `W·EΦ = E[T₁] + E[Ω₀T₂] + E[F·t]`

An exact formula for the mean of the equal-sign ladder functional `Φ` in terms of bounded letters.

* `tOne x y' = a*K̂𝒢S̃c'`, `tTwo x y' = a*K̂𝒢S̃𝒢c'` (bounded letters only; `a = ι₁x`, `c' = ι₁y'`);
* **`phiSame_mean_eq hA`**: `W·EΦ(x,y') = E[T₁] + E[Ω₀T₂] + E[F(x,y')·t]`, with `Ω₀ = omega0`,
  `t = tSame S̃ 𝒢 = W⁻¹Tr(S̃𝒢S̃𝒢)`, and all three integrands integrable. Proof:
  `phiSame_eq_form`, `phiSame_split` a.s. (`FullSource.ae_mul_layerLin`), `t3_ibp` with `D = S̃`.

The remaining estimates (`E[T₁] = c·x*KMy' + O(W⁻²)`, `E[Ω₀T₂] = O(δ₀ + W⁻¹)`,
`E[Ft] = EF·Et + O(W⁻¹)`, `Et = c(x₀ - 1) + bx₁`) are proved in `phiSameMean_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `T₁ = a*K̂𝒢S̃c'`. -/
def tOne (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω * sTilde W b) *ᵥ physVec y')

/-- `T₂ = a*K̂𝒢S̃𝒢c'`. -/
def tTwoS (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (x y' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω * sTilde W b * gRes b E X ω) *ᵥ physVec y')

/-- **The exact mean identity of `W·Φ`.** -/
theorem phiSame_mean_eq (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ x y' : Fin W → ℂ,
      Integrable (tOne b E X x y') (freshLaw W b) ∧
      Integrable (fun ω => omega0 b E X ω * tTwoS b E X x y' ω) (freshLaw W b) ∧
      Integrable (fun ω => fForm b E X x y' ω * tSame b (sTilde W b) (gRes b E X ω))
        (freshLaw W b) ∧
      (W : ℂ) * ∫ ω, phiSame b E X x y' ω ∂freshLaw W b =
        ∫ ω, tOne b E X x y' ω ∂freshLaw W b +
          ∫ ω, omega0 b E X ω * tTwoS b E X x y' ω ∂freshLaw W b +
          ∫ ω, fForm b E X x y' ω * tSame b (sTilde W b) (gRes b E X ω) ∂freshLaw W b := by
  obtain ⟨W₁, h3⟩ := t3_ibp hA hb0 hb hκ
  obtain ⟨W₂, hi⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 2
  refine ⟨max W₁ W₂, fun W hW E hE X hY x y' => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  set μ := freshLaw W b
  obtain ⟨hFt, hTS, hT3i, hT3⟩ := h3 W (le_of_max_le_left hW) E hE X hY (sTilde W b) x y'
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have nx := PassiveCovariance.vecNorm_nonneg x
  have ny := PassiveCovariance.vecNorm_nonneg y'
  have hS := norm_sTilde_le (W := W) hb0 hb
  -- integrability of `T₁`, `T₂`
  have hT1 : Integrable (tOne b E X x y') μ := by
    refine hi W (le_of_max_le_right hW) E hE X hY.posSemidef _
      ((continuous_const.dotProduct (((continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const).matrix_mulVec continuous_const)).measurable.comp hGm).aestronglyMeasurable
      (vecNorm x * vecNorm y') fun ω => ?_
    have hB := one_le_one_add_btFun b E X ω
    refine (norm_form_le _ _ _).trans ?_
    rw [vecNorm_physVec, vecNorm_physVec]
    have hK := norm_kHat_gRes_le b E X ω
    calc vecNorm x * vecNorm y' * ‖kHat b E X * gRes b E X ω * sTilde W b‖ ≤
        vecNorm x * vecNorm y' * ((1 + btFun b E X ω) * 1) := by
          gcongr; exact (Matrix.l2_opNorm_mul _ _).trans (by gcongr)
      _ ≤ vecNorm x * vecNorm y' * (1 + btFun b E X ω) ^ 2 := by
          gcongr; nlinarith
  have hT2 : Integrable (tTwoS b E X x y') μ := by
    refine hi W (le_of_max_le_right hW) E hE X hY.posSemidef _
      ((continuous_const.dotProduct ((((continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const).matrix_mul continuous_id).matrix_mulVec
          continuous_const)).measurable.comp hGm).aestronglyMeasurable
      (vecNorm x * vecNorm y') fun ω => ?_
    refine (norm_form_le _ _ _).trans ?_
    rw [vecNorm_physVec, vecNorm_physVec]
    have hK := norm_kHat_gRes_le b E X ω
    have hG := norm_gRes_le_one_add b E X ω
    have hm : ‖kHat b E X * gRes b E X ω * sTilde W b * gRes b E X ω‖ ≤
        (1 + btFun b E X ω) * 1 * (1 + btFun b E X ω) :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul hK hS (norm_nonneg _) (by linarith [norm_nonneg (kHat b E X * gRes b E X ω)])))
        hG (norm_nonneg _) (by linarith [norm_nonneg (kHat b E X * gRes b E X ω)]))
    calc _ ≤ vecNorm x * vecNorm y' * ((1 + btFun b E X ω) * 1 * (1 + btFun b E X ω)) := by
          gcongr
      _ = _ := by ring
  have hOT : Integrable (fun ω => omega0 b E X ω * tTwoS b E X x y' ω) μ := by
    have e : (fun ω => omega0 b E X ω * tTwoS b E X x y' ω) = fun ω =>
        (boundaryZ b E + E) * tTwoS b E X x y' ω +
          selfTau b (gRes b E X ω) * tTwoS b E X x y' ω := funext fun ω => by
      simp only [omega0]; ring
    rw [e]; exact (hT2.const_mul _).add hTS
  refine ⟨hT1, hOT, hFt, ?_⟩
  -- the a.s. split
  have hae : ∀ᵐ ω ∂μ, (W : ℂ) * phiSame b E X x y' ω =
      (boundaryZ b E + E) * tTwoS b E X x y' ω + tOne b E X x y' ω -
        star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω * sTilde W b *
          (gRes b E X ω * layerLin ω)) *ᵥ physVec y') := by
    filter_upwards [FullSource.ae_mul_layerLin hb h1 h2 hY] with ω hω
    rw [phiSame_eq_form, phiSame_split b E X ω hω]
    rfl
  have hI : Integrable (fun ω => (boundaryZ b E + E) * tTwoS b E X x y' ω + tOne b E X x y' ω) μ :=
    (hT2.const_mul _).add hT1
  rw [← integral_const_mul, integral_congr_ae hae, integral_sub hI hT3i,
    integral_add (hT2.const_mul _) hT1, integral_const_mul, hT3]
  have e : (fun ω => omega0 b E X ω * tTwoS b E X x y' ω) = fun ω =>
      (boundaryZ b E + E) * tTwoS b E X x y' ω +
        selfTau b (gRes b E X ω) * tTwoS b E X x y' ω := funext fun ω => by
    simp only [omega0]; ring
  have hTS' : Integrable (fun ω => selfTau b (gRes b E X ω) * tTwoS b E X x y' ω) μ := hTS
  rw [e, integral_add (hT2.const_mul _) hTS', integral_const_mul]
  simp only [tTwoS]
  ring

end BlockBand.SourceProcess.FullSourceCovariance
