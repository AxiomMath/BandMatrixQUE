module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepQuad
public import BlockBand.Transmission.PathScalar.Dissipative

/-!
# The cubic fresh moment `E[(x*Δy)(x'*Quad y')]`, conductance-weighted

With `freshQuad = -ΔQ(ΔQ)*` (`freshQuad_eq`, `ηQQ* = RYR* =: ηM`), the moment is
`-Σ_k E[(x*Δy)(x'*Δq_k)conj(y'*Δq_k)]`. Hölder `(2, 4, 4)` and the fresh bounds
`‖u*Δv‖_p ≤ C_p ε‖u‖‖v‖`, `ε = W^{-1/2} + δ₀ + W⁻¹`, give `≤ C ε³ C_f⁴ Σ_k‖q_k‖²`, and
`Σ_k‖q_k‖² = Re Tr M = q/η = g/(4η²)` (`trace_resolvent_sandwich`). With `δ₀ ≤ η⁻¹ + 1`,
`ε³ ≤ C(W^{-3/2} + (δ₀ + W⁻¹)²)`. Hence, from the Gaussian inputs:

* **`freshDeltaQuadCovG_holds : FreshDeltaQuadCovG`**: the bound
  `C C_f⁴(W^{-3/2} + covErr + (δ₀ + W⁻¹)²)` **times `(1 + g)`**, `g` the conductance of `X`,
  with the integrability of the product.

The unweighted `FreshDeltaQuadCov` (uniform in `g`) needs the cancellation of the Gaussian third
moment of the linear fluctuation when `g ≫ W^{1/2}`; Hölder does not see it. On
the closed chain `g ≤ R²/2` on the alive set (`cond_le_of_current`), so the weighted form suffices
there.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSourceCovariance (covErr)
open BlockBand.Transmission.Bridge
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The weighted cubic bound** (`FreshDeltaQuadCov` times `1 + g`). -/
def FreshDeltaQuadCovG : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
    ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (x y x' y' : Fin W → ℂ) (Cf : ℝ), vecNorm x ≤ Cf → vecNorm y ≤ Cf →
        vecNorm x' ≤ Cf → vecNorm y' ≤ Cf →
        Integrable (fun F => bilinear x (freshDelta b E X F) y *
            bilinear x' (ClosedForm.freshQuad b E X F) y') (freshLaw W b) ∧
        ‖∫ F, bilinear x (freshDelta b E X F) y * bilinear x' (ClosedForm.freshQuad b E X F) y'
            ∂freshLaw W b‖ ≤
          C * Cf ^ 4 * (1 + conductanceOf (passiveTransmission b E X)) *
            ((W : ℝ)⁻¹ / Real.sqrt W + covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2)

/-! ## Hölder `(2, 4, 4)` -/

instance holder_two_two_one : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

instance holder_four_four_two : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩

theorem eLpNorm_triple_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b c : α → ℂ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) :
    eLpNorm (fun x => a x * (b x * star (c x))) 1 μ ≤
      eLpNorm a 2 μ * (eLpNorm b 4 μ * eLpNorm c 4 μ) := by
  have h1 := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) ha (hb.mul hc.star)
  have h2 := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hb hc.star
  have h3 : eLpNorm (star c) 4 μ = eLpNorm c 4 μ := eLpNorm_star
  rw [h3] at h2
  exact h1.trans (by gcongr; exact h2)

/-! ## `L^p` bounds of `u*Δv` -/

theorem eLpNorm_bilinear_fresh_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {Cm Cl p : ℝ}
    (hCm : 0 ≤ Cm) (hCl : 0 ≤ Cl) (hp : 1 ≤ p)
    (hmean : ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
      Cm * (jetDistance0 b E X + (W : ℝ)⁻¹))
    (hcent : ∀ u v : Fin W → ℂ,
      eLpNorm (fun ω => bilinear u (freshDelta b E X ω -
          matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal p)
          (freshLaw W b) ≤
        ENNReal.ofReal (Cl * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u * vecNorm v))
    (u v : Fin W → ℂ) :
    eLpNorm (fun ω => bilinear u (freshDelta b E X ω) v) (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal ((Cl + Cm) * ((Real.sqrt W)⁻¹ + jetDistance0 b E X + (W : ℝ)⁻¹) *
        vecNorm u * vecNorm v) := by
  set M := matrixExpect (freshLaw W b) (freshDelta b E X)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have e : (fun ω => bilinear u (freshDelta b E X ω) v) =
      (fun ω => bilinear u (freshDelta b E X ω - M) v) + fun _ => bilinear u M v := by
    funext ω; simp [bilinear_sub']
  have hu := Transmission.PassiveCovariance.vecNorm_nonneg u
  have hv := Transmission.PassiveCovariance.vecNorm_nonneg v
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hc : eLpNorm (fun _ : LayerSample W .oneBlockOnePort => bilinear u M v)
      (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) * vecNorm u * vecNorm v) := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      (NeZero.ne (freshLaw W b)), measure_univ, ENNReal.one_rpow, mul_one, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((Transmission.PassiveCovariance.norm_bilinear_le u M v).trans
      ?_)
    calc vecNorm u * ‖M‖ * vecNorm v ≤ vecNorm u * (Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) *
          vecNorm v := by gcongr
      _ = _ := by ring
  rw [e]
  refine (eLpNorm_add_le hp1).trans ((add_le_add (hcent u v) hc).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs : 0 ≤ (Real.sqrt W)⁻¹ := by positivity
  have hW : 0 ≤ (W : ℝ)⁻¹ := by positivity
  nlinarith [mul_nonneg (mul_nonneg hCl hu) hv, mul_nonneg (mul_nonneg hCm hu) hv,
    mul_nonneg (mul_nonneg (mul_nonneg hCl hu) hv) hW,
    mul_nonneg (mul_nonneg (mul_nonneg hCm hu) hv) hs]

/-! ## Arithmetic -/

theorem cube_add_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) : (a + c) ^ 3 ≤ 4 * (a ^ 3 + c ^ 3) := by
  nlinarith [sq_nonneg (a - c), mul_nonneg ha hc, mul_nonneg (mul_nonneg ha hc) (add_nonneg ha hc)]

theorem eps_cube_le {W : ℕ} (hW : 1 ≤ W) {δ D c : ℝ} (hδ : 0 ≤ δ) (hδD : δ ≤ D)
    (hc : 0 ≤ c) :
    ((Real.sqrt W)⁻¹ + δ + (W : ℝ)⁻¹) ^ 3 ≤
      16 * (2 + D) * ((W : ℝ)⁻¹ / Real.sqrt W + c + (δ + (W : ℝ)⁻¹) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hs1 : 1 ≤ Real.sqrt W := Real.one_le_sqrt.mpr (by exact_mod_cast hW)
  set u := (Real.sqrt W)⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hv : (W : ℝ)⁻¹ = u ^ 2 := by rw [hu, inv_pow, Real.sq_sqrt hW0.le]
  have hw : (W : ℝ)⁻¹ / Real.sqrt W = u ^ 3 := by rw [hv, div_eq_mul_inv, ← hu]; ring
  rw [hw, hv]
  have hvu : u ^ 2 ≤ u := by nlinarith
  have h1 : (u + δ + u ^ 2) ^ 3 ≤ (2 * u + δ) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity); linarith
  have h2 := cube_add_le (by positivity : (0 : ℝ) ≤ 2 * u) hδ
  have hD : 0 ≤ D := hδ.trans hδD
  have h3 : δ ^ 3 ≤ D * (δ + u ^ 2) ^ 2 := by
    have : δ ^ 2 ≤ (δ + u ^ 2) ^ 2 := pow_le_pow_left₀ hδ (by nlinarith) 2
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ D * (δ + u ^ 2) ^ 2 := mul_le_mul hδD this (sq_nonneg _) hD
  have h4 : 0 ≤ (δ + u ^ 2) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ u ^ 3 := by positivity
  nlinarith [mul_nonneg hD h5, mul_nonneg hD hc, mul_nonneg hD h4]

/-- `Σ_k ‖q_k‖² = Re Tr(QQᴴ)`. -/
theorem sum_vecNorm_col_sq (Q : Matrix (Fin W) (Fin W) ℂ) :
    ∑ k, vecNorm (fun i => Q i k) ^ 2 = (Q * Qᴴ).trace.re := by
  simp only [vecNorm]
  rw [Finset.sum_congr rfl fun k _ => Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast rfl

/-! ## The weighted bound -/

/-- **`FreshDeltaQuadCovG` from the Gaussian inputs.** -/
theorem freshDeltaQuadCovG_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    FreshDeltaQuadCovG := by
  intro b hb0 hb κ hκ
  obtain ⟨Cm2, Cl2, W2, hCm2, hCl2, hD2⟩ :=
    BlockBand.SourceProcess.RawTag.delta_fresh_bounds hGA hLp b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨Cm4, Cl4, W4, hCm4, hCl4, hD4⟩ :=
    BlockBand.SourceProcess.RawTag.delta_fresh_bounds hGA hLp b hb0 hb κ hκ 4 (by norm_num)
  set η₀ : ℝ := (1 - b) * κ / 4 with hη₀def
  have hη₀ : 0 < η₀ := by
    have : 0 < 1 - b := by linarith
    positivity
  set A := Cl2 + Cm2
  set B := Cl4 + Cm4
  set D₀ := η₀⁻¹ + 1
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D₀ := by positivity
  refine ⟨A * B ^ 2 * (16 * (2 + D₀)) / (4 * η₀ ^ 2), max (max W2 W4) 1, by positivity, ?_⟩
  intro W hW E hE s hs X hX x y x' y' Cf hx hy hx' hy'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW2, hW4⟩, hW1⟩ := hW
  obtain ⟨-, hmean2, hcent2⟩ := hD2 W hW2 E hE X hX
  obtain ⟨-, hmean4, hcent4⟩ := hD4 W hW4 E hE X hX
  have hE1 : -2 < E := by linarith [hE.1]
  have hE2 : E < 2 := by linarith [hE.2]
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hηge : η₀ ≤ etaZ b E := BlockBand.SourceProcess.FullSource.etaZ_ge hb0 hb hκ hE
  have hCf : 0 ≤ Cf := (Transmission.PassiveCovariance.vecNorm_nonneg x).trans hx
  -- the square root `Q` of `M = RYR*/η`
  have hM : (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ).PosSemidef :=
    hX.mul_mul_conjTranspose_same _
  obtain ⟨S, hS⟩ := exists_mul_conjTranspose_eq hM
  set c : ℂ := (((Real.sqrt (etaZ b E))⁻¹ : ℝ) : ℂ)
  set Q := c • S
  have hcc : ((etaZ b E : ℝ) : ℂ) * (c * star c) = 1 := by
    have hr : (Real.sqrt (etaZ b E))⁻¹ * (Real.sqrt (etaZ b E))⁻¹ = (etaZ b E)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hη.le]
    simp only [c, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, hr, ← Complex.ofReal_mul, mul_inv_cancel₀ hη.ne', Complex.ofReal_one]
  have hQ : passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ =
      ((etaZ b E : ℝ) : ℂ) • (Q * Qᴴ) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, hS]
    rw [show ((etaZ b E : ℝ) : ℂ) * c * star c = 1 by rw [mul_assoc]; exact hcc, one_smul]
  -- the a.e. expansion of the cubic product
  have hΔm : Measurable fun F => freshDelta b E X F :=
    BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E measurable_const
      measurable_id
  have hbm : ∀ u v : Fin W → ℂ, Measurable fun F => bilinear u (freshDelta b E X F) v :=
    fun u v => BlockBand.SourceProcess.RawTag.measurable_bilinear_jt measurable_const hΔm
      measurable_const
  set q : Fin W → Fin W → ℂ := fun k i => Q i k
  set g : Fin W → LayerSample W .oneBlockOnePort → ℂ := fun k F =>
    bilinear x (freshDelta b E X F) y *
      (bilinear x' (freshDelta b E X F) (q k) * star (bilinear y' (freshDelta b E X F) (q k)))
  have heq : (fun F => bilinear x (freshDelta b E X F) y *
      bilinear x' (ClosedForm.freshQuad b E X F) y') =ᵐ[freshLaw W b]
      fun F => -∑ k, g k F := by
    filter_upwards [BlockBand.Transmission.PassiveLayer.ae_good W hb0 hW1] with F hF
    rw [freshQuad_eq b E hη hX hF.1 hF.2 Q hQ]
    have hneg : ∀ N : Matrix (Fin W) (Fin W) ℂ, bilinear x' (-N) y' = -bilinear x' N y' := by
      intro N; simp [bilinear, neg_mulVec]
    rw [hneg, bilinear_mul_conjTranspose]
    simp only [col_mul, mul_neg, Finset.mul_sum, g, q]
    rfl
  -- the per-term Hölder bounds
  have e2 : ENNReal.ofReal 2 = 2 := by norm_num
  have e4 : ENNReal.ofReal 4 = 4 := by norm_num
  set ε := (Real.sqrt W)⁻¹ + jetDistance0 b E X + (W : ℝ)⁻¹
  have hε : 0 ≤ ε := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    positivity
  have hterm : ∀ k, eLpNorm (g k) 1 (freshLaw W b) ≤
      ENNReal.ofReal (A * ε * Cf * Cf * ((B * ε * Cf * vecNorm (q k)) *
        (B * ε * Cf * vecNorm (q k)))) := by
    intro k
    have hq := Transmission.PassiveCovariance.vecNorm_nonneg (q k)
    have hx0 := Transmission.PassiveCovariance.vecNorm_nonneg x
    have hy0 := Transmission.PassiveCovariance.vecNorm_nonneg y
    have hx0' := Transmission.PassiveCovariance.vecNorm_nonneg x'
    have hy0' := Transmission.PassiveCovariance.vecNorm_nonneg y'
    have ha : eLpNorm (fun F => bilinear x (freshDelta b E X F) y) 2 (freshLaw W b) ≤
        ENNReal.ofReal (A * ε * vecNorm x * vecNorm y) := by
      have h := eLpNorm_bilinear_fresh_le hCm2 hCl2 (by norm_num) hmean2 hcent2 x y
      rwa [e2] at h
    have hb' : eLpNorm (fun F => bilinear x' (freshDelta b E X F) (q k)) 4 (freshLaw W b) ≤
        ENNReal.ofReal (B * ε * vecNorm x' * vecNorm (q k)) := by
      have h := eLpNorm_bilinear_fresh_le hCm4 hCl4 (by norm_num) hmean4 hcent4 x' (q k)
      rwa [e4] at h
    have hc' : eLpNorm (fun F => bilinear y' (freshDelta b E X F) (q k)) 4 (freshLaw W b) ≤
        ENNReal.ofReal (B * ε * vecNorm y' * vecNorm (q k)) := by
      have h := eLpNorm_bilinear_fresh_le hCm4 hCl4 (by norm_num) hmean4 hcent4 y' (q k)
      rwa [e4] at h
    have ha2 : A * ε * vecNorm x * vecNorm y ≤ A * ε * Cf * Cf := by gcongr
    have hb2 : B * ε * vecNorm x' * vecNorm (q k) ≤ B * ε * Cf * vecNorm (q k) := by gcongr
    have hc2 : B * ε * vecNorm y' * vecNorm (q k) ≤ B * ε * Cf * vecNorm (q k) := by gcongr
    refine (eLpNorm_triple_le (hbm x y).aestronglyMeasurable (hbm x' (q k)).aestronglyMeasurable
      (hbm y' (q k)).aestronglyMeasurable).trans ((mul_le_mul'
        (ha.trans (ENNReal.ofReal_le_ofReal ha2))
        (mul_le_mul' (hb'.trans (ENNReal.ofReal_le_ofReal hb2))
          (hc'.trans (ENNReal.ofReal_le_ofReal hc2)))).trans (le_of_eq ?_))
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (hbm x y).mul ((hbm x' (q k)).mul (continuous_star.measurable.comp (hbm y' (q k))))
  have hint : ∀ k, Integrable (g k) (freshLaw W b) := fun k =>
    ⟨(hgm k).aestronglyMeasurable, by
      rw [HasFiniteIntegral, ← eLpNorm_one_eq_lintegral_enorm (hgm k).aestronglyMeasurable]
      exact (hterm k).trans_lt ENNReal.ofReal_lt_top⟩
  have hsum : Integrable (fun F => -∑ k, g k F) (freshLaw W b) :=
    (integrable_finsetSum _ fun k _ => hint k).neg
  refine ⟨hsum.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_neg, norm_neg, integral_finsetSum _ fun k _ => hint k]
  have hk : ∀ k, ‖∫ F, g k F ∂freshLaw W b‖ ≤
      A * B ^ 2 * ε ^ 3 * Cf ^ 4 * vecNorm (q k) ^ 2 := by
    intro k
    have hq := Transmission.PassiveCovariance.vecNorm_nonneg (q k)
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [integral_norm_eq_lintegral_enorm (hint k).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm (hgm k).aestronglyMeasurable]
    refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (hterm k)).trans (le_of_eq ?_)
    ring
  -- the trace `Σ‖q_k‖² = g/(4η²)`
  have hT : ∑ k, vecNorm (q k) ^ 2 =
      conductanceOf (passiveTransmission b E X) / (4 * etaZ b E ^ 2) := by
    rw [sum_vecNorm_col_sq]
    have h1 := congrArg (fun M => (Matrix.trace M).re) hQ
    simp only [trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at h1
    rw [trace_resolvent_sandwich b E hη hX] at h1
    have h3 : conductanceOf (passiveTransmission b E X) =
        4 * etaZ b E * (passiveQ b E X).trace.re := by
      simp only [conductanceOf, passiveTransmission, trace_smul, smul_eq_mul,
        Complex.re_ofReal_mul]
    rw [h3]
    field_simp
    linarith
  have hg0 := BlockBand.SourceProcess.FullSourceCovariance.conductance_nonneg b E hη.le hX
  have hδD : jetDistance0 b E X ≤ D₀ := by
    have := BlockBand.Transmission.PathScalar.jetDistance0_le_bound hb0 hb hE1 hE2 hX
    have : (etaZ b E)⁻¹ ≤ η₀⁻¹ := inv_anti₀ hη₀ hηge
    simp only [D₀]; linarith
  have hce := covErr_nonneg hb hκ hE s hX
  have hcube := eps_cube_le hW1 (norm_nonneg _) hδD hce
  set Wt := (W : ℝ)⁻¹ / Real.sqrt W + covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2
  have hWt : 0 ≤ Wt := by positivity
  have hgη : conductanceOf (passiveTransmission b E X) / (4 * etaZ b E ^ 2) ≤
      (1 + conductanceOf (passiveTransmission b E X)) / (4 * η₀ ^ 2) := by
    have h4 : 4 * η₀ ^ 2 ≤ 4 * etaZ b E ^ 2 := by
      have := pow_le_pow_left₀ hη₀.le hηge 2; linarith
    calc conductanceOf (passiveTransmission b E X) / (4 * etaZ b E ^ 2) ≤
          conductanceOf (passiveTransmission b E X) / (4 * η₀ ^ 2) :=
          div_le_div_of_nonneg_left hg0 (by positivity) h4
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  calc ‖∑ k, ∫ F, g k F ∂freshLaw W b‖
      ≤ ∑ k, ‖∫ F, g k F ∂freshLaw W b‖ := norm_sum_le _ _
    _ ≤ ∑ k, A * B ^ 2 * ε ^ 3 * Cf ^ 4 * vecNorm (q k) ^ 2 := Finset.sum_le_sum fun k _ => hk k
    _ = A * B ^ 2 * ε ^ 3 * Cf ^ 4 *
          (conductanceOf (passiveTransmission b E X) / (4 * etaZ b E ^ 2)) := by
        rw [← Finset.mul_sum, hT]
    _ ≤ A * B ^ 2 * (16 * (2 + D₀) * Wt) * Cf ^ 4 *
          ((1 + conductanceOf (passiveTransmission b E X)) / (4 * η₀ ^ 2)) := by
        gcongr
        exact hcube
    _ = A * B ^ 2 * (16 * (2 + D₀)) / (4 * η₀ ^ 2) * Cf ^ 4 *
          (1 + conductanceOf (passiveTransmission b E X)) * Wt := by
        field_simp

end BlockBand.SourceProcess.PhysApprox.B3
