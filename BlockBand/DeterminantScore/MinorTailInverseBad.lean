module

public import BlockBand.DeterminantScore.MinorTailInverseGood
public import BlockBand.DeterminantScore.MinorTailInverseTrace
public import BlockBand.DeterminantScore.MinorTailInverseNull

/-!
# The bad-event moment `E♯ q_B^{-2} ≤ C_ξ W^ξ`

The local window lemma and codimension-two interlacing give `V_B ≥ cW/η` at `η = W^{-1+γ}`,
outside an event of any fixed failure power; thus `q_B² ≥ c/(Wη)` there, and the diagonal floor
`q_B² ≥ t` pays the complement.

`badMoment_holds (hC : CoareaContract) (hLW : PhysicalLocalWindowStatement)`: for `b, T, ϑ`
and `ξ > 0` there is `C` with `E♯_{α,S} q_B^{-2} ≤ C W^ξ` for `4 ≤ n ≤ TW`, `ϑ`-bulk ranks, every
model, pair, splitting law, pair frame, measurable unit eigenvector `w(θ)` of `K` and minor frame
(`pairExpect` of `(minorQSq)⁻¹`; all energies).

Proof:
* the exceptional event `Ω` of `PhysicalLocalWindowStatement` (observable `B = 0`,
  `γ = min(ξ, 1/4)`, `D = 1`) is replaced by its measurable hull `Ω' = toMeasurable P♯ Ω` (same
  pair-law measure); `pairExpect_indicator_eq` (`CoareaContract.pairLaw_formula`) transfers
  `P♯(Ω') ≤ C W^{-1}` to the coarea coordinates;
* at a point of the pair-law support (Hermitian blocks, unit `v`, `det(H_R - E) ≠ 0`, Hermitian
  `G'` with `det B ≠ 0` (`ae_minor_det_ne_zero_gue`), nonzero sector weight), the reconstructed
  matrix has `λ_α = E` (`CoareaContract.reconstructed_rank`), and the Schur complement
  `A = F(E) + G - E` at the reconstructed `G` satisfies `U_v*AU_v = M` (`schur_compress`), so
  `B = V*AV` with the isometry `V = U_v U_w`;
* off `Ω'`: `N_A([-C₁η, C₁η]) ≥ cWη` and `card_window_le_trace` give
  `cWη - 2 ≤ (C₁η)² V_B`, hence `q_B^{-2} ≤ (t²V_B)⁻¹ ≤ K W^γ` (`bad_real`, with the small-`W`
  case paid by `q_B^{-2} ≤ t⁻¹`); on `Ω'`: `q_B^{-2} ≤ t⁻¹ = 2W/s`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTailInverse

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open BlockBand.LocalWindow
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

/-!
## Measurability of the deleted-row quantities
-/

theorem measurable_outerK {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun θ : OuterData p i => outerK U θ := by
  unfold outerK outerK0
  have hUv : Measurable fun θ : OuterData p i => U θ.2.2 := hU.comp measurable_snd.snd
  have hF : Measurable fun θ : OuterData p i => physicalCoareaF θ.1.1 θ.1.2.1 θ.1.2.2 θ.2.1 :=
    measurable_physF.comp (measurable_fst.prodMk measurable_snd.fst)
  exact measurable_matMul (measurable_matMul (measurable_matConjT hUv)
    (measurable_matSub hF (measurable_smul_one measurable_snd.fst))) hUv

theorem measurable_rowMean {U : FrameMap p i} (hU : Measurable U)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : Measurable w) :
    Measurable fun θ : OuterData p i => rowMean U w θ := by
  unfold rowMean
  have hmv := measurable_mulVec' (measurable_outerK hU) hw
  refine Complex.measurable_re.comp ?_
  simp only [dotProduct, Pi.star_apply]
  exact Finset.measurable_sum _ fun j _ =>
    (continuous_star.measurable.comp ((measurable_pi_apply j).comp hw)).mul
      ((measurable_pi_apply j).comp hmv)

theorem measurable_minorB {U : FrameMap p i} (hU : Measurable U)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : Measurable w)
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : Measurable Uw) :
    Measurable fun z : OuterData p i × FrameMatrix p => minorB U w Uw z.1 z.2 := by
  unfold minorB
  have hV : Measurable fun z : OuterData p i × FrameMatrix p => Uw (w z.1) :=
    hUw.comp (hw.comp measurable_fst)
  exact measurable_matMul (measurable_matMul (measurable_matConjT hV) (measurable_outerM hU)) hV

/-- `(θ, G') ↦ q_B²` is jointly measurable. -/
theorem measurable_minorQSq (s : ℝ) {U : FrameMap p i} (hU : Measurable U)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : Measurable w)
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : Measurable Uw) :
    Measurable fun z : OuterData p i × FrameMatrix p => minorQSq s U w Uw z.1 z.2 := by
  have hB := measurable_minorB hU hw hUw
  have hBi := measurable_inv_matrix.comp hB
  have htr : Measurable fun z : OuterData p i × FrameMatrix p =>
      (minorB U w Uw z.1 z.2)⁻¹.trace.re :=
    Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp hBi)
  have hV : Measurable fun z : OuterData p i × FrameMatrix p => minorV U w Uw z.1 z.2 :=
    measurable_invSq.comp hB
  have hm : Measurable fun z : OuterData p i × FrameMatrix p => rowMean U w z.1 :=
    (measurable_rowMean hU hw).comp measurable_fst
  unfold minorQSq
  exact (((hm.sub (measurable_const.mul htr)).pow_const 2).add measurable_const).add
    (measurable_const.mul hV)

/-!
## The Schur complement at the reconstructed Gaussian
-/

/-- `U_v* A U_v = M` for `A = F(E) + G - E` at the reconstructed `G` (unit `v`). -/
theorem schur_compress {U : FrameMap p i} (hU : IsPairFrame p i U) (ω : SplitState p i) (E : ℝ)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1) (G' : FrameMatrix p) :
    (U v)ᴴ * schurA p i ω (reconstructedGaussian p i U ω E v G') E * U v =
      frameM p i U ω E v G' := by
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  set F := physicalCoareaF ω.1 ω.2.1 ω.2.2 E with hF
  set W := U v with hW
  have h1 : Wᴴ * vecMulVec v (star v) = 0 := by
    ext a b
    have := congrFun hUv a
    simp only [mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply, ← mul_assoc,
      ← Finset.sum_mul, this, zero_mul]
  set X := Wᴴ * F * W + G' with hX
  have e : schurA p i ω (reconstructedGaussian p i U ω E v G') E =
      (E : ℂ) • vecMulVec v (star v) + W * X * Wᴴ - (E : ℂ) • 1 := by
    unfold schurA schurK0 reconstructedGaussian
    simp only [← hF, ← hW, ← hX]
    abel
  have h2 : Wᴴ * (W * X * Wᴴ) * W = X := by
    calc Wᴴ * (W * X * Wᴴ) * W = (Wᴴ * W) * X * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, h1, Matrix.zero_mul, smul_zero, zero_add, h2, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, hUU]
  rfl

theorem schurA_rec_isHermitian (U : FrameMap p i) {ω : SplitState p i} (hR : ω.1.IsHermitian)
    (hV : ω.2.2.IsHermitian) (E : ℝ) (v : PairSite p i → ℂ) {G' : FrameMatrix p}
    (hG' : G'.IsHermitian) :
    (schurA p i ω (reconstructedGaussian p i U ω E v G') E).IsHermitian := by
  have hF := physicalCoareaF_isHermitian hR ω.2.1 hV E
  have hX : ((U v)ᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * U v + G').IsHermitian :=
    (isHermitian_conjTranspose_mul_mul (U v) hF).add hG'
  have hE : ((E : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one]; simp
  unfold schurA schurK0 reconstructedGaussian
  exact (hF.sub hE).add (((vecMulVec_smul_isHermitian E v).add
    (isHermitian_mul_mul_conjTranspose (U v) hX)).sub hF)

/-- **Codimension-two interlacing at the reconstructed point**: a count `N_A([-C₁η, C₁η]) ≥ cWη`
gives `cWη - 2 ≤ (C₁η)² V_B`. -/
theorem count_le_minorV {U : FrameMap p i} (hU : IsPairFrame p i U)
    {w : OuterData p i → (FrameIndex p → ℂ)}
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : IsMinorFrame Uw)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) (hw1 : l2Norm (w θ) = 1) {G' : FrameMatrix p} (hG' : G'.IsHermitian)
    (hdetB : (minorB U w Uw θ G').det ≠ 0) {N a : ℝ} (ha : 0 < a)
    (hcount : N ≤ BlockBand.Internal.Contracts.Inputs.spectralSum
      (schurA p i θ.1 (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') θ.2.1)
      (fun l => if |l| ≤ a then 1 else 0)) :
    N - 2 ≤ a ^ 2 * minorV U w Uw θ G' := by
  set A := schurA p i θ.1 (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') θ.2.1
  have hA : A.IsHermitian := schurA_rec_isHermitian U hR hV θ.2.1 θ.2.2 hG'
  obtain ⟨hUU, -⟩ := hU.2 θ.2.2 hv
  obtain ⟨hVV, -⟩ := hUw.2 (w θ) hw1
  set V := U θ.2.2 * Uw (w θ)
  have hiso : Vᴴ * V = 1 := by
    simp only [V, conjTranspose_mul]
    rw [show (Uw (w θ))ᴴ * (U θ.2.2)ᴴ * (U θ.2.2 * Uw (w θ)) =
      (Uw (w θ))ᴴ * ((U θ.2.2)ᴴ * U θ.2.2) * Uw (w θ) by simp only [Matrix.mul_assoc],
      hUU, Matrix.mul_one, hVV]
  have hcomp : Vᴴ * A * V = minorB U w Uw θ G' := by
    simp only [V, conjTranspose_mul]
    rw [show (Uw (w θ))ᴴ * (U θ.2.2)ᴴ * A * (U θ.2.2 * Uw (w θ)) =
      (Uw (w θ))ᴴ * ((U θ.2.2)ᴴ * A * U θ.2.2) * Uw (w θ) by simp only [Matrix.mul_assoc],
      schur_compress hU θ.1 θ.2.1 hv G']
    rfl
  have key := card_window_le_trace hA hiso (by rw [hcomp]; exact hdetB) ha
  rw [hcomp, card_pairSite] at key
  have hW := p.W_pos
  have hcard : ((Fintype.card (MinorIndex p) : ℕ) : ℝ) = 2 * (p.W : ℝ) - 2 := by
    rw [Fintype.card_fin, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hcard] at key
  have e : ((2 * p.W : ℕ) : ℝ) - (2 * (p.W : ℝ) - 2) = 2 := by push_cast; ring
  rw [e] at key
  have : minorV U w Uw θ G' = ((minorB U w Uw θ G')⁻¹ * (minorB U w Uw θ G')⁻¹).trace.re := rfl
  rw [this]
  linarith

/-!
## The real estimate
-/

/-- From `cWη - 2 ≤ (C₁η)²V`, `Wη = e ≥ 1`, `X ≥ t`, `X ≥ t²V` (`t = s/(2W)`) and
`W ≤ W_c` whenever `ce < 4`: `X⁻¹ ≤ (8C₁²/(s²c) + 2W_c/s) e`. -/
theorem bad_real {W s c C₁ e η X V Wc : ℝ} (hW : 0 < W) (hs : 0 < s) (hc : 0 < c)
    (hC₁ : 0 < C₁) (hWη : W * η = e) (he : 1 ≤ e) (hWc : 0 ≤ Wc)
    (hsmall : c * e < 4 → W ≤ Wc) (hX : s / (2 * W) ≤ X) (hXV : (s / (2 * W)) ^ 2 * V ≤ X)
    (hcount : c * W * η - 2 ≤ (C₁ * η) ^ 2 * V) :
    X⁻¹ ≤ (8 * C₁ ^ 2 / (s ^ 2 * c) + 2 * Wc / s) * e := by
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have he0 : 0 < e := lt_of_lt_of_le one_pos he
  by_cases hce : 4 ≤ c * e
  · have h1 : c * e / 2 ≤ C₁ ^ 2 * V * η ^ 2 := by
      have : c * W * η = c * e := by rw [← hWη]; ring
      nlinarith
    have hηe : η = e / W := by field_simp; linarith
    have h2 : c * W ^ 2 / 2 ≤ C₁ ^ 2 * V * e := by
      rw [hηe] at h1
      have h1' : c * e / 2 * W ^ 2 ≤ C₁ ^ 2 * V * e ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ W ^ 2)
        calc c * e / 2 * W ^ 2 ≤ C₁ ^ 2 * V * (e / W) ^ 2 * W ^ 2 := this
          _ = C₁ ^ 2 * V * e ^ 2 := by field_simp
      have : (c * W ^ 2 / 2) * e ≤ (C₁ ^ 2 * V * e) * e := by nlinarith
      exact le_of_mul_le_mul_right this he0
    have h3 : s ^ 2 * V ≤ 4 * W ^ 2 * X := by
      have : (s / (2 * W)) ^ 2 * V = s ^ 2 * V / (4 * W ^ 2) := by field_simp; ring
      rw [this, div_le_iff₀ (by positivity)] at hXV
      linarith
    have h4 : s ^ 2 * c ≤ 8 * C₁ ^ 2 * e * X := by
      have h5 : s ^ 2 * (c * W ^ 2 / 2) ≤ s ^ 2 * (C₁ ^ 2 * V * e) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h6 : C₁ ^ 2 * e * (s ^ 2 * V) ≤ C₁ ^ 2 * e * (4 * W ^ 2 * X) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h7 : s ^ 2 * c * W ^ 2 ≤ 8 * C₁ ^ 2 * e * X * W ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right h7 (by positivity)
    have h8 : X⁻¹ ≤ 8 * C₁ ^ 2 / (s ^ 2 * c) * e := by
      rw [inv_eq_one_div, div_mul_eq_mul_div, div_le_div_iff₀ hX0 (by positivity)]
      linarith
    have h9 : 0 ≤ 2 * Wc / s * e := by positivity
    nlinarith
  · have hWle := hsmall (lt_of_not_ge hce)
    have h1 : X⁻¹ ≤ 2 * W / s := by
      calc X⁻¹ ≤ (s / (2 * W))⁻¹ := inv_anti₀ (by positivity) hX
        _ = 2 * W / s := inv_div _ _
    have h2 : 2 * W / s ≤ 2 * Wc / s := by gcongr
    have h3 : 2 * Wc / s ≤ 2 * Wc / s * e := le_mul_of_one_le_right (by positivity) he
    have h4 : 0 ≤ 8 * C₁ ^ 2 / (s ^ 2 * c) * e := by positivity
    nlinarith

/-!
## The bad-event moment
-/

/-- **`E♯ q_B^{-2} ≤ C_ξ W^ξ`**, under the `CoareaContract` and
 (`PhysicalLocalWindowStatement`, part (i)).
-/
theorem badMoment_holds (hC : CoareaContract) (hLW : PhysicalLocalWindowStatement) :
    ∀ b T ϑ ξ : ℝ, 0 < ϑ → 0 < ξ → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
    ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
    ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
      pairExpect α (splitS p) U Pω (fun θ G' =>
          ENNReal.ofReal (minorQSq (splitS p) U w Uw θ G')⁻¹) ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ ξ) := by
  intro b T ϑ ξ hϑ hξ
  obtain ⟨δ, c, C₁, k, -, -, hc, hC₁, hLW'⟩ := hLW b T ϑ hϑ
  set γ := min ξ (1 / 4) with hγdef
  have hγ0 : 0 < γ := lt_min hξ (by norm_num)
  have hγ1 : γ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨CΩ, hCΩ⟩ := hLW' γ hγ0 hγ1 1 one_pos 1 one_pos 0
  set sb := min (1 - 2 * b) b with hsb
  set Wc := (4 / c) ^ γ⁻¹ with hWc
  have hWc0 : 0 ≤ Wc := Real.rpow_nonneg (by positivity) _
  set K := 8 * C₁ ^ 2 / (sb ^ 2 * c) + 2 * Wc / sb with hK
  set C' := max CΩ 0 with hC'
  refine ⟨2 * C' / sb + K, ?_⟩
  intro p hb hn model α hα i Pω hPω U hU w hw Uw hUw
  have hs : splitS p = sb := by unfold splitS Parameters.c; rw [hb]
  have hsp := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsb0 : 0 < sb := hs ▸ hsp
  have ht := pairTime_splitS_pos p
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW : (0 : ℝ) < p.W := by linarith
  have hK0 : 0 ≤ K := by positivity
  set s := splitS p with hsdef
  obtain ⟨Ω, -, hΩα, hΩ⟩ := hCΩ p hb hn model i Pω hPω (fun _ _ => 0)
    (Or.inl ⟨fun _ => 0, measurable_const, fun _ => ⟨isHermitian_zero, by simp⟩,
      fun _ _ => rfl⟩)
  set μ := splitPairLaw p i α Pω with hμ
  set Ω' := toMeasurable μ Ω with hΩ'
  have hΩ'm : MeasurableSet Ω' := measurableSet_toMeasurable _ _
  have hΩ'μ : μ Ω' ≤ ENNReal.ofReal (CΩ * (p.W : ℝ) ^ (-(1 : ℝ))) := by
    rw [hΩ', measure_toMeasurable]; exact hΩα α
  set η := (p.W : ℝ) ^ (-1 + γ) with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos hW _
  set e := (p.W : ℝ) ^ γ with hedef
  have he : 1 ≤ e := Real.one_le_rpow hW1 hγ0.le
  have hWη : (p.W : ℝ) * η = e := by
    rw [hηdef, hedef]
    calc (p.W : ℝ) * (p.W : ℝ) ^ (-1 + γ) = (p.W : ℝ) ^ (1 : ℝ) * (p.W : ℝ) ^ (-1 + γ) := by
          rw [Real.rpow_one]
      _ = (p.W : ℝ) ^ γ := by rw [← Real.rpow_add hW]; norm_num
  have hsmall : c * e < 4 → (p.W : ℝ) ≤ Wc := by
    intro h
    have h1 : e ≤ 4 / c := by rw [le_div_iff₀ hc]; linarith
    calc (p.W : ℝ) = e ^ γ⁻¹ := by
          rw [hedef, Real.rpow_rpow_inv hW.le hγ0.ne']
      _ ≤ (4 / c) ^ γ⁻¹ := Real.rpow_le_rpow (by positivity) h1 (inv_nonneg.mpr hγ0.le)
  have hteq : (pairTime p s : ℝ) = s / (2 * (p.W : ℝ)) := pairTime_splitS_eq p
  -- the pointwise bound
  set Φ : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ G' =>
    ENNReal.ofReal (2 * (p.W : ℝ) / s) *
      Ω'.indicator 1 (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') +
    ENNReal.ofReal (K * e) with hΦ
  have hmono : pairExpect α s U Pω (fun θ G' =>
      ENNReal.ofReal (minorQSq s U w Uw θ G')⁻¹) ≤ pairExpect α s U Pω Φ := by
    refine pairExpect_mono_ae hPω α U fun θ hR hV hv hE => ?_
    have hKH : (outerK U θ).IsHermitian := by
      rw [← outerKs_eq_outerK hU hv]; exact outerKs_isHermitian U hR hV
    obtain ⟨hw1, -⟩ := hw.2 θ hv hKH
    obtain ⟨hVV, hVw⟩ := hUw.2 (w θ) hw1
    have hmk : 2 * p.W - 1 = (2 * p.W - 2) + 1 := by have := p.W_pos; omega
    filter_upwards [ae_isHermitian_gue (pairTime p s),
      ae_minor_det_ne_zero_gue hmk ht (outerKs U θ) hw1 hVV hVw] with G' hG' hdet hsw
    have hdetB : (minorB U w Uw θ G').det ≠ 0 := by
      unfold minorB; rw [outerM_eq]; exact hdet
    obtain ⟨hXt, hXV, -⟩ := minorQSq_ge s U hR hV w Uw hG'
    have hXpos : 0 < minorQSq s U w Uw θ G' := lt_of_lt_of_le (by exact_mod_cast ht) hXt
    have hXinv : (minorQSq s U w Uw θ G')⁻¹ ≤ 2 * (p.W : ℝ) / s := by
      calc (minorQSq s U w Uw θ G')⁻¹ ≤ ((pairTime p s : ℝ))⁻¹ :=
            inv_anti₀ (by exact_mod_cast ht) hXt
        _ = 2 * (p.W : ℝ) / s := inv_pairTime_eq p
    simp only [hΦ]
    by_cases hx : (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') ∈ Ω'
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      exact le_add_right (ENNReal.ofReal_le_ofReal hXinv)
    · rw [indicator_of_notMem hx, mul_zero, zero_add]
      refine ENNReal.ofReal_le_ofReal ?_
      have hxΩ : (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G') ∉ Ω :=
        fun h => hx (subset_toMeasurable _ _ h)
      have hsec : negativeCount (frameM p i U θ.1 θ.2.1 θ.2.2 G') +
          negativeCount (θ.1.1 - (θ.2.1 : ℂ) • 1) = α.val := by
        by_contra h
        apply hsw
        unfold sectorWeight outerM
        split_ifs
        simp
      have hdetM : (frameM p i U θ.1 θ.2.1 θ.2.2 G').det ≠ 0 := by
        intro h0
        apply hsw
        unfold sectorWeight outerM
        rw [h0]; simp
      have hrank := hC.reconstructed_rank p α i U hU θ.1 θ.2.1 θ.2.2 G'
        (assemble_reconstructedGaussian_isHermitian p i U hR hV θ.2.1 θ.2.2 hG') hv hE hdetM hsec
      have hEq : physicalOrderedEigenvalue p
          (assemble p i θ.1 (reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G')) α = θ.2.1 :=
        hrank.1
      have hwin := (hΩ _ hxΩ α hα).1.1
      dsimp only at hwin
      rw [hEq] at hwin
      have hcount := count_le_minorV hU hUw hR hV hv hw1 hG' hdetB (by positivity) hwin
      have hXt' : s / (2 * (p.W : ℝ)) ≤ minorQSq s U w Uw θ G' := by rw [← hteq]; exact hXt
      have hXV' : (s / (2 * (p.W : ℝ))) ^ 2 * minorV U w Uw θ G' ≤ minorQSq s U w Uw θ G' := by
        rw [← hteq]; exact hXV
      have := bad_real hW hsp hc hC₁ hWη he hWc0 hsmall hXt' hXV' hcount
      rw [hs] at this ⊢
      exact this
  -- integrate the bound
  have hcm : Measurable fun z : OuterData p i × FrameMatrix p => ENNReal.ofReal (K * e) :=
    measurable_const
  have h1 := pairExpect_add_le_of_measurable α s hU.1 Pω (fun θ G' =>
    ENNReal.ofReal (2 * (p.W : ℝ) / s) *
      Ω'.indicator 1 (θ.1, reconstructedGaussian p i U θ.1 θ.2.1 θ.2.2 G'))
    (fun _ _ => ENNReal.ofReal (K * e)) hcm
  rw [pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top,
    pairExpect_indicator_eq hC hPω hU α hΩ'm] at h1
  have h2 := pairExpect_const_mul α s U Pω (ENNReal.ofReal_ne_top (r := K * e))
    (fun _ _ => (1 : ℝ≥0∞))
  simp only [mul_one] at h2
  rw [h2] at h1
  have h3 := pairExpect_one_le hC hPω hU α
  calc _ ≤ pairExpect α s U Pω Φ := hmono
    _ ≤ _ := h1
    _ ≤ ENNReal.ofReal (2 * (p.W : ℝ) / s) * ENNReal.ofReal (C' * (p.W : ℝ) ^ (-(1 : ℝ))) +
          ENNReal.ofReal (K * e) * 1 := by
        gcongr
        exact hΩ'μ.trans (ENNReal.ofReal_le_ofReal (by
          gcongr; exact le_max_left _ _))
    _ = ENNReal.ofReal (2 * C' / s + K * e) := by
        rw [mul_one, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        rw [Real.rpow_neg_one]
        field_simp
    _ ≤ ENNReal.ofReal ((2 * C' / sb + K) * (p.W : ℝ) ^ ξ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hs]
        have hWξ : 1 ≤ (p.W : ℝ) ^ ξ := Real.one_le_rpow hW1 hξ.le
        have heξ : e ≤ (p.W : ℝ) ^ ξ := Real.rpow_le_rpow_of_exponent_le hW1 (min_le_left _ _)
        have hC'0 : 0 ≤ 2 * C' / sb := by positivity
        nlinarith [mul_le_mul_of_nonneg_left heξ hK0, mul_le_mul_of_nonneg_left hWξ hC'0]

end BlockBand.DeterminantScore.MinorTailInverse
