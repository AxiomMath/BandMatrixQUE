module

public import BlockBand.Critical.MatrixClosing.Reduction
public import BlockBand.Critical.Herglotz.Transfer

/-!
# Matrix closing: consequences for the entire law

The matrix closing theorem applies uniformly to the old data, so the limiting physical source
matrix is `𝒯 = Re𝒦 + ηB^{1/2}𝖢_p(0)B^{1/2}`.

* `MatrixClosingStatement.atZero`: the matrix closing law against every realization of `𝖢_r(0)`
  (`IsCanonicalCauchyAtZero`), uniformly in the old data.
* `collarFunction_eval_ofReal_isHermitian`, `ae_closingMatrix_isHermitian`: the lossless closing
  matrix is Hermitian a.s.; `ae_isHermitian_of_isCanonicalCauchyAtZero`: so is `𝖢_r(0)`.
* `closedSourceMatrix_isHermitian`, `norm_closedSourcePhase_of_isHermitian`, `phaseFun`, `phaseRe`,
  `phaseIm`: the phase of `ClosedSourceMomentValue` as bounded continuous tests.
* **`MatrixClosingStatement.closedSource`**: for fixed `E`, deterministic `K`, `σ`, the collar
  expectation of `exp{-iΣσ_j𝒯_jj}` with `𝒯 = closedSourceMatrix b E K 𝒞_W` converges, uniformly in the
  old data, to the inner integral `∫ exp{-iΣσ_j𝒯_jj}(K, C₀) dP'` of `ClosedSourceMomentValue`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz
open BlockBand.Internal.Contracts.CoareaPalm (freshEigenvalue)
open scoped ComplexConjugate

variable {W : ℕ}

theorem microShift_zero (W : ℕ) (e : ℝ) : microShift W e 0 = 0 := by
  simp [microShift]

/-- **The matrix closing law at `0`.** From `MatrixClosingStatement`:
for every realization `C₀` of `𝖢_r(0)` (`IsCanonicalCauchyAtZero`, the object entering
`closedSourceMatrix`/`ClosedSourceMomentValue`), the law of `-iJ*{2(I - U𝔯)⁻¹ - I}J` under the
collar law is uniformly close to that of `C₀` on every bounded continuous test.
-/
theorem MatrixClosingStatement.atZero (h : MatrixClosingStatement) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {r : ℕ} {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    {C₀ : Ω' → Matrix (Fin r) (Fin r) ℂ} (hC₀ : IsCanonicalCauchyAtZero r P' Ξ C₀)
    (Φ : BoundedContinuousFunction (Matrix (Fin r) (Fin r) ℂ) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (W₀ : ℕ), 0 < δ ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b e X ≤ δ →
      ∀ J : Matrix (Fin 2 × Fin W) (Fin r) ℂ, Jᴴ * J = 1 →
        AEMeasurable (closingMatrix b e 0 X J) (collarLaw W b) ∧
        |∫ ω, Φ (closingMatrix b e 0 X J ω) ∂collarLaw W b - ∫ ω, Φ (C₀ ω) ∂P'| ≤ ε := by
  obtain ⟨C, hC, hae⟩ := exists_isCanonicalCauchy_ae_eq hC₀
  let ev : C(Fin 1 → Matrix (Fin r) (Fin r) ℂ, Matrix (Fin r) (Fin r) ℂ) :=
    ⟨fun v => v 0, continuous_apply 0⟩
  obtain ⟨δ, W₀, hδ, hmain⟩ := h b hb0 hb κ hκ r 1 (fun _ => 0) Ω' P' Ξ C hC
    (Φ.compContinuous ev) ε hε
  refine ⟨δ, W₀, hδ, fun W hW hW₀ e he X hX hd J hJ => ?_⟩
  obtain ⟨hm, hle⟩ := hmain W hW hW₀ e he X hX hd J hJ
  have hfun : (fun ω => ev (shiftedClosing b e (fun _ : Fin 1 => (0 : ℝ)) X J ω)) =
      closingMatrix b e 0 X J := by
    funext ω
    simp [ev, shiftedClosing, microShift_zero]
  refine ⟨hfun ▸ ev.continuous.measurable.comp_aemeasurable hm, ?_⟩
  have h1 : ∫ ω, (Φ.compContinuous ev) (shiftedClosing b e (fun _ => 0) X J ω) ∂collarLaw W b =
      ∫ ω, Φ (closingMatrix b e 0 X J ω) ∂collarLaw W b := by
    rw [← hfun]; rfl
  have h2 : ∫ ω, (Φ.compContinuous ev) (fun _ : Fin 1 => C ω ((0 : ℝ) : ℂ)) ∂P' =
      ∫ ω, Φ (C₀ ω) ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp [ev, hω]
  rw [h1, h2] at hle
  exact hle

/-!
## Hermitian values
-/

/-- `F_W(x)` is Hermitian at every real point. -/
theorem collarFunction_eval_ofReal_isHermitian {r : ℕ} (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ)
    (ω : CollarSample W) (x : ℝ) : ((collarFunction b e X J ω).eval x).IsHermitian := by
  rw [collarFunction, eval_ofAtoms]
  refine (Collar.Kernel.rePart_isHermitian _).add ?_
  show (∑ ℓ, _)ᴴ = _
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hR := (collarResidue_posSemidef b e X J ω ℓ).1
  have : (((poleScale W e * freshEigenvalue (portSchurFin e X ω) ℓ : ℝ) : ℂ) - x)⁻¹ =
      (((poleScale W e * freshEigenvalue (portSchurFin e X ω) ℓ - x)⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  simp only [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hR.eq]

/-- The closing matrix of a lossless old response is Hermitian almost surely. -/
theorem ae_closingMatrix_isHermitian {r : ℕ} {b : ℝ} (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    (hW : 0 < W) {e : ℝ} (he : e ∈ bulkInterval κ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) :
    ∀ᵐ ω ∂collarLaw W b, (closingMatrix b e 0 X J ω).IsHermitian := by
  filter_upwards [ae_collarFunction_eval_eq hb hW e (boundaryZ_im_pos hb hκ he)
    (poleScale_pos hW hκ he) hX J 0] with ω hω
  rw [microShift_zero] at hω
  rw [← hω]
  exact collarFunction_eval_ofReal_isHermitian b e X J ω 0

/-- A realization of the `𝖢_r(0)` is Hermitian almost surely (limit in probability of the
Hermitian symmetric cutoffs).
-/
theorem ae_isHermitian_of_isCanonicalCauchyAtZero {r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    {C₀ : Ω → Matrix (Fin r) (Fin r) ℂ} (hC₀ : IsCanonicalCauchyAtZero r P Ξ C₀) :
    ∀ᵐ ω ∂P, (C₀ ω).IsHermitian := by
  have hent : ∀ i j : Fin r, (fun ω => C₀ ω j i) =ᵐ[P] fun ω => conj (C₀ ω i j) := by
    intro i j
    have hsymm : ∀ R ω, truncatedCauchyEntry r (Ξ ω) R j i =
        conj (truncatedCauchyEntry r (Ξ ω) R i j) := by
      intro R ω
      unfold truncatedCauchyEntry
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    have hconj : TendstoInMeasure P (fun R ω => truncatedCauchyEntry r (Ξ ω) R j i) atTop
        (fun ω => conj (C₀ ω i j)) := by
      intro ε hε
      have := hC₀.limit i j ε hε
      refine this.congr fun R => ?_
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, hsymm, Complex.isometry_conj.edist_eq]
    exact tendstoInMeasure_ae_unique (hC₀.limit j i) hconj
  have hall : ∀ᵐ ω ∂P, ∀ i j : Fin r, C₀ ω j i = conj (C₀ ω i j) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact hent i
  filter_upwards [hall] with ω hω
  ext i j
  rw [conjTranspose_apply, hω i j, Complex.star_def, Complex.conj_conj]

/-!
## The closed-source phase of `ClosedSourceMomentValue`
-/

section Phase

variable {p : ℕ}

theorem closedSourceMatrix_isHermitian (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ)
    {H : Matrix (Fin p) (Fin p) ℂ} (hH : H.IsHermitian) :
    (closedSourceMatrix b e K H).IsHermitian := by
  have hS : (cfc Real.sqrt (probeGram b e K)).IsHermitian :=
    (cfc_predicate (p := IsSelfAdjoint) Real.sqrt (probeGram b e K) :)
  have hRe : (matrixRePart K).IsHermitian := Collar.Kernel.rePart_isHermitian K
  have hSHS : (cfc Real.sqrt (probeGram b e K) * H * cfc Real.sqrt (probeGram b e K)).IsHermitian := by
    have := isHermitian_mul_mul_conjTranspose (cfc Real.sqrt (probeGram b e K)) hH
    rwa [hS.eq] at this
  unfold closedSourceMatrix
  refine hRe.add ?_
  simp only [IsHermitian, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hSHS.eq]

theorem norm_closedSourcePhase_of_isHermitian (σ : Fin p → ℤˣ) {T : Matrix (Fin p) (Fin p) ℂ}
    (hT : T.IsHermitian) : ‖closedSourcePhase σ T‖ = 1 := by
  have hdiag : ∀ j, (T j j).im = 0 := fun j => by
    have := congrFun (congrFun hT j) j
    rw [conjTranspose_apply, Complex.star_def] at this
    exact Complex.conj_eq_iff_im.1 this
  have hsum : (∑ j, (((σ j : ℤ) : ℂ) * T j j)).im = 0 := by
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Complex.mul_im, hdiag j]
  unfold closedSourcePhase
  rw [Complex.norm_exp]
  simp [Complex.mul_re, hsum]

/-- `M ↦ exp{-iΣ_j σ_j 𝒯_jj}`, `𝒯 = closedSourceMatrix b e K (Re M)`: equals the phase of
`ClosedSourceMomentValue` on Hermitian `M`, and has modulus one everywhere. -/
def phaseFun (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ)
    (M : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  closedSourcePhase σ (closedSourceMatrix b e K (Collar.Kernel.rePart M))

theorem norm_phaseFun (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ)
    (M : Matrix (Fin p) (Fin p) ℂ) : ‖phaseFun b e K σ M‖ = 1 :=
  norm_closedSourcePhase_of_isHermitian σ
    (closedSourceMatrix_isHermitian b e K (Collar.Kernel.rePart_isHermitian M))

theorem continuous_phaseFun (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ) :
    Continuous (phaseFun b e K σ) := by
  have hRe : Continuous fun M : Matrix (Fin p) (Fin p) ℂ => Collar.Kernel.rePart M := by
    unfold Collar.Kernel.rePart
    refine Continuous.const_smul ?_ ((2 : ℂ)⁻¹)
    exact continuous_id.add (continuous_id (X := Matrix (Fin p) (Fin p) ℂ)).matrix_conjTranspose
  have hT : Continuous fun M : Matrix (Fin p) (Fin p) ℂ =>
      closedSourceMatrix b e K (Collar.Kernel.rePart M) := by
    unfold closedSourceMatrix
    refine continuous_const.add (Continuous.const_smul ?_ (((BlockBand.Internal.Contracts.TransmissionPath.etaZ b e : ℝ) : ℂ)))
    exact (continuous_const.matrix_mul hRe).matrix_mul continuous_const
  have hd : Continuous fun M : Matrix (Fin p) (Fin p) ℂ =>
      ∑ j, (((σ j : ℤ) : ℂ) * closedSourceMatrix b e K (Collar.Kernel.rePart M) j j) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (hT.matrix_elem j j)
  unfold phaseFun closedSourcePhase
  exact Complex.continuous_exp.comp ((continuous_const.mul hd).neg)

/-- Real part of `phaseFun` as a bounded continuous test. -/
def phaseRe (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ) :
    BoundedContinuousFunction (Matrix (Fin p) (Fin p) ℂ) ℝ :=
  .mkOfBound ⟨fun M => (phaseFun b e K σ M).re,
    Complex.continuous_re.comp (continuous_phaseFun b e K σ)⟩ 2 fun M N => by
    have h1 := Complex.abs_re_le_norm (phaseFun b e K σ M)
    have h2 := Complex.abs_re_le_norm (phaseFun b e K σ N)
    rw [norm_phaseFun] at h1 h2
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    linarith [abs_sub (phaseFun b e K σ M).re (phaseFun b e K σ N).re]

/-- Imaginary part of `phaseFun` as a bounded continuous test. -/
def phaseIm (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ) :
    BoundedContinuousFunction (Matrix (Fin p) (Fin p) ℂ) ℝ :=
  .mkOfBound ⟨fun M => (phaseFun b e K σ M).im,
    Complex.continuous_im.comp (continuous_phaseFun b e K σ)⟩ 2 fun M N => by
    have h1 := Complex.abs_im_le_norm (phaseFun b e K σ M)
    have h2 := Complex.abs_im_le_norm (phaseFun b e K σ N)
    rw [norm_phaseFun] at h1 h2
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    linarith [abs_sub (phaseFun b e K σ M).im (phaseFun b e K σ N).im]

theorem integral_phaseFun_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (b e : ℝ) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ) {M : Ω → Matrix (Fin p) (Fin p) ℂ}
    (hM : AEMeasurable M μ) :
    ∫ ω, phaseFun b e K σ (M ω) ∂μ =
      ((∫ ω, phaseRe b e K σ (M ω) ∂μ : ℝ) : ℂ) + ((∫ ω, phaseIm b e K σ (M ω) ∂μ : ℝ) : ℂ) *
        Complex.I := by
  have hint : Integrable (fun ω => phaseFun b e K σ (M ω)) μ := by
    refine Integrable.of_bound ((continuous_phaseFun b e K σ).measurable.comp_aemeasurable hM).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun ω => (norm_phaseFun b e K σ (M ω)).le)
  have hre := integral_re hint
  have him := integral_im hint
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
    exact hre.symm
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    rw [add_zero]; exact him.symm

end Phase

/-- **The matrix closing law for closed source moments** (`ClosedSourceMomentValue`).
From `MatrixClosingStatement`: at a fixed bulk energy `E`, for every deterministic probe source matrix `K` (`p × p`, `B = probeGram b E K`)
and signs `σ`, and every realization `C₀` of the `𝖢_p(0)`, the collar expectation of the
phase `exp{-iΣ_jσ_j𝒯_jj}` of `𝒯 = Re K + ηB^{1/2}𝒞_W B^{1/2}` (`closedSourceMatrix`, with the
physical closing matrix `𝒞_W = -iJ*{2(I - U𝔯)⁻¹ - I}J` in place of `𝖢_p(0)`) is uniformly close to
`E exp{-iΣ_jσ_j𝒯_jj}` with `𝖢_p(0)`, the inner integral of `ClosedSourceMomentValue`.
-/
theorem MatrixClosingStatement.closedSource (h : MatrixClosingStatement) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) {E : ℝ} (hE : E ∈ bulkInterval κ) {p : ℕ}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin p → ℂ))} {C₀ : Ω' → Matrix (Fin p) (Fin p) ℂ}
    (hC₀ : IsCanonicalCauchyAtZero p P' Ξ C₀) (K : Matrix (Fin p) (Fin p) ℂ) (σ : Fin p → ℤˣ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (δ : ℝ) (W₀ : ℕ), 0 < δ ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        matchedDistance b E X ≤ δ →
      ∀ J : Matrix (Fin 2 × Fin W) (Fin p) ℂ, Jᴴ * J = 1 →
        ‖∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (closingMatrix b E 0 X J ω))
            ∂collarLaw W b -
          ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C₀ ω)) ∂P'‖ ≤ ε := by
  have := hC₀.decorated.prob
  obtain ⟨δ₁, W₁, hδ₁, h1⟩ := h.atZero hb0 hb hκ hC₀ (phaseRe b E K σ) (half_pos hε)
  obtain ⟨δ₂, W₂, hδ₂, h2⟩ := h.atZero hb0 hb hκ hC₀ (phaseIm b E K σ) (half_pos hε)
  refine ⟨min δ₁ δ₂, max W₁ W₂, lt_min hδ₁ hδ₂, fun W hW hW₀ X hX hd J hJ => ?_⟩
  obtain ⟨hm, hle1⟩ := h1 W hW (le_of_max_le_left hW₀) E hE X hX (hd.trans (min_le_left _ _)) J hJ
  obtain ⟨-, hle2⟩ := h2 W hW (le_of_max_le_right hW₀) E hE X hX (hd.trans (min_le_right _ _)) J hJ
  have hCm : AEMeasurable C₀ P' := by
    refine (Measurable.of_eval_matrix _ fun i j => hC₀.measurable i j).aemeasurable
  have e1 : ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (closingMatrix b E 0 X J ω))
      ∂collarLaw W b = ∫ ω, phaseFun b E K σ (closingMatrix b E 0 X J ω) ∂collarLaw W b := by
    refine integral_congr_ae ?_
    filter_upwards [ae_closingMatrix_isHermitian hb hκ hW hE hX J] with ω hω
    rw [phaseFun, rePart_eq_self hω]
  have e2 : ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C₀ ω)) ∂P' =
      ∫ ω, phaseFun b E K σ (C₀ ω) ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [ae_isHermitian_of_isCanonicalCauchyAtZero hC₀] with ω hω
    rw [phaseFun, rePart_eq_self hω]
  rw [e1, e2, integral_phaseFun_eq b E K σ hm, integral_phaseFun_eq b E K σ hCm]
  set a := ∫ ω, phaseRe b E K σ (closingMatrix b E 0 X J ω) ∂collarLaw W b
  set a' := ∫ ω, phaseRe b E K σ (C₀ ω) ∂P'
  set c := ∫ ω, phaseIm b E K σ (closingMatrix b E 0 X J ω) ∂collarLaw W b
  set c' := ∫ ω, phaseIm b E K σ (C₀ ω) ∂P'
  have : ((a : ℂ) + (c : ℂ) * Complex.I) - ((a' : ℂ) + (c' : ℂ) * Complex.I) =
      ((a - a' : ℝ) : ℂ) + ((c - c' : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  linarith

end BlockBand.Critical.MatrixClosing
