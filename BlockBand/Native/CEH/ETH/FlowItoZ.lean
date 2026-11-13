module

public import BlockBand.Native.CEH.ETH.FlowItoZAlg

/-!
# CEH ETH: Itô formula for the imaginary chain `Z` along the characteristic flow

`Z_t = Re⟨Im R_{1,t∧s} A Im R_{2,t∧s} Aᴴ⟩` is a continuous semimartingale along the
characteristic flow, with

* drift `1_{t ≤ s} · (-¼)(Re tr(K D₁₁) - Re tr(K D₁₂) - Re tr(K D₂₁) + Re tr(K D₂₂))`, where
  `K = N⁻¹Aᴴ` and `D_{PQ} = flowDrift2 P Q A m_P m_Q` is the drift matrix of the chain
  `Re tr(K P A Q)`, `P ∈ {R₁, R₁ᴴ}`, `Q ∈ {R₂, R₂ᴴ}`, `m_{Rᴴ} = m̄`;
* bracket density `1_{t ≤ s} · (1/N) ∑_x (Re fz_D R₁ R₂ A E_x)²`, `E_x = hermBasis x`, with
  `fz_D R₁ R₂ A E = ⟨fz_imS R₁ E · A Im R₂ Aᴴ⟩ + ⟨Im R₁ A · fz_imS R₂ E · Aᴴ⟩` and
  `fz_imS R E = (2i)⁻¹(RER - RᴴERᴴ)` (`∂_E Z = -Re fz_D(E)`).
The CEH form of the drift (`isContinuousSemimartingale_imChain_flowResolvent_ceh`) is
`1_{t ≤ s} Re fz_cehDrift(R₁, R₂, A, m₁, m₂, z_{1,t}, z_{2,t})`, i.e. CEH (7.2) in variance time
(see `fz_driftC_eq_ceh`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH
open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization BlockBand.Native.CEH.Flow
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

/-!
### Linear combinations of `C²` test functions
-/

section Comb

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `p ↦ c (f₁ p - f₂ p - f₃ p + f₄ p)`. -/
def fz_comb (c : ℝ) (f₁ f₂ f₃ f₄ : E → ℝ) : E → ℝ := fun p => c * (f₁ p - f₂ p - f₃ p + f₄ p)

variable {c : ℝ} {f₁ f₂ f₃ f₄ : E → ℝ} {p : E}

theorem fz_fderiv_comb (h₁ : DifferentiableAt ℝ f₁ p) (h₂ : DifferentiableAt ℝ f₂ p)
    (h₃ : DifferentiableAt ℝ f₃ p) (h₄ : DifferentiableAt ℝ f₄ p) :
    fderiv ℝ (fz_comb c f₁ f₂ f₃ f₄) p =
      c • (fderiv ℝ f₁ p - fderiv ℝ f₂ p - fderiv ℝ f₃ p + fderiv ℝ f₄ p) :=
  ((((h₁.hasFDerivAt.sub h₂.hasFDerivAt).sub h₃.hasFDerivAt).add h₄.hasFDerivAt).const_mul
    c).fderiv

theorem fz_differentiableAt_fderiv {f : E → ℝ} (h : ContDiffAt ℝ 2 f p) :
    DifferentiableAt ℝ (fderiv ℝ f) p :=
  (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem fz_fderiv_fderiv_comb (h₁ : ContDiffAt ℝ 2 f₁ p) (h₂ : ContDiffAt ℝ 2 f₂ p)
    (h₃ : ContDiffAt ℝ 2 f₃ p) (h₄ : ContDiffAt ℝ 2 f₄ p) :
    fderiv ℝ (fderiv ℝ (fz_comb c f₁ f₂ f₃ f₄)) p =
      c • (fderiv ℝ (fderiv ℝ f₁) p - fderiv ℝ (fderiv ℝ f₂) p - fderiv ℝ (fderiv ℝ f₃) p +
        fderiv ℝ (fderiv ℝ f₄) p) := by
  have hev : fderiv ℝ (fz_comb c f₁ f₂ f₃ f₄) =ᶠ[𝓝 p]
      fun q => c • (fderiv ℝ f₁ q - fderiv ℝ f₂ q - fderiv ℝ f₃ q + fderiv ℝ f₄ q) := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp), h₃.eventually (by simp),
      h₄.eventually (by simp)] with q hq₁ hq₂ hq₃ hq₄
    exact fz_fderiv_comb (hq₁.differentiableAt (by norm_num)) (hq₂.differentiableAt (by norm_num))
      (hq₃.differentiableAt (by norm_num)) (hq₄.differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  exact (((((fz_differentiableAt_fderiv h₁).hasFDerivAt.sub
    (fz_differentiableAt_fderiv h₂).hasFDerivAt).sub
    (fz_differentiableAt_fderiv h₃).hasFDerivAt).add
    (fz_differentiableAt_fderiv h₄).hasFDerivAt).const_smul c).fderiv

end Comb

section CombIto

variable {d : ℕ} {c : ℝ} {f₁ f₂ f₃ f₄ : ℝ × (Fin d → ℝ) → ℝ} {p : ℝ × (Fin d → ℝ)}

theorem fz_partialTime_comb (h₁ : DifferentiableAt ℝ f₁ p) (h₂ : DifferentiableAt ℝ f₂ p)
    (h₃ : DifferentiableAt ℝ f₃ p) (h₄ : DifferentiableAt ℝ f₄ p) :
    partialTime (fz_comb c f₁ f₂ f₃ f₄) p =
      c * (partialTime f₁ p - partialTime f₂ p - partialTime f₃ p + partialTime f₄ p) := by
  unfold partialTime
  rw [fz_fderiv_comb h₁ h₂ h₃ h₄]
  simp
  ring

theorem fz_partialSpace_comb (h₁ : DifferentiableAt ℝ f₁ p) (h₂ : DifferentiableAt ℝ f₂ p)
    (h₃ : DifferentiableAt ℝ f₃ p) (h₄ : DifferentiableAt ℝ f₄ p) (i : Fin d) :
    partialSpace (fz_comb c f₁ f₂ f₃ f₄) p i =
      c * (partialSpace f₁ p i - partialSpace f₂ p i - partialSpace f₃ p i +
        partialSpace f₄ p i) := by
  unfold partialSpace
  rw [fz_fderiv_comb h₁ h₂ h₃ h₄]
  simp
  ring

theorem fz_partialSpace2_comb (h₁ : ContDiffAt ℝ 2 f₁ p) (h₂ : ContDiffAt ℝ 2 f₂ p)
    (h₃ : ContDiffAt ℝ 2 f₃ p) (h₄ : ContDiffAt ℝ 2 f₄ p) (i j : Fin d) :
    partialSpace2 (fz_comb c f₁ f₂ f₃ f₄) p i j =
      c * (partialSpace2 f₁ p i j - partialSpace2 f₂ p i j - partialSpace2 f₃ p i j +
        partialSpace2 f₄ p i j) := by
  unfold partialSpace2
  rw [fz_fderiv_fderiv_comb h₁ h₂ h₃ h₄]
  simp
  ring

theorem fz_mul_comb_distrib (u c x₁ x₂ x₃ x₄ : ℝ) :
    u * (c * (x₁ - x₂ - x₃ + x₄)) = c * (u * x₁) - c * (u * x₂) - c * (u * x₃) + c * (u * x₄) := by
  ring

/-- The Itô drift is linear in the (`C²`) test function. -/
theorem fz_itoDrift_comb (y : Fin d → ℝ) (t : ℝ≥0) (b : Fin d → ℝ)
    (a : Matrix (Fin d) (Fin d) ℝ) (h₁ : ContDiffAt ℝ 2 f₁ ((t : ℝ), y))
    (h₂ : ContDiffAt ℝ 2 f₂ ((t : ℝ), y)) (h₃ : ContDiffAt ℝ 2 f₃ ((t : ℝ), y))
    (h₄ : ContDiffAt ℝ 2 f₄ ((t : ℝ), y)) :
    itoDrift (fz_comb c f₁ f₂ f₃ f₄) y t b a =
      c * (itoDrift f₁ y t b a - itoDrift f₂ y t b a - itoDrift f₃ y t b a +
        itoDrift f₄ y t b a) := by
  have d₁ := h₁.differentiableAt (by norm_num)
  have d₂ := h₂.differentiableAt (by norm_num)
  have d₃ := h₃.differentiableAt (by norm_num)
  have d₄ := h₄.differentiableAt (by norm_num)
  unfold itoDrift
  simp only [fz_partialTime_comb d₁ d₂ d₃ d₄, fz_partialSpace_comb d₁ d₂ d₃ d₄,
    fz_partialSpace2_comb h₁ h₂ h₃ h₄, fz_mul_comb_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end CombIto

/-!
### The combined test function on the state space
-/

variable {N : ℕ}

theorem fz_conj_flowSpectral (z m : ℂ) (s σ : ℝ) :
    conj (flowSpectral z m s σ) = flowSpectral (conj z) (conj m) s σ := by
  simp [flowSpectral, map_add, map_mul, Complex.conj_ofReal]

/-- The flow domain is invariant under conjugation of the parameters. -/
theorem fz_flowDomain_conj (z m : ℂ) (s : ℝ) :
    flowDomain N (conj z) (conj m) s = flowDomain N z m s := by
  ext y
  simp only [flowDomain, Set.mem_ofPred_eq, flowSpectral_im, Complex.conj_im]
  constructor <;> intro h h' <;> apply h <;> linarith

/-- **Adjoint bridge** on the state space: `R(z̄, m̄) = R(z, m)ᴴ`. -/
theorem fz_flowR_conj (z m : ℂ) (s : ℝ) (y : Fin (N * N + 1) → ℝ) :
    flowR (conj z) (conj m) s y = (flowR z m s y)ᴴ := by
  change _ = (Phase1.resolvent (vecHerm N (flowBlk y)) (flowSpectral z m s (flowLast y)))ᴴ
  rw [Phase1.resolvent_conjTranspose (vecHerm_isHermitian _), fz_conj_flowSpectral]
  rfl

/-- **Adjoint bridge** along the flow: `R_σ(z̄, m̄) = R_σ(z, m)ᴴ` (the condition
`0 ≤ Im z · Im m` is preserved by conjugation). -/
theorem fz_flowResolvent_conj {Ω : Type*} {F : Matrix (Fin N) (Fin N) ℂ}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (z m : ℂ) (s σ : ℝ≥0) (ω : Ω)
    (hH : (F + G σ ω).IsHermitian) :
    flowResolvent F G (conj z) (conj m) s σ ω = (flowResolvent F G z m s σ ω)ᴴ := by
  change _ = (Phase1.resolvent (F + G σ ω) (flowSpectral z m s σ))ᴴ
  rw [Phase1.resolvent_conjTranspose hH, fz_conj_flowSpectral]
  rfl

theorem fz_conj_hm {z m : ℂ} (hm : 0 ≤ z.im * m.im) : 0 ≤ (conj z).im * (conj m).im := by
  simpa [Complex.conj_im] using hm

/-- The test function `-¼(φ₁₁ - φ₁₂ - φ₂₁ + φ₂₂)`, `φ_{PQ} = Re tr(K P A Q)`, `K = N⁻¹Aᴴ`. -/
def fz_test (A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) :
    ℝ × (Fin (N * N + 1) → ℝ) → ℝ :=
  fz_comb (-(1 / 4)) (flowTest2 ((N : ℂ)⁻¹ • Aᴴ) A z₁ m₁ z₂ m₂ s)
    (flowTest2 ((N : ℂ)⁻¹ • Aᴴ) A z₁ m₁ (conj z₂) (conj m₂) s)
    (flowTest2 ((N : ℂ)⁻¹ • Aᴴ) A (conj z₁) (conj m₁) z₂ m₂ s)
    (flowTest2 ((N : ℂ)⁻¹ • Aᴴ) A (conj z₁) (conj m₁) (conj z₂) (conj m₂) s)

theorem fz_test_apply (A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ)
    (p : ℝ × (Fin (N * N + 1) → ℝ)) :
    fz_test A z₁ m₁ z₂ m₂ s p = (fz_chain (flowR z₁ m₁ s p.2) (flowR z₂ m₂ s p.2) A).re := by
  simp only [fz_test, fz_comb, flowTest2_apply, fz_flowR_conj, fz_re_chain_eq_reTr]

variable {A : Matrix (Fin N) (Fin N) ℂ} {z₁ m₁ z₂ m₂ : ℂ} {s : ℝ} {y : Fin (N * N + 1) → ℝ}

theorem fz_mem_flowDomain2_conj₂ (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) :
    y ∈ flowDomain2 N z₁ m₁ (conj z₂) (conj m₂) s := by
  rw [flowDomain2, fz_flowDomain_conj]; exact hy

theorem fz_mem_flowDomain2_conj₁ (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) :
    y ∈ flowDomain2 N (conj z₁) (conj m₁) z₂ m₂ s := by
  rw [flowDomain2, fz_flowDomain_conj]; exact hy

theorem fz_mem_flowDomain2_conj₁₂ (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) :
    y ∈ flowDomain2 N (conj z₁) (conj m₁) (conj z₂) (conj m₂) s := by
  rw [flowDomain2, fz_flowDomain_conj, fz_flowDomain_conj]; exact hy

theorem fz_contDiffAt_flowTest2 (K : Matrix (Fin N) (Fin N) ℂ) {w₁ n₁ w₂ n₂ : ℂ}
    (hy : y ∈ flowDomain2 N w₁ n₁ w₂ n₂ s) (t : ℝ) :
    ContDiffAt ℝ 2 (flowTest2 K A w₁ n₁ w₂ n₂ s) (t, y) :=
  contDiffAt_invTest2 _ _ _ _ K A (isUnit_flow hy.1 t) (isUnit_flow hy.2 t)

theorem fz_contDiffAt_test (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ) :
    ContDiffAt ℝ 2 (fz_test A z₁ m₁ z₂ m₂ s) (t, y) :=
  contDiffAt_const.mul ((((fz_contDiffAt_flowTest2 _ hy t).sub
    (fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₂ hy) t)).sub
    (fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁ hy) t)).add
    (fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁₂ hy) t))

theorem fz_test_contDiffOn (A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) :
    ContDiffOn ℝ 2 (fz_test A z₁ m₁ z₂ m₂ s) (Set.univ ×ˢ flowDomain2 N z₁ m₁ z₂ m₂ s) :=
  fun p hp => (fz_contDiffAt_test (y := p.2) hp.2 p.1).contDiffWithinAt

theorem measurable_fz_test (A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) :
    Measurable (fz_test A z₁ m₁ z₂ m₂ s) :=
  measurable_const.mul ((((measurable_flowTest2 _ A _ _ _ _ s).sub
    (measurable_flowTest2 _ A _ _ _ _ s)).sub (measurable_flowTest2 _ A _ _ _ _ s)).add
    (measurable_flowTest2 _ A _ _ _ _ s))

theorem fz_partialTime_test (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ) :
    partialTime (fz_test A z₁ m₁ z₂ m₂ s) (t, y) = 0 := by
  unfold fz_test
  rw [fz_partialTime_comb ((fz_contDiffAt_flowTest2 _ hy t).differentiableAt (by norm_num))
    ((fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₂ hy) t).differentiableAt (by norm_num))
    ((fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁ hy) t).differentiableAt (by norm_num))
    ((fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁₂ hy) t).differentiableAt
      (by norm_num)),
    partialTime_flowTest2 hy, partialTime_flowTest2 (fz_mem_flowDomain2_conj₂ hy),
    partialTime_flowTest2 (fz_mem_flowDomain2_conj₁ hy),
    partialTime_flowTest2 (fz_mem_flowDomain2_conj₁₂ hy)]
  ring

/-- **Itô drift** of `Z` before time `s`: `Re fz_driftC`. -/
theorem fz_itoDrift_test (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ≥0) :
    itoDrift (fz_test A z₁ m₁ z₂ m₂ s) y t (sumVec 0 fun _ => 1) (blockCov (gueCovVec N)) =
      (fz_driftC (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A m₁ m₂).re := by
  unfold fz_test
  rw [fz_itoDrift_comb y t _ _ (fz_contDiffAt_flowTest2 _ hy t)
    (fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₂ hy) t)
    (fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁ hy) t)
    (fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁₂ hy) t),
    itoDrift_flowTest2 hy, itoDrift_flowTest2 (fz_mem_flowDomain2_conj₂ hy),
    itoDrift_flowTest2 (fz_mem_flowDomain2_conj₁ hy),
    itoDrift_flowTest2 (fz_mem_flowDomain2_conj₁₂ hy), fz_re_driftC_eq_reTr]
  simp only [fz_flowR_conj]

/-- The space derivative of `Z` along `E_x`: `∂_x Z = -Re fz_D(E_x)`. -/
theorem fz_partialSpace_test_blk (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ)
    (k : Fin (N * N)) :
    partialSpace (fz_test A z₁ m₁ z₂ m₂ s) (t, y) (finSumFinEquiv (Sum.inl k)) =
      -(fz_D (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A (hermBasis (finProdFinEquiv.symm k))).re := by
  unfold fz_test
  rw [fz_partialSpace_comb ((fz_contDiffAt_flowTest2 _ hy t).differentiableAt (by norm_num))
    ((fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₂ hy) t).differentiableAt (by norm_num))
    ((fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁ hy) t).differentiableAt (by norm_num))
    ((fz_contDiffAt_flowTest2 _ (fz_mem_flowDomain2_conj₁₂ hy) t).differentiableAt
      (by norm_num)),
    partialSpace_flowTest2_blk hy, partialSpace_flowTest2_blk (fz_mem_flowDomain2_conj₂ hy),
    partialSpace_flowTest2_blk (fz_mem_flowDomain2_conj₁ hy),
    partialSpace_flowTest2_blk (fz_mem_flowDomain2_conj₁₂ hy)]
  simp only [fz_flowR_conj]
  exact fz_re_D_eq _ _ _ _

/-- **Itô bracket** of `Z` before time `s`: `(1/N) ∑_x (Re fz_D(E_x))²`. -/
theorem fz_itoBracket_test (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ≥0) :
    itoBracket (fz_test A z₁ m₁ z₂ m₂ s) y t (blockCov (gueCovVec N)) =
      1 / (N : ℝ) * ∑ x, (fz_D (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A (hermBasis x)).re ^ 2 := by
  unfold itoBracket
  rw [sum_fin_split]
  simp only [blockCov_inr, zero_mul, Finset.sum_const_zero, add_zero,
    sum_fin_split (fun j => blockCov _ _ j * _ * _), blockCov_inl_inl, blockCov_inl_inr,
    gueCovVec_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    fz_partialSpace_test_blk hy]
  rw [sum_hermBasis_reindex (fun E => 1 / (N : ℝ) *
    -(fz_D (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A E).re *
    -(fz_D (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A E).re), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-!
### The stochastic layer
-/

section Stochastic

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Matrix (Fin N) (Fin N) ℂ}

/-- Core form: `Re fz_chain` with drift `1_{t ≤ s} Re fz_driftC` and bracket
`1_{t ≤ s} (1/N) ∑_x (Re fz_D(E_x))²`. -/
theorem fz_isContinuousSemimartingale_chain (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im)
    (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (fz_chain (flowResolvent F G z₁ m₁ s (min t s) ω)
        (flowResolvent F G z₂ m₂ s (min t s) ω) A).re)
      (fun t ω _ => if t ≤ s then
        (fz_driftC (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A
          m₁ m₂).re else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (fz_D (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω)
          A (hermBasis x)).re ^ 2 else 0) := by
  set ρ : Ω → WithTop ℝ≥0 := fun _ => (s : WithTop ℝ≥0)
  have hst := BlockBand.SourceProcess.Stochastic.Semimartingale.stoppedSemimartingale_holds
    (N * N + 1) Ω Q 𝓖 _ _ _ (isContinuousSemimartingale_flowState (F := F) hG) ρ
    (isStoppingTime_const 𝓖 _)
  have hU : ∀ t ω, stoppedProcess (flowState F G) ρ t ω ∈ flowDomain2 N z₁ m₁ z₂ m₂ s := by
    intro t ω
    rw [stoppedProcess_flowState]
    have hle := NNReal.coe_le_coe.mpr (min_le_right t s)
    simp only [flowDomain2, flowDomain, Set.mem_inter_iff, Set.mem_ofPred_eq, flowState,
      flowLast_sumVec]
    exact ⟨flowSpectral_im_ne_zero hz₁ hm₁ hle, flowSpectral_im_ne_zero hz₂ hm₂ hle⟩
  have hito := BlockBand.SourceProcess.Stochastic.SemimartingaleIto.semimartingaleItoFormula_holds
    (N * N + 1) Ω Q 𝓖 _ _ _ hst (flowDomain2 N z₁ m₁ z₂ m₂ s) (isOpen_flowDomain2 z₁ m₁ z₂ m₂ s)
    (Eventually.of_forall fun ω t => hU t ω) (fz_test A z₁ m₁ z₂ m₂ s)
    (measurable_fz_test A z₁ m₁ z₂ m₂ s) (fz_test_contDiffOn A z₁ m₁ z₂ m₂ s)
  have hsw : ∀ {E : Type} [Zero E] (f : E) (t : ℝ≥0) (ω : Ω),
      switchAfter ρ (fun _ _ => f) t ω = if t ≤ s then f else 0 := by
    intro E _ f t ω
    simp only [switchAfter, ρ, WithTop.coe_le_coe]
  have hR : ∀ (z m : ℂ) t ω, flowR z m s (stoppedProcess (flowState F G) ρ t ω) =
      flowResolvent F G z m s (min t s) ω := by
    intro z m t ω
    rw [stoppedProcess_flowState, flowR_flowState hF hG]
  have e1 : (fun (t : ℝ≥0) ω (_ : Fin 1) => fz_test A z₁ m₁ z₂ m₂ s
      ((t : ℝ), stoppedProcess (flowState F G) ρ t ω)) =
      fun t ω _ => (fz_chain (flowResolvent F G z₁ m₁ s (min t s) ω)
        (flowResolvent F G z₂ m₂ s (min t s) ω) A).re := by
    funext t ω i
    rw [fz_test_apply, hR, hR]
  have e2 : (fun (t : ℝ≥0) ω (_ : Fin 1) => itoDrift (fz_test A z₁ m₁ z₂ m₂ s)
      (stoppedProcess (flowState F G) ρ t ω) t
      (switchAfter ρ (fun _ _ => sumVec 0 fun _ => 1) t ω)
      (switchAfter ρ (fun _ _ => blockCov (e := 1) (gueCovVec N)) t ω)) =
      fun t ω _ => if t ≤ s then
        (fz_driftC (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A
          m₁ m₂).re else 0 := by
    funext t ω i
    rw [hsw, hsw]
    split_ifs with h
    · rw [fz_itoDrift_test (hU t ω), hR, hR, min_eq_left h]
    · simp [itoDrift, fz_partialTime_test (hU t ω)]
  have e3 : (fun (t : ℝ≥0) ω => Matrix.of fun (_ _ : Fin 1) =>
      itoBracket (fz_test A z₁ m₁ z₂ m₂ s) (stoppedProcess (flowState F G) ρ t ω) t
      (switchAfter ρ (fun _ _ => blockCov (e := 1) (gueCovVec N)) t ω)) =
      fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (fz_D (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω)
          A (hermBasis x)).re ^ 2 else 0 := by
    funext t ω
    rw [hsw]
    split_ifs with h
    · rw [fz_itoBracket_test (hU t ω), hR, hR, min_eq_left h]
    · rw [itoBracket_zero]
  rw [e1, e2, e3] at hito
  exact hito

/-- **Itô formula for the imaginary chain** `Z_t = Re⟨Im R_{1,t∧s} A Im R_{2,t∧s} Aᴴ⟩` along the
characteristic flow (hypotheses of `isContinuousSemimartingale_avgRe2_flowResolvent`). Drift: `1_{t ≤ s}` times the real `-¼`-combination of
the four drifts `Re tr(K flowDrift2 P Q A m_P m_Q)`, `K = N⁻¹Aᴴ`, `P ∈ {R₁, R₁ᴴ}`,
`Q ∈ {R₂, R₂ᴴ}`, `m_{Rᴴ} = m̄`. Bracket density: `1_{t ≤ s} (1/N) ∑_x (Re fz_D R₁ R₂ A E_x)²`. -/
theorem isContinuousSemimartingale_imChain_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im)
    (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (normalizedTrace
        (External.CEH.imaginaryPart (flowResolvent F G z₁ m₁ s (min t s) ω) * A *
          External.CEH.imaginaryPart (flowResolvent F G z₂ m₂ s (min t s) ω) * Aᴴ)).re)
      (fun t ω _ => if t ≤ s then -(1 / 4) *
        (reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s t ω)
            (flowResolvent F G z₂ m₂ s t ω) A m₁ m₂) -
          reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s t ω)
            (flowResolvent F G z₂ m₂ s t ω)ᴴ A m₁ (conj m₂)) -
          reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s t ω)ᴴ
            (flowResolvent F G z₂ m₂ s t ω) A (conj m₁) m₂) +
          reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 (flowResolvent F G z₁ m₁ s t ω)ᴴ
            (flowResolvent F G z₂ m₂ s t ω)ᴴ A (conj m₁) (conj m₂))) else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (fz_D (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω)
          A (hermBasis x)).re ^ 2 else 0) := by
  have h := fz_isContinuousSemimartingale_chain hG hF hz₁ hm₁ hz₂ hm₂ s A
  simp only [fz_chain, fz_re_driftC_eq_reTr] at h
  exact h

/-- **CEH form of the drift**: the same semimartingale, with drift
`1_{t ≤ s} Re fz_cehDrift(R₁, R₂, A, m₁, m₂, z_{1,t}, z_{2,t})`, CEH (7.2) in variance time
(`λ = 1`, no `+Z` term, `η_i` the signed `Im z_{i,t}`). -/
theorem isContinuousSemimartingale_imChain_flowResolvent_ceh
    (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im)
    (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (fz_chain (flowResolvent F G z₁ m₁ s (min t s) ω)
        (flowResolvent F G z₂ m₂ s (min t s) ω) A).re)
      (fun t ω _ => if t ≤ s then
        (fz_cehDrift (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A m₁ m₂
          (flowSpectral z₁ m₁ s t) (flowSpectral z₂ m₂ s t)).re else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (fz_D (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω)
          A (hermBasis x)).re ^ 2 else 0) := by
  have h := fz_isContinuousSemimartingale_chain hG hF hz₁ hm₁ hz₂ hm₂ s A
  have e : (fun (t : ℝ≥0) (ω : Ω) (_ : Fin 1) => if t ≤ s then
      (fz_driftC (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A
        m₁ m₂).re else 0) =
      fun t ω _ => if t ≤ s then
        (fz_cehDrift (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A m₁ m₂
          (flowSpectral z₁ m₁ s t) (flowSpectral z₂ m₂ s t)).re else 0 := by
    funext t ω i
    split_ifs with hts
    · have hle := NNReal.coe_le_coe.mpr hts
      exact congrArg Complex.re (fz_driftC_eq_cehDrift (hF.add (hG.hermitian t ω))
        (flowSpectral_im_ne_zero hz₁ hm₁ hle) (flowSpectral_im_ne_zero hz₂ hm₂ hle) A m₁ m₂)
    · rfl
  rw [e] at h
  exact h

end Stochastic

end BlockBand.Native.CEH.ETH
