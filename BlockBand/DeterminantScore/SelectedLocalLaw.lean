module

public import BlockBand.LocalWindow.ProofPartOneLocal
public import BlockBand.LocalWindow.ProofETHCenter

/-!
# The fixed-exterior averaged local law for the complex trace

* `measurable_inv_matrix`, `measurable_trace_resolvent`: `G ↦ Tr (F + G - z)⁻¹` is measurable.
* `trace_readout`: off the CEH averaged bad event at `B = 1` (loss `N^δ`) at `z` with
  `Im z > 0`, if the branch has `⟨M(z)⟩ = m`, `Im m ≠ 0`, then
  `‖Tr (F + √s W - z)⁻¹ - N m‖ ≤ N^δ/Im z`.
* **`gue_trace_bad_le`**: the complex-trace analogue of
  `ProofPartOne.gue_poisson_bad_le`. Fixed `A, C` and `ε, δ, D > 0` first; then `N₀`; for every
  `p`, pair `i` with `d = 2W ≥ N₀`, `s > 0`, Hermitian `F` (deterministic: the exterior is fixed)
  with `s^{-1/2}‖F‖ ≤ C d^A`, real `e`, `η > 0` and positive root
  `m = ⟨(F - z - s m)⁻¹⟩`, `z = e + iη`, with `d^ε ≤ d η Im m/π` and `|z| ≤ √s d^{A + 1/ε}`:
  `GUE_d(s/d){G : d^δ/η < ‖Tr (F + G - z)⁻¹ - d m‖} ≤ d^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedLocalLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge
open BlockBand.LocalWindow.ProofCertificate BlockBand.LocalWindow.ProofPartOne
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section Measurable

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The matrix inverse is Borel measurable (`A⁻¹ = det(A)⁻¹ • adj A`). -/
theorem measurable_inv_matrix : Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  have h1 : Continuous (fun A : Matrix ι ι ℂ => A.det) := continuous_id.matrix_det
  have h2 : Continuous (fun A : Matrix ι ι ℂ => A.adjugate) := continuous_id.matrix_adjugate
  have : (fun A : Matrix ι ι ℂ => A⁻¹) = fun A => Ring.inverse A.det • A.adjugate := by
    funext A; exact Matrix.inv_def A
  rw [this]
  simp only [Ring.inverse_eq_inv']
  exact (h1.measurable.inv).smul h2.measurable

/-- `G ↦ Tr (F + G - z)⁻¹` is measurable. -/
theorem measurable_trace_resolvent (F : Matrix ι ι ℂ) (z : ℂ) :
    Measurable (fun G : Matrix ι ι ℂ => ((F + G - z • (1 : Matrix ι ι ℂ))⁻¹).trace) := by
  have hc : Continuous (fun G : Matrix ι ι ℂ => F + G - z • (1 : Matrix ι ι ℂ)) :=
    (continuous_const.add continuous_id).sub continuous_const
  have ht : Continuous (fun A : Matrix ι ι ℂ => A.trace) := continuous_id.matrix_trace
  exact ht.measurable.comp (measurable_inv_matrix.comp hc.measurable)

end Measurable

section Readout

variable {N : ℕ}

/-- `⟨Im M⟩ = Im m` when `⟨M⟩ = m` (as complex numbers). -/
theorem normalizedTrace_imaginaryPart (hN : 0 < N) (M : CEH.SourceMatrix N) {m : ℂ}
    (hm : CEH.normalizedTrace M = m) :
    CEH.normalizedTrace (CEH.imaginaryPart M) = ((m.im : ℝ) : ℂ) := by
  unfold CEH.imaginaryPart CEH.normalizedTrace
  rw [trace_smul, trace_sub, trace_conjTranspose, smul_eq_mul]
  unfold CEH.normalizedTrace at hm
  have hm' : M.trace = (N : ℂ) * m := by
    rw [← hm, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hN.ne'), one_mul]
  rw [hm', Complex.star_def, map_mul, Complex.conj_natCast, ← mul_sub, Complex.sub_conj]
  have : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  push_cast; ring

/-- **Readout of the complex trace**: off the averaged bad event at `B = 1`, loss `N^δ`, at `z`
with `Im z > 0`, if `⟨M(z)⟩ = m` with `Im m ≠ 0`, then
`‖Tr (F + √s W - z)⁻¹ - N m‖ ≤ N^δ/Im z`. -/
theorem trace_readout (hN : 0 < N) {s : ℝ} (F : CEH.SourceHermitian N)
    (M : CEH.MDEBranch (Real.sqrt s) F) {z : ℂ} (hz : 0 < z.im) {m : ℂ}
    (hm : CEH.normalizedTrace (M.matrix z) = m) (hmim : m.im ≠ 0)
    (δ : ℝ) (W : CEH.SourceHermitian N) (hW : W ∉ CEH.averagedBadEvent M 1 z δ) :
    ‖((CEH.deformedMatrix (Real.sqrt s) F W - z • 1)⁻¹).trace - (N : ℂ) * m‖ ≤
      (N : ℝ) ^ δ / z.im := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hImM : CEH.normalizedTrace (CEH.imaginaryPart (M.matrix z)) ≠ 0 := by
    rw [normalizedTrace_imaginaryPart hN _ hm]
    exact_mod_cast hmim
  have hctrl := averagedControl_one hN (M.matrix z) z hImM
  simp only [CEH.averagedBadEvent, Set.mem_ofPred_eq, not_lt] at hW
  rw [hctrl, abs_of_pos hz, Matrix.mul_one] at hW
  set X := CEH.deformedMatrix (Real.sqrt s) F W - z • (1 : CEH.SourceMatrix N)
  have hR : CEH.sourceResolvent (Real.sqrt s) F W z = X⁻¹ := rfl
  rw [hR] at hW
  have hdiff : CEH.normalizedTrace (X⁻¹ - M.matrix z) = (N : ℂ)⁻¹ * (X⁻¹.trace - N * m) := by
    unfold CEH.normalizedTrace at hm ⊢
    rw [trace_sub, mul_sub, hm, mul_sub, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast] at hW
  have hNη : 0 < (N : ℝ) * z.im := mul_pos hNr hz
  have k : (N : ℝ) ^ δ * (1 / ((N : ℝ) * z.im)) = (N : ℝ)⁻¹ * ((N : ℝ) ^ δ / z.im) := by
    field_simp
  rw [k] at hW
  exact le_of_mul_le_mul_left hW (inv_pos.mpr hNr)

end Readout

section Local

/-- The trace of the resolvent is invariant under reindexing. -/
theorem trace_inv_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ((reindex e e A)⁻¹).trace = (A⁻¹).trace := by
  rw [inv_reindex, reindex_apply]
  unfold Matrix.trace
  exact e.symm.sum_comp (fun j => A⁻¹ j j)

/-- **The fixed-exterior averaged local law for the complex trace** (the grid local law), from
the external local law `Inputs.ExternalLocalGUE` at `B = 1`, `PairGUELawBridgeStatement` and
`MDEBranchIdentification`. Fixed `A, C` and `ε, δ, D > 0` first; then `N₀`; for every `p`, pair
`i` with `d = 2W ≥ N₀`, `s > 0`, Hermitian `F` with `s^{-1/2}‖F‖ ≤ C d^A`, real `e`, `η > 0` and positive root
`m = ⟨(F - z - s m)⁻¹⟩` (`z = e + iη`) with `d^ε ≤ d η Im m/π` and `|z| ≤ √s d^{A + 1/ε}`:
`GUE_d(s/d){G : d^δ/η < ‖Tr (F + G - z)⁻¹ - d m‖} ≤ d^{-D}`. -/
theorem gue_trace_bad_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification)
    (A C ε δ D : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s : ℝ, 0 < s →
      ∀ F : PairMatrix p i, F.IsHermitian →
        (Real.sqrt s)⁻¹ * ‖F‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
        ∀ e η : ℝ, 0 < η → ∀ m : ℂ, 0 < m.im →
          m = BlockBand.Palm.certificateMatrixTrace F ((e : ℂ) + Complex.I * η + s * m) →
          ((2 * p.W : ℕ) : ℝ) ^ ε ≤ ((2 * p.W : ℕ) : ℝ) * η * (m.im / Real.pi) →
          ‖(e : ℂ) + Complex.I * η‖ ≤ Real.sqrt s * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε) →
          gueMeasure (PairSite p i) (pairTime p s)
              {G | ((2 * p.W : ℕ) : ℝ) ^ δ / η <
                ‖((F + G - ((e : ℂ) + Complex.I * η) • (1 : PairMatrix p i))⁻¹).trace -
                  ((2 * p.W : ℕ) : ℂ) * m‖} ≤
            ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := hELG A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun p i hN s hs F hF hFn e η hη m hm hroot hdom hz => ?_⟩
  set d : ℕ := 2 * p.W with hd_def
  have hd : 0 < d := by have := p.W_pos; omega
  set eq := pairEquiv p i
  set F' : CEH.SourceHermitian d := ⟨reindex eq eq F, hF.submatrix _⟩
  obtain ⟨⟨M⟩, -, -⟩ := hMDE d hd s hs F'
  set z : ℂ := (e : ℂ) + Complex.I * η with hz_def
  have hzim : z.im = η := by simp [z]
  have hbr := branch_eq_of_root hMDE hd hs F' M (z := z) (by rw [hzim]; exact hη) hm
    (by rw [certificateMatrixTrace_reindex]; exact hroot)
  have hdomain : CEH.InLocalLawDomain M A ε z := by
    refine ⟨by rw [hzim]; exact hη.ne', ?_, hz⟩
    unfold CEH.sourceDensity
    rw [hbr.2, hzim, abs_of_pos hη, abs_of_pos hm]
    exact hdom
  have hFn' : (Real.sqrt s)⁻¹ * ‖F'.1‖ ≤ C * (d : ℝ) ^ A :=
    (mul_le_mul_of_nonneg_left (norm_reindex_le eq F) (by positivity)).trans hFn
  have hbad := (h d hN s hs F' hFn' M z hdomain).2 1
  set S : Set (PairMatrix p i) := {G | (d : ℝ) ^ δ / η <
    ‖((F + G - z • (1 : PairMatrix p i))⁻¹).trace - (d : ℂ) * m‖}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const
      (((measurable_trace_resolvent F z).sub measurable_const).norm)
  have hpre : {W : CEH.SourceHermitian d | pairSample p i s W ∈ S} ⊆
      CEH.averagedBadEvent M 1 z δ := by
    intro W hW
    by_contra hW'
    have hread := trace_readout hd F' M (by rw [hzim]; exact hη) hbr.2 hm.ne' δ W hW'
    have heqm : F + pairSample p i s W - z • (1 : PairMatrix p i) =
        reindex eq.symm eq.symm (CEH.deformedMatrix (Real.sqrt s) F' W - z • 1) := by
      ext x y
      simp [pairSample, CEH.deformedMatrix, F', eq, reindex_apply, Matrix.sub_apply,
        Matrix.add_apply, Matrix.one_apply]
    have hlt := hW
    simp only [S, Set.mem_ofPred_eq] at hlt
    rw [heqm, trace_inv_reindex, ← hzim] at hlt
    exact absurd hread (not_le.mpr hlt)
  calc gueMeasure (PairSite p i) (pairTime p s) S
      = gueSourceLaw d {W | pairSample p i s W ∈ S} := gueMeasure_pair_apply p i hBridge hs hS
    _ ≤ gueSourceLaw d (CEH.averagedBadEvent M 1 z δ) := measure_mono hpre
    _ ≤ _ := hbad

/-- **The grid local law at the Dyson root** (`m = pairDyson F s z`, the `freshDyson`
after reindexing; identified with any positive root by
`ProofETH.pairDyson_eq_of_isDysonRoot`).
Same quantifier order as `gue_trace_bad_le`;
the hypotheses on `m` become `0 < Im m_z` and the root equation for `m_z = pairDyson F s z`.
-/
theorem gue_trace_bad_le_pairDyson (hBridge : PairGUELawBridgeStatement)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (A C ε δ D : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s : ℝ, 0 < s →
      ∀ F : PairMatrix p i, F.IsHermitian →
        (Real.sqrt s)⁻¹ * ‖F‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
        ∀ e η : ℝ, 0 < η → ∀ m : ℂ, 0 < m.im →
          m = BlockBand.Palm.certificateMatrixTrace F ((e : ℂ) + Complex.I * η + s * m) →
          ((2 * p.W : ℕ) : ℝ) ^ ε ≤ ((2 * p.W : ℕ) : ℝ) * η * (m.im / Real.pi) →
          ‖(e : ℂ) + Complex.I * η‖ ≤ Real.sqrt s * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε) →
          BlockBand.LocalWindow.pairDyson p i F s ((e : ℂ) + Complex.I * η) = m ∧
          gueMeasure (PairSite p i) (pairTime p s)
              {G | ((2 * p.W : ℕ) : ℝ) ^ δ / η <
                ‖((F + G - ((e : ℂ) + Complex.I * η) • (1 : PairMatrix p i))⁻¹).trace -
                  ((2 * p.W : ℕ) : ℂ) *
                    BlockBand.LocalWindow.pairDyson p i F s ((e : ℂ) + Complex.I * η)‖} ≤
            ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := gue_trace_bad_le hBridge hELG hMDE A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun p i hN s hs F hF hFn e η hη m hm hroot hdom hz => ?_⟩
  have hid : BlockBand.LocalWindow.pairDyson p i F s ((e : ℂ) + Complex.I * η) = m := by
    refine BlockBand.LocalWindow.ProofETH.pairDyson_eq_of_isDysonRoot p i hF hs
      (by simp [hη.le]) ⟨hm, ?_⟩
    conv_lhs => rw [hroot]
    unfold BlockBand.Palm.certificateMatrixTrace BlockBand.Palm.certificateMatrixResolvent
    rw [div_eq_inv_mul]
  refine ⟨hid, ?_⟩
  rw [hid]
  exact h p i hN s hs F hF hFn e η hη m hm hroot hdom hz

end Local

end BlockBand.DeterminantScore.SelectedLocalLaw
