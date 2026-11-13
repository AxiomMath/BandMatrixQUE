module

public import BlockBand.LocalWindow.LawBridgeStatement
public import BlockBand.LocalWindow.ProofLocalLaw
public import BlockBand.LocalWindow.ProofCrowding
public import BlockBand.LocalWindow.ProofNormEvent
public import BlockBand.Window.Count.SpectralSmoothing

/-!
# The averaged local law for the fresh pair block, given `ω`

Conditionally on the exterior data, the external averaged local law for the fresh `GUE` pair block
controls the Poisson sums of the pair matrix, for part (i) of the physical local-window lemma.

## Main results

* `norm_reindex_le`: `‖reindex e e A‖ ≤ ‖A‖` (`L²` operator norm).
* `measurable_pairSample`, `gueMeasure_pair_apply` (from the law bridge
  `PairGUELawBridgeStatement`).
* `spectralSum_eq_count`: on Hermitian matrices the contract's `Inputs.spectralSum` is
  `Window.Count.spectralSum` (Borel measurable in the matrix).
* **`gue_poisson_bad_le`**: for a fixed Hermitian pair matrix `F` (the deformation at a fixed
  energy, given `ω`), a fixed real `e`, height `η > 0` and a positive root
  `m = ⟨(F - z - s m)⁻¹⟩`, `z = e + iη`, in the domain `d η Im m/π ≥ d^ε` of
  the external local law (`d = 2W`), the fresh block `G ~ GUE_d(s/d)` satisfies
  `|Σ_λ η²/(λ² + η²) - d η Im m| ≤ d^δ` for `F + G - e` outside a set of `GUE_d(s/d)`-measure
  `≤ d^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartOne

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.LawBridge
open BlockBand.LocalWindow.ProofCertificate
open scoped ENNReal NNReal Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Norm

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem toE_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ κ) :
    T (reindex e e A) v =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (T A ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm v)) := by
  ext k
  simp [mulVec, dotProduct, reindex_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]

/-- The `L²` operator norm does not increase under reindexing. -/
theorem norm_reindex_le (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖reindex e e A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  change ‖T (reindex e e A) v‖ ≤ _
  rw [toE_reindex, LinearIsometryEquiv.norm_map]
  calc _ ≤ ‖LinearMap.toContinuousLinearMap (T A)‖ *
        ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm v‖ :=
        ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap (T A)) _
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; rfl

/-- On Hermitian matrices, `Inputs.spectralSum A f = Window.Count.spectralSum f A`. -/
theorem spectralSum_eq_count {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralSum A f = BlockBand.Window.Count.spectralSum f A := by
  unfold BlockBand.Window.Count.spectralSum
  rw [dite_eq_left_of_eq_true (eq_true hA), spectralSum_eq_sum hA]

theorem measurable_poissonWeight (η : ℝ) : Measurable (poissonWeight η) := by
  unfold poissonWeight
  fun_prop

end Norm

section Bridge

variable (p : Parameters) (i : ZMod p.n)

theorem measurable_pairSample (s : ℝ) : Measurable (pairSample p i s) := by
  have hre : Measurable (reindex (pairEquiv p i).symm (pairEquiv p i).symm :
      Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → PairMatrix p i) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
    simp only [reindex_apply, submatrix_apply]
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  exact hre.comp ((continuous_const_smul _).measurable.comp measurable_subtype_coe)

/-- Probabilities of measurable pair events under `GUE_d(s/d)` are `gueSourceLaw (2W)`
probabilities of the transported sample `pairSample`, given the law bridge
`PairGUELawBridgeStatement`. -/
theorem gueMeasure_pair_apply (hBridge : PairGUELawBridgeStatement) {s : ℝ} (hs : 0 < s)
    {S : Set (PairMatrix p i)} (hS : MeasurableSet S) :
    gueMeasure (PairSite p i) (pairTime p s) S =
      gueSourceLaw (2 * p.W) {W | pairSample p i s W ∈ S} := by
  rw [hBridge p i s hs, Measure.map_apply (measurable_pairSample p i s) hS]
  rfl

end Bridge

section Local

/-- **The averaged local law at `B = 1` for the fresh pair block, conditional on `ω`**
(through the external local law `Inputs.ExternalLocalGUE`). Fixed `A, C` and
`ε, δ, D > 0` first; then `N₀`; for every `p`, pair `i` with `d = 2W ≥ N₀`, `s > 0`, Hermitian
`F` with `s^{-1/2}‖F‖ ≤ C d^A`, real `e`, `η > 0` and positive root
`m = ⟨(F - (e + iη) - s m)⁻¹⟩` with `d^ε ≤ d η Im m/π` and `|e + iη| ≤ √s d^{A + 1/ε}`:
`GUE_d(s/d){G : d^δ < |Σ_{λ ∈ Spec(F + G - e)} η²/(λ² + η²) - d η Im m|} ≤ d^{-D}`. -/
theorem gue_poisson_bad_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
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
              {G | ((2 * p.W : ℕ) : ℝ) ^ δ <
                |spectralSum (F + G - (e : ℂ) • 1) (poissonWeight η) -
                  ((2 * p.W : ℕ) : ℝ) * η * m.im|} ≤
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
  -- the measurable version of the bad set
  set S : Set (PairMatrix p i) := {G | G.IsHermitian ∧ (d : ℝ) ^ δ <
    |BlockBand.Window.Count.spectralSum (poissonWeight η) (F + G - (e : ℂ) • 1) -
      (d : ℝ) * η * m.im|}
  have hS : MeasurableSet S := by
    refine (BlockBand.Window.Count.measurableSet_isHermitian).inter ?_
    have hf : Measurable fun G : PairMatrix p i =>
        BlockBand.Window.Count.spectralSum (poissonWeight η) (F + G - (e : ℂ) • 1) :=
      (BlockBand.Window.Count.measurable_spectralSum (measurable_poissonWeight η)).comp
        ((continuous_const.add continuous_id).sub continuous_const).measurable
    exact measurableSet_lt measurable_const (hf.sub measurable_const).abs
  have hnull : gueMeasure (PairSite p i) (pairTime p s) {G | ¬ G.IsHermitian} = 0 := by
    have := BlockBand.Angular.PairCoareaBridge.ae_gueMeasure_isHermitian (PairSite p i)
      (pairTime p s)
    rwa [ae_iff] at this
  have hsub : {G : PairMatrix p i | (d : ℝ) ^ δ <
      |spectralSum (F + G - (e : ℂ) • 1) (poissonWeight η) - (d : ℝ) * η * m.im|} ⊆
      S ∪ {G | ¬ G.IsHermitian} := by
    intro G hG
    by_cases hG' : G.IsHermitian
    · left
      refine ⟨hG', ?_⟩
      have hA : (F + G - (e : ℂ) • 1).IsHermitian :=
        (hF.add hG').sub (by
          rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
            Complex.conj_ofReal])
      rw [← spectralSum_eq_count hA]
      exact hG
    · right; exact hG'
  have hpre : {W : CEH.SourceHermitian d | pairSample p i s W ∈ S} ⊆
      CEH.averagedBadEvent M 1 z δ := by
    intro W hW
    by_contra hW'
    have hread := poisson_readout hd F' M e hη hbr.2 hm.ne' δ W hW'
    obtain ⟨hHerm, hlt⟩ := hW
    have hA : (F + pairSample p i s W - (e : ℂ) • 1).IsHermitian :=
      (hF.add hHerm).sub (by
        rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
          Complex.conj_ofReal])
    have heqm : F + pairSample p i s W - (e : ℂ) • 1 =
        reindex eq.symm eq.symm (CEH.deformedMatrix (Real.sqrt s) F' W - (e : ℂ) • 1) := by
      ext x y
      simp [pairSample, CEH.deformedMatrix, F', eq, reindex_apply, Matrix.sub_apply,
        Matrix.add_apply, Matrix.one_apply]
    rw [← spectralSum_eq_count hA, heqm, ProofCrowding.spectralSum_reindex] at hlt
    linarith
  calc gueMeasure (PairSite p i) (pairTime p s) {G | (d : ℝ) ^ δ <
        |spectralSum (F + G - (e : ℂ) • 1) (poissonWeight η) - (d : ℝ) * η * m.im|}
      ≤ gueMeasure (PairSite p i) (pairTime p s) (S ∪ {G | ¬ G.IsHermitian}) :=
        measure_mono hsub
    _ ≤ gueMeasure (PairSite p i) (pairTime p s) S +
          gueMeasure (PairSite p i) (pairTime p s) {G | ¬ G.IsHermitian} := measure_union_le _ _
    _ = gueSourceLaw d {W | pairSample p i s W ∈ S} := by
        rw [hnull, add_zero, gueMeasure_pair_apply p i hBridge hs hS]
    _ ≤ gueSourceLaw d (CEH.averagedBadEvent M 1 z δ) := measure_mono hpre
    _ ≤ _ := hbad

end Local

end BlockBand.LocalWindow.ProofPartOne
