module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalPath
public import BlockBand.SourceProcess.PhysApprox.B3ModulAdapt

/-!
# Adaptedness of the tested step

For an admissible frame (`growthSigma W n_s`-measurable), with the past replacement
`rho W j` (a measurable `rho`-invariant function is `b3Sigma W j`-measurable):
* `physTseq_rho`, `b3ObsAll_rho`, **`measurable_pTest_past`**: a prelimit cylinder test at times
  of lengths `≤ j` is `b3Sigma W j`-measurable;
* `genA_rho`, `measurable_genA_past`: the cut drift up to a length `≤ j`;
* **`sm_gram_past`**, **`sm_zHat_past`**: the closed Gram state at a length in `[n_s, j]` and the
  state with the discrete jumps at a time of length `≤ j` are `b3Sigma W j`-measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2 BlockBand.SourceProcess.PhysApprox.B3.Modul
open scoped NNReal

variable {K np : ℕ} {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

theorem eigen_congr {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst h; rfl

theorem physTseq_rho {j : ℕ} (hj : closeLen s W ≤ j) (y : ProbedPath W np × ℝ) (k : ℕ) :
    physTseq b E s W (rho W j np y).1.1 k = physTseq b E s W y.1.1 k := by
  unfold physTseq
  have e : farTransmission b E W (closeLen s W) (rho W j np y).1.1 =
      farTransmission b E W (closeLen s W) y.1.1 := by
    simp only [farTransmission, rho, farReflection_extPast b E hj]
  split_ifs with hk
  · rw [eigen_congr _ _ e]
  · rfl

theorem closeLen_le_limLenAll (u : ℝ≥0) : closeLen s W ≤ limLenAll s W u :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith [u.2]) (Nat.cast_nonneg W))

section Adapted

variable (hV : Measurable[growthSigma W (closeLen s W)] V)
include hV

theorem b3ObsAll_rho {j : ℕ} (l : LIdx K np) {u : ℝ≥0}
    (hu : limLenAll s W u ≤ j) (y : ProbedPath W np × ℝ) :
    b3ObsAll b E s h τ m W V l u (rho W j np y) = b3ObsAll b E s h τ m W V l u y := by
  have hc := closeLen_le_limLenAll (s := s) (W := W) u
  rcases l with e | k | ij
  · simp only [b3ObsAll, b3ClosedGramAt_rho s h τ m hc hu hV]
  · simp only [b3ObsAll, physTseq_rho (hc.trans hu)]
  · simp only [b3ObsAll, b3ClosedKAt_rho s h τ m hc hu]

/-- **The prelimit test is measurable at the left endpoint.** -/
theorem measurable_pTest_past {j : ℕ} {r : ℕ} (i : Fin r → LIdx K np)
    (u : Fin r → ℝ≥0) (hu : ∀ l, limLenAll s W (u l) ≤ j)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) :
    Measurable[b3Sigma W j np] (pTest b E s h τ m W V i u φ) := by
  refine measurable_of_rho (measurable_pTest (hV.mono
    (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl) i u φ) fun y => ?_
  simp only [pTest, b3ObsAll_rho hV _ (hu _)]

theorem genA_rho {j : ℕ} {v : ℝ≥0} (hv : limLenAll s W v ≤ j) (e : GIdx K np)
    (y : ProbedPath W np × ℝ) :
    genA χ b E s τ m (pG b E s h τ m W V) e v (rho W j np y) =
      genA χ b E s τ m (pG b E s h τ m W V) e v y := by
  unfold genA
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr' : limLenAll s W r.toNNReal ≤ j := (Nat.floor_mono (mul_le_mul_of_nonneg_left (by
    have : ((r.toNNReal : ℝ≥0) : ℝ) ≤ v := by
      rw [Real.coe_toNNReal _ hr.1.le]; exact hr.2
    linarith) (Nat.cast_nonneg W))).trans hv
  simp only [gY_pG, b3ClosedGramAt_rho s h τ m (closeLen_le_limLenAll _) hr' hV]

theorem measurable_genA_past (hχ : Continuous χ) {j : ℕ} {v : ℝ≥0}
    (hv : limLenAll s W v ≤ j) (e : GIdx K np) :
    Measurable[b3Sigma W j np] fun y => genA χ b E s τ m (pG b E s h τ m W V) e v y := by
  have hVm : Measurable V := hV.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hG : StronglyMeasurable (Function.uncurry (pG b E s h τ m W V)) := sm_pG hVm
  have h1 := (sm_genA (b := b) (E := E) (s := s) (τ := τ) (m := m) hG hχ e).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable fun y : ProbedPath W np × ℝ => (v, y))
  rw [Function.comp_def] at h1
  exact measurable_of_rho h1.measurable fun y => genA_rho hV hv e y

/-- **The closed Gram state at a length in `[n_s, j]` is `b3Sigma W j`-measurable.** -/
theorem sm_gram_past {n j : ℕ} (hs : closeLen s W ≤ n) (hnj : n ≤ j) :
    StronglyMeasurable[b3Sigma W j np] fun y => b3ClosedGramAt b E s h τ m W n V y := by
  have hm : Measurable[b3Sigma W j np] fun y => fun e : GIdx K np =>
      gramEntry e (b3ClosedGramAt b E s h τ m W n V y) := by
    let _ : MeasurableSpace (ProbedPath W np × ℝ) := b3Sigma W j np
    exact measurable_pi_iff.2 fun e => measurable_b3X_past s h τ m hs hnj hV (Sum.inl e)
  have h2 : StronglyMeasurable[b3Sigma W j np] fun y =>
      gramOfEntries fun e : GIdx K np => gramEntry e (b3ClosedGramAt b E s h τ m W n V y) := by
    let _ : MeasurableSpace (ProbedPath W np × ℝ) := b3Sigma W j np
    exact continuous_gramOfEntries.comp_stronglyMeasurable hm.stronglyMeasurable
  simpa only [gramOfEntries_entries] using h2

theorem sm_zHat_past (hχ : Continuous χ) {j : ℕ} {v : ℝ≥0}
    (hv : limLenAll s W v ≤ j) :
    StronglyMeasurable[b3Sigma W j np] (zHat χ b E s h τ m W V v) := by
  have hc := closeLen_le_limLenAll (s := s) (W := W) v
  have hY : StronglyMeasurable[b3Sigma W j np] fun y => yHat b E s h τ m W (limLenAll s W v) V y :=
    (sm_gram_past hV hc hv).sub stronglyMeasurable_const
  have h0 : limLenAll s W 0 = closeLen s W := by simp [limLenAll, closeLen]
  have hY0 : StronglyMeasurable[b3Sigma W j np] fun y => y0P b E s h τ m W V y :=
    (sm_gram_past (n := limLenAll s W 0) hV (by rw [h0]) (by rw [h0]; exact hc.trans hv)).sub
      stronglyMeasurable_const
  have hx : StronglyMeasurable[b3Sigma W j np] fun y => fun e : GIdx K np =>
      gramEntry e (yHat b E s h τ m W (limLenAll s W v) V y) - gramEntry e (y0P b E s h τ m W V y) -
        genA χ b E s τ m (pG b E s h τ m W V) e v y := by
    have hA := fun e => measurable_genA_past (b := b) (E := E) (h := h) (τ := τ) (m := m) hV hχ
      hv e
    let _ : MeasurableSpace (ProbedPath W np × ℝ) := b3Sigma W j np
    refine (measurable_pi_iff.2 fun e => ?_).stronglyMeasurable
    exact (((ClosedLimit.continuous_gramEntry e).comp_stronglyMeasurable hY).measurable.sub
      ((ClosedLimit.continuous_gramEntry e).comp_stronglyMeasurable hY0).measurable).sub (hA e)
  exact hY.prodMk (hx.prodMk hY0)

end Adapted

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
