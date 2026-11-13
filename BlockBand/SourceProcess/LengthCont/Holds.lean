module

public import BlockBand.SourceProcess.LengthCont.Pin
public import BlockBand.SourceProcess.ComplexSourceLaw.Sequence

/-!
# Length continuity from the one-layer bounds

The complex source data at two lengths `r_j` and `⌊W_jT⌋` with `r_j/W_j → T` are close in
probability, by the one-layer increment bounds and Doob's inequality.

Proof. Fix a critical sequence `(W_j, r_j)` and put `R_j = ⌊W_j T⌋`. Eventually both lengths lie
in the window `|n - TW_j| < δW_j` of `LayerIncrementBounds`, and `W_j ≥ W₀`. Between them lie
`N_j = |r_j - R_j| = o(W_j)` layers. For each real coordinate, the Doob estimate
(`measureReal_abs_sub_ge_le`) bounds the probability of a deviation `≥ ε/2` by
`(16/ε² + 4/ε) N_j C / W_j`; real and imaginary parts are combined with `‖z‖ ≤ |Re z| + |Im z|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionSequences
open BlockBand.SourceProcess.ComplexSourceLaw

/-- The one-width estimate between lengths `a` and `a + N`. -/
theorem measure_entry_sub_ge_le (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) (r : Fin 4)
    (i k : Fin np) {ε C : ℝ} (hε : 0 < ε) (a N : ℕ)
    (hb : ∀ n, a ≤ n → n < a + N → ∀ s : Bool,
      MemLp (incr (sourceCoord b E W τ m r i k s) n) 2 (probedPathLaw W np b) ∧
      ∫ x, |(probedPathLaw W np b)[incr (sourceCoord b E W τ m r i k s) n |
          probedSigma W np n] x| ∂probedPathLaw W np b ≤ C / W ∧
      ∫ x, mart (probedPathLaw W np b) (probedSigma W np) (sourceCoord b E W τ m r i k s) n x ^ 2
          ∂probedPathLaw W np b ≤ C / W) :
    probedPathLaw W np b {x | ε ≤ ‖complexSourceData b E W (a + N) τ m x r i k -
        complexSourceData b E W a τ m x r i k‖} ≤
      ENNReal.ofReal (2 * ((16 / ε ^ 2 + 4 / ε) * (N * (C / W)))) := by
  set μ := probedPathLaw W np b
  have hε2 : 0 < ε / 2 := by positivity
  have key : ∀ s : Bool, μ.real {x | ε / 2 ≤ |sourceCoord b E W τ m r i k s (a + N) x -
      sourceCoord b E W τ m r i k s a x|} ≤ (16 / ε ^ 2 + 4 / ε) * (N * (C / W)) := by
    intro s
    have h := measureReal_abs_sub_ge_le (μ := μ) (probedSigma W np)
      (sourceCoord b E W τ m r i k s) (probedSigma_le W np) (probedSigma_mono W np)
      (stronglyMeasurable_sourceCoord_sigma b E W τ m r i k s) a N hε2
      (fun i' hi => (hb (a + i') (Nat.le_add_right a i') (by omega) s).1)
      (fun i' hi => (hb (a + i') (Nat.le_add_right a i') (by omega) s).2.1)
      (fun i' hi => (hb (a + i') (Nat.le_add_right a i') (by omega) s).2.2)
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  have hsub : {x | ε ≤ ‖complexSourceData b E W (a + N) τ m x r i k -
      complexSourceData b E W a τ m x r i k‖} ⊆
      {x | ε / 2 ≤ |sourceCoord b E W τ m r i k true (a + N) x -
          sourceCoord b E W τ m r i k true a x|} ∪
        {x | ε / 2 ≤ |sourceCoord b E W τ m r i k false (a + N) x -
          sourceCoord b E W τ m r i k false a x|} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union, sourceCoord, ite_true,
      Bool.false_eq_true, ite_false] at hx ⊢
    have h1 := Complex.norm_le_abs_re_add_abs_im (complexSourceData b E W (a + N) τ m x r i k -
      complexSourceData b E W a τ m x r i k)
    rw [Complex.sub_re, Complex.sub_im] at h1
    by_contra hcon
    push Not at hcon
    linarith [hcon.1, hcon.2]
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc μ.real {x | ε ≤ ‖complexSourceData b E W (a + N) τ m x r i k -
        complexSourceData b E W a τ m x r i k‖}
      ≤ μ.real ({x | ε / 2 ≤ |sourceCoord b E W τ m r i k true (a + N) x -
          sourceCoord b E W τ m r i k true a x|} ∪
        {x | ε / 2 ≤ |sourceCoord b E W τ m r i k false (a + N) x -
          sourceCoord b E W τ m r i k false a x|}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ (16 / ε ^ 2 + 4 / ε) * (N * (C / W)) + (16 / ε ^ 2 + 4 / ε) * (N * (C / W)) :=
        add_le_add (key true) (key false)
    _ = 2 * ((16 / ε ^ 2 + 4 / ε) * (N * (C / W))) := by ring

/-- The one-width estimate between two arbitrary lengths `p, q`. -/
theorem measure_entry_sub_ge_le' (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) (r : Fin 4)
    (i k : Fin np) {ε C : ℝ} (hε : 0 < ε) (p q : ℕ)
    (hb : ∀ n, min p q ≤ n → n < max p q → ∀ s : Bool,
      MemLp (incr (sourceCoord b E W τ m r i k s) n) 2 (probedPathLaw W np b) ∧
      ∫ x, |(probedPathLaw W np b)[incr (sourceCoord b E W τ m r i k s) n |
          probedSigma W np n] x| ∂probedPathLaw W np b ≤ C / W ∧
      ∫ x, mart (probedPathLaw W np b) (probedSigma W np) (sourceCoord b E W τ m r i k s) n x ^ 2
          ∂probedPathLaw W np b ≤ C / W) :
    probedPathLaw W np b {x | ε ≤ ‖complexSourceData b E W p τ m x r i k -
        complexSourceData b E W q τ m x r i k‖} ≤
      ENNReal.ofReal (2 * ((16 / ε ^ 2 + 4 / ε) * (|(p : ℝ) - q| * (C / W)))) := by
  rcases le_total p q with hpq | hqp
  · have h := measure_entry_sub_ge_le b E τ m W r i k (C := C) hε p (q - p) fun n h1 h2 =>
      hb n (by rw [min_eq_left hpq]; exact h1) (by rw [max_eq_right hpq]; omega)
    rw [Nat.add_sub_cancel' hpq] at h
    have hN : ((q - p : ℕ) : ℝ) = |(p : ℝ) - q| := by
      have : (p : ℝ) ≤ q := by exact_mod_cast hpq
      rw [Nat.cast_sub hpq, abs_sub_comm, abs_of_nonneg (by linarith)]
    simp_rw [norm_sub_rev (complexSourceData b E W p τ m _ r i k)]
    rwa [hN] at h
  · have h := measure_entry_sub_ge_le b E τ m W r i k (C := C) hε q (p - q) fun n h1 h2 =>
      hb n (by rw [min_eq_right hqp]; exact h1) (by rw [max_eq_left hqp]; omega)
    rw [Nat.add_sub_cancel' hqp] at h
    have hN : ((p - q : ℕ) : ℝ) = |(p : ℝ) - q| := by
      have : (q : ℝ) ≤ p := by exact_mod_cast hqp
      rw [Nat.cast_sub hqp, abs_of_nonneg (by linarith)]
    rwa [hN] at h

end BlockBand.SourceProcess.LengthCont
