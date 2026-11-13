module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartSigma
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Fixed-rank feasible states with bounded trace and `e_r` bounded below are good

**`chartGood_of_stratum`**: if `G` is feasible, `Re Tr M ≤ T` (`T ≥ 1`), `e_{r+1}(B) = 0`,
`e_r(B) ≥ η`, `e_{r'+1}(M - B) = 0`, `e_{r'}(M - B) ≥ η` (`η > 0`), and
`δ ≤ η / (2^|c| T^r)`, `δ ≤ η / (2^|c| T^{r'})`, then `ChartGood D δ G`: every nonzero
eigenvalue of `B` and of `M - B` is at least `δ` (`principalMinorSum_eq_esymm`, `esymm_gap`;
`B, M - B ⪰ 0` and their eigenvalues are at most `Re Tr M` by feasibility).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.RankBarrierProof
open scoped ComplexOrder

variable {c : Type*} [Fintype c] [DecidableEq c]

omit [DecidableEq c] in
theorem psd_of_feasible {D : Matrix c c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}
    (hG : GramFeasible D G) : G.2.PosSemidef ∧ (G.1 - G.2).PosSemidef := by
  obtain ⟨n, P, V, hPH, hPP, -, rfl⟩ := hG
  refine ⟨?_, ?_⟩
  · show (nearGram P V).PosSemidef
    rw [nearGram_eq P hPH hPP V]; exact posSemidef_conjTranspose_mul_self _
  · show (sourceGram V - nearGram P V).PosSemidef
    rw [farGram_eq P hPH hPP V]; exact posSemidef_conjTranspose_mul_self _

theorem re_trace_eq_sum_eL {A : Matrix c c ℂ} (hA : Aᴴ = A) : (A.trace).re = ∑ i, eL A i := by
  have h := (isHermitian_hermPart A).trace_eq_sum_eigenvalues
  have h2 : A.trace = (hermPart A).trace := by rw [hermPart_of_herm hA]
  rw [h2, h, Complex.re_sum]
  simp [eL]

theorem eL_le_trace {A : Matrix c c ℂ} (hA : A.PosSemidef) (i : c) : eL A i ≤ (A.trace).re := by
  have hP : (hermPart A).PosSemidef := by rw [hermPart_of_herm hA.1]; exact hA
  rw [re_trace_eq_sum_eL hA.1]
  exact Finset.single_le_sum (f := eL A) (fun j _ => hP.eigenvalues_nonneg j) (mem_univ i)

theorem gap_of_esymm {A : Matrix c c ℂ} (hA : A.PosSemidef) {T : ℝ} (hT1 : 1 ≤ T)
    (hT : (A.trace).re ≤ T) {r : ℕ} (hz : principalMinorSum (r + 1) A = 0) {η : ℝ}
    (hη : η ≤ principalMinorSum r A) {δ : ℝ} (hδ : δ ≤ η / (2 ^ Fintype.card c * T ^ r))
    (i : c) : eL A i = 0 ∨ δ ≤ eL A i := by
  have hP : (hermPart A).PosSemidef := by rw [hermPart_of_herm hA.1]; exact hA
  have h0 : ∀ j, 0 ≤ eL A j := fun j => hP.eigenvalues_nonneg j
  rcases (h0 i).eq_or_lt with h | h
  · exact Or.inl h.symm
  · right
    rw [principalMinorSum_eq_esymm hA] at hz hη
    have hg := esymm_gap h0 hT1 (fun j => (eL_le_trace hA j).trans hT) hz hη i h
    refine hδ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith

/-- **Stratum states with trace and `e_r` bounds are good.** -/
theorem chartGood_of_stratum {D : Matrix c c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}
    (hG : GramFeasible D G) {T : ℝ} (hT1 : 1 ≤ T) (hT : (G.1.trace).re ≤ T) {r r' : ℕ} {η : ℝ}
    (hzB : principalMinorSum (r + 1) G.2 = 0) (hηB : η ≤ principalMinorSum r G.2)
    (hzC : principalMinorSum (r' + 1) (G.1 - G.2) = 0)
    (hηC : η ≤ principalMinorSum r' (G.1 - G.2)) {δ : ℝ}
    (hδB : δ ≤ η / (2 ^ Fintype.card c * T ^ r)) (hδC : δ ≤ η / (2 ^ Fintype.card c * T ^ r')) :
    ChartGood D δ G := by
  obtain ⟨hB, hC⟩ := psd_of_feasible hG
  have htr : (G.1.trace).re = (G.2.trace).re + ((G.1 - G.2).trace).re := by
    rw [trace_sub, Complex.sub_re]; ring
  have hB0 : 0 ≤ (G.2.trace).re := by
    rw [re_trace_eq_sum_eL hB.1]
    have hP : (hermPart G.2).PosSemidef := by rw [hermPart_of_herm hB.1]; exact hB
    exact Finset.sum_nonneg fun j _ => hP.eigenvalues_nonneg j
  have hC0 : 0 ≤ ((G.1 - G.2).trace).re := by
    rw [re_trace_eq_sum_eL hC.1]
    have hP : (hermPart (G.1 - G.2)).PosSemidef := by rw [hermPart_of_herm hC.1]; exact hC
    exact Finset.sum_nonneg fun j _ => hP.eigenvalues_nonneg j
  exact ⟨hG, gap_of_esymm hB hT1 (by linarith) hzB hηB hδB,
    gap_of_esymm hC hT1 (by linarith) hzC hηC hδC⟩

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
