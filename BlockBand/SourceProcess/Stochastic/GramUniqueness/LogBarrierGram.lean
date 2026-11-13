module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.LogBarrierAmbient
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramGeneratorCoord
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The log barrier at every feasible Gram state

`gramGenerator_cutLog_le`: for `0 < D₀`, a signature `𝖣`, `k` and `K` there is `C` such that
for every `ε > 0` and every feasible `H` with `Re Tr M ≤ K`:
* if `e_k(B) ≥ ε` then `𝒢(cutH ε ∘ e_k ∘ B)(H) ≤ C`;
* if `e_k(M − B) ≥ ε` then `𝒢(cutH ε ∘ e_k ∘ (M − B))(H) ≤ C`.

`C` does not depend on `ε`. Route: a small realization (`exists_small_realization`), the ambient log
barrier `generator_cut_minorSq_le` with the near/far line structure of `RankBarrier/NearFar`
(near drift `−(D₀N/4)PV` gives `L = kD₀N/2 ≤ kD₀|c|`, far drift `L = 0`), and monotone constants.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.RankBarrierProof

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Uniform constant of the near log barrier. -/
def logNearConst (D0 : ℝ) (D : Matrix c c ℂ) (k : ℕ) (K : ℝ) : ℝ :=
  k * D0 * Fintype.card c + 1 / 2 * (((2 * Fintype.card c : ℝ) * (2 * Fintype.card c : ℝ) * 2) *
    (2 * ((2 * Fintype.card c : ℝ) ^ k * (Fintype.card c : ℝ) ^ k) *
      ((k : ℝ) * (Real.sqrt D0 / 2 * (Real.sqrt (2 * Fintype.card c) *
        (Real.sqrt (2 * Fintype.card c) + Real.sqrt K * ‖D‖ * Real.sqrt K + 1))))) ^ 2)

/-- Uniform constant of the far log barrier. -/
def logFarConst (D0 : ℝ) (D : Matrix c c ℂ) (k : ℕ) (K : ℝ) : ℝ :=
  0 + 1 / 2 * (((2 * Fintype.card c : ℝ) * (2 * Fintype.card c : ℝ) * 2) *
    (2 * ((2 * Fintype.card c : ℝ) ^ k * (Fintype.card c : ℝ) ^ k) *
      ((k : ℝ) * ((Real.sqrt (2 * Fintype.card c) * Real.sqrt K) *
        (Fintype.card c * (Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K)))))) ^ 2)

omit [DecidableEq c] in
theorem near_drift_hasDerivAt (k : ℕ) (D0 : ℝ) (N : ℕ) {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ)
    (hPP : P * P = P) (V : Matrix (Fin m) c ℂ) :
    HasDerivAt (fun t : ℝ => minorSq k (P * (V + t • sourceDrift D0 N P V)) / (k.factorial : ℝ) ^ 2)
      (k * 1 * (2 * (-(D0 * N / 4))) * (minorSq k (P * V) / (k.factorial : ℝ) ^ 2)) 0 := by
  set α : ℝ := -(D0 * N / 4)
  set C := minorSq k (P * V) / (k.factorial : ℝ) ^ 2
  have hfun : (fun t : ℝ => minorSq k (P * (V + t • sourceDrift D0 N P V)) /
      (k.factorial : ℝ) ^ 2) = fun t => ((1 + t * α) ^ 2) ^ k * C := by
    funext t
    rw [near_drift_line D0 N P hPP, minorSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hu : HasDerivAt (fun t : ℝ => (1 + t * α) ^ 2) (2 * α) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const α).const_add 1).pow 2
    exact this.congr_deriv (by simp)
  rw [hfun]
  exact ((hu.pow k).mul_const C).congr_deriv (by simp)

/-- **Log barrier at feasible states.** -/
theorem gramGenerator_cutLog_le {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    (k : ℕ) (K : ℝ) {ε : ℝ} (hε : 0 < ε) {H : Matrix c c ℂ × Matrix c c ℂ}
    (hH : GramFeasible D H) (hK : (H.1.trace).re ≤ K) :
    (ε ≤ principalMinorSum k H.2 →
      gramGenerator D0 D (fun G => cutH ε (principalMinorSum k G.2)) H ≤
        logNearConst D0 D k K) ∧
    (ε ≤ principalMinorSum k (H.1 - H.2) →
      gramGenerator D0 D (fun G => cutH ε (principalMinorSum k (G.1 - G.2))) H ≤
        logFarConst D0 D k K) := by
  obtain ⟨n, N0, P0, V0, hP0, hV0, rfl⟩ := exists_realization_of_feasible hH
  obtain ⟨m, N, P, V, hm, hNm, hP, hV, hG⟩ := exists_small_realization hP0 hV0
  rw [← hG] at hK ⊢
  rw [re_trace_fst_gramPair] at hK
  obtain ⟨hPH, hPP, -⟩ := id hP
  have hR : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsw : 0 ≤ Real.sqrt D0 / 2 := by positivity
  have hVR : ‖V‖ ≤ Real.sqrt K := by
    rw [← Real.sqrt_sq (norm_nonneg V)]; exact Real.sqrt_le_sqrt hK
  have hm' : (m : ℝ) ≤ 2 * Fintype.card c := by exact_mod_cast hm
  have hPn : ‖P‖ ≤ Real.sqrt (2 * Fintype.card c) := by
    rw [← Real.sqrt_sq (norm_nonneg P), frob_sq_nearProjection hP]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNm.trans hm)
  have hcards : (Fintype.card (SourceNoise (Fin m)) : ℝ) ≤
      (2 * Fintype.card c : ℝ) * (2 * Fintype.card c : ℝ) * 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; gcongr
  have hcardX : (Fintype.card ((Fin k → Fin m) × (Fin k → c)) : ℝ) ≤
      (2 * Fintype.card c : ℝ) ^ k * (Fintype.card c : ℝ) ^ k := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]; push_cast; gcongr
  constructor
  · intro hε'
    have e := sdeGenerator_comp_gramPair_eq (f := fun G => cutH ε (principalMinorSum k G.2))
      hD0.le hP hD hV ((contDiff_cutH hε).comp (contDiff_ek_snd (c := c) k))
    rw [← e]
    have hfun : (fun W : Matrix (Fin m) c ℂ => cutH ε (principalMinorSum k (gramPair P W).2)) =
        fun W => cutH ε (minorSq k (P * W) / (k.factorial : ℝ) ^ 2) :=
      funext fun W => by rw [show (gramPair P W).2 = nearGram P W from rfl,
        congrFun (nearMinor_fun k P hPH hPP) W]
    rw [hfun]
    have hε2 : ε ≤ minorSq k (P * V) / (k.factorial : ℝ) ^ 2 := by
      rw [← congrFun (nearMinor_fun k P hPH hPP) V]; exact hε'
    have hw : ∀ a : SourceNoise (Fin m), ∀ l,
        ‖sourceWeight D0 a.2 * (P * gramProjection P V D) l a.1.2‖ ≤
          Real.sqrt D0 / 2 * (‖P‖ * defectRadius P D (Real.sqrt K)) := by
      intro a l
      rw [norm_mul, norm_sourceWeight]
      exact mul_le_mul_of_nonneg_left ((frob_entry_le _ _ _).trans ((frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_left (gramProjection_norm_le hVR) (norm_nonneg _)))) hsw
    refine (generator_cut_minorSq_le k P (sourceDrift D0 N P) (sourceDiffusion D0 P D) V
      ((k : ℝ) * (Real.sqrt D0 / 2 * (‖P‖ * defectRadius P D (Real.sqrt K))))
      (k * D0 * N / 2) hε hε2 (near_drift_hasDerivAt k D0 N P hPP V) (le_of_eq (by ring))
      (fun a => ⟨_, fun t p => near_lin D0 P D a V t p,
        fun p => norm_rowSlope_le _ _ _ (hw a) p⟩)).trans ?_
    unfold logNearConst defectRadius
    have hN : (N : ℝ) ≤ 2 * Fintype.card c := by exact_mod_cast hNm.trans hm
    gcongr
    have hk : 0 ≤ (k : ℝ) * D0 := by positivity
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) hk
  · intro hε'
    have e := sdeGenerator_comp_gramPair_eq
      (f := fun G => cutH ε (principalMinorSum k (G.1 - G.2)))
      hD0.le hP hD hV ((contDiff_cutH hε).comp (contDiff_ek_fst_sub_snd (c := c) k))
    rw [← e]
    have hfun : (fun W : Matrix (Fin m) c ℂ =>
        cutH ε (principalMinorSum k ((gramPair P W).1 - (gramPair P W).2))) =
        fun W => cutH ε (minorSq k ((1 - P) * W) / (k.factorial : ℝ) ^ 2) :=
      funext fun W => by
        rw [show (gramPair P W).1 - (gramPair P W).2 = sourceGram W - nearGram P W from rfl,
          congrFun (farMinor_fun k P hPH hPP) W]
    rw [hfun]
    have hε2 : ε ≤ minorSq k ((1 - P) * V) / (k.factorial : ℝ) ^ 2 := by
      rw [← congrFun (farMinor_fun k P hPH hPP) V]; exact hε'
    have hz : ∀ a : SourceNoise (Fin m), ∀ m',
        ‖sourceWeight D0 a.2 * (D * Vᴴ) m' a.1.2‖ ≤ Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K) := by
      intro a m'
      rw [norm_mul, norm_sourceWeight]
      refine mul_le_mul_of_nonneg_left ((frob_entry_le _ _ _).trans ((frobenius_norm_mul _ _).trans
        ?_)) hsw
      rw [frobenius_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_left hVR (norm_nonneg _)
    have hy : ∀ a : SourceNoise (Fin m), ∀ m', ‖(P * V) a.1.1 m'‖ ≤ ‖P‖ * Real.sqrt K :=
      fun a m' => (frob_entry_le _ _ _).trans ((frobenius_norm_mul _ _).trans
        (mul_le_mul_of_nonneg_left hVR (norm_nonneg _)))
    have hdd : HasDerivAt (fun t : ℝ =>
        minorSq k ((1 - P) * (V + t • sourceDrift D0 N P V)) / (k.factorial : ℝ) ^ 2) 0 0 := by
      simp_rw [far_drift_line D0 N P hPP V]
      exact hasDerivAt_const _ _
    refine (generator_cut_minorSq_le k (1 - P) (sourceDrift D0 N P) (sourceDiffusion D0 P D) V
      ((k : ℝ) * ((‖P‖ * Real.sqrt K) *
        (Fintype.card c * (Real.sqrt D0 / 2 * (‖D‖ * Real.sqrt K))))) 0 hε hε2 hdd
      (by simp) (fun a => ⟨_, fun t p => far_lin D0 P hPP D a V t p,
        fun p => norm_colSlope_le _ _ _ (by positivity) (by positivity) (hz a) (hy a) p⟩)).trans ?_
    unfold logFarConst
    gcongr

end BlockBand.SourceProcess.Stochastic.GramUniqueness
