module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankBarrierUniform
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Gram generator in Gram coordinates and the rank barrier at every feasible state

`gramGenerator D0 𝖣 f G` is the generator of the Gram martingale problem written only with the
Gram coefficients, the drift `gramDriftEntry` `(0, -(D₀/2) g B)` and the covariance
`gramCovEntry`: no ambient dimension, rank `Naux` or projection appears.

* `sdeGenerator_comp_gramPair_eq` — the chain rule "sdeGenerator (f ∘ gramPair) = Gram generator
  of f" at every constrained frame (needed for the uniqueness of the Gram martingale problem);
* `gramGenerator_rankBarrier` — the Gram rank barrier at **every feasible Gram state**
  (`GramFeasible`: "these are identities/inequalities of the drift and
  covariance, so they hold for every solution … every feasible Gram state has a finite factor
  realization"), with a constant depending only on `D₀, 𝖣, k, K`;
* `principalMinorSum_nonneg_of_feasible` — `e_k(B) ≥ 0`, `e_k(M − B) ≥ 0` at feasible states.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

section Generic
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} [Fintype X]

/-- Generator value from a drift `d` and complex brackets `Γ` (bilinear) and `Γ'` (sesquilinear)
in the coordinates `coord` with real frame `u, v`. -/
def genCoord (f : F → ℝ) (G d : F) (u v : X → F) (Γ Γ' : X → X → ℂ) : ℝ :=
  fderiv ℝ f G d + (1 / 2 : ℝ) * ∑ e, ∑ e', bracketForm
    (fderiv ℝ (fderiv ℝ f) G (u e) (u e')) (fderiv ℝ (fderiv ℝ f) G (u e) (v e'))
    (fderiv ℝ (fderiv ℝ f) G (v e) (u e')) (fderiv ℝ (fderiv ℝ f) G (v e) (v e'))
    (Γ e e') (Γ' e e')

theorem genSplit_eq_genCoord (f : F → ℝ) (G d : F) (coord : X → F → ℂ) (u v : X → F)
    (hdec : ∀ x, x = ∑ e, ((coord e x).re • u e + (coord e x).im • v e))
    {κ : Type*} [Fintype κ] (ν : κ → F) (Γ Γ' : X → X → ℂ)
    (h1 : ∀ e e', ∑ a, coord e (ν a) * coord e' (ν a) = Γ e e')
    (h2 : ∀ e e', ∑ a, coord e (ν a) * star (coord e' (ν a)) = Γ' e e') :
    genSplit f G d ν = genCoord f G d u v Γ Γ' := by
  unfold genSplit genCoord
  congr 2
  have key := fun a => bilin_self_eq
    (ContinuousLinearMap.toLinearMap₁₂ (fderiv ℝ (fderiv ℝ f) G)) coord u v hdec (ν a)
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    real_quad_eq_bracketForm] at key
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => ?_
  rw [sum_bracketForm, h1, h2]

end Generic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Transposed Gram coordinate `(r, i, j) ↦ (r, j, i)`. -/
def gramSwap (e : Fin 2 × c × c) : Fin 2 × c × c := (e.1, e.2.2, e.2.1)

/-- **The Gram generator** (Gram drift and covariance; no ambient data). -/
def gramGenerator (D0 : ℝ) (D : Matrix c c ℂ) (f : Matrix c c ℂ × Matrix c c ℂ → ℝ)
    (G : Matrix c c ℂ × Matrix c c ℂ) : ℝ :=
  genCoord f G (gramDriftG D0 D G) gramUnit (fun e => Complex.I • gramUnit e)
    (fun e e' => gramCovEntry D0 D e e' G) (fun e e' => gramCovEntry D0 D e (gramSwap e') G)

/-- **Chain rule**: the source generator of `f ∘ gramPair` is the Gram generator of `f`. -/
theorem sdeGenerator_comp_gramPair_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {D0 : ℝ}
    (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ}
    (hP : IsNearProjection P Naux) (hD : IsSignature D) (hV : TwoProjection P D V)
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (fun W => f (gramPair P W)) V =
      gramGenerator D0 D f (gramPair P V) := by
  rw [sdeGenerator_comp_gramPair hf]
  have hdr : gramDrift D0 Naux P D V = gramDriftG D0 D (gramPair P V) := by
    rw [gramDrift_eq hD0 hP hV]; rfl
  rw [hdr]
  refine genSplit_eq_genCoord f _ _ gramEntry gramUnit _ gram_decomp _ _ _
    (fun e e' => gramNoise_cov_entry hD0 hP hD hV e e') (fun e e' => ?_)
  simp only [fun a => star_gramEntry_of_herm (gramNoise_herm D0 hP.1 D a V).1
    (gramNoise_herm D0 hP.1 D a V).2 e']
  exact gramNoise_cov_entry hD0 hP hD hV e _

omit [DecidableEq c] in
/-- A feasible state has a realization with a natural rank. -/
theorem exists_realization_of_feasible {D : Matrix c c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}
    (hG : GramFeasible D G) :
    ∃ (n N : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) c ℂ),
      IsNearProjection P N ∧ TwoProjection P D V ∧ gramPair P V = G := by
  obtain ⟨n, P, V, hPH, hPP, hV, hGe⟩ := hG
  obtain ⟨N, -, hN⟩ := exists_nat_trace_of_idem P hPP
  exact ⟨n, N, P, V, ⟨hPH, hPP, hN⟩, hV, hGe⟩

omit [DecidableEq c] in
theorem re_trace_fst_gramPair {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) :
    ((gramPair P V).1.trace).re = ‖V‖ ^ 2 := by
  show (sourceGram V).trace.re = _
  rw [sourceGram_trace, Complex.ofReal_re]

/-- `e_k(B) ≥ 0` and `e_k(M − B) ≥ 0` at every feasible state. -/
theorem principalMinorSum_nonneg_of_feasible {D : Matrix c c ℂ}
    {G : Matrix c c ℂ × Matrix c c ℂ} (hG : GramFeasible D G) (k : ℕ) :
    0 ≤ principalMinorSum k G.2 ∧ 0 ≤ principalMinorSum k (G.1 - G.2) := by
  obtain ⟨n, N, P, V, hP, -, rfl⟩ := exists_realization_of_feasible hG
  exact ⟨principalMinorSum_near_nonneg hP.1 hP.2.1 k V,
    principalMinorSum_far_nonneg hP.1 hP.2.1 k V⟩

/-- **The Gram rank barrier at every feasible Gram state**, uniform constant. -/
theorem gramGenerator_rankBarrier {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ}
    (hD : IsSignature D) (k : ℕ) (K : ℝ) :
    ∃ C : ℝ, ∀ G : Matrix c c ℂ × Matrix c c ℂ, GramFeasible D G → (G.1.trace).re ≤ K →
      gramGenerator D0 D (fun H => principalMinorSum k H.2) G ≤ C * principalMinorSum k G.2 ∧
      gramGenerator D0 D (fun H => principalMinorSum k (H.1 - H.2)) G ≤
        C * principalMinorSum k (G.1 - G.2) := by
  obtain ⟨C, hC⟩ := gramRankBarrierUniform_holds D0 D hD0 hD k K
  refine ⟨C, fun G hG hK => ?_⟩
  obtain ⟨n, N, P, V, hP, hV, rfl⟩ := exists_realization_of_feasible hG
  rw [re_trace_fst_gramPair] at hK
  obtain ⟨h1, h2⟩ := hC n N P V hP hV hK
  rw [← sdeGenerator_comp_gramPair_eq hD0.le hP hD hV (contDiff_ek_snd k),
    ← sdeGenerator_comp_gramPair_eq hD0.le hP hD hV (contDiff_ek_fst_sub_snd k)]
  exact ⟨h1, h2⟩

end BlockBand.SourceProcess.Stochastic.GramUniqueness
