module

public import BlockBand.SourceProcess.ComplexCutoff.FrameBounds

/-!
# Rank-free bounds for the complex source data of a frame

Frobenius norms on all matrices. For frames `V, V₁, V₂`, a near projection `P` and the
source signature `𝖣`, the source data `(𝒦, M_pr, B_pr, (M𝖣M)_pr)` of `modelSourceData` satisfy
(by Schatten Cauchy–Schwarz, and the same bound for the current difference):

* `norm_data_le`: if every entry of `𝒦` is at most `κ`, every entry is at most
  `κ + ‖V‖² + ‖V‖⁴`;
* `norm_data_sub_le`: if every entry of `𝒦₁ - 𝒦₂` is at most `κ`, every entry difference is at
  most `κ + ‖V₁ - V₂‖(‖V₁‖ + ‖V₂‖)(1 + ‖V₁‖² + ‖V₂‖²)`.
The bounds do not depend on `ι`, on the cap `K` or on the cutoff.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.CutoffLimit BlockBand.Internal.Contracts.TransmissionLaws

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section General

variable {r c ι : Type*} [Fintype r] [Fintype c] [Fintype ι]

/-- An entry is at most the Frobenius norm. -/
theorem norm_entry_le (A : Matrix r c ℂ) (i : r) (j : c) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [← hsSq_eq, hsSq]
    have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

omit [Fintype r] in
/-- Scaling the columns by numbers of modulus at most one does not increase the norm. -/
theorem norm_mul_diagonal_le [Fintype r] [DecidableEq c] {d : c → ℂ} (hd : ∀ k, ‖d k‖ ≤ 1)
    (A : Matrix r c ℂ) : ‖A * diagonal d‖ ≤ ‖A‖ := by
  have h : ‖A * diagonal d‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [← hsSq_eq, ← hsSq_eq, hsSq, hsSq]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [mul_diagonal, norm_mul, mul_pow]
    have h0 : ‖d j‖ ^ 2 ≤ 1 := by
      have := hd j
      have := norm_nonneg (d j)
      nlinarith
    nlinarith [sq_nonneg ‖A i j‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `‖W₁ᴴW₁ - W₂ᴴW₂‖ ≤ ‖W₁ - W₂‖(‖W₁‖ + ‖W₂‖)`. -/
theorem norm_gram_sub_le (W₁ W₂ : Matrix ι c ℂ) :
    ‖W₁ᴴ * W₁ - W₂ᴴ * W₂‖ ≤ ‖W₁ - W₂‖ * (‖W₁‖ + ‖W₂‖) := by
  have e : W₁ᴴ * W₁ - W₂ᴴ * W₂ = W₁ᴴ * (W₁ - W₂) + (W₁ - W₂)ᴴ * W₂ := by
    rw [Matrix.mul_sub, conjTranspose_sub, Matrix.sub_mul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h1 := frobenius_norm_mul W₁ᴴ (W₁ - W₂)
  have h2 := frobenius_norm_mul (W₁ - W₂)ᴴ W₂
  rw [frobenius_norm_conjTranspose] at h1 h2
  nlinarith

theorem norm_gram_le (W : Matrix ι c ℂ) : ‖Wᴴ * W‖ ≤ ‖W‖ ^ 2 := by
  have h := frobenius_norm_mul Wᴴ W
  rw [frobenius_norm_conjTranspose] at h
  nlinarith

variable [DecidableEq ι] {P : Matrix ι ι ℂ} {Naux : ℕ}

/-- `‖PV‖ ≤ ‖V‖` for a Hermitian idempotent `P`. -/
theorem norm_proj_mul_le' (hPH : Pᴴ = P) (hPP : P * P = P) (V : Matrix ι c ℂ) :
    ‖P * V‖ ≤ ‖V‖ := by
  have e1 : (P * V)ᴴ * (P * V) = Vᴴ * P * V := by
    rw [conjTranspose_mul, hPH, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ P P, hPP]
  have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPH, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, hPP, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  have e2 : ((1 - P) * V)ᴴ * ((1 - P) * V) = Vᴴ * V - Vᴴ * P * V := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ, hQ, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one]
  have hsum : hsSq V = hsSq (P * V) + hsSq ((1 - P) * V) := by
    rw [hsSq_eq_re_trace, hsSq_eq_re_trace, hsSq_eq_re_trace, e1, e2, trace_sub, Complex.sub_re]
    ring
  have h : ‖P * V‖ ^ 2 ≤ ‖V‖ ^ 2 := by
    rw [← hsSq_eq, ← hsSq_eq, hsum]
    linarith [hsSq_nonneg ((1 - P) * V)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `‖PV‖ ≤ ‖V‖` for an orthogonal projection `P`. -/
theorem norm_proj_mul_le (hP : IsNearProjection P Naux) (V : Matrix ι c ℂ) : ‖P * V‖ ≤ ‖V‖ :=
  norm_proj_mul_le' hP.1 hP.2.1 V

omit [Fintype c] [DecidableEq ι] in
theorem nearGram_eq (hP : IsNearProjection P Naux) (V : Matrix ι c ℂ) :
    nearGram P V = (P * V)ᴴ * (P * V) := by
  obtain ⟨hPH, hPP, -⟩ := hP
  rw [nearGram, conjTranspose_mul, hPH, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ P P, hPP]

end General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} {Naux : ℕ} {K np : ℕ}

theorem norm_signature_sandwich_le (A B : Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) :
    ‖A * srcSignature K (Fin np) * B‖ ≤ ‖A‖ * ‖B‖ := by
  have h : ‖A * srcSignature K (Fin np)‖ ≤ ‖A‖ := by
    unfold srcSignature
    refine norm_mul_diagonal_le (fun k => ?_) A
    rcases k with ⟨_, σ⟩ | _
    · by_cases hσ : σ = 0 <;> simp [hσ]
    · simp
  exact (frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem norm_probeBlock_le (A : Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ) (i j : Fin np) :
    ‖probeBlock A i j‖ ≤ ‖A‖ :=
  norm_entry_le A _ _

/-- **Entry bound of the source data.** -/
theorem norm_data_le (hP : IsNearProjection P Naux) {Kc : Matrix (Fin np) (Fin np) ℂ} {κ : ℝ}
    (hK : ∀ i j, ‖Kc i j‖ ≤ κ) (V : Matrix ι (SrcCol K (Fin np)) ℂ) (r : Fin 4) (i j : Fin np) :
    ‖modelSourceData (srcSignature K (Fin np)) Kc (gramPair P V) r i j‖ ≤
      κ + ‖V‖ ^ 2 + ‖V‖ ^ 4 := by
  have hK0 : 0 ≤ κ := (norm_nonneg _).trans (hK i j)
  have hV2 : 0 ≤ ‖V‖ ^ 2 := by positivity
  have hV4 : 0 ≤ ‖V‖ ^ 4 := by positivity
  have hM := norm_gram_le V
  have hPV := norm_proj_mul_le hP V
  fin_cases r
  · have := hK i j
    show ‖Kc i j‖ ≤ _
    linarith
  · have := norm_probeBlock_le (sourceGram V) i j
    show ‖probeBlock (sourceGram V) i j‖ ≤ _
    rw [sourceGram] at this ⊢
    linarith
  · have := norm_probeBlock_le (nearGram P V) i j
    have h2 := norm_gram_le (P * V)
    have h3 : ‖P * V‖ ^ 2 ≤ ‖V‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPV 2
    show ‖probeBlock (nearGram P V) i j‖ ≤ _
    rw [nearGram_eq hP] at this ⊢
    linarith
  · have := norm_probeBlock_le (sourceGram V * srcSignature K (Fin np) * sourceGram V) i j
    have h2 := norm_signature_sandwich_le (sourceGram V) (sourceGram V)
    have h3 : ‖sourceGram V‖ * ‖sourceGram V‖ ≤ ‖V‖ ^ 4 := by
      have := norm_nonneg (sourceGram V)
      have h4 : ‖sourceGram V‖ ≤ ‖V‖ ^ 2 := norm_gram_le V
      nlinarith
    show ‖probeBlock (sourceGram V * srcSignature K (Fin np) * sourceGram V) i j‖ ≤ _
    linarith

/-- **Entry bound of the difference of two source data.** -/
theorem norm_data_sub_le (hP : IsNearProjection P Naux) {Kc₁ Kc₂ : Matrix (Fin np) (Fin np) ℂ}
    {κ : ℝ} (hK12 : ∀ i j, ‖Kc₁ i j - Kc₂ i j‖ ≤ κ) (V₁ V₂ : Matrix ι (SrcCol K (Fin np)) ℂ)
    (r : Fin 4) (i j : Fin np) :
    ‖modelSourceData (srcSignature K (Fin np)) Kc₁ (gramPair P V₁) r i j -
        modelSourceData (srcSignature K (Fin np)) Kc₂ (gramPair P V₂) r i j‖ ≤
      κ + ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) := by
  have hK : 0 ≤ κ := (norm_nonneg _).trans (hK12 i j)
  have he := norm_nonneg (V₁ - V₂)
  have h1 := norm_nonneg V₁
  have h2 := norm_nonneg V₂
  have hM := norm_gram_sub_le V₁ V₂
  have hbase : ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) ≤
      ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) := by
    have : 0 ≤ ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) := by positivity
    nlinarith [sq_nonneg ‖V₁‖, sq_nonneg ‖V₂‖]
  fin_cases r
  · have := hK12 i j
    show ‖Kc₁ i j - Kc₂ i j‖ ≤ _
    have : 0 ≤ ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) := by positivity
    linarith
  · have := norm_probeBlock_le (sourceGram V₁ - sourceGram V₂) i j
    show ‖probeBlock (sourceGram V₁) i j - probeBlock (sourceGram V₂) i j‖ ≤ _
    simp only [probeBlock, Matrix.sub_apply, sourceGram] at this ⊢
    linarith
  · have := norm_probeBlock_le (nearGram P V₁ - nearGram P V₂) i j
    rw [nearGram_eq hP, nearGram_eq hP] at this
    have hP' := norm_gram_sub_le (P * V₁) (P * V₂)
    rw [← Matrix.mul_sub] at hP'
    have q0 := norm_proj_mul_le hP (V₁ - V₂)
    have q1 := norm_proj_mul_le hP V₁
    have q2 := norm_proj_mul_le hP V₂
    have q3 : ‖P * (V₁ - V₂)‖ * (‖P * V₁‖ + ‖P * V₂‖) ≤ ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) :=
      mul_le_mul q0 (add_le_add q1 q2) (by positivity) he
    show ‖probeBlock (nearGram P V₁) i j - probeBlock (nearGram P V₂) i j‖ ≤ _
    rw [nearGram_eq hP, nearGram_eq hP]
    simp only [probeBlock, Matrix.sub_apply] at this ⊢
    linarith
  · have e : sourceGram V₁ * srcSignature K (Fin np) * sourceGram V₁ -
        sourceGram V₂ * srcSignature K (Fin np) * sourceGram V₂ =
        (sourceGram V₁ - sourceGram V₂) * srcSignature K (Fin np) * sourceGram V₁ +
          sourceGram V₂ * srcSignature K (Fin np) * (sourceGram V₁ - sourceGram V₂) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    have a1 := norm_signature_sandwich_le (sourceGram V₁ - sourceGram V₂) (sourceGram V₁)
    have a2 := norm_signature_sandwich_le (sourceGram V₂) (sourceGram V₁ - sourceGram V₂)
    have a3 := norm_add_le
      ((sourceGram V₁ - sourceGram V₂) * srcSignature K (Fin np) * sourceGram V₁)
      (sourceGram V₂ * srcSignature K (Fin np) * (sourceGram V₁ - sourceGram V₂))
    have n1 : ‖sourceGram V₁‖ ≤ ‖V₁‖ ^ 2 := norm_gram_le V₁
    have n2 : ‖sourceGram V₂‖ ≤ ‖V₂‖ ^ 2 := norm_gram_le V₂
    have hd : ‖sourceGram V₁ - sourceGram V₂‖ ≤ ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) := hM
    have hMn := norm_nonneg (sourceGram V₁ - sourceGram V₂)
    have key : ‖sourceGram V₁ - sourceGram V₂‖ * (‖sourceGram V₁‖ + ‖sourceGram V₂‖) ≤
        ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) :=
      mul_le_mul hd (add_le_add n1 n2) (by positivity) (by positivity)
    have hfin : ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) ≤
        ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) := by
      have : 0 ≤ ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
    have hn : ‖sourceGram V₁ * srcSignature K (Fin np) * sourceGram V₁ -
        sourceGram V₂ * srcSignature K (Fin np) * sourceGram V₂‖ ≤
        ‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖) * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) := by
      rw [e]
      have hr : ‖sourceGram V₁ - sourceGram V₂‖ * ‖sourceGram V₁‖ +
          ‖sourceGram V₂‖ * ‖sourceGram V₁ - sourceGram V₂‖ =
          ‖sourceGram V₁ - sourceGram V₂‖ * (‖sourceGram V₁‖ + ‖sourceGram V₂‖) := by ring
      linarith [a3, a1, a2, key, hfin]
    have := norm_entry_le (sourceGram V₁ * srcSignature K (Fin np) * sourceGram V₁ -
        sourceGram V₂ * srcSignature K (Fin np) * sourceGram V₂) (Sum.inr i) (Sum.inr j)
    rw [Matrix.sub_apply] at this
    exact this.trans (hn.trans (le_add_of_nonneg_left hK))

end BlockBand.SourceProcess.ComplexCutoff
