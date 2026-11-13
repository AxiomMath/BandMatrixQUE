module

public import BlockBand.Internal.Contracts.Layers

/-!
# Calculus of resolvent words

* `tcv_wordEval_succ`: the recursion `w(G) = D₀ G^{ε₀} w'(G)`, `w'` the word of the tail.
* `tcv_norm_wordEval_le`: `‖w(G)‖ ≤ K^{ℓ+1} ‖G‖^ℓ` when every `‖D_j‖ ≤ K` (operator norm).
* `tcv_continuous_wordEval`, `tcv_contDiff_word`: continuity in `G`, and `C¹` along a `C¹`
  family `x ↦ G(x)`.
* `tcv_word_hasFDerivAt` (**product rule**): if `dG(v) = -G (Λ v) G` with every `Λ v` Hermitian
  (so also `d(Gᴴ)(v) = -Gᴴ (Λ v) Gᴴ`), then `d w(G)(v) = Σ_{m<ℓ} a_m (Λ v) c_m` with
  `‖a_m‖ ‖c_m‖ ≤ K^{ℓ+1} ‖G‖^{ℓ+1}`; `tcv_clm_norm_le` bounds such a derivative by
  `ℓ B ‖Λ‖`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A resolvent letter: `G` or `Gᴴ`. -/
def tcvLetter (e : Bool) (G : Matrix n n ℂ) : Matrix n n ℂ := if e then Gᴴ else G

theorem tcv_norm_letter (e : Bool) (G : Matrix n n ℂ) : ‖tcvLetter e G‖ = ‖G‖ := by
  cases e
  · rfl
  · exact Matrix.l2_opNorm_conjTranspose G

omit [Fintype n] [DecidableEq n] in
theorem tcv_continuous_letter (e : Bool) : Continuous (tcvLetter (n := n) e) := by
  cases e
  · exact continuous_id
  · exact continuous_id.matrix_conjTranspose

/-- The empty word is its deterministic letter. -/
theorem tcv_wordEval_zero (ε : Fin 0 → Bool) (D : Fin 1 → Matrix n n ℂ) (G : Matrix n n ℂ) :
    wordEval ε D G = D 0 := by
  simp [wordEval]

/-- **Recursion** `w(G) = D₀ G^{ε₀} w'(G)` with `w'` the word of the tail. -/
theorem tcv_wordEval_succ {ℓ : ℕ} (ε : Fin (ℓ + 1) → Bool) (D : Fin (ℓ + 2) → Matrix n n ℂ)
    (G : Matrix n n ℂ) :
    wordEval ε D G = D 0 * tcvLetter (ε 0) G *
      wordEval (fun j => ε j.succ) (fun j => D j.succ) G := by
  simp only [wordEval, List.ofFn_succ, List.prod_cons, tcvLetter]
  simp only [Fin.succ_zero_eq_one, Matrix.mul_assoc]

/-- `‖w(G)‖ ≤ K^{ℓ+1} ‖G‖^ℓ` when every deterministic letter has norm `≤ K`. -/
theorem tcv_norm_wordEval_le {K : ℝ} (hK : 0 ≤ K) :
    ∀ {ℓ : ℕ} (ε : Fin ℓ → Bool) (D : Fin (ℓ + 1) → Matrix n n ℂ) (G : Matrix n n ℂ),
      (∀ j, ‖D j‖ ≤ K) → ‖wordEval ε D G‖ ≤ K ^ (ℓ + 1) * ‖G‖ ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro ε D G hD
    rw [tcv_wordEval_zero]
    simpa using hD 0
  | succ ℓ ih =>
    intro ε D G hD
    rw [tcv_wordEval_succ]
    have h1 := ih (fun j => ε j.succ) (fun j => D j.succ) G (fun j => hD _)
    have h0 := hD 0
    have hG := norm_nonneg G
    calc ‖D 0 * tcvLetter (ε 0) G * wordEval (fun j => ε j.succ) (fun j => D j.succ) G‖
        ≤ ‖D 0‖ * ‖tcvLetter (ε 0) G‖ *
            ‖wordEval (fun j => ε j.succ) (fun j => D j.succ) G‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ K * ‖G‖ * (K ^ (ℓ + 1) * ‖G‖ ^ ℓ) := by
          rw [tcv_norm_letter]
          gcongr
      _ = K ^ (ℓ + 1 + 1) * ‖G‖ ^ (ℓ + 1) := by ring

/-- Words are continuous in the resolvent. -/
theorem tcv_continuous_wordEval :
    ∀ {ℓ : ℕ} (ε : Fin ℓ → Bool) (D : Fin (ℓ + 1) → Matrix n n ℂ),
      Continuous (fun G : Matrix n n ℂ => wordEval ε D G) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro ε D
    simp only [tcv_wordEval_zero]
    exact continuous_const
  | succ ℓ ih =>
    intro ε D
    simp only [tcv_wordEval_succ]
    exact (continuous_const.mul (tcv_continuous_letter _)).mul (ih _ _)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The conjugate transpose as an `ℝ`-linear map. -/
def tcvConjLin : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun A := Aᴴ
  map_add' A B := conjTranspose_add A B
  map_smul' r A := by
    rw [conjTranspose_smul]
    simp

/-- The conjugate transpose as an `ℝ`-continuous linear map. -/
def tcvConjCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap (tcvConjLin (n := n))

omit [DecidableEq n] in
theorem tcvConjCLM_apply (A : Matrix n n ℂ) : tcvConjCLM A = Aᴴ := rfl

/-- `C¹` families of letters. -/
theorem tcv_contDiff_letter {G : V → Matrix n n ℂ} (hG : ContDiff ℝ 1 G) (e : Bool) :
    ContDiff ℝ 1 (fun x => tcvLetter e (G x)) := by
  cases e
  · exact hG
  · exact (tcvConjCLM (n := n)).contDiff.comp hG

/-- Words in a `C¹` family are `C¹`. -/
theorem tcv_contDiff_word {G : V → Matrix n n ℂ} (hG : ContDiff ℝ 1 G) :
    ∀ {ℓ : ℕ} (ε : Fin ℓ → Bool) (D : Fin (ℓ + 1) → Matrix n n ℂ),
      ContDiff ℝ 1 (fun x => wordEval ε D (G x)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro ε D
    simp only [tcv_wordEval_zero]
    exact contDiff_const
  | succ ℓ ih =>
    intro ε D
    simp only [tcv_wordEval_succ]
    exact (contDiff_const.mul (tcv_contDiff_letter hG _)).mul (ih _ _)

/-- Derivative of a letter: `d(G^e)(v) = -G^e (Λ v) G^e` when `dG(v) = -G (Λ v) G` and `Λ v`
is Hermitian. -/
theorem tcv_letter_hasFDerivAt {G : V → Matrix n n ℂ} {Λ : V →L[ℝ] Matrix n n ℂ}
    (hΛ : ∀ v, (Λ v)ᴴ = Λ v) {x : V} {T : V →L[ℝ] Matrix n n ℂ} (hT : HasFDerivAt G T x)
    (hTv : ∀ v, T v = -(G x * Λ v * G x)) (e : Bool) :
    ∃ T' : V →L[ℝ] Matrix n n ℂ, HasFDerivAt (fun y => tcvLetter e (G y)) T' x ∧
      ∀ v, T' v = -(tcvLetter e (G x) * Λ v * tcvLetter e (G x)) := by
  cases e
  · exact ⟨T, hT, hTv⟩
  · refine ⟨tcvConjCLM.comp T, (tcvConjCLM (n := n)).hasFDerivAt.comp x hT, fun v => ?_⟩
    rw [ContinuousLinearMap.comp_apply, tcvConjCLM_apply, hTv, conjTranspose_neg,
      conjTranspose_mul, conjTranspose_mul, hΛ]
    simp only [tcvLetter, ite_true, Matrix.mul_assoc]

/-- **Product rule for words.** If `dG(v) = -G (Λ v) G` at every point and every `Λ v` is
Hermitian, then at every `x`, `d w(G)(v) = Σ_{m<ℓ} a_m (Λ v) c_m` with
`‖a_m‖ ‖c_m‖ ≤ K^{ℓ+1} ‖G x‖^{ℓ+1}`. -/
theorem tcv_word_hasFDerivAt {G : V → Matrix n n ℂ} {Λ : V →L[ℝ] Matrix n n ℂ}
    (hΛ : ∀ v, (Λ v)ᴴ = Λ v)
    (hG : ∀ x, ∃ T : V →L[ℝ] Matrix n n ℂ, HasFDerivAt G T x ∧ ∀ v, T v = -(G x * Λ v * G x))
    {K : ℝ} (hK : 0 ≤ K) (x : V) :
    ∀ {ℓ : ℕ} (ε : Fin ℓ → Bool) (D : Fin (ℓ + 1) → Matrix n n ℂ), (∀ j, ‖D j‖ ≤ K) →
      ∃ T : V →L[ℝ] Matrix n n ℂ, HasFDerivAt (fun y => wordEval ε D (G y)) T x ∧
        ∃ a c : Fin ℓ → Matrix n n ℂ, (∀ v, T v = ∑ m, a m * Λ v * c m) ∧
          ∀ m, ‖a m‖ * ‖c m‖ ≤ K ^ (ℓ + 1) * ‖G x‖ ^ (ℓ + 1) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro ε D _
    refine ⟨0, ?_, Fin.elim0, Fin.elim0, fun v => by simp, fun m => Fin.elim0 m⟩
    simp only [tcv_wordEval_zero]
    exact hasFDerivAt_const _ _
  | succ ℓ ih =>
    intro ε D hD
    obtain ⟨T₀, hT₀, hT₀v⟩ := hG x
    obtain ⟨TL, hTL, hTLv⟩ := tcv_letter_hasFDerivAt hΛ hT₀ hT₀v (ε 0)
    obtain ⟨TR, hTR, a', c', hTRv, hac'⟩ :=
      ih (fun j => ε j.succ) (fun j => D j.succ) (fun j => hD _)
    set L := tcvLetter (ε 0) (G x) with hLdef
    set R := wordEval (fun j => ε j.succ) (fun j => D j.succ) (G x) with hRdef
    have h1 : HasFDerivAt (fun y => D 0 * tcvLetter (ε 0) (G y)) (D 0 • TL) x :=
      hTL.const_mul (D 0)
    have h2 := h1.mul' hTR
    have hfun : (fun y => wordEval ε D (G y)) =
        (fun y => D 0 * tcvLetter (ε 0) (G y)) *
          (fun y => wordEval (fun j => ε j.succ) (fun j => D j.succ) (G y)) := by
      funext y
      rw [tcv_wordEval_succ]
      rfl
    rw [hfun]
    refine ⟨_, h2, Fin.cons (-(D 0 * L)) (fun m => D 0 * L * a' m),
      Fin.cons (L * R) c', fun v => ?_, fun m => ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, _root_.add_apply,
        _root_.smul_apply, hTRv, hTLv, ← hLdef, ← hRdef]
      rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, smul_eq_mul,
        Finset.mul_sum]
      simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      abel
    · have hR := tcv_norm_wordEval_le hK (fun j => ε j.succ) (fun j => D j.succ) (G x)
        (fun j => hD _)
      have hL : ‖L‖ = ‖G x‖ := tcv_norm_letter _ _
      have hG0 := norm_nonneg (G x)
      have hD0 := hD 0
      refine Fin.cases ?_ (fun m => ?_) m
      · simp only [Fin.cons_zero, norm_neg]
        calc ‖D 0 * L‖ * ‖L * R‖ ≤ (‖D 0‖ * ‖L‖) * (‖L‖ * ‖R‖) := by
              gcongr
              · exact norm_mul_le _ _
              · exact norm_mul_le _ _
          _ ≤ (K * ‖G x‖) * (‖G x‖ * (K ^ (ℓ + 1) * ‖G x‖ ^ ℓ)) := by
              rw [hL]
              gcongr
          _ = K ^ (ℓ + 1 + 1) * ‖G x‖ ^ (ℓ + 1 + 1) := by ring
      · simp only [Fin.cons_succ]
        have := hac' m
        calc ‖D 0 * L * a' m‖ * ‖c' m‖ ≤ (‖D 0‖ * ‖L‖) * (‖a' m‖ * ‖c' m‖) := by
              rw [← mul_assoc]
              gcongr
              refine (norm_mul_le _ _).trans ?_
              gcongr
              exact norm_mul_le _ _
          _ ≤ (K * ‖G x‖) * (K ^ (ℓ + 1) * ‖G x‖ ^ (ℓ + 1)) := by
              rw [hL]
              gcongr
          _ = K ^ (ℓ + 1 + 1) * ‖G x‖ ^ (ℓ + 1 + 1) := by ring

/-- A derivative of the form `v ↦ Σ_{m<ℓ} a_m (Λ v) c_m` with `‖a_m‖ ‖c_m‖ ≤ B` has norm
`≤ ℓ B ‖Λ‖`. -/
theorem tcv_clm_norm_le {ℓ : ℕ} {Λ T : V →L[ℝ] Matrix n n ℂ} {a c : Fin ℓ → Matrix n n ℂ}
    (hT : ∀ v, T v = ∑ m, a m * Λ v * c m) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m, ‖a m‖ * ‖c m‖ ≤ B) : ‖T‖ ≤ ℓ * B * ‖Λ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [hT]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m, ‖a m * Λ v * c m‖ ≤ ∑ _m : Fin ℓ, B * (‖Λ‖ * ‖v‖) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have h1 : ‖a m * Λ v * c m‖ ≤ ‖a m‖ * ‖Λ v‖ * ‖c m‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
        have h2 := Λ.le_opNorm v
        calc ‖a m * Λ v * c m‖ ≤ ‖a m‖ * ‖Λ v‖ * ‖c m‖ := h1
          _ = (‖a m‖ * ‖c m‖) * ‖Λ v‖ := by ring
          _ ≤ B * (‖Λ‖ * ‖v‖) := by gcongr; exact hB m
    _ = ℓ * B * ‖Λ‖ * ‖v‖ := by simp; ring

end BlockBand.Layers
