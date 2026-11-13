module

public import BlockBand.Transmission.PassiveLayer.TMWord
public import BlockBand.Transmission.PassiveCovariance.VitaliL2

/-!
# Calculus of passive words: closure under differentiation

For a `C¹` family `x ↦ 𝒢(x)` with `d𝒢(v) = -𝒢 (Λv) 𝒢` and every `Λv` Hermitian:
* `tm_letter_hasFDerivAt`: the derivative of every letter is `ldA (Λv) ldC`, i.e.
  `-(P𝒢) Λv (𝒢Q)` for `P𝒢Q` and `-(𝒢Q)ᴴ Λv (P𝒢)ᴴ` for its adjoint; `‖ldA‖, ‖ldC‖ ≤ Λ(K, 𝒢)`
  (`norm_ldA_le`, `norm_ldC_le`). So `K` enters only as `Kι₁𝒢`.
* `tm_word_hasFDerivAt` (**product rule**): `d w(𝒢)(v) = Σ_{m<ℓ} a_m (Λv) c_m` with
  `‖a_m‖‖c_m‖ ≤ K_d^{ℓ+1} Λ^{ℓ+1}`; `tm_clm_norm_le` bounds such a derivative by `ℓ B ‖Λ‖`.
* `tmTr`: `N ↦ W⁻¹ Tr N` as an `ℝ`-linear map, `‖W⁻¹ Tr N‖ ≤ ‖N‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `M ↦ P M Q` as an `ℝ`-continuous linear map. -/
def sandCLM (P : Matrix (Fin W) (LS W) ℂ) (Q : Matrix (LS W) (Fin W) ℂ) :
    Matrix (LS W) (LS W) ℂ →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => P * M * Q
      map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r M => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem sandCLM_apply (P : Matrix (Fin W) (LS W) ℂ) (Q : Matrix (LS W) (Fin W) ℂ)
    (M : Matrix (LS W) (LS W) ℂ) : sandCLM P Q M = P * M * Q := rfl

/-- The conjugate transpose as an `ℝ`-continuous linear map. -/
def conjCLM (W : ℕ) : Matrix (Fin W) (Fin W) ℂ →L[ℝ] Matrix (Fin W) (Fin W) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun r A => by rw [conjTranspose_smul]; simp }

theorem conjCLM_apply (A : Matrix (Fin W) (Fin W) ℂ) : conjCLM W A = Aᴴ := rfl

/-- The normalized trace `N ↦ W⁻¹ Tr N` (real-linear). -/
def tmTr (W : ℕ) : Matrix (Fin W) (Fin W) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => (W : ℂ)⁻¹ * N.trace
      map_add' := fun N N' => by simp [Matrix.trace_add, mul_add]
      map_smul' := fun r N => by simp [Matrix.trace_smul]; ring }

theorem tmTr_apply (N : Matrix (Fin W) (Fin W) ℂ) : tmTr W N = (W : ℂ)⁻¹ * N.trace := rfl

/-- `‖W⁻¹ Tr N‖ ≤ ‖N‖`. -/
theorem norm_tmTr_le (N : Matrix (Fin W) (Fin W) ℂ) : ‖tmTr W N‖ ≤ ‖N‖ := by
  rw [tmTr_apply, norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  have hW : (0 : ℝ) < W := by exact_mod_cast h
  have ht : ‖N.trace‖ ≤ W * ‖N‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖N.diag i‖ ≤ ∑ _i : Fin W, ‖N‖ :=
          Finset.sum_le_sum fun i _ => PassiveCovariance.norm_entry_le N i i
      _ = W * ‖N‖ := by simp
  calc (W : ℝ)⁻¹ * ‖N.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖N‖) := by gcongr
    _ = ‖N‖ := by field_simp

/-- Left derivative factor of a letter. -/
def ldA (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool) (G : Matrix (LS W) (LS W) ℂ) :
    Matrix (Fin W) (LS W) ℂ :=
  if l.2 then -(G * lQ W l.1)ᴴ else -(lP K l.1 * G)

/-- Right derivative factor of a letter. -/
def ldC (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool) (G : Matrix (LS W) (LS W) ℂ) :
    Matrix (LS W) (Fin W) ℂ :=
  if l.2 then (lP K l.1 * G)ᴴ else G * lQ W l.1

theorem norm_ldA_le (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool)
    (G : Matrix (LS W) (LS W) ℂ) : ‖ldA K l G‖ ≤ lam K G := by
  unfold ldA; split_ifs
  · rw [norm_neg, Matrix.l2_opNorm_conjTranspose]; exact norm_mul_lQ_le K G l.1
  · rw [norm_neg]; exact norm_lP_mul_le K G l.1

theorem norm_ldC_le (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool)
    (G : Matrix (LS W) (LS W) ℂ) : ‖ldC K l G‖ ≤ lam K G := by
  unfold ldC; split_ifs
  · rw [Matrix.l2_opNorm_conjTranspose]; exact norm_lP_mul_le K G l.1
  · exact norm_mul_lQ_le K G l.1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem tm_contDiff_letter {G : V → Matrix (LS W) (LS W) ℂ} (hG : ContDiff ℝ 1 G)
    (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool) :
    ContDiff ℝ 1 (fun x => tmLetter K l (G x)) := by
  have h : ContDiff ℝ 1 (fun x => lP K l.1 * G x * lQ W l.1) :=
    (sandCLM (lP K l.1) (lQ W l.1)).contDiff.comp hG
  unfold tmLetter
  split_ifs
  · exact (conjCLM W).contDiff.comp h
  · exact h

/-- Words in a `C¹` family are `C¹`. -/
theorem tm_contDiff_word {G : V → Matrix (LS W) (LS W) ℂ} (hG : ContDiff ℝ 1 G)
    (K : Matrix (Fin W) (Fin W) ℂ) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ),
      ContDiff ℝ 1 (fun x => tmWord K wd D (G x)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro wd D
    simp only [tmWord_zero]
    exact contDiff_const
  | succ ℓ ih =>
    intro wd D
    simp only [tmWord_succ]
    exact (contDiff_const.mul (tm_contDiff_letter hG K _)).mul (ih _ _)

/-- **Derivative of a letter**: `d ℓ(𝒢)(v) = ldA (Λv) ldC`. -/
theorem tm_letter_hasFDerivAt {G : V → Matrix (LS W) (LS W) ℂ}
    {Λ : V →L[ℝ] Matrix (LS W) (LS W) ℂ} (hΛ : ∀ v, (Λ v)ᴴ = Λ v) {x : V}
    {T : V →L[ℝ] Matrix (LS W) (LS W) ℂ} (hT : HasFDerivAt G T x)
    (hTv : ∀ v, T v = -(G x * Λ v * G x)) (K : Matrix (Fin W) (Fin W) ℂ) (l : Fin 6 × Bool) :
    ∃ T' : V →L[ℝ] Matrix (Fin W) (Fin W) ℂ, HasFDerivAt (fun y => tmLetter K l (G y)) T' x ∧
      ∀ v, T' v = ldA K l (G x) * Λ v * ldC K l (G x) := by
  obtain ⟨j, e⟩ := l
  have h1 : HasFDerivAt (fun y => lP K j * G y * lQ W j) ((sandCLM (lP K j) (lQ W j)).comp T) x :=
    (sandCLM (lP K j) (lQ W j)).hasFDerivAt.comp x hT
  cases e
  · refine ⟨_, h1, fun v => ?_⟩
    rw [ContinuousLinearMap.comp_apply, hTv, sandCLM_apply]
    simp only [ldA, ldC, Bool.false_eq_true, ite_false, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  · refine ⟨(conjCLM W).comp ((sandCLM (lP K j) (lQ W j)).comp T),
      (conjCLM W).hasFDerivAt.comp x h1, fun v => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTv, sandCLM_apply,
      conjCLM_apply]
    simp only [ldA, ldC, ite_true, Matrix.mul_neg, Matrix.neg_mul, conjTranspose_neg,
      conjTranspose_mul, hΛ, Matrix.mul_assoc]

/-- **Product rule for passive words.** -/
theorem tm_word_hasFDerivAt {G : V → Matrix (LS W) (LS W) ℂ}
    {Λ : V →L[ℝ] Matrix (LS W) (LS W) ℂ} (hΛ : ∀ v, (Λ v)ᴴ = Λ v) {x : V}
    (hG : ∃ T : V →L[ℝ] Matrix (LS W) (LS W) ℂ, HasFDerivAt G T x ∧
      ∀ v, T v = -(G x * Λ v * G x))
    (K : Matrix (Fin W) (Fin W) ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) :
    ∀ {ℓ : ℕ} (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ),
      (∀ j, ‖D j‖ ≤ Kd) →
      ∃ T : V →L[ℝ] Matrix (Fin W) (Fin W) ℂ, HasFDerivAt (fun y => tmWord K wd D (G y)) T x ∧
        ∃ (a : Fin ℓ → Matrix (Fin W) (LS W) ℂ) (c : Fin ℓ → Matrix (LS W) (Fin W) ℂ),
          (∀ v, T v = ∑ m, a m * Λ v * c m) ∧
          ∀ m, ‖a m‖ * ‖c m‖ ≤ Kd ^ (ℓ + 1) * lam K (G x) ^ (ℓ + 1) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro wd D _
    refine ⟨0, ?_, Fin.elim0, Fin.elim0, fun v => by simp, fun m => Fin.elim0 m⟩
    simp only [tmWord_zero]
    exact hasFDerivAt_const _ _
  | succ ℓ ih =>
    intro wd D hD
    obtain ⟨T₀, hT₀, hT₀v⟩ := hG
    obtain ⟨TL, hTL, hTLv⟩ := tm_letter_hasFDerivAt hΛ hT₀ hT₀v K (wd 0)
    obtain ⟨TR, hTR, a', c', hTRv, hac'⟩ :=
      ih (fun j => wd j.succ) (fun j => D j.succ) (fun j => hD _)
    set L := tmLetter K (wd 0) (G x) with hLdef
    set R := tmWord K (fun j => wd j.succ) (fun j => D j.succ) (G x) with hRdef
    set Λx := lam K (G x) with hΛx
    have h1 : HasFDerivAt (fun y => D 0 * tmLetter K (wd 0) (G y)) (D 0 • TL) x :=
      hTL.const_mul (D 0)
    have h2 := h1.mul' hTR
    have hfun : (fun y => tmWord K wd D (G y)) =
        (fun y => D 0 * tmLetter K (wd 0) (G y)) *
          (fun y => tmWord K (fun j => wd j.succ) (fun j => D j.succ) (G y)) := by
      funext y
      rw [tmWord_succ]
      rfl
    rw [hfun]
    refine ⟨_, h2, Fin.cons (D 0 * ldA K (wd 0) (G x)) (fun m => D 0 * L * a' m),
      Fin.cons (ldC K (wd 0) (G x) * R) c', fun v => ?_, fun m => ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, _root_.add_apply,
        _root_.smul_apply, hTRv, hTLv, ← hLdef, ← hRdef]
      rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul, smul_eq_mul,
        Finset.mul_sum]
      simp only [Matrix.mul_assoc]
      exact add_comm _ _
    · have hR := norm_tmWord_le K hKd (fun j => wd j.succ) (fun j => D j.succ) (G x)
        (fun j => hD _)
      have hL : ‖L‖ ≤ Λx := norm_tmLetter_le K (wd 0) (G x)
      have hA : ‖ldA K (wd 0) (G x)‖ ≤ Λx := norm_ldA_le K (wd 0) (G x)
      have hC : ‖ldC K (wd 0) (G x)‖ ≤ Λx := norm_ldC_le K (wd 0) (G x)
      have hΛ0 : 0 ≤ Λx := zero_le_one.trans (one_le_lam K (G x))
      have hD0 := hD 0
      refine Fin.cases ?_ (fun m => ?_) m
      · simp only [Fin.cons_zero]
        calc ‖D 0 * ldA K (wd 0) (G x)‖ * ‖ldC K (wd 0) (G x) * R‖
            ≤ (‖D 0‖ * ‖ldA K (wd 0) (G x)‖) * (‖ldC K (wd 0) (G x)‖ * ‖R‖) := by
              gcongr
              · exact Matrix.l2_opNorm_mul _ _
              · exact Matrix.l2_opNorm_mul _ _
          _ ≤ (Kd * Λx) * (Λx * (Kd ^ (ℓ + 1) * Λx ^ ℓ)) := by gcongr
          _ = Kd ^ (ℓ + 1 + 1) * Λx ^ (ℓ + 1 + 1) := by ring
      · simp only [Fin.cons_succ]
        have := hac' m
        calc ‖D 0 * L * a' m‖ * ‖c' m‖ ≤ (‖D 0‖ * ‖L‖) * (‖a' m‖ * ‖c' m‖) := by
              rw [← mul_assoc]
              gcongr
              refine (Matrix.l2_opNorm_mul _ _).trans ?_
              gcongr
              exact norm_mul_le _ _
          _ ≤ (Kd * Λx) * (Kd ^ (ℓ + 1) * Λx ^ (ℓ + 1)) := by gcongr
          _ = Kd ^ (ℓ + 1 + 1) * Λx ^ (ℓ + 1 + 1) := by ring

/-- A derivative `v ↦ Σ_{m<ℓ} a_m (Λv) c_m` with `‖a_m‖‖c_m‖ ≤ B` has norm `≤ ℓ B ‖Λ‖`. -/
theorem tm_clm_norm_le {ℓ : ℕ} {Λ : V →L[ℝ] Matrix (LS W) (LS W) ℂ}
    {T : V →L[ℝ] Matrix (Fin W) (Fin W) ℂ} {a : Fin ℓ → Matrix (Fin W) (LS W) ℂ}
    {c : Fin ℓ → Matrix (LS W) (Fin W) ℂ} (hT : ∀ v, T v = ∑ m, a m * Λ v * c m) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ m, ‖a m‖ * ‖c m‖ ≤ B) : ‖T‖ ≤ ℓ * B * ‖Λ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [hT]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m, ‖a m * Λ v * c m‖ ≤ ∑ _m : Fin ℓ, B * (‖Λ‖ * ‖v‖) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have h1 : ‖a m * Λ v * c m‖ ≤ ‖a m‖ * ‖Λ v‖ * ‖c m‖ := by
          refine (Matrix.l2_opNorm_mul _ _).trans ?_
          gcongr
          exact Matrix.l2_opNorm_mul _ _
        have h2 := Λ.le_opNorm v
        calc ‖a m * Λ v * c m‖ ≤ ‖a m‖ * ‖Λ v‖ * ‖c m‖ := h1
          _ = (‖a m‖ * ‖c m‖) * ‖Λ v‖ := by ring
          _ ≤ B * (‖Λ‖ * ‖v‖) := by gcongr; exact hB m
    _ = ℓ * B * ‖Λ‖ * ‖v‖ := by simp; ring

end BlockBand.Transmission.PassiveLayer
