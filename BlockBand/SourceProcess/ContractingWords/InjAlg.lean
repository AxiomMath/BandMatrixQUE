module

public import BlockBand.SourceProcess.ContractingWords.MatchFirst

/-!
# The injection of one fresh layer, deterministic

`newWord A c N D S w` with `c_ℓ` the injection weights (`|c_ℓ| ≤ c₀/W²`):
* `newWord_single_sub`: for `w = [(ℓ, s)]` the injection is exactly `c_ℓ Tr(D*D S_s)`;
* for `|w| ≥ 2` (proved in the sibling module, `newWord_long_sub_le`) it is `≤ (|w|+2)Λ^{|w|+3}/W²`, `Λ = 1 + 3(1+K+c₀)G²`,
  `G = 1 + ‖N‖ + ‖D‖` ("cut at another letter": a second, trace-class letter `N*A_ℓN` carries
  the trace, and the new row `D*D` enters through its operator norm only).
Tools: `norm_list_prod_sub_le_mat` (telescoping in operator norm), `norm_trace_le_card`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem norm_list_prod_sub_le_mat {n : Type} [Fintype n] [DecidableEq n] {α : Type*}
    (L : List α) (f g : α → Matrix n n ℂ) :
    ‖(L.map f).prod - (L.map g).prod‖ ≤
      (L.map fun x => ‖f x - g x‖).sum * (L.map fun x => 1 + ‖f x‖ + ‖g x‖).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hP : ‖(L.map f).prod‖ ≤ (L.map fun x => 1 + ‖f x‖ + ‖g x‖).prod := by
      refine (norm_list_prod_le _).trans ?_
      rw [List.map_map]
      exact list_prod_le_of_le L _ _ (fun x _ => by
        simp only [Function.comp_apply]; positivity) fun x _ => by
        simp only [Function.comp_apply]; linarith [norm_nonneg (g x)]
    have e : f a * (L.map f).prod - g a * (L.map g).prod =
        (f a - g a) * (L.map f).prod + g a * ((L.map f).prod - (L.map g).prod) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e]
    have h1 := norm_mul_le (f a - g a) (L.map f).prod
    have h2 := norm_mul_le (g a) ((L.map f).prod - (L.map g).prod)
    have hS0 : 0 ≤ (L.map fun x => ‖f x - g x‖).sum :=
      List.sum_nonneg fun z hz => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hz; exact norm_nonneg _
    have hP0 : 0 ≤ (L.map fun x => 1 + ‖f x‖ + ‖g x‖).prod :=
      List.prod_nonneg fun z hz => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp hz; show 0 ≤ 1 + ‖f x‖ + ‖g x‖; positivity
    have hf := norm_nonneg (f a); have hg := norm_nonneg (g a)
    have hd := norm_nonneg (f a - g a)
    calc _ ≤ ‖f a - g a‖ * ‖(L.map f).prod‖ +
          ‖g a‖ * ‖(L.map f).prod - (L.map g).prod‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ ‖f a - g a‖ * (L.map fun x => 1 + ‖f x‖ + ‖g x‖).prod +
          ‖g a‖ * ((L.map fun x => ‖f x - g x‖).sum * (L.map fun x => 1 + ‖f x‖ + ‖g x‖).prod) :=
          add_le_add (mul_le_mul_of_nonneg_left hP hd) (mul_le_mul_of_nonneg_left ih hg)
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg hd (add_nonneg hf hg)) hP0, mul_nonneg hS0 hP0,
            mul_nonneg (mul_nonneg hS0 hf) hP0]

theorem norm_trace_le_card (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖M.trace‖ ≤ 2 * W * ‖M‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖M.diag i‖ ≤ ∑ _i : Fin 2 × Fin W, ‖M‖ :=
        Finset.sum_le_sum fun i _ => BlockBand.SourceProcess.FullSource.norm_entry_le_op M i i
    _ = 2 * W * ‖M‖ := by simp [Finset.card_univ]

/-- `|Tr(N*AN·S·M)| ≤ Tr|A|·‖N‖²‖S‖‖M‖` for Hermitian `A`. -/
theorem norm_trace_letter_le {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (N S M : Matrix n n ℂ) :
    ‖(Nᴴ * A * N * S * M).trace‖ ≤ nuclearNorm A * (‖N‖ * ‖S‖ * ‖M‖ * ‖N‖) := by
  have e : (Nᴴ * A * N * S * M).trace = (A * (N * S * M * Nᴴ)).trace := by
    rw [show Nᴴ * A * N * S * M = Nᴴ * (A * (N * S * M)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (norm_trace_herm_mul_le hA _).trans (mul_le_mul_of_nonneg_left ?_ (nuclearNorm_nonneg _))
  have h1 := norm_mul_le (N * S * M) Nᴴ
  have h2 := norm_mul_le (N * S) M
  have h3 := norm_mul_le N S
  rw [Matrix.l2_opNorm_conjTranspose] at h1
  have := norm_nonneg M; have := norm_nonneg N
  calc ‖N * S * M * Nᴴ‖ ≤ ‖N * S * M‖ * ‖N‖ := h1
    _ ≤ ‖N‖ * ‖S‖ * ‖M‖ * ‖N‖ := by gcongr; exact h2.trans (by gcongr)

/-- **A one-letter word**: the injection is `c_ℓ Tr(D*D S_s)`. -/
theorem newWord_single_sub (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ) (S : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : TraceLetter nT nI) (s : Separator) :
    newWord A c N D S [(ℓ, s)] - newWord A (fun _ => 0) N D S [(ℓ, s)] =
      (c ℓ : ℂ) * (Dᴴ * D * S s).trace := by
  simp [newWord, Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul]

end BlockBand.SourceProcess.ContractingWords
