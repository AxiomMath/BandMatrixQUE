module

public import BlockBand.SourceProcess.ClosedSummedProof.LayerDriftG

/-!
# The contracting error sum of `LayerCov` for polarized Gram words

For the polarized Gram letters `gramLetters J V e e'` and a frame `V` with `Re Tr VᴴV ≤ R`, the
contracting sum of `LayerCov` is at most `64 max(R,0)·contrGram` (`contrCov_gram_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix Complex
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {c : Type} [Fintype c]

theorem trace_rk1_two {ι : Type} [Fintype ι] (u u' : ι → ℂ) (X Y : Matrix ι ι ℂ) :
    (rk1 u * X * (rk1 u' * Y)).trace = bilinear u X u' * bilinear u' Y u := by
  have e : rk1 u * X * rk1 u' = (bilinear u X u') • vecMulVec u (star u') := by
    ext x y
    simp only [rk1, bilinear, mul_apply, vecMulVec_apply, Pi.star_apply, Matrix.smul_apply,
      smul_eq_mul, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [← Matrix.mul_assoc, e, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  simp only [Matrix.trace, diag_apply, mul_apply, vecMulVec_apply, bilinear, dotProduct, mulVec,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  ring

omit [Fintype c] in
theorem bilinear_col {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (T : Matrix ι ι ℂ) (x y : c) :
    bilinear (colOf V x) T (colOf V y) = (Vᴴ * T * V) x y := by
  simp only [bilinear, dotProduct, mulVec, mul_apply, colOf, conjTranspose_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem norm_bilinear_pol_le {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (T : Matrix ι ι ℂ)
    (a b c' d : c) (k l : Fin 4) :
    ‖bilinear (polVec (colOf V b) (colOf V a) k) T (polVec (colOf V d) (colOf V c') l)‖ ≤
      4 * ∑ x, ∑ y, ‖(Vᴴ * T * V) x y‖ := by
  have hS : ∀ x y, ‖(Vᴴ * T * V) x y‖ ≤ ∑ x, ∑ y, ‖(Vᴴ * T * V) x y‖ := fun x y =>
    (Finset.single_le_sum (f := fun y => ‖(Vᴴ * T * V) x y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ y)).trans (Finset.single_le_sum (f := fun x => ∑ y, ‖(Vᴴ * T * V) x y‖)
        (fun _ _ => by positivity) (Finset.mem_univ x))
  have e : bilinear (polVec (colOf V b) (colOf V a) k) T (polVec (colOf V d) (colOf V c') l) =
      bilinear (colOf V b) T (colOf V d) + I ^ (l : ℕ) * bilinear (colOf V b) T (colOf V c') +
        star (I ^ (k : ℕ)) * bilinear (colOf V a) T (colOf V d) +
        star (I ^ (k : ℕ)) * I ^ (l : ℕ) * bilinear (colOf V a) T (colOf V c') := by
    simp only [bilinear, polVec, star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [e, bilinear_col, bilinear_col, bilinear_col, bilinear_col]
  have hn : ‖I ^ (l : ℕ)‖ = 1 := by simp [norm_pow]
  have hn' : ‖star (I ^ (k : ℕ))‖ = 1 := by rw [norm_star]; simp [norm_pow]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hn, hn', one_mul, one_mul, one_mul]
  linarith [hS b d, hS b c', hS a d, hS a c']

theorem vecNorm_polVec_sq_le {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (a b : c) (k : Fin 4)
    {R : ℝ} (hR : (Vᴴ * V).trace.re ≤ R) :
    vecNorm (polVec (colOf V b) (colOf V a) k) ^ 2 ≤ 4 * max R 0 := by
  rw [vecNorm, Real.sq_sqrt (by positivity)]
  have h1 := sum_col_sq_le V b
  have h2 := sum_col_sq_le V a
  have h3 : ∑ x, ‖polVec (colOf V b) (colOf V a) k x‖ ^ 2 ≤
      ∑ x, 2 * (‖V x b‖ ^ 2 + ‖V x a‖ ^ 2) :=
    Finset.sum_le_sum fun x _ => norm_polVec_sq_le _ _ k x
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at h3
  have := le_max_left R 0
  linarith

/-- **The contracting sum of `LayerCov`** for polarized Gram words: `≤ 64 max(R,0)·contrGram`. -/
theorem contrCov_gram_le {W : ℕ} (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) (V : Matrix (Fin 2 × Fin W) c ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e e' : Fin 2 × c × c) (k l : Fin 4)
    (σ σ' : Separator) {R : ℝ} (hR : (Vᴴ * V).trace.re ≤ R) :
    ((contrCov [(tagL k, σ)] [(tagR l, σ')]).map fun Zs =>
        ‖coreProd (gramLetters J V e e') (sepOf b E XX) Zs‖).sum ≤
      64 * max R 0 * contrGram b E XX V := by
  rw [contrCov_one, gramLetters_tagL, gramLetters_tagR]
  set M := max R 0
  have hM : 0 ≤ M := le_max_right _ _
  set u := polVec (colOf V e.2.2) (colOf V e.2.1) k
  set u' := polVec (colOf V e'.2.2) (colOf V e'.2.1) l
  have hu := vecNorm_polVec_sq_le V e.2.1 e.2.2 k hR
  have hu' := vecNorm_polVec_sq_le V e'.2.1 e'.2.2 l hR
  have huu : vecNorm u' * vecNorm u ≤ 4 * M := by
    nlinarith [vecNorm_nonneg u, vecNorm_nonneg u', sq_nonneg (vecNorm u - vecNorm u')]
  have pt : ∀ τ τ' : Separator, ‖(entryLetter V e k * sepOf b E XX τ *
      (entryLetter V e' l * sepOf b E XX τ')).trace‖ ≤
        16 * M * ∑ x, ∑ y, ‖(Vᴴ * sepOf b E XX τ * V) x y‖ := fun τ τ' => by
    rw [entryLetter, entryLetter, trace_rk1_two, norm_mul]
    have h1 := norm_bilinear_pol_le V (sepOf b E XX τ) e.2.1 e.2.2 e'.2.1 e'.2.2 k l
    have h2 := (norm_bilinear_le u' (sepOf b E XX τ') u).trans
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (vecNorm_nonneg u')
        (norm_sepOf_le b E hXX hη τ')) (vecNorm_nonneg u))
    have hS : 0 ≤ ∑ x, ∑ y, ‖(Vᴴ * sepOf b E XX τ * V) x y‖ := by positivity
    calc ‖bilinear u (sepOf b E XX τ) u'‖ * ‖bilinear u' (sepOf b E XX τ') u‖
        ≤ (4 * ∑ x, ∑ y, ‖(Vᴴ * sepOf b E XX τ * V) x y‖) * (4 * M) :=
          mul_le_mul h1 (h2.trans huu) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun τ' _ => pt τ τ').trans (le_of_eq ?_)
  simp only [Finset.sum_const, contrGram, contrSepSet, Finset.mul_sum]
  rw [Finset.card_insert_of_notMem (by decide), Finset.card_insert_of_notMem (by decide),
    Finset.card_insert_of_notMem (by decide), Finset.card_singleton]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  push_cast; ring

end BlockBand.SourceProcess.ClosedSummedProof
