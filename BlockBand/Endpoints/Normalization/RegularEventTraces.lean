module

public import BlockBand.Endpoints.Normalization.RegularEventCertificate
public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Coarea.PoleExclusionLaw

/-!
# Regular prior event: the one-trace error `χ` is a matched trace

We identify the error `χ` of the regularity certificate with the matched-trace observables and
bound its tail probability.

## Deterministic identities (no measure)

* `regularEvent_matrixTrace_reindex`: the certificate trace is invariant under reindexing by
  any bijection (`pairDeformation`, `blockDeformation` use an arbitrary `σ`).
* `regularEvent_norm_chi`: for Hermitian `F`, real `c, e` and any `a`,
  `‖certificateChi F c e (conj a)‖ = ‖N⁻¹ Tr (F - e - c a)⁻¹ - a‖` (conjugation).
* `regularEvent_pair_chi_le`: for Hermitian `H_R`, `V` (any `C`, any real `s`, `e`) the pair
  error satisfies `‖χ(pairDeformation σ ω e, s, e, conj a(e))‖ ≤ max_{k ∈ {i,i+1}}
  ‖W⁻¹ Tr P_k (K(e) - s a)⁻¹ - a‖`, exactly the observable of
  `MatchedTracesContract.residualPair` (`K = pairResidual`).
* `regularEvent_block_chi_eq`: for Hermitian `H_R`, `p.b = b`, `|e| ≤ 2`,
  `‖χ(blockDeformation σ ω e, c, e, conj a(e))‖ = ‖W⁻¹ Tr (z₀ - Σ)⁻¹ - a‖` with
  `Σ = C*(H_R - e)⁻¹C`, `z₀ = commonZ b e` (`z₀ = -e - c a` because `|a| = 1`), and
  `oneBlockComplement` of every reassembled `H = assembleBlock ω G` is this `Σ`
  (`regularEvent_oneBlockComplement_assemble`): the observable of
  `MatchedTracesContract.commonPort`.

## Probability (Markov at a fixed order `q = D + 2`)

* `regularEvent_pair_trace_tail` (from `MatchedTracesContract.residualPair` at
  `s = min(b, 1-2b) = pairS p`): `b, κ, T` first; for every `t > 0`, `D > 0` there is `W₀`
  such that for `W ≥ W₀`, `n ≤ TW`, every model, pair, splitting law at `pairS p` and
  `e ∈ bulkInterval κ`: `Pω{t ≤ max_k ‖…‖} ≤ W^{-D}/2`.
* `regularEvent_block_trace_tail` (from `MatchedTracesContract.commonPort`): the same for
  the one-block splitting law, transported from `model.law` by `IsBlockSplitting`
  (outer-measure transport `regularEvent_block_le_law`; no measurability of the event used).
* `regularEvent_ae_blockState_isHermitian`: `Pω`-a.s. `H_R` is Hermitian (block splitting).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Palm BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Generic finite linear algebra
-/

section Generic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem regularEvent_trace_reindex (σ : ι ≃ κ) (A : Matrix ι ι ℂ) :
    (reindex σ σ A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diag_apply]
  exact Equiv.sum_comp σ.symm (fun i => A i i)

omit [Fintype ι] [Fintype κ] in
theorem regularEvent_reindex_sub_smul (σ : ι ≃ κ) (A : Matrix ι ι ℂ) (z : ℂ) :
    reindex σ σ A - z • (1 : Matrix κ κ ℂ) = reindex σ σ (A - z • 1) := by
  ext a b
  simp [Matrix.reindex_apply, Matrix.one_apply]

/-- The certificate trace is invariant under reindexing. -/
theorem regularEvent_matrixTrace_reindex (σ : ι ≃ κ) (F : Matrix ι ι ℂ) (z : ℂ) :
    certificateMatrixTrace (reindex σ σ F) z = certificateMatrixTrace F z := by
  unfold certificateMatrixTrace certificateMatrixResolvent
  rw [regularEvent_reindex_sub_smul, Matrix.inv_reindex, regularEvent_trace_reindex,
    Fintype.card_congr σ]

omit [Fintype ι] in
theorem regularEvent_shift_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ℝ) :
    (A - (x : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  refine hA.sub ?_
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- Conjugation of the certificate trace of a Hermitian matrix. -/
theorem regularEvent_conj_matrixTrace (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (z : ℂ) :
    conj (certificateMatrixTrace F z) = certificateMatrixTrace F (conj z) := by
  unfold certificateMatrixTrace certificateMatrixResolvent
  have h1 : (F - z • (1 : Matrix ι ι ℂ))ᴴ = F - conj z • 1 := by
    rw [conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one, Complex.star_def]
  rw [map_div₀, ← Complex.star_def, ← Matrix.trace_conjTranspose,
    Matrix.conjTranspose_nonsing_inv, h1, Complex.star_def, map_natCast]

/-- `‖χ(F, c, e, conj a)‖ = ‖N⁻¹ Tr (F - e - c a)⁻¹ - a‖` for Hermitian `F`. -/
theorem regularEvent_norm_chi (F : Matrix ι ι ℂ) (hF : F.IsHermitian) (c e : ℝ) (a : ℂ) :
    ‖certificateChi F c e (conj a)‖ =
      ‖certificateMatrixTrace F ((e : ℂ) + c * a) - a‖ := by
  unfold certificateChi
  rw [← Complex.norm_conj, map_sub, regularEvent_conj_matrixTrace F hF, Complex.conj_conj]
  congr 3
  simp [map_add, map_mul, Complex.conj_ofReal]

theorem regularEvent_norm_avg_sub_le (x y a : ℂ) :
    ‖(x + y) / 2 - a‖ ≤ max ‖x - a‖ ‖y - a‖ := by
  have h : (x + y) / 2 - a = ((x - a) + (y - a)) / 2 := by ring
  rw [h, norm_div, Complex.norm_two]
  have := norm_add_le (x - a) (y - a)
  have h1 := le_max_left ‖x - a‖ ‖y - a‖
  have h2 := le_max_right ‖x - a‖ ‖y - a‖
  linarith

end Generic

/-!
## 2. Markov at a fixed order and the polynomial choice of `W₀`
-/

section Markov

/-- Markov's inequality from an `L^q` bound; no measurability is needed (a non-measurable
function has `eLpNorm = ∞`). -/
theorem regularEvent_markov {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) {q t K : ℝ} (hq : 0 < q) (ht : 0 < t) (hK : 0 ≤ K)
    (h : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal K) :
    μ {x | t ≤ f x} ≤ ENNReal.ofReal ((K / t) ^ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hm := meas_ge_le_mul_pow_eLpNorm_enorm μ hq0 ENNReal.ofReal_ne_top (f := f)
    (ε := ENNReal.ofReal t) (by simpa using ht) (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [ENNReal.toReal_ofReal hq.le] at hm
  have hsub : {x | t ≤ f x} ⊆ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := by
    intro x hx
    change ENNReal.ofReal t ≤ ‖f x‖ₑ
    rw [Real.enorm_eq_ofReal (hf x)]
    exact ENNReal.ofReal_le_ofReal hx
  refine (measure_mono hsub).trans (hm.trans ?_)
  calc (ENNReal.ofReal t)⁻¹ ^ q * eLpNorm f (ENNReal.ofReal q) μ ^ q
      ≤ (ENNReal.ofReal t)⁻¹ ^ q * (ENNReal.ofReal K) ^ q := by
        gcongr
    _ = ENNReal.ofReal ((K / t) ^ q) := by
        rw [← ENNReal.ofReal_inv_of_pos ht, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 ht.le) hq.le,
          ENNReal.ofReal_rpow_of_nonneg hK hq.le, ← ENNReal.ofReal_mul (by positivity),
          ← Real.mul_rpow (by positivity) hK, inv_mul_eq_div]

/-- `(A/W)^{D+2} ≤ W^{-D}/2` for all large `W`. -/
theorem regularEvent_poly_small {A D : ℝ} (hA : 0 ≤ A) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → (A / W) ^ (D + 2) ≤ (W : ℝ) ^ (-D) / 2 := by
  refine ⟨⌈2 * A ^ (D + 2)⌉₊ + 1, fun W hW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := le_trans (Nat.le_add_left 1 _) hW
    exact_mod_cast this
  have hWpos : (0 : ℝ) < W := by linarith
  have hWx : 2 * A ^ (D + 2) ≤ W := by
    have h1 := Nat.le_ceil (2 * A ^ (D + 2))
    have h2 : ((⌈2 * A ^ (D + 2)⌉₊ : ℕ) : ℝ) ≤ W := by
      exact_mod_cast (Nat.le_succ _).trans hW
    linarith
  have hP : 0 < (W : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
  rw [Real.div_rpow hA hWpos.le, Real.rpow_add hWpos, Real.rpow_two, Real.rpow_neg hWpos.le,
    div_le_div_iff₀ (by positivity) (by norm_num)]
  have hW2 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  calc A ^ (D + 2) * 2 ≤ (W : ℝ) ^ 2 := by linarith
    _ = ((W : ℝ) ^ D)⁻¹ * ((W : ℝ) ^ D * (W : ℝ) ^ 2) := by field_simp

/-- Markov plus the polynomial choice: an `L^q` bound `C √q / W` at `q = D + 2` gives
probability at most `W^{-D}/2` of `t ≤ f`, for `W ≥ W₀(C, t, D)`. -/
theorem regularEvent_tail_of_eLpNorm {C t D : ℝ} (ht : 0 < t) (hD : 0 < D) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → 0 < W →
      ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}, (∀ x, 0 ≤ f x) →
        eLpNorm f (ENNReal.ofReal (D + 2)) μ ≤
          ENNReal.ofReal (C * Real.sqrt (D + 2) / W) →
        μ {x | t ≤ f x} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D) / 2) := by
  set A : ℝ := max (C * Real.sqrt (D + 2) / t) 0
  have hA : 0 ≤ A := le_max_right _ _
  obtain ⟨W₀, hW₀⟩ := regularEvent_poly_small (D := D) hA
  refine ⟨W₀, fun W hW hWpos α _ μ f hf hL => ?_⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hK : C * Real.sqrt (D + 2) / W ≤ A * t / W := by
    apply div_le_div_of_nonneg_right _ hWr.le
    have : C * Real.sqrt (D + 2) = C * Real.sqrt (D + 2) / t * t := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le
  have hm := regularEvent_markov μ hf (by linarith : (0 : ℝ) < D + 2) ht
    (by positivity : 0 ≤ A * t / W) (hL.trans (ENNReal.ofReal_le_ofReal hK))
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  have : A * t / W / t = A / W := by field_simp
  rw [this]
  exact hW₀ W hW

end Markov

/-!
## 3. The pair: `χ` against `MatchedTracesContract.residualPair`
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

theorem regularEvent_physicalCoareaF_isHermitian {α β : Type*} [Fintype α] [DecidableEq α]
    {H_R : Matrix α α ℂ} (hR : H_R.IsHermitian) (C : Matrix α β ℂ) {V : Matrix β β ℂ}
    (hV : V.IsHermitian) (e : ℝ) : (physicalCoareaF H_R C V e).IsHermitian := by
  unfold physicalCoareaF physicalCoareaResolvent
  exact hV.sub (isHermitian_conjTranspose_mul_mul C (regularEvent_shift_isHermitian hR e).inv)

/-- The pair trace is the average of the two block traces. -/
theorem regularEvent_pair_matrixTrace (X : PairMatrix p i) (z : ℂ) :
    certificateMatrixTrace X z =
      (pairBlockTrace p i (X - z • 1)⁻¹ i + pairBlockTrace p i (X - z • 1)⁻¹ (i + 1)) / 2 := by
  unfold certificateMatrixTrace certificateMatrixResolvent pairBlockTrace
  set M := (X - z • (1 : PairMatrix p i))⁻¹
  have hsplit : M.trace = (∑ x : PairSite p i, if x.1.1 = i then M x x else 0) +
      ∑ x : PairSite p i, if x.1.1 = i + 1 then M x x else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases x.2 with h | h
    · have h' : x.1.1 ≠ i + 1 := by rw [h]; exact ContractClauses.pair_ne_succ p i
      have e1 : (if x.1.1 = i then M x x else 0) = M x x := by simp [h]
      have e2 : (if x.1.1 = i + 1 then M x x else 0) = 0 := by simp [h']
      rw [e1, e2, add_zero]; rfl
    · have h' : x.1.1 ≠ i := by rw [h]; exact (ContractClauses.pair_ne_succ p i).symm
      have e1 : (if x.1.1 = i then M x x else 0) = 0 := by simp [h']
      have e2 : (if x.1.1 = i + 1 then M x x else 0) = M x x := by simp [h]
      rw [e1, e2, zero_add]; rfl
  rw [hsplit, ContractClauses.card_pairSite]
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  push_cast
  field_simp

/-- **`χ` of the pair is dominated by the residual-pair traces** (deterministic). For
Hermitian `H_R`, `V`, any coupling `C`, any reindexing `σ` and real `s, e`. -/
theorem regularEvent_pair_chi_le (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i)))
    (ω : SplitState p i) (h1 : ω.1.IsHermitian) (h3 : ω.2.2.IsHermitian) (s e : ℝ) :
    ‖certificateChi (pairDeformation p i σ ω e) s e (conj (matchedA e))‖ ≤
      max ‖pairBlockTrace p i ((pairResidual p i ω e - ((s : ℂ) * matchedA e) • 1)⁻¹) i -
          matchedA e‖
        ‖pairBlockTrace p i ((pairResidual p i ω e - ((s : ℂ) * matchedA e) • 1)⁻¹) (i + 1) -
          matchedA e‖ := by
  have hF := regularEvent_physicalCoareaF_isHermitian h1 ω.2.1 h3 e
  have hFσ : (pairDeformation p i σ ω e).IsHermitian := by
    unfold pairDeformation
    rw [Matrix.reindex_apply]
    exact hF.submatrix _
  rw [regularEvent_norm_chi _ hFσ, pairDeformation, regularEvent_matrixTrace_reindex,
    regularEvent_pair_matrixTrace]
  have heq : pairResidual p i ω e - ((s : ℂ) * matchedA e) • 1 =
      physicalCoareaF ω.1 ω.2.1 ω.2.2 e - ((e : ℂ) + s * matchedA e) • 1 := by
    unfold pairResidual
    rw [add_smul, sub_sub]
  rw [heq]
  exact regularEvent_norm_avg_sub_le _ _ _

theorem regularEvent_pairS_eq {b : ℝ} (h : p.b = b) : pairS p = min b (1 - 2 * b) := by
  unfold pairS Parameters.c
  rw [h]

/-- **Pair trace tail** (Markov on `MatchedTracesContract.residualPair` at
`s = min(b, 1-2b)`, order `q = D + 2`). `b, κ, T` first; for every `t > 0` and `D > 0` a
width `W₀`; for `W ≥ W₀`, `n ≤ TW`, every model, pair `i`, splitting law at `pairS p` and
`e ∈ bulkInterval κ`: the residual-pair traces deviate by at least `t` with
`Pω`-probability at most `W^{-D}/2`. -/
theorem regularEvent_pair_trace_tail (hMT : MatchedTracesContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ T : ℝ} (hκ : 0 < κ) :
    ∀ t : ℝ, 0 < t → ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (pairS p) Pω → ∀ e ∈ bulkInterval κ,
      Pω {ω | t ≤ max
          ‖pairBlockTrace p i ((pairResidual p i ω e - ((pairS p : ℂ) * matchedA e) • 1)⁻¹) i -
            matchedA e‖
          ‖pairBlockTrace p i ((pairResidual p i ω e - ((pairS p : ℂ) * matchedA e) • 1)⁻¹)
            (i + 1) - matchedA e‖} ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) := by
  intro t ht D hD
  set s : ℝ := min b (1 - 2 * b)
  have hs : 0 < s := lt_min hb0 (by linarith)
  have hs2 : s < 2 * min (1 - 2 * b) b := by
    rw [min_comm]; linarith
  obtain ⟨ε₀, C, hε₀, hRP⟩ := hMT.residualPair b hb0 hb1 κ T s hκ hs hs2
  obtain ⟨W₁, hW₁⟩ := regularEvent_tail_of_eLpNorm (C := C) ht hD
  refine ⟨max W₁ ⌈(D + 2) / ε₀⌉₊, ?_⟩
  intro p hpb hW hn model i Pω hsplit e he
  have hps : pairS p = s := regularEvent_pairS_eq p hpb
  rw [hps] at hsplit ⊢
  have hWpos := p.W_pos
  have hq : D + 2 ≤ ε₀ * p.W := by
    have h1 : ((⌈(D + 2) / ε₀⌉₊ : ℕ) : ℝ) ≤ p.W := by exact_mod_cast (le_max_right _ _).trans hW
    have h2 := Nat.le_ceil ((D + 2) / ε₀)
    have h3 : (D + 2) / ε₀ ≤ p.W := h2.trans h1
    rw [div_le_iff₀ hε₀] at h3
    linarith
  have hL := hRP p hpb hn model i Pω hsplit e he (D + 2) (by linarith) hq
  exact hW₁ p.W ((le_max_left _ _).trans hW) hWpos Pω
    (fun _ => le_max_of_le_left (norm_nonneg _)) hL

end Pair

/-!
## 4. One block: `χ` against `MatchedTracesContract.commonPort`
-/

section Block

variable (p : Parameters) (k : ZMod p.n)

theorem regularEvent_card_blockSite : Fintype.card (BlockSite p k) = p.W := by
  classical
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun x : p.Site => x.1 = k) =
      ({k} : Finset (ZMod p.n)) ×ˢ (Finset.univ : Finset (Fin p.W)) := by
    ext ⟨a, w⟩
    simp [eq_comm]
  rw [hfilter, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
    one_mul]

/-- The one-block certificate trace is the normalized block trace. -/
theorem regularEvent_block_matrixTrace (X : Matrix (BlockSite p k) (BlockSite p k) ℂ) (z : ℂ) :
    certificateMatrixTrace X z = oneBlockTrace p k (X - z • 1)⁻¹ := by
  unfold certificateMatrixTrace certificateMatrixResolvent oneBlockTrace
  rw [regularEvent_card_blockSite, div_eq_inv_mul]

/-- `|a(e)| = 1` on `[-2,2]`, hence `a⁻¹ = conj a`. -/
theorem regularEvent_matchedA_inv {e : ℝ} (he : |e| ≤ 2) : (matchedA e)⁻¹ = conj (matchedA e) := by
  have hrad : 0 ≤ 4 - e ^ 2 := by nlinarith [abs_le.1 he, sq_abs e]
  have hn : Complex.normSq (matchedA e) = 1 := by
    rw [Complex.normSq_apply]
    simp only [matchedA]
    nlinarith [Real.sq_sqrt hrad]
  rw [Complex.inv_def, hn]
  simp

/-- `z₀ = a⁻¹ + 2ba = -e - (1-2b) a` on `[-2,2]`. -/
theorem regularEvent_commonZ_eq {b e : ℝ} (he : |e| ≤ 2) :
    commonZ b e = -((e : ℂ) + ((1 - 2 * b : ℝ) : ℂ) * matchedA e) := by
  unfold commonZ
  rw [regularEvent_matchedA_inv he]
  apply Complex.ext
  · simp [matchedA]; ring
  · simp [matchedA]; ring

/-- The one-block complement of a reassembled matrix is `C*(H_R - e)⁻¹C`. -/
theorem regularEvent_oneBlockComplement_assemble (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (e : ℝ) :
    oneBlockComplement p k (assembleBlock p k ω G) e = ω.2ᴴ * (ω.1 - (e : ℂ) • 1)⁻¹ * ω.2 := by
  unfold oneBlockComplement
  have h1 : (fun x y : OffBlockSite p k => assembleBlock p k ω G x.1 y.1) = ω.1 := by
    funext x y
    simp [assembleBlock, x.2, y.2]
  have h2 : (fun (x : OffBlockSite p k) (y : BlockSite p k) => assembleBlock p k ω G x.1 y.1) =
      ω.2 := by
    funext x y
    simp [assembleBlock, x.2, y.2]
  simp only [h1, h2]

/-- **`χ` of one block is the common-port trace** (deterministic; conjugation step of triage
C3). For Hermitian `H_R`, `p.b = b` and `|e| ≤ 2`. -/
theorem regularEvent_block_chi_eq (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (ω : BlockState p k) (h1 : ω.1.IsHermitian) {b e : ℝ} (hpb : p.b = b) (he : |e| ≤ 2) :
    ‖certificateChi (blockDeformation p k σ ω e) p.c e (conj (matchedA e))‖ =
      ‖oneBlockTrace p k ((commonZ b e • 1 - ω.2ᴴ * (ω.1 - (e : ℂ) • 1)⁻¹ * ω.2)⁻¹) -
        matchedA e‖ := by
  have hF : (blockF p k ω e).IsHermitian := by
    unfold blockF
    exact regularEvent_physicalCoareaF_isHermitian h1 ω.2 isHermitian_zero e
  have hFσ : (blockDeformation p k σ ω e).IsHermitian := by
    unfold blockDeformation
    rw [Matrix.reindex_apply]
    exact hF.submatrix _
  rw [regularEvent_norm_chi _ hFσ, blockDeformation, regularEvent_matrixTrace_reindex,
    regularEvent_block_matrixTrace]
  have heq : blockF p k ω e - ((e : ℂ) + (p.c : ℂ) * matchedA e) • 1 =
      commonZ b e • 1 - ω.2ᴴ * (ω.1 - (e : ℂ) • 1)⁻¹ * ω.2 := by
    rw [regularEvent_commonZ_eq he]
    unfold blockF physicalCoareaF physicalCoareaResolvent Parameters.c
    rw [hpb, neg_smul]
    abel
  rw [heq]

theorem regularEvent_measurable_assembleBlock :
    Measurable (fun x : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      assembleBlock p k x.1 x.2) := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  unfold assembleBlock
  have h1 : Measurable (fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      z.1.1) := measurable_fst.comp measurable_fst
  have h2 : Measurable (fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      z.1.2) := measurable_snd.comp measurable_fst
  have h4 : Measurable (fun z : BlockState p k × Matrix (BlockSite p k) (BlockSite p k) ℂ =>
      z.2) := measurable_snd
  split_ifs
  · exact Matrix.measurable_apply.comp h4
  · exact continuous_star.measurable.comp (Matrix.measurable_apply.comp h2)
  · exact Matrix.measurable_apply.comp h2
  · exact Matrix.measurable_apply.comp h1

theorem regularEvent_isProbabilityMeasure_gue (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

variable {p k}

/-- Every one-block splitting law is a probability measure. -/
theorem regularEvent_isProbabilityMeasure_blockSplitting {model : p.GaussianRingModel}
    {Pω : Measure (BlockState p k)} (h : IsBlockSplitting p k model Pω) :
    IsProbabilityMeasure Pω := by
  have := regularEvent_isProbabilityMeasure_gue (BlockSite p k) (blockTime p)
  constructor
  have h1 := congrArg (fun μ : Measure p.SiteMatrix => μ Set.univ) h
  simp only [measure_univ] at h1
  rw [Measure.map_apply (regularEvent_measurable_assembleBlock p k) MeasurableSet.univ,
    Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod] at h1
  rw [measure_univ (μ := gueMeasure (BlockSite p k) (blockTime p)), mul_one] at h1
  exact h1

/-- **Outer-measure transport** from the one-block splitting law to the physical law: if every
reassembly of every `ω ∈ B` lies in `S`, then `Pω B ≤ P(S)`. No measurability of `B` or `S`. -/
theorem regularEvent_block_le_law {model : p.GaussianRingModel} {Pω : Measure (BlockState p k)}
    (h : IsBlockSplitting p k model Pω) (B : Set (BlockState p k)) (S : Set p.SiteMatrix)
    (hBS : ∀ ω ∈ B, ∀ G, assembleBlock p k ω G ∈ S) :
    Pω B ≤ (model.law : Measure p.SiteMatrix) S := by
  have := regularEvent_isProbabilityMeasure_gue (BlockSite p k) (blockTime p)
  have := regularEvent_isProbabilityMeasure_blockSplitting h
  have hB : Pω B = (Pω.prod (gueMeasure (BlockSite p k) (blockTime p))) (B ×ˢ Set.univ) := by
    rw [Measure.prod_prod, measure_univ, mul_one]
  rw [hB, ← h]
  refine le_trans (measure_mono ?_) (Measure.le_map_apply
    (regularEvent_measurable_assembleBlock p k).aemeasurable S)
  rintro ⟨ω, G⟩ ⟨hω, -⟩
  exact hBS ω hω G

/-- `Pω`-almost surely the exterior block `H_R` of a one-block splitting law is Hermitian. -/
theorem regularEvent_ae_blockState_isHermitian {model : p.GaussianRingModel}
    {Pω : Measure (BlockState p k)} (h : IsBlockSplitting p k model Pω) :
    ∀ᵐ ω ∂Pω, ω.1.IsHermitian := by
  rw [ae_iff]
  refine le_antisymm ?_ zero_le
  have hS : (model.law : Measure p.SiteMatrix) {H | ¬ H.IsHermitian} = 0 := by
    have := model.isPhysical.1
    rwa [ae_iff] at this
  rw [← hS]
  refine regularEvent_block_le_law h _ _ fun ω hω G hH => hω ?_
  ext x y
  have := congrFun (congrFun hH x.1) y.1
  simpa [assembleBlock, x.2, y.2, Matrix.conjTranspose_apply] using this

/-- **One-block trace tail** (Markov on `MatchedTracesContract.commonPort`, order `q = D + 2`,
transported to the splitting law). `b, κ, T` first; for every `t > 0`, `D > 0` a width `W₀`;
for `W ≥ W₀`, `n ≤ TW`, every model, block `k`, one-block splitting law and
`e ∈ bulkInterval κ`: `Pω{t ≤ ‖W⁻¹ Tr (z₀ - C*(H_R - e)⁻¹C)⁻¹ - a‖} ≤ W^{-D}/2`. -/
theorem regularEvent_block_trace_tail (hMT : MatchedTracesContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ T : ℝ} (hκ : 0 < κ) :
    ∀ t : ℝ, 0 < t → ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ,
    ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω → ∀ e ∈ bulkInterval κ,
      Pω {ω | t ≤ ‖oneBlockTrace p k ((commonZ b e • 1 - ω.2ᴴ * (ω.1 - (e : ℂ) • 1)⁻¹ * ω.2)⁻¹) -
          matchedA e‖} ≤ ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) := by
  intro t ht D hD
  obtain ⟨ε₀, C, hε₀, hCP⟩ := hMT.commonPort b hb0 hb1 κ T hκ
  obtain ⟨W₁, hW₁⟩ := regularEvent_tail_of_eLpNorm (C := C) ht hD
  refine ⟨max W₁ ⌈(D + 2) / ε₀⌉₊, ?_⟩
  intro p hpb hW hn model k Pω hsplit e he
  have hWpos := p.W_pos
  have hq : D + 2 ≤ ε₀ * p.W := by
    have h1 : ((⌈(D + 2) / ε₀⌉₊ : ℕ) : ℝ) ≤ p.W := by exact_mod_cast (le_max_right _ _).trans hW
    have h2 := Nat.le_ceil ((D + 2) / ε₀)
    have h3 : (D + 2) / ε₀ ≤ p.W := h2.trans h1
    rw [div_le_iff₀ hε₀] at h3
    linarith
  have hL := hCP p hpb hn model k e he (D + 2) (by linarith) hq
  have hlaw := hW₁ p.W ((le_max_left _ _).trans hW) hWpos (model.law : Measure p.SiteMatrix)
    (fun _ => norm_nonneg _) hL
  refine le_trans (regularEvent_block_le_law hsplit _ _ fun ω hω G => ?_) hlaw
  change t ≤ _ at hω
  change t ≤ _
  rw [regularEvent_oneBlockComplement_assemble]
  exact hω

end Block

end BlockBand.Endpoints.Normalization
