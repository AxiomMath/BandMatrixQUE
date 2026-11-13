module

public import BlockBand.SourceProcess.ContractingWords.MatchUnits

/-!
# Matching the second-order drift terms

For an ordinary word `w` with `A_J = currentOf 𝕏` (so `P + A_J = 𝕊*P𝕊`), `B = sepOf 𝕏`:
the second-order sum of `word_drift_expand`,
`Σ_{p<q} Σ_k κ_k pairF(p, q, B_pG_kB_q, B_qH_kB_p)`, equals
`W⁻¹ Σ_{i<j} pairContraction(D₀/2, P, P + A_J, M_{ij}, N_{ij})` (the form of `wordDrift_eval`) up to
`2κ₀ Σ_{Z ∈ contrTwo w} |Tr Z|`, `κ₀ ≥ |κ₂|, |κ₃|` (the same-sign coefficients `σ₋/(4η²W)`).
This file proves it for one pair (`pair_one`); the sum is `drift_second`.
Sum bookkeeping: `contrOne_sum`, `contrTwo_sum`, `contrCov_sum`, `fin_pair_sum`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.FullSourceGenerator

variable {W nT nI : ℕ}

theorem list_sum_flatMap {α β : Type*} (L : List α) (g : α → List β) (f : β → ℝ) :
    ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

theorem list_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The sum over the sixteen pairs of contracting separators. -/
abbrev sepSum (F : Separator → Separator → List (TraceWord nT nI))
    (f : List (TraceWord nT nI) → ℝ) : ℝ :=
  ((contrSeps.flatMap fun σ => contrSeps.map fun σ' => F σ σ').map f).sum

theorem le_sepSum (F : Separator → Separator → List (TraceWord nT nI))
    {f : List (TraceWord nT nI) → ℝ} (hf : ∀ Zs, 0 ≤ f Zs) {σ σ' : Separator}
    (hσ : σ ∈ contrSeps) (hσ' : σ' ∈ contrSeps) : f (F σ σ') ≤ sepSum F f := by
  refine List.single_le_sum (fun x hx => ?_) _ ?_
  · obtain ⟨Zs, -, rfl⟩ := List.mem_map.mp hx; exact hf _
  · exact List.mem_map_of_mem (List.mem_flatMap.mpr ⟨σ, hσ, List.mem_map_of_mem hσ'⟩)

theorem sepSum_nonneg (F : Separator → Separator → List (TraceWord nT nI))
    {f : List (TraceWord nT nI) → ℝ} (hf : ∀ Zs, 0 ≤ f Zs) : 0 ≤ sepSum F f :=
  List.sum_nonneg fun x hx => by obtain ⟨Zs, -, rfl⟩ := List.mem_map.mp hx; exact hf _

theorem contrOne_sum (w : TraceWord nT nI) (f : List (TraceWord nT nI) → ℝ) :
    ((contrOne w).map f).sum =
      ∑ p ∈ Finset.range w.length, ((contrSeps.map fun σ => [setSepAt w p σ]).map f).sum := by
  rw [contrOne, list_sum_flatMap, list_sum_range]

theorem contrTwo_sum (w : TraceWord nT nI) (f : List (TraceWord nT nI) → ℝ) :
    ((contrTwo w).map f).sum = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
      sepSum (fun σ σ' => [setLastSep (pairS₁ w i j) σ, setLastSep (pairS₂ w i j) σ']) f := by
  rw [contrTwo, list_sum_flatMap, list_sum_range]
  simp only [list_sum_flatMap, list_sum_range]
  refine Finset.sum_comm' fun j i => ?_
  simp only [Finset.mem_range, Finset.mem_Ioo]
  omega

theorem contrCov_sum (w v : TraceWord nT nI) (f : List (TraceWord nT nI) → ℝ) :
    ((contrCov w v).map f).sum = ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length,
      sepSum (fun σ σ' => [setLastSep (w.rotate (i + 1)) σ ++ setLastSep (v.rotate (j + 1)) σ'])
        f := by
  rw [contrCov, list_sum_flatMap, list_sum_range]
  simp only [list_sum_flatMap, list_sum_range]

theorem fin_pair_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → ℕ → M) :
    ∑ p : Fin n, ∑ q ∈ Finset.Ioi p, F p q = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ioo i n, F i j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.Ioo i n, F i j)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Fin.map_valEmbedding_Ioi, Finset.sum_map]
  rfl

theorem mem_ord_of_sub {w S : TraceWord nT nI} (hw : IsOrdinaryWord w) (h : ∀ x ∈ S, x ∈ w) :
    ∀ x ∈ S, x.2 = .id ∨ x.2 = .proj := fun x hx => hw.2 x (h x hx)

theorem mem_take_rotate {w : TraceWord nT nI} {k m : ℕ} :
    ∀ x ∈ (w.rotate k).take m, x ∈ w := fun _ hx =>
  (List.mem_rotate).mp (List.mem_of_mem_take hx)

theorem sepAt_ord {w : TraceWord nT nI} (hw : IsOrdinaryWord w) {i : ℕ} (hi : i < w.length) :
    sepAt w i = .id ∨ sepAt w i = .proj := by
  have : sepAt w i = w[i].2 := by simp [sepAt, hi]
  rw [this]; exact hw.2 _ (List.getElem_mem hi)

theorem get_eq_sepAt (w : TraceWord nT nI) (i : Fin w.length) : (w.get i).2 = sepAt w i := by
  simp [sepAt]

/-- The value of one pair `i < j` with the four tensors. -/
abbrev pairVal (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI)
    (i j : ℕ) : ℂ :=
  ∑ k, fscK b E s W k * ((pairM A (sepOf b E XX) w i j * fscG b E XX k).trace *
    (pairN A (sepOf b E XX) w i j * fscH b E XX k).trace)

/-- **One pair**: the two opposite-sign tensors give `W⁻¹ pairContraction`; the same-sign
tensors give two contracting products. -/
theorem pair_one (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hJ : A .current = currentOf b E XX) {w : TraceWord nT nI} (hw : IsOrdinaryWord w)
    {κ₀ : ℝ} (hκ : ‖fscK b E s W 2‖ ≤ κ₀ ∧ ‖fscK b E s W 3‖ ≤ κ₀) {i j : ℕ} (hij : i < j)
    (hj : j < w.length) :
    ‖pairVal b E s XX A w i j - (W : ℂ)⁻¹ * pairContraction ((transportD0 b E / 2 : ℝ) : ℂ)
        (sepOf b E XX .proj) (sepOf b E XX .proj + A .current) (pairM A (sepOf b E XX) w i j)
        (pairN A (sepOf b E XX) w i j)‖ ≤
      2 * κ₀ * sepSum (fun σ σ' => [setLastSep (pairS₁ w i j) σ, setLastSep (pairS₂ w i j) σ'])
        fun Zs => ‖coreProd A (sepOf b E XX) Zs‖ := by
  have hP' : sepOf b E XX .proj + A .current =
      (twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX := by
    rw [hJ, currentOf]; simp [sepOf]
  have n1 : pairS₁ w i j ≠ [] := ne_nil_of_length_pos (by rw [length_pairS₁ w hij hj]; omega)
  have n2 : pairS₂ w i j ≠ [] := ne_nil_of_length_pos (by rw [length_pairS₂ w hij hj]; omega)
  have o1 : ∀ k m : ℕ, ∀ x ∈ (w.rotate k).take m, x.2 = .id ∨ x.2 = .proj := fun k m =>
    mem_ord_of_sub hw mem_take_rotate
  have hk : ∀ k : Fin 4, k = 2 ∨ k = 3 →
      ‖(pairM A (sepOf b E XX) w i j * fscG b E XX k).trace *
          (pairN A (sepOf b E XX) w i j * fscH b E XX k).trace‖ ≤
        sepSum (fun σ σ' => [setLastSep (pairS₁ w i j) σ, setLastSep (pairS₂ w i j) σ'])
          fun Zs => ‖coreProd A (sepOf b E XX) Zs‖ := fun k hk => by
    obtain ⟨σ, hσ, e1⟩ := exists_contr_pair b E XX A n1 (o1 _ _) (sepAt_ord hw hj) hk
    obtain ⟨σ', hσ', e2⟩ := exists_contr_pair b E XX A n2 (o1 _ _) (sepAt_ord hw (hij.trans hj)) hk
    have e1' : (pairM A (sepOf b E XX) w i j * fscG b E XX k).trace =
        wval A (sepOf b E XX) (setLastSep (pairS₁ w i j) σ) := e1
    have e2' : (pairN A (sepOf b E XX) w i j * fscH b E XX k).trace =
        wval A (sepOf b E XX) (setLastSep (pairS₂ w i j) σ') := by
      rw [fscH_eq b E XX hk]; exact e2
    rw [e1', e2', ← coreProd_two]
    exact le_sepSum (fun σ σ' => [setLastSep (pairS₁ w i j) σ, setLastSep (pairS₂ w i j) σ'])
      (fun _ => norm_nonneg _) hσ hσ'
  have e : pairVal b E s XX A w i j - (W : ℂ)⁻¹ * pairContraction
      ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj) (sepOf b E XX .proj + A .current)
        (pairM A (sepOf b E XX) w i j) (pairN A (sepOf b E XX) w i j) =
      fscK b E s W 2 * ((pairM A (sepOf b E XX) w i j * fscG b E XX 2).trace *
          (pairN A (sepOf b E XX) w i j * fscH b E XX 2).trace) +
        fscK b E s W 3 * ((pairM A (sepOf b E XX) w i j * fscG b E XX 3).trace *
          (pairN A (sepOf b E XX) w i j * fscH b E XX 3).trace) := by
    rw [pairVal, Fin.sum_univ_four, hP', pairContraction]
    simp only [fscK, fscG, fscH, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, sepOf]
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul (fscK b E s W 2), norm_mul (fscK b E s W 3)]
  have h2 := hk 2 (Or.inl rfl)
  have h3 := hk 3 (Or.inr rfl)
  have hk0 : 0 ≤ κ₀ := (norm_nonneg _).trans hκ.1
  have := mul_le_mul hκ.1 h2 (norm_nonneg _) hk0
  have := mul_le_mul hκ.2 h3 (norm_nonneg _) hk0
  linarith

end BlockBand.SourceProcess.ContractingWords
