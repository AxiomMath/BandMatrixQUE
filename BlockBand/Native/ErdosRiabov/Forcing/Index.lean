module

public import BlockBand.Native.ErdosRiabov.Forcing.Defs

/-!
# Forcing bounds: index identifications

The pair data of the forcing term list are the error quantities of named sub-patterns (0-based slots
`i < j`):
* segment: `gSeg = G_{[i,j]}` is the chain of `segPat σ i j` with sites `segSites x i j`
  (length `j - i + 1`), and `mSeg = mChain (segPat …) (segSites …)` (`chainM` shift lemma);
  hence `aG - aM = 𝒴` of the segment (`aG_sub_aM`);
* glue: `gHead_i S^q gTail_j` is the chain of `gluePat σ i j` with sites `glueSites x i j q`
  (length `k - (j - i) + 1`), and `mGlue = mChain (gluePat …) (glueSites …)` (a direct `funext`
  of `glueChain`/`glueObs`); hence `bG - bM = 𝒳`, resp. `𝒴`, of the glued chain;
* rotation (F1): `gTail_j gHead_j` is the chain of `rotPat σ j` (length `k + 1`, first and
  last entry `σ_j`) with sites `rotSites x j`;
* cut: a chain with last observable `1` is `gSeg 0 c * B_c * gSeg (c+1) (n-1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Forcing

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol

variable {N k : ℕ}

/-!
## Lists of slots
-/

section Lists

variable {α : Type*}

theorem drop_take_ofFn (g : Fin k → α) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) :
    ((List.ofFn g).take j).drop i = List.ofFn (fun l : Fin (j - i) => g ⟨i + l, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_take, List.length_ofFn]
    omega
  · intro n h1 h2
    simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn]

theorem drop_ofFn (g : Fin k → α) {j : ℕ} (hj : j ≤ k) :
    (List.ofFn g).drop j = List.ofFn (fun l : Fin (k - j) => g ⟨j + l, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
  · intro n h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]

theorem take_ofFn (g : Fin k → α) {j : ℕ} (hj : j ≤ k) :
    (List.ofFn g).take j = List.ofFn (fun l : Fin j => g ⟨l, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]

end Lists

section Slots

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem segProd_eq_ofFn (B R : Fin k → Matrix ι ι ℂ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ k) :
    segProd B R i j =
      (List.ofFn (fun l : Fin (j - i) => R ⟨i + l, by omega⟩ * B ⟨i + l, by omega⟩)).prod := by
  rw [segProd, slotList, drop_take_ofFn _ hij hj]

theorem gTail_eq_ofFn (B R : Fin k → Matrix ι ι ℂ) (j : Fin k) :
    gTail B R j =
      (List.ofFn (fun l : Fin (k - j) => R ⟨j + l, by omega⟩ * B ⟨j + l, by omega⟩)).prod := by
  rw [gTail, ← segProd_top_succ, segProd_eq_ofFn B R j.isLt.le le_rfl]

/-- A segment `G_{[i,j]}` as a slot product of length `j - i + 1` with last observable `1`. -/
theorem gSeg_eq_slotProd (B R : Fin k → Matrix ι ι ℂ) (i j : Fin k) (hij : i ≤ j) :
    gSeg B R i j = slotProd
      (fun l : Fin ((j : ℕ) - i + 1) => if (l : ℕ) < (j : ℕ) - i then B ⟨i + l, by omega⟩ else 1)
      (fun l => R ⟨i + l, by omega⟩) := by
  rw [gSeg, segProd_eq_ofFn B R hij j.isLt.le, slotProd, slotList, List.ofFn_succ',
    List.prod_concat]
  congr 1
  · refine congrArg List.prod (congrArg List.ofFn (funext fun l => ?_))
    simp only [Fin.val_castSucc, l.isLt, ite_true]
  · simp only [Fin.val_last, lt_irrefl, ite_false, Matrix.mul_one]
    congr 1
    exact Fin.ext (by simp only; omega)

end Slots

/-!
## The `chainM` shift
-/

theorem chainTilde_shift (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) {m m' : ℕ → ℂ}
    {A A' : ℕ → Fin N → ℂ} (c : ℕ) (n : ℕ) :
    ∀ j l, l - j = n → (∀ p, j ≤ p → p ≤ l → m' p = m (p + c)) →
      (∀ p, j ≤ p → p < l → A' p = A (p + c)) →
      Split.chainTilde σ S m A (j + c) (l + c) = Split.chainTilde σ S m' A' j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn hm hA
  rw [Split.chainTilde_eq σ S m A, Split.chainTilde_eq σ S m' A' j l]
  by_cases hjl : j < l
  · have hjl' : j + c < l + c := by omega
    simp only [hjl, hjl', ite_true]
    have e1 : m (j + c) = m' j := (hm j le_rfl hjl.le).symm
    have e2 : m (l + c) = m' l := (hm l hjl.le le_rfl).symm
    have e3 : A (j + c) = A' j := (hA j le_rfl hjl).symm
    have h1 : Split.chainTilde σ S m A (j + c + 1) (l + c) =
        Split.chainTilde σ S m' A' (j + 1) l := by
      rw [show j + c + 1 = (j + 1) + c by omega]
      exact ih (l - (j + 1)) (by omega) (j + 1) l rfl (fun p hp hp' => hm p (by omega) hp')
        (fun p hp hp' => hA p (by omega) hp')
    rw [e1, e2, e3, h1]
    congr 2
    rw [← Finset.map_add_right_Ioo j l c, Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    simp only [addRightEmbedding_apply]
    rw [(hm i (by omega) (by omega)).symm,
      ih (i - j) (by omega) j i rfl (fun p hp hp' => hm p hp (by omega))
        (fun p hp hp' => hA p hp (by omega)),
      ih (l - i) (by omega) i l rfl (fun p hp hp' => hm p (by omega) hp')
        (fun p hp hp' => hA p (by omega) hp')]
  · have hjl' : ¬ j + c < l + c := by omega
    simp only [hjl, hjl', ite_false]

theorem chainM_shift (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) {m m' : ℕ → ℂ}
    {A A' : ℕ → Fin N → ℂ} (c : ℕ) {j l : ℕ} (hm : ∀ p, j ≤ p → p ≤ l → m' p = m (p + c))
    (hA : ∀ p, j ≤ p → p < l → A' p = A (p + c)) :
    Split.chainM σ S m A (j + c) (l + c) = Split.chainM σ S m' A' j l := by
  rw [Split.chainM, Split.chainM, chainTilde_shift σ S c (l - j) j l rfl hm hA,
    ← Finset.map_add_right_Icc j l c, Finset.prod_map]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_Icc.mp hi
  simp only [addRightEmbedding_apply]
  exact (hm i hi'.1 hi'.2).symm

/-!
## Segments
-/

section Segment

/-- The segment pattern `(σ_i, …, σ_j)` (0-based), of length `j - i + 1`. -/
def segPat (σ : Fin k → Bool) (i j : Fin k) : Fin ((j : ℕ) - i + 1) → Bool :=
  fun l => σ ⟨min ((i : ℕ) + l) (k - 1), by omega⟩

/-- The segment sites `(x_i, …, x_j)` (the last one is unused by the isotropic chain). -/
def segSites (x : Fin k → Fin N) (i j : Fin k) : Fin ((j : ℕ) - i + 1) → Fin N :=
  fun l => x ⟨min ((i : ℕ) + l) (k - 1), by omega⟩

theorem segPat_apply (σ : Fin k → Bool) {i j : Fin k} (hij : i ≤ j) (l : Fin ((j : ℕ) - i + 1)) :
    segPat σ i j l = σ ⟨(i : ℕ) + l, by omega⟩ := by
  unfold segPat
  congr 1
  exact Fin.ext (by simp only; omega)

theorem segSites_apply (x : Fin k → Fin N) {i j : Fin k} (hij : i ≤ j)
    (l : Fin ((j : ℕ) - i + 1)) : segSites x i j l = x ⟨(i : ℕ) + l, by omega⟩ := by
  unfold segSites
  congr 1
  exact Fin.ext (by simp only; omega)

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-- `G_{[i,j]}` is the isotropic chain of the segment, for slots `B` that are `S^{x_l}` on
`[i, j)`. -/
theorem gSeg_eq_gChain (B : Fin k → Matrix (Fin N) (Fin N) ℂ) {i j : Fin k} (hij : i ≤ j)
    (hB : ∀ l : Fin k, i ≤ l → l < j → B l = obsMat P.S (x l)) :
    gSeg B (slotsH P.z σ t H) i j =
      gChain (patZ P.z (segPat σ i j) t) (isoSlots P.S (segSites x i j)) H := by
  rw [gSeg_eq_slotProd _ _ i j hij, gChain]
  congr 1
  · funext l
    unfold isoSlots
    by_cases hl : (l : ℕ) < (j : ℕ) - i
    · rw [ite_eq_left hl, ite_eq_left (by omega), hB _ (by simp only [Fin.le_def]; omega)
        (by simp only [Fin.lt_def]; omega), segSites_apply x hij]
    · rw [ite_eq_right hl, ite_eq_right (by omega)]
  · funext l
    simp only [slotsH, patZ, segPat_apply σ hij]

theorem isoSlots_obs {j : Fin k} (l : Fin k) (hl : l < j) :
    isoSlots P.S x l = obsMat P.S (x l) := by
  unfold isoSlots
  rw [ite_eq_left (by have := j.isLt; simp only [Fin.lt_def] at hl; omega)]

/-- `M_{[i,j]}` is the `M`-term of the segment. -/
theorem mSeg_eq_mChain {i j : Fin k} (hij : i ≤ j) :
    mSeg P σ x t i j = P.mChain (segPat σ i j) (segSites x i j) t := by
  rw [mSeg, PsiData.mChain, show (i : ℕ) + 1 = 1 + i by omega,
    show (j : ℕ) + 1 = ((j : ℕ) - i + 1) + i by omega]
  refine chainM_shift t P.S (i : ℕ) (fun p hp hp' => ?_) (fun p hp hp' => ?_)
  · unfold patM
    rw [dite_eq_left ⟨hp, hp'⟩, dite_eq_left ⟨by omega, by omega⟩, segPat_apply σ hij]
    congr 2
    exact Fin.ext (by simp only; omega)
  · unfold obsSeq
    rw [dite_eq_left ⟨hp, by omega⟩, dite_eq_left ⟨by omega, by omega⟩, segSites_apply x hij]
    congr 2
    exact Fin.ext (by simp only; omega)

/-- `aG - aM = 𝒴` of the segment, at the diagonal entry `(q, q)` -/
theorem aG_sub_aM (B : Fin k → Matrix (Fin N) (Fin N) ℂ) {i j : Fin k} (hij : i ≤ j)
    (hB : ∀ l : Fin k, i ≤ l → l < j → B l = obsMat P.S (x l)) (q : Fin N) :
    aG P σ t H B i j q - aM P σ x t i j q =
      P.isoErr (segPat σ i j) q q (segSites x i j) t H := by
  rw [aG, aM, gSeg_eq_gChain P σ x t H B hij hB, mSeg_eq_mChain P σ x t hij, PsiData.isoErr,
    ite_eq_left rfl]

theorem aG_sub_aM_av {i j : Fin k} (hij : i ≤ j) (q : Fin N) :
    aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q =
      P.isoErr (segPat σ i j) q q (segSites x i j) t H :=
  aG_sub_aM P σ x t H _ hij (fun _ _ _ => rfl) q

theorem aG_sub_aM_iso {i j : Fin k} (hij : i ≤ j) (q : Fin N) :
    aG P σ t H (isoSlots P.S x) i j q - aM P σ x t i j q =
      P.isoErr (segPat σ i j) q q (segSites x i j) t H :=
  aG_sub_aM P σ x t H _ hij (fun l _ hl => isoSlots_obs P x l hl) q

end Segment

/-!
## Glued chains
-/

section Glue

section Slots

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The glued slot product `G_{[1,i]} X G_{[j,k]}` (0-based slots), of length `k - (j-i) + 1`:
slots `l ≤ i` are the original ones (observable `X` at `l = i`), slots `l > i` are the original
slots `l + (j - i) - 1`. -/
theorem glue_prod (B R : Fin k → Matrix ι ι ℂ) {i j : Fin k} (hij : i < j)
    (X : Matrix ι ι ℂ) :
    gHead B R i * X * gTail B R j = slotProd
      (fun l : Fin (k - ((j : ℕ) - i) + 1) =>
        if (l : ℕ) < i then B ⟨min (l : ℕ) (k - 1), by omega⟩ else if (l : ℕ) = i then X
        else B ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩)
      (fun l => if (l : ℕ) ≤ i then R ⟨min (l : ℕ) (k - 1), by omega⟩
        else R ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩) := by
  have hij' : (i : ℕ) < j := hij
  rw [gHead, segProd_eq_ofFn B R (Nat.zero_le _) i.isLt.le, gTail_eq_ofFn, slotProd, slotList]
  have e : (List.ofFn (fun l : Fin ((i : ℕ) - 0) =>
        R ⟨0 + l, by omega⟩ * B ⟨0 + l, by omega⟩)).prod * R i * X *
      (List.ofFn (fun l : Fin (k - j) =>
        R ⟨j + l, by omega⟩ * B ⟨j + l, by omega⟩)).prod =
      (List.ofFn (fun l : Fin ((i : ℕ) - 0) => R ⟨0 + l, by omega⟩ * B ⟨0 + l, by omega⟩) ++
        [R i * X] ++ List.ofFn (fun l : Fin (k - j) =>
          R ⟨j + l, by omega⟩ * B ⟨j + l, by omega⟩)).prod := by
    simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_assoc]
  rw [e]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  · intro n h1 h2
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] at h1
    simp only [List.getElem_ofFn]
    by_cases hn : n < i
    · rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn,
        List.length_cons, List.length_nil]; omega), List.getElem_append_left
        (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
      simp only [hn, show n ≤ (i : ℕ) by omega, ite_true]
      congr 2 <;> exact Fin.ext (by simp only; omega)
    · by_cases hn' : n = i
      · subst hn'
        rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn,
          List.length_cons, List.length_nil]; omega), List.getElem_append_right
          (by simp only [List.length_ofFn]; omega)]
        simp only [List.length_ofFn, lt_irrefl, le_refl, ite_true, ite_false]
        simp only [Nat.sub_zero, Nat.sub_self, List.getElem_cons_zero]
        have e2 : (⟨min (i : ℕ) (k - 1), by omega⟩ : Fin k) = i :=
          Fin.ext (show min (i : ℕ) (k - 1) = i by omega)
        rw [e2]
      · rw [List.getElem_append_right (by simp only [List.length_append, List.length_ofFn,
          List.length_cons, List.length_nil]; omega), List.getElem_ofFn]
        simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
        rw [ite_eq_right hn, ite_eq_right hn', ite_eq_right (by omega)]
        congr 2 <;> exact Fin.ext (by simp only; omega)

end Slots

/-- The glued pattern `(σ_0, …, σ_i, σ_j, …, σ_{k-1})` (0-based), of length `k - (j-i) + 1`. -/
def gluePat (σ : Fin k → Bool) (i j : Fin k) : Fin (k - ((j : ℕ) - i) + 1) → Bool :=
  fun l => if (l : ℕ) ≤ i then σ ⟨min (l : ℕ) (k - 1), by omega⟩
    else σ ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩

/-- The glued sites `(x_0, …, x_{i-1}, q, x_j, …, x_{k-1})`. -/
def glueSites (x : Fin k → Fin N) (i j : Fin k) (q : Fin N) :
    Fin (k - ((j : ℕ) - i) + 1) → Fin N :=
  fun l => if (l : ℕ) < i then x ⟨min (l : ℕ) (k - 1), by omega⟩ else if (l : ℕ) = i then q
    else x ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

theorem glueChain_patM {i j : Fin k} (hij : i < j) :
    Split.glueChain ((i : ℕ) + 1) ((j : ℕ) + 1) (patM P.z σ) = patM P.z (gluePat σ i j) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  funext p
  unfold Split.glueChain patM
  by_cases hp : p ≤ (i : ℕ) + 1
  · rw [ite_eq_left hp]
    by_cases h1 : 1 ≤ p
    · rw [dite_eq_left ⟨h1, by omega⟩, dite_eq_left ⟨h1, by omega⟩]
      unfold gluePat
      rw [ite_eq_left (show (p - 1 : ℕ) ≤ i by omega)]
      congr 2
      exact Fin.ext (by simp only; omega)
    · rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  · rw [ite_eq_right hp]
    by_cases h2 : p ≤ k - ((j : ℕ) - i) + 1
    · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, h2⟩]
      unfold gluePat
      rw [ite_eq_right (show ¬ ((p - 1 : ℕ) ≤ i) by omega)]
      congr 2
      exact Fin.ext (by simp only; omega)
    · rw [dite_eq_right (by omega), dite_eq_right (by omega)]

theorem glueObs_obsSeq {i j : Fin k} (hij : i < j) (q : Fin N) :
    Split.glueObs ((i : ℕ) + 1) ((j : ℕ) + 1) (Split.rowObs P.S q) (obsSeq P.S x) =
      obsSeq P.S (glueSites x i j q) := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  funext p
  unfold Split.glueObs obsSeq
  by_cases hp : p < (i : ℕ) + 1
  · rw [ite_eq_left hp]
    by_cases h1 : 1 ≤ p
    · rw [dite_eq_left ⟨h1, by omega⟩, dite_eq_left ⟨h1, by omega⟩]
      unfold glueSites
      rw [ite_eq_left (show (p - 1 : ℕ) < i by omega)]
      congr 2
      exact Fin.ext (by simp only; omega)
    · rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  · rw [ite_eq_right hp]
    by_cases hq : p = (i : ℕ) + 1
    · rw [ite_eq_left hq, dite_eq_left ⟨by omega, by omega⟩]
      unfold glueSites
      rw [ite_eq_right (show ¬ ((p - 1 : ℕ) < i) by omega),
        ite_eq_left (show (p - 1 : ℕ) = i by omega)]
    · rw [ite_eq_right hq]
      by_cases h2 : p ≤ k - ((j : ℕ) - i) + 1
      · rw [dite_eq_left ⟨by omega, by omega⟩, dite_eq_left ⟨by omega, h2⟩]
        unfold glueSites
        rw [ite_eq_right (show ¬ ((p - 1 : ℕ) < i) by omega),
          ite_eq_right (show ¬ ((p - 1 : ℕ) = i) by omega)]
        congr 2
        exact Fin.ext (by simp only; omega)
      · rw [dite_eq_right (by omega), dite_eq_right (by omega)]

/-- `M^{(q)}_{[1,i],[j,k]}` is the `M`-term of the glued chain. -/
theorem mGlue_eq_mChain {i j : Fin k} (hij : i < j) (q : Fin N) :
    mGlue P σ x t i j q = P.mChain (gluePat σ i j) (glueSites x i j q) t := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  rw [mGlue, PsiData.mChain, glueChain_patM P σ hij, glueObs_obsSeq P x hij,
    show k - ((j : ℕ) + 1) + ((i : ℕ) + 1) + 1 = k - ((j : ℕ) - i) + 1 by omega]

theorem obsSeq_glue_last {i j : Fin k} (hij : i < j) (q : Fin N) :
    obsSeq P.S (glueSites x i j q) (k - ((j : ℕ) - i) + 1) = obsSeq P.S x k := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  unfold obsSeq glueSites
  rw [dite_eq_left ⟨by omega, le_rfl⟩, dite_eq_left ⟨by omega, le_rfl⟩]
  simp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

/-- The glued resolvent product is the glued chain, for slots `B` that are `S^{x_l}` (the
isotropic case also needs the identity in the last slot). -/
theorem glue_gChain (B : Fin k → Matrix (Fin N) (Fin N) ℂ) (B' : (n : ℕ) →
    (Fin n → Fin N) → Fin n → Matrix (Fin N) (Fin N) ℂ) {i j : Fin k} (hij : i < j) (q : Fin N)
    (hB : ∀ l : Fin (k - ((j : ℕ) - i) + 1),
      (if (l : ℕ) < i then B ⟨min (l : ℕ) (k - 1), by omega⟩
        else if (l : ℕ) = i then obsMat P.S q
        else B ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩) =
        B' _ (glueSites x i j q) l) :
    gHead B (slotsH P.z σ t H) i * obsMat P.S q * gTail B (slotsH P.z σ t H) j =
      gChain (patZ P.z (gluePat σ i j) t) (B' _ (glueSites x i j q)) H := by
  rw [glue_prod _ _ hij, gChain]
  congr 1
  · funext l
    exact hB l
  · funext l
    simp only [slotsH, patZ, gluePat]
    split_ifs <;> rfl

theorem glue_avSlots {i j : Fin k} (hij : i < j) (q : Fin N)
    (l : Fin (k - ((j : ℕ) - i) + 1)) :
    (if (l : ℕ) < i then avSlots P.S x ⟨min (l : ℕ) (k - 1), by omega⟩
      else if (l : ℕ) = i then obsMat P.S q
      else avSlots P.S x ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩) =
      avSlots P.S (glueSites x i j q) l := by
  simp only [avSlots, glueSites]
  split_ifs <;> rfl

theorem glue_isoSlots {i j : Fin k} (hij : i < j) (q : Fin N)
    (l : Fin (k - ((j : ℕ) - i) + 1)) :
    (if (l : ℕ) < i then isoSlots P.S x ⟨min (l : ℕ) (k - 1), by omega⟩
      else if (l : ℕ) = i then obsMat P.S q
      else isoSlots P.S x ⟨min ((l : ℕ) + ((j : ℕ) - i) - 1) (k - 1), by omega⟩) =
      isoSlots P.S (glueSites x i j q) l := by
  have hij' : (i : ℕ) < j := hij
  have hj := j.isLt
  have hl := l.isLt
  simp only [isoSlots, glueSites]
  split_ifs <;> first | rfl | omega

/-- av: `b_G - b_M = 𝒳` of the glued chain. -/
theorem bGav_sub_bMav {i j : Fin k} (hij : i < j) (q : Fin N) :
    bGav P σ x t H i j q - bMav P σ x t i j q =
      P.avErr (gluePat σ i j) (glueSites x i j q) t H := by
  rw [bGav, bMav, glue_gChain P σ x t H _ (fun n y => avSlots P.S y) hij q
    (glue_avSlots P x hij q), mGlue_eq_mChain P σ x t hij, PsiData.avErr,
    obsSeq_glue_last P x hij q]

/-- iso: `b_G - b_M = 𝒴` of the glued chain. -/
theorem bGiso_sub_bMiso {i j : Fin k} (hij : i < j) (a b q : Fin N) :
    bGiso P σ x t H a b i j q - bMiso P σ x t a b i j q =
      P.isoErr (gluePat σ i j) a b (glueSites x i j q) t H := by
  rw [bGiso, bMiso, glue_gChain P σ x t H _ (fun n y => isoSlots P.S y) hij q
    (glue_isoSlots P x hij q), mGlue_eq_mChain P σ x t hij, PsiData.isoErr]

theorem bMiso_eq {i j : Fin k} (hij : i < j) (a b q : Fin N) :
    bMiso P σ x t a b i j q =
      if a = b then P.mChain (gluePat σ i j) (glueSites x i j q) t a else 0 := by
  rw [bMiso, mGlue_eq_mChain P σ x t hij]

end Glue

/-!
## Rotation and cut
-/

section Rot

theorem add_mod_lt_k {j n : ℕ} (hn : n + j < k) : (j + n) % k = j + n :=
  Nat.mod_eq_of_lt (by omega)

theorem add_mod_ge_k {j n : ℕ} (hj : j < k) (hn : k ≤ n + j) (hn' : n < k) :
    (j + n) % k = j + n - k := by
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

section Slots

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `G_{[j,k]} G_{[1,j]}` (0-based: slots `j, …, k-1, 0, …, j`) as a slot product of length
`k + 1`: slot `l < k` is the original slot `(j + l) mod k`, slot `k` is `R_j` with `1`. -/
theorem rot_prod (B R : Fin k → Matrix ι ι ℂ) (j : Fin k) :
    gTail B R j * gHead B R j = slotProd
      (fun l : Fin (k + 1) => if (l : ℕ) < k then
        B ⟨((j : ℕ) + l) % k, Nat.mod_lt _ j.pos⟩ else 1)
      (fun l => R ⟨((j : ℕ) + l) % k, Nat.mod_lt _ j.pos⟩) := by
  have hj := j.isLt
  rw [gTail_eq_ofFn, gHead, segProd_eq_ofFn B R (Nat.zero_le _) j.isLt.le, slotProd, slotList]
  have e : (List.ofFn (fun l : Fin (k - j) =>
        R ⟨j + l, by omega⟩ * B ⟨j + l, by omega⟩)).prod *
      ((List.ofFn (fun l : Fin ((j : ℕ) - 0) =>
        R ⟨0 + l, by omega⟩ * B ⟨0 + l, by omega⟩)).prod * R j) =
      (List.ofFn (fun l : Fin (k - j) => R ⟨j + l, by omega⟩ * B ⟨j + l, by omega⟩) ++
        List.ofFn (fun l : Fin ((j : ℕ) - 0) => R ⟨0 + l, by omega⟩ * B ⟨0 + l, by omega⟩) ++
        [R j]).prod := by
    simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_assoc]
  rw [e]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  · intro n h1 h2
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] at h1
    simp only [List.getElem_ofFn]
    by_cases hn : n + j < k
    · rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn]; omega),
        List.getElem_append_left (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
      rw [ite_eq_left (by omega)]
      congr 2 <;> exact Fin.ext (by simp only; rw [add_mod_lt_k hn])
    · by_cases hn' : n < k
      · rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn]; omega),
          List.getElem_append_right (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
        rw [ite_eq_left hn']
        have hmod : ((j : ℕ) + n) % k = j + n - k := add_mod_ge_k hj (by omega) hn'
        congr 2 <;> exact Fin.ext (by simp only [List.length_ofFn, hmod]; omega)
      · rw [List.getElem_append_right (by simp only [List.length_append, List.length_ofFn]; omega)]
        simp only [List.length_append, List.length_ofFn]
        rw [ite_eq_right hn', Matrix.mul_one]
        have hnk : n = k := by omega
        have h0 : n - (k - ↑j + (↑j - 0)) = 0 := by omega
        simp only [h0, List.getElem_cons_zero]
        congr 1
        exact Fin.ext (show (j : ℕ) = ((j : ℕ) + n) % k by
          rw [hnk, Nat.add_mod_right, Nat.mod_eq_of_lt hj])

/-- A slot product of length `n` with last observable `1`, cut after slot `c`:
`slotProd = G_{[0,c]} B_c G_{[c+1,n-1]}`. -/
theorem slotProd_cut {n : ℕ} (B R : Fin n → Matrix ι ι ℂ) (c : ℕ) (hc : c + 1 < n)
    (hB : B ⟨n - 1, by omega⟩ = 1) :
    slotProd B R = gSeg B R ⟨0, by omega⟩ ⟨c, by omega⟩ * B ⟨c, by omega⟩ *
      gSeg B R ⟨c + 1, by omega⟩ ⟨n - 1, by omega⟩ := by
  rw [gSeg, gSeg, segProd_eq_ofFn B R (Nat.zero_le _) (by simp only; omega),
    segProd_eq_ofFn B R (by simp only; omega) (by simp only; omega), slotProd, slotList]
  simp only
  have e : (List.ofFn (fun l : Fin (c - 0) => R ⟨0 + l, by omega⟩ * B ⟨0 + l, by omega⟩)).prod *
      R ⟨c, by omega⟩ * B ⟨c, by omega⟩ *
      ((List.ofFn (fun l : Fin (n - 1 - (c + 1)) =>
        R ⟨c + 1 + l, by omega⟩ * B ⟨c + 1 + l, by omega⟩)).prod * R ⟨n - 1, by omega⟩) =
      (List.ofFn (fun l : Fin (c - 0) => R ⟨0 + l, by omega⟩ * B ⟨0 + l, by omega⟩) ++
        [R ⟨c, by omega⟩ * B ⟨c, by omega⟩] ++
        List.ofFn (fun l : Fin (n - 1 - (c + 1)) =>
          R ⟨c + 1 + l, by omega⟩ * B ⟨c + 1 + l, by omega⟩) ++
        [R ⟨n - 1, by omega⟩ * B ⟨n - 1, by omega⟩]).prod := by
    simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, hB, Matrix.mul_assoc]
  rw [e]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    omega
  · intro m h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hm : m < c
    · rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn,
        List.length_cons, List.length_nil]; omega), List.getElem_append_left
        (by simp only [List.length_append, List.length_ofFn, List.length_cons,
          List.length_nil]; omega), List.getElem_append_left
        (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
      congr 2 <;> exact Fin.ext (by simp only; omega)
    · by_cases hm' : m = c
      · subst hm'
        rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn,
          List.length_cons, List.length_nil]; omega), List.getElem_append_left
          (by simp only [List.length_append, List.length_ofFn, List.length_cons,
            List.length_nil]; omega), List.getElem_append_right
          (by simp only [List.length_ofFn]; omega)]
        simp only [List.length_ofFn, Nat.sub_zero, Nat.sub_self, List.getElem_cons_zero]
      · by_cases hm'' : m < n - 1
        · rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn,
            List.length_cons, List.length_nil]; omega), List.getElem_append_right
            (by simp only [List.length_append, List.length_ofFn, List.length_cons,
              List.length_nil]; omega), List.getElem_ofFn]
          simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
          congr 2 <;> exact Fin.ext (by simp only; omega)
        · rw [List.getElem_append_right (by simp only [List.length_append, List.length_ofFn,
            List.length_cons, List.length_nil]; omega)]
          simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
          have hmn : m = n - 1 := by omega
          subst hmn
          simp only [show n - 1 - (c - 0 + (0 + 1) + (n - 1 - (c + 1))) = 0 by omega,
            List.getElem_cons_zero]

end Slots

/-- The rotated pattern `(σ_j, …, σ_{k-1}, σ_0, …, σ_j)` of length `k + 1`. -/
def rotPat (σ : Fin k → Bool) (j : Fin k) : Fin (k + 1) → Bool :=
  fun l => σ ⟨((j : ℕ) + l) % k, Nat.mod_lt _ j.pos⟩

/-- The rotated sites `(x_j, …, x_{k-1}, x_0, …, x_j)`. -/
def rotSites (x : Fin k → Fin N) (j : Fin k) : Fin (k + 1) → Fin N :=
  fun l => x ⟨((j : ℕ) + l) % k, Nat.mod_lt _ j.pos⟩

theorem rotPat_first_last (σ : Fin k → Bool) (j : Fin k) :
    rotPat σ j 0 = rotPat σ j (Fin.last k) := by
  unfold rotPat
  congr 1
  exact Fin.ext (by simp only [Fin.val_zero, Fin.val_last, add_zero, Nat.add_mod_right])

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-- `G_{[j,k]} S^{x_k} G_{[1,j]}` is the isotropic chain of the rotated pattern. -/
theorem rot_gChain (j : Fin k) :
    gTail (avSlots P.S x) (slotsH P.z σ t H) j * gHead (avSlots P.S x) (slotsH P.z σ t H) j =
      gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H := by
  rw [rot_prod, gChain]
  congr 1
  funext l
  unfold isoSlots avSlots rotSites
  simp only [Nat.add_lt_add_iff_right]

/-- The length-one averaged error: `𝒳¹((σ_j); p) = Σ_b S_{pb} (G_j - m_j)_{bb}`. -/
theorem avErr_one_eq (j : Fin k) (p : Fin N) :
    P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H =
      ∑ b, (P.S p b : ℂ) *
        (slotsH P.z σ t H j - VS.patConj (σ j) (semicircleM P.z) • 1) b b := by
  have hm : patM P.z (fun _ : Fin 1 => σ j) 1 = VS.patConj (σ j) (semicircleM P.z) :=
    patM_of_mem P.z (fun _ : Fin 1 => σ j) 0
  have h1 : obsSeq P.S (fun _ : Fin 1 => p) 1 = Split.rowObs P.S p := by
    rw [obsSeq, dite_eq_left ⟨le_rfl, le_rfl⟩]
  have hg : gChain (patZ P.z (fun _ : Fin 1 => σ j) t) (avSlots P.S (fun _ : Fin 1 => p)) H =
      slotsH P.z σ t H j * obsMat P.S p := by
    simp [gChain, Chains.slotProd, Chains.slotList, avSlots, slotsH, patZ]
  rw [PsiData.avErr, Evol.mChain_one, h1, hg, trace_mul_obsMat, hm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Split.rowObs, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one]
  ring

/-- The (F1) trace as a sum over the diagonal of the rotated chain. -/
theorem famF1_av_term (j : Fin k) :
    trace (gHead (avSlots P.S x) (slotsH P.z σ t H) j *
        bandSelfEnergy P.S (slotsH P.z σ t H j - VS.patConj (σ j) (semicircleM P.z) • 1) *
        gTail (avSlots P.S x) (slotsH P.z σ t H) j) =
      ∑ p, P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H *
        gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H p p := by
  rw [Matrix.trace_mul_cycle, ← rot_gChain P σ x t H j, bandSelfEnergy, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal, avErr_one_eq P σ t H j p, mul_comm]

/-- The isotropic (F1) entry: `(G_{[1,j]} 𝒮[G_j - m_j] G_{[j,k]})_{ab} =
Σ_p 𝒳¹(p) (G_{[1,j]})_{ap} (G_{[j,k]})_{pb}`. -/
theorem famF1_iso_term (j : Fin k) (a b : Fin N) :
    (gHead (isoSlots P.S x) (slotsH P.z σ t H) j *
        bandSelfEnergy P.S (slotsH P.z σ t H j - VS.patConj (σ j) (semicircleM P.z) • 1) *
        gTail (isoSlots P.S x) (slotsH P.z σ t H) j) a b =
      ∑ p, P.avErr (fun _ : Fin 1 => σ j) (fun _ : Fin 1 => p) t H *
        (gHead (isoSlots P.S x) (slotsH P.z σ t H) j a p *
          gTail (isoSlots P.S x) (slotsH P.z σ t H) j p b) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bandSelfEnergy, Matrix.mul_diagonal, avErr_one_eq P σ t H j p]
  ring

end Rot

/-!
## Head, tail and cut as chains of sub-patterns
-/

section HeadTail

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-- `G_{[1,j]}` (isotropic slots) is the chain of the segment `[0, j]`. -/
theorem gHead_iso_eq (j : Fin k) :
    gHead (isoSlots P.S x) (slotsH P.z σ t H) j =
      gChain (patZ P.z (segPat σ ⟨0, j.pos⟩ j) t)
        (isoSlots P.S (segSites x ⟨0, j.pos⟩ j)) H :=
  gSeg_eq_gChain (i := ⟨0, j.pos⟩) (j := j) P σ x t H _ (by simp only [Fin.le_def]; omega)
    (fun l _ hl => isoSlots_obs P x l hl)

/-- `G_{[j,k]}` (isotropic slots, last observable `1`) is the chain of the segment
`[j, k-1]`. -/
theorem gTail_iso_eq (j : Fin k) :
    gTail (isoSlots P.S x) (slotsH P.z σ t H) j =
      gChain (patZ P.z (segPat σ j ⟨k - 1, by have := j.isLt; omega⟩) t)
        (isoSlots P.S (segSites x j ⟨k - 1, by have := j.isLt; omega⟩)) H := by
  have hj := j.isLt
  have hjl : j ≤ (⟨k - 1, by omega⟩ : Fin k) := by simp only [Fin.le_def]; omega
  rw [← gSeg_eq_gChain P σ x t H _ hjl (fun l _ hl => isoSlots_obs P x l hl), gTail_eq_ofFn,
    gSeg_eq_slotProd _ _ _ _ hjl, slotProd, slotList]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    omega
  · intro n h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hn : n < k - 1 - (j : ℕ)
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn]
      unfold isoSlots
      rw [ite_eq_right (by simp only; omega), Matrix.mul_one]

/-- The cut of the rotated chain after slot `c` (`c + 1 < k + 1`), with the two pieces as
chains of segments of the rotated pattern. -/
theorem rot_cut (j : Fin k) (c : ℕ) (hc : c + 1 < k) :
    gChain (patZ P.z (rotPat σ j) t) (isoSlots P.S (rotSites x j)) H =
      gChain (patZ P.z (segPat (rotPat σ j) ⟨0, by omega⟩ ⟨c, by omega⟩) t)
          (isoSlots P.S (segSites (rotSites x j) ⟨0, by omega⟩ ⟨c, by omega⟩)) H *
        obsMat P.S (rotSites x j ⟨c, by omega⟩) *
        gChain (patZ P.z (segPat (rotPat σ j) ⟨c + 1, by omega⟩ ⟨k, by omega⟩) t)
          (isoSlots P.S (segSites (rotSites x j) ⟨c + 1, by omega⟩ ⟨k, by omega⟩)) H := by
  have h1 := slotProd_cut (isoSlots P.S (rotSites x j)) (slotsH P.z (rotPat σ j) t H) c
    (by omega) (by unfold isoSlots; rw [ite_eq_right (by simp only; omega)])
  have hB : ∀ l : Fin (k + 1), l < ⟨k, by omega⟩ →
      isoSlots P.S (rotSites x j) l = obsMat P.S (rotSites x j l) := fun l hl =>
    isoSlots_obs P (rotSites x j) l hl
  show slotProd (isoSlots P.S (rotSites x j)) (slotsH P.z (rotPat σ j) t H) = _
  rw [h1, isoSlots_obs P (rotSites x j) ⟨c, by omega⟩
      (show (⟨c, by omega⟩ : Fin (k + 1)) < ⟨k, by omega⟩ by simp only [Fin.lt_def]; omega),
    gSeg_eq_gChain P (rotPat σ j) (rotSites x j) t H _
      (by simp only [Fin.le_def]; omega) (fun l _ hl => hB l (lt_of_lt_of_le hl
        (by simp only [Fin.le_def]; omega))),
    gSeg_eq_gChain P (rotPat σ j) (rotSites x j) t H _
      (by simp only [Fin.le_def]; omega) (fun l _ hl => hB l (by
        simpa using hl))]
  rfl

end HeadTail

end BlockBand.Native.ErdosRiabov.Forcing
