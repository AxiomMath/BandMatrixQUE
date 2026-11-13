module

public import BlockBand.SourceProcess.PhysApprox.B3GenSplit

/-!
# The birth sums of `ComplexClosedSummed`

Target: `GenReqBirth`, whose summand
`genBirthStep` is the third summand of `b3SummedErr` (`b3SummedErr_eq_gen`, `rfl`). Helper
lemmas are in the sub-namespace `B3.Birth`.

**Reduction proved here** (`genReqBirth_of_steps`): there are at most `np` birth steps
(`Birth.card_steps_le`), so the birth sum `genBirthSum` tends to `0` as soon as the birth error
of every single birth step does, uniformly in the step. At a birth step `j` (`⌊Wτ_i⌋ = j` for
the newborn tags `i`), the coordinates split into
* **old** coordinates (no newborn index): the birth target is `0` (`birthTarget_of_not_new`) and
  the birth error is the regular one-step increment, estimate `ComplexBirthOld`;
* **new** coordinates (some newborn index): the coordinate vanishes at length `j`
  (`Birth.b3X_new_eq_zero`: the newborn probe column is `0` before its birth), so the birth error is
  `X_{j+1} − target`. By `birthTarget_newDiag_gram`, `birthTarget_newDiag_k` and
  `birthTarget_of_not_newDiag` the target is `d_* m_i` on the two Gram diagonals of a newborn
  `i`, `a m_i` on its `𝒦` diagonal, and `0` on every other new coordinate. Estimates
  `ComplexBirthGramDiag`, `ComplexBirthKDiag`, `ComplexBirthCross` (`complexBirthNew_of_parts`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal ComplexConjugate

/-!
## Birth targets and newborn coordinates
-/

/-- The birth target of the coordinate `c` at the birth step `j`. -/
def birthTarget (b E : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) (c : CIdx K np) : ℂ :=
  cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)

/-- A column is **newborn** at step `j`: a probe column `i` with `⌊Wτ_i⌋ = j`. -/
def IsNewCol {np K : ℕ} (τ : Fin np → ℝ) (W j : ℕ) : SrcCol K (Fin np) → Prop
  | Sum.inl _ => False
  | Sum.inr i => ⌊(W : ℝ) * τ i⌋₊ = j

/-- A coordinate is **new** at step `j`: one of its indices is a newborn tag. -/
def IsNewCoord {np K : ℕ} (τ : Fin np → ℝ) (W j : ℕ) : CIdx K np → Prop
  | Sum.inl e => IsNewCol τ W j e.2.1 ∨ IsNewCol τ W j e.2.2
  | Sum.inr ij => ⌊(W : ℝ) * τ ij.1⌋₊ = j ∨ ⌊(W : ℝ) * τ ij.2⌋₊ = j

/-- A coordinate is a **newborn diagonal**: `M_ii`, `B_ii` or `𝒦_ii` of a newborn tag `i`. -/
def IsNewDiag {np K : ℕ} (τ : Fin np → ℝ) (W j : ℕ) (c : CIdx K np) : Prop :=
  ∃ i : Fin np, ⌊(W : ℝ) * τ i⌋₊ = j ∧
    (c = Sum.inr (i, i) ∨ ∃ σ : Fin 2, c = Sum.inl (σ, Sum.inr i, Sum.inr i))

namespace Birth

section Algebra

variable {α β γ : Type*}

theorem mul_apply_row_zero [Fintype β] {A : Matrix α β ℂ} {B : Matrix β γ ℂ} {i : α}
    (h : ∀ y, A i y = 0) (l : γ) : (A * B) i l = 0 := by
  simp [Matrix.mul_apply, h]

theorem mul_apply_col_zero [Fintype β] {A : Matrix α β ℂ} {B : Matrix β γ ℂ} {i : γ}
    (h : ∀ y, B y i = 0) (l : α) : (A * B) l i = 0 := by
  simp [Matrix.mul_apply, h]

theorem conjTranspose_apply_row_zero {V : Matrix β γ ℂ} {i : γ} (h : ∀ y, V y i = 0) (y : β) :
    Vᴴ i y = 0 := by
  simp [Matrix.conjTranspose_apply, h]

end Algebra

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W j : ℕ}

/-- The probe column of a tag is `0` up to its birth length (`n ≤ ⌊Wτ_i⌋`). -/
theorem probeColumns_unborn {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (g : Fin np → Fin W → ℂ) (x : Fin n × Fin W) : probeColumns W n τ m g x i = 0 := by
  simp only [probeColumns]
  rw [ite_eq_right]
  omega

theorem probeFrame_unborn {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (x : ProbedPath W np) (z : Fin 2 × Fin W) : probeFrame b E W n τ m x z i = 0 := by
  unfold probeFrame
  exact mul_apply_col_zero (fun y => probeColumns_unborn hi x.2 y) z

theorem complexSourceK_unborn_row {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (x : ProbedPath W np) (l : Fin np) : complexSourceK b E W n τ m x i l = 0 := by
  unfold complexSourceK
  exact mul_apply_row_zero (mul_apply_row_zero
    (conjTranspose_apply_row_zero fun y => probeColumns_unborn hi x.2 y)) l

theorem complexSourceK_unborn_col {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (x : ProbedPath W np) (l : Fin np) : complexSourceK b E W n τ m x l i = 0 := by
  unfold complexSourceK
  exact mul_apply_col_zero (fun y => probeColumns_unborn hi x.2 y) l

theorem b3ClosedKAt_unborn_row {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (y : ProbedPath W np × ℝ) (l : Fin np) : b3ClosedKAt b E s h τ m W n y i l = 0 := by
  have hF : ∀ z, (probeFrame b E W n τ m y.1)ᴴ i z = 0 :=
    conjTranspose_apply_row_zero fun z => probeFrame_unborn hi y.1 z
  simp only [b3ClosedKAt, Matrix.sub_apply, Matrix.smul_apply, complexSourceK_unborn_row hi,
    Matrix.mul_assoc, mul_apply_row_zero hF, smul_zero, sub_zero]

theorem b3ClosedKAt_unborn_col {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (y : ProbedPath W np × ℝ) (l : Fin np) : b3ClosedKAt b E s h τ m W n y l i = 0 := by
  have hF : ∀ z, probeFrame b E W n τ m y.1 z i = 0 := fun z => probeFrame_unborn hi y.1 z
  simp only [b3ClosedKAt, Matrix.sub_apply, Matrix.smul_apply, complexSourceK_unborn_col hi,
    mul_apply_col_zero hF, smul_zero, sub_zero]

theorem b3ClosedFrameAt_unborn {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (z : Fin 2 × Fin W) : b3ClosedFrameAt b E s h τ m W n Vs y z (Sum.inr i) = 0 := by
  unfold b3ClosedFrameAt
  exact mul_apply_col_zero (fun z' => by simp [b3OpenFrameAt, probeFrame_unborn hi]) z

theorem b3ClosedGramAt_unborn_row {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (l : SrcCol K (Fin np)) :
    (b3ClosedGramAt b E s h τ m W n Vs y).1 (Sum.inr i) l = 0 ∧
      (b3ClosedGramAt b E s h τ m W n Vs y).2 (Sum.inr i) l = 0 := by
  have hr := conjTranspose_apply_row_zero (fun z =>
    b3ClosedFrameAt_unborn (b := b) (E := E) (s := s) (h := h) (m := m) hi Vs y z)
  simp only [b3ClosedGramAt, gramPair, sourceGram, nearGram]
  exact ⟨mul_apply_row_zero hr l, mul_apply_row_zero (mul_apply_row_zero hr) l⟩

theorem b3ClosedGramAt_unborn_col {n : ℕ} {i : Fin np} (hi : n ≤ ⌊(W : ℝ) * τ i⌋₊)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (l : SrcCol K (Fin np)) :
    (b3ClosedGramAt b E s h τ m W n Vs y).1 l (Sum.inr i) = 0 ∧
      (b3ClosedGramAt b E s h τ m W n Vs y).2 l (Sum.inr i) = 0 := by
  simp only [b3ClosedGramAt, gramPair, sourceGram, nearGram]
  exact ⟨mul_apply_col_zero (fun z => b3ClosedFrameAt_unborn hi Vs y z) l,
    mul_apply_col_zero (fun z => b3ClosedFrameAt_unborn hi Vs y z) l⟩

/-- **A new coordinate vanishes before the birth**: at length `j`, every coordinate with a
newborn index is `0`. -/
theorem b3X_new_eq_zero (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    {c : CIdx K np} (hc : IsNewCoord τ W j c) (y : ProbedPath W np × ℝ) :
    b3X b E s h τ m W j Vs c y = 0 := by
  rcases c with ⟨σ, k, l⟩ | ⟨i, l⟩
  · simp only [b3X, cEntry, gramEntry]
    rcases hc with hk | hl
    · rcases k with k | k
      · exact (hk : False).elim
      · have h0 := b3ClosedGramAt_unborn_row (b := b) (E := E) (s := s) (h := h) (m := m)
          (le_of_eq hk.symm) Vs y l
        split_ifs <;> simp [h0.1, h0.2]
    · rcases l with l | l
      · exact (hl : False).elim
      · have h0 := b3ClosedGramAt_unborn_col (b := b) (E := E) (s := s) (h := h) (m := m)
          (le_of_eq hl.symm) Vs y k
        split_ifs <;> simp [h0.1, h0.2]
  · simp only [b3X, cEntry]
    rcases hc with hi | hl
    · exact b3ClosedKAt_unborn_row (le_of_eq hi.symm) y l
    · exact b3ClosedKAt_unborn_col (le_of_eq hl.symm) y i

/-!
## The birth targets
-/

theorem b3KBirthAt_apply (a a' : Fin np) :
    b3KBirthAt E τ m W j a a' =
      if a = a' ∧ ⌊(W : ℝ) * τ a⌋₊ = j then matchedA E * (m a : ℂ) else 0 := by
  simp only [b3KBirthAt, Matrix.sum_apply]
  rw [Finset.sum_eq_single a]
  · by_cases ha : ⌊(W : ℝ) * τ a⌋₊ = j
    · by_cases haa : a = a'
      · subst haa; simp [ha]
      · simp [ha, haa, Matrix.single_apply_of_ne]
    · simp [ha]
  · intro i _ hia
    split_ifs
    · simp [Matrix.single_apply_of_ne, hia]
    · simp
  · simp

theorem b3BirthAt_apply (k l : SrcCol K (Fin np)) :
    (b3BirthAt b τ m W j).1 k l = (b3BirthAt b τ m W j).2 k l ∧
      (b3BirthAt b τ m W j).1 k l =
        ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j ∧ k = Sum.inr i ∧ l = Sum.inr i then
          ((dStar b * m i : ℝ) : ℂ) else 0 := by
  simp only [b3BirthAt, Prod.fst_sum, Prod.snd_sum, Matrix.sum_apply]
  refine ⟨Finset.sum_congr rfl fun i _ => ?_, Finset.sum_congr rfl fun i _ => ?_⟩
  · split_ifs <;> simp
  · by_cases hi : ⌊(W : ℝ) * τ i⌋₊ = j
    · by_cases hk : k = Sum.inr i ∧ l = Sum.inr i
      · obtain ⟨rfl, rfl⟩ := hk; simp [hi]
      · rw [ite_eq_left hi, ite_eq_right (fun h' => hk h'.2)]
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [Matrix.single_apply_of_ne (h := fun h' => hk ⟨h'.1.symm, h'.2.symm⟩), mul_zero]
    · simp [hi]

theorem gramEntry_b3BirthAt (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    gramEntry e (b3BirthAt b τ m W j) =
      ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j ∧ e.2.1 = Sum.inr i ∧ e.2.2 = Sum.inr i then
          ((dStar b * m i : ℝ) : ℂ) else 0 := by
  have h0 := b3BirthAt_apply (b := b) (τ := τ) (m := m) (W := W) (j := j) e.2.1 e.2.2
  simp only [gramEntry]
  split_ifs
  · exact h0.2
  · rw [← h0.1, h0.2]

/-- **Old coordinates have target `0`.** -/
theorem birthTarget_of_not_new {c : CIdx K np} (hc : ¬ IsNewCoord τ W j c) :
    birthTarget b E τ m W j c = 0 := by
  rcases c with e | ⟨a, a'⟩
  · simp only [birthTarget, cEntry, gramEntry_b3BirthAt]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    rintro ⟨hi, hk, -⟩
    exact hc (Or.inl (by rw [hk]; exact hi))
  · simp only [birthTarget, cEntry, b3KBirthAt_apply]
    rw [ite_eq_right]
    rintro ⟨-, ha⟩
    exact hc (Or.inl ha)

/-- **New coordinates other than the newborn diagonals have target `0`.** -/
theorem birthTarget_of_not_newDiag {c : CIdx K np} (hc : ¬ IsNewDiag τ W j c) :
    birthTarget b E τ m W j c = 0 := by
  rcases c with ⟨σ, k, l⟩ | ⟨a, a'⟩
  · simp only [birthTarget, cEntry, gramEntry_b3BirthAt]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    rintro ⟨hi, hk, hl⟩
    exact hc ⟨i, hi, Or.inr ⟨σ, by rw [show k = Sum.inr i from hk, show l = Sum.inr i from hl]⟩⟩
  · simp only [birthTarget, cEntry, b3KBirthAt_apply]
    rw [ite_eq_right]
    rintro ⟨hEq, ha⟩
    subst hEq
    exact hc ⟨a, ha, Or.inl rfl⟩

/-- The Gram diagonal target of a newborn tag is `d_* m_i`. -/
theorem birthTarget_newDiag_gram {i : Fin np} (hi : ⌊(W : ℝ) * τ i⌋₊ = j) (σ : Fin 2) :
    birthTarget b E τ m W j (Sum.inl (σ, Sum.inr i, Sum.inr i) : CIdx K np) =
      ((dStar b * m i : ℝ) : ℂ) := by
  simp only [birthTarget, cEntry, gramEntry_b3BirthAt]
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro i' _ hne
    rw [ite_eq_right]
    rintro ⟨-, hk, -⟩
    exact hne (Sum.inr_injective hk).symm
  · simp

/-- The `𝒦` diagonal target of a newborn tag is `a m_i`. -/
theorem birthTarget_newDiag_k {i : Fin np} (hi : ⌊(W : ℝ) * τ i⌋₊ = j) :
    birthTarget b E τ m W j (Sum.inr (i, i) : CIdx K np) = matchedA E * (m i : ℂ) := by
  simp [birthTarget, cEntry, b3KBirthAt_apply, hi]

/-!
## At most `np` birth steps
-/

theorem card_steps_le (τ : Fin np → ℝ) (W : ℕ) (S : Finset ℕ) :
    (S.filter fun j => IsBirthStep τ W j).card ≤ np := by
  calc (S.filter fun j => IsBirthStep τ W j).card
      ≤ (Finset.univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊).card := by
        refine Finset.card_le_card fun j hj => ?_
        obtain ⟨-, i, hi⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    _ ≤ (Finset.univ : Finset (Fin np)).card := Finset.card_image_le
    _ = np := by simp

end Birth

open Birth

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W j : ℕ}

/-!
## The birth-step estimates and the reduction
-/

/-- **Old coordinates at a birth step**: the regular one-step increment of a coordinate
with no newborn index is `o(1)` in `L¹` on the alive set, uniformly over the birth steps. It is
the one-step size `C_p Tr M/√W` of the increments, which follows from the conditional second
moments that the regular half of the generator estimates provides at steps without a birth,
applied at the birth step itself (the old entries obey the update `RawTag.RawUpdate` at every
step, born tags or not). -/
def ComplexBirthOld : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ c : CIdx K np, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j →
        ¬ IsNewCoord τ W j c →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3dX b E s h τ m W j (Vs W) c) y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- **New coordinates at a birth step**: the value one step after the birth is its birth
target, in `L¹` on the alive set, uniformly over the birth steps. Split further by
`complexBirthNew_of_parts`. -/
def ComplexBirthNew : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ c : CIdx K np, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j → IsNewCoord τ W j c →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            b3X b E s h τ m W (j + 1) (Vs W) c y - birthTarget b E τ m W j c) y‖ₑ
          ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- The birth error of one step at a new coordinate. -/
theorem Birth.genBirthStep_new (R : ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {c : CIdx K np}
    (hc : IsNewCoord τ W j c) :
    genBirthStep b E s h τ m R W j Vs c =
      ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
        b3X b E s h τ m W (j + 1) Vs c y - birthTarget b E τ m W j c) y‖ₑ ∂closedLaw b W np := by
  unfold genBirthStep
  refine lintegral_congr fun y => ?_
  congr 2
  funext y'
  simp only [b3dX, b3X_new_eq_zero Vs hc y', sub_zero, birthTarget]

/-- The birth error of one step at an old coordinate. -/
theorem Birth.genBirthStep_old (R : ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {c : CIdx K np}
    (hc : ¬ IsNewCoord τ W j c) :
    genBirthStep b E s h τ m R W j Vs c =
      ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator
        (b3dX b E s h τ m W j Vs c) y‖ₑ ∂closedLaw b W np := by
  have h0 := birthTarget_of_not_new (b := b) (E := E) (m := m) hc
  simp only [birthTarget] at h0
  unfold genBirthStep
  refine lintegral_congr fun y => ?_
  congr 2
  funext y'
  rw [h0, sub_zero]

/-- **Reduction: per-step estimates ⇒ `GenReqBirth`** (the birth half of the generator
estimates). -/
theorem genReqBirth_of_steps (hO : ComplexBirthOld) (hN : ComplexBirthNew) :
    GenReqBirth := by
  intro b E np τ m T s h K Vs hD R c
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun _ => by rw [hεt]; exact le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  have hn : (0 : ℝ) < (np : ℝ) + 1 := by positivity
  set θ := ε.toReal / ((np : ℝ) + 1) with hθdef
  have hθ : 0 < θ := div_pos hεr hn
  filter_upwards [hO b E np τ m T s h K Vs hD R θ hθ c, hN b E np τ m T s h K Vs hD R θ hθ c]
    with W hOW hNW
  have hterm : ∀ j ∈ genBirthSteps s T τ W,
      genBirthStep b E s h τ m R W j (Vs W) c ≤ ENNReal.ofReal θ := by
    intro j hj
    obtain ⟨hjI, hjB⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hjI
    by_cases hc : IsNewCoord τ W j c
    · rw [Birth.genBirthStep_new R _ hc]
      exact hNW j hj1 hj2 hjB hc
    · rw [Birth.genBirthStep_old R _ hc]
      exact hOW j hj1 hj2 hjB hc
  calc genBirthSum b E s T h τ m R W (Vs W) c
      ≤ (genBirthSteps s T τ W).card • ENNReal.ofReal θ :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ ≤ np • ENNReal.ofReal θ := nsmul_le_nsmul_left zero_le (card_steps_le τ W _)
    _ ≤ ((np : ℝ≥0∞) + 1) * ENNReal.ofReal θ := by
        rw [nsmul_eq_mul]
        gcongr
        exact le_self_add
    _ = ε := by
        rw [show ((np : ℝ≥0∞) + 1) = ENNReal.ofReal ((np : ℝ) + 1) by
          rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
            ENNReal.ofReal_one], ← ENNReal.ofReal_mul (by positivity)]
        have e : ((np : ℝ) + 1) * θ = ε.toReal := by
          rw [hθdef]; field_simp
        rw [e, ENNReal.ofReal_toReal hεt]

/-!
## The new coordinates: diagonals and cross entries
-/

/-- **New Gram diagonal**: one step after its birth, the closed squared
norm `M_ii` and near norm `B_ii` of a newborn tag are `d_* m_i`, in `L¹` on the alive set. -/
def ComplexBirthGramDiag : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ (i : Fin np) (σ : Fin 2),
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            gramEntry (σ, Sum.inr i, Sum.inr i) (b3ClosedGramAt b E s h τ m W (j + 1) (Vs W) y) -
              ((dStar b * m i : ℝ) : ℂ)) y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- **Fresh `𝒦` diagonal**: one step after its birth, the closed `𝒦_ii`
of a newborn tag is `a m_i`, in `L¹` on the alive set. -/
def ComplexBirthKDiag : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ i : Fin np,
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator (fun y =>
            b3ClosedKAt b E s h τ m W (j + 1) y i i - matchedA E * (m i : ℂ)) y‖ₑ
          ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- **Cross entries**: one step after a birth, every new
coordinate that is not a newborn diagonal (old/new and new/new overlaps of the Gram and `𝒦`
coordinates, including the current columns) is `o(1)` in `L¹` on the alive set ("old/new cross
variances are at most `Cm Tr M_pr/W`"). -/
def ComplexBirthCross : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R θ : ℝ), 0 < θ → ∀ c : CIdx K np,
      ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsNewCoord τ W j c →
        ¬ IsNewDiag τ W j c →
        ∫⁻ y, ‖(b3Alive b E s h τ m R W j (Vs W)).indicator
            (b3X b E s h τ m W (j + 1) (Vs W) c) y‖ₑ ∂closedLaw b W np ≤ ENNReal.ofReal θ

/-- **Reduction: diagonals and cross entries ⇒ the new-coordinate estimate.** -/
theorem complexBirthNew_of_parts (hG : ComplexBirthGramDiag) (hK : ComplexBirthKDiag)
    (hX : ComplexBirthCross) : ComplexBirthNew := by
  intro b E np τ m T s h K Vs hD R θ hθ c
  have hGi := fun (i : Fin np) (σ : Fin 2) => hG b E np τ m T s h K Vs hD R θ hθ i σ
  have hKi := fun (i : Fin np) => hK b E np τ m T s h K Vs hD R θ hθ i
  filter_upwards [hX b E np τ m T s h K Vs hD R θ hθ c, Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 (hGi i), Filter.eventually_all.2 hKi]
    with W hXW hGW hKW
  intro j hj1 hj2 _ hc
  by_cases hd : IsNewDiag τ W j c
  · obtain ⟨i, hi, hci | ⟨σ, hci⟩⟩ := hd
    · subst hci
      rw [birthTarget_newDiag_k hi]
      exact hKW i j hj1 hj2 hi
    · subst hci
      rw [birthTarget_newDiag_gram hi]
      exact hGW i σ j hj1 hj2 hi
  · rw [birthTarget_of_not_newDiag hd]
    simpa only [sub_zero] using hXW j hj1 hj2 hc hd

/-- **`GenReqBirth` from the four birth-step estimates.** -/
theorem genReqBirth_of_parts (hO : ComplexBirthOld) (hG : ComplexBirthGramDiag)
    (hK : ComplexBirthKDiag) (hX : ComplexBirthCross) : GenReqBirth :=
  genReqBirth_of_steps hO (complexBirthNew_of_parts hG hK hX)

end BlockBand.SourceProcess.PhysApprox.B3
