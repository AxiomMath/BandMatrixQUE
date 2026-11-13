module

public import BlockBand.SourceProcess.ContractingWords.PosCovAbs
public import BlockBand.SourceProcess.FullSourceGenerator.MatchingEval

/-!
# Trace words as positional words

For a trace word `w`, letters `A` and a separator assignment by position `Ts : ℕ → Separator → M`,
`posTr (wl A w) (fun i => Ts i (w.get i).2) = Tr Π_i (A_{x_i} Ts_i(s_i))` (`posTr_word`). On the
word shapes:
* `posTr_word_const`: `Ts i = B` gives `wval A B w`;
* `posTr_word_single`: `w = L ++ x :: R`, `X` at `|L|`: `Tr(seg L·A_xX·seg R)`;
* `posTr_word_pair`: `w = L ++ x :: (Mid ++ y :: R)`, `X` at `|L|`, `Y` at `|L|+1+|Mid|`:
  `Tr(seg L·A_xX·seg Mid·A_yY·seg R)`;
* `posCut_word`: a positional cut of `wl A w` with `Σ_l|c_l| ≤ K^{|w|}` (Hermitian letters, `Tr|A| ≤ K`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSourceGenerator

variable {n : Type} [Fintype n] [DecidableEq n] {nT nI : ℕ}

/-- The letters of `w` by position. -/
def wl (A : TraceLetter nT nI → Matrix n n ℂ) (w : TraceWord nT nI) :
    Fin w.length → Matrix n n ℂ := fun i => A (w.get i).1

theorem ofFn_eq_mapIdx {α β : Type*} (w : List α) (F : ℕ → α → β) :
    List.ofFn (fun i : Fin w.length => F i (w.get i)) = w.mapIdx F := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem mapIdx_eq_map_of {α β : Type*} (l : List α) (F : ℕ → α → β) (f : α → β)
    (h : ∀ i (hi : i < l.length), F i l[i] = f l[i]) : l.mapIdx F = l.map f :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp [h i (by simpa using h1)]

/-- **Positional value of a trace word.** -/
theorem posTr_word (A : TraceLetter nT nI → Matrix n n ℂ) (w : TraceWord nT nI)
    (Ts : ℕ → Separator → Matrix n n ℂ) :
    posTr (wl A w) (fun i => Ts i (w.get i).2) =
      (w.mapIdx fun i x => A x.1 * Ts i x.2).prod.trace := by
  rw [posTr, ← ofFn_eq_mapIdx]; rfl

theorem posTr_word_const (A : TraceLetter nT nI → Matrix n n ℂ) (B : Separator → Matrix n n ℂ)
    (w : TraceWord nT nI) : posTr (wl A w) (fun i => B (w.get i).2) = wval A B w := by
  rw [posTr_word A w fun _ s => B s, mapIdx_eq_map_of w _ (fun x => A x.1 * B x.2)
    (fun _ _ => rfl)]
  rfl

/-- The single-slot assignment. -/
def slot1 (B : Separator → Matrix n n ℂ) (p : ℕ) (X : Matrix n n ℂ) : ℕ → Separator → Matrix n n ℂ :=
  fun i s => if i = p then X else B s

/-- The two-slot assignment. -/
def slot2 (B : Separator → Matrix n n ℂ) (p q : ℕ) (X Y : Matrix n n ℂ) :
    ℕ → Separator → Matrix n n ℂ :=
  fun i s => if i = p then X else if i = q then Y else B s

theorem posTr_word_single (A : TraceLetter nT nI → Matrix n n ℂ) (B : Separator → Matrix n n ℂ)
    (L R : TraceWord nT nI) (x : TraceLetter nT nI × Separator) (X : Matrix n n ℂ) :
    posTr (wl A (L ++ x :: R)) (fun i => slot1 B L.length X i ((L ++ x :: R).get i).2) =
      (segProd A B L * (A x.1 * X) * segProd A B R).trace := by
  rw [posTr_word, List.mapIdx_append, List.mapIdx_cons]
  rw [mapIdx_eq_map_of L _ (fun z => A z.1 * B z.2) fun i hi => by simp [slot1, Nat.ne_of_lt hi],
    mapIdx_eq_map_of R _ (fun z => A z.1 * B z.2) fun i hi => by simp [slot1]]
  simp [slot1, segProd, Matrix.mul_assoc]

theorem posTr_word_pair (A : TraceLetter nT nI → Matrix n n ℂ) (B : Separator → Matrix n n ℂ)
    (L Mid R : TraceWord nT nI) (x y : TraceLetter nT nI × Separator) (X Y : Matrix n n ℂ) :
    posTr (wl A (L ++ x :: (Mid ++ y :: R))) (fun i => slot2 B L.length (L.length + 1 + Mid.length)
        X Y i ((L ++ x :: (Mid ++ y :: R)).get i).2) =
      (segProd A B L * (A x.1 * X) * segProd A B Mid * (A y.1 * Y) * segProd A B R).trace := by
  rw [posTr_word, List.mapIdx_append, List.mapIdx_cons, List.mapIdx_append, List.mapIdx_cons]
  rw [mapIdx_eq_map_of L _ (fun z => A z.1 * B z.2) fun i hi => by
      simp only [slot2]; split_ifs <;> first | rfl | omega,
    mapIdx_eq_map_of Mid _ (fun z => A z.1 * B z.2) fun i hi => by
      simp only [slot2]; split_ifs <;> first | rfl | omega,
    mapIdx_eq_map_of R _ (fun z => A z.1 * B z.2) fun i hi => by
      simp only [slot2]; split_ifs <;> first | rfl | omega]
  simp only [slot2, List.prod_append, List.prod_cons]
  split_ifs <;> first | omega | simp [segProd, Matrix.mul_assoc]

/-- **Positional cut of a nonempty word.** -/
theorem posCut_word (A : TraceLetter nT nI → Matrix n n ℂ) (hA : ∀ ℓ, (A ℓ).IsHermitian)
    {K : ℝ} (hK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K) {w : TraceWord nT nI} (hw : w ≠ []) :
    PosCut (wl A w) (K ^ w.length) := by
  have hpos : 0 < w.length := List.length_pos_of_ne_nil hw
  suffices h : ∀ {r : ℕ} (hr : 0 < r) (F : Fin r → Matrix n n ℂ), (∀ i, (F i).IsHermitian) →
      (∀ i, nuclearNorm (F i) ≤ K) → PosCut F (K ^ r) from
    h hpos (wl A w) (fun i => hA _) (fun i => hK _)
  intro r hr F hF hFK
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨ι, hι, c, x, y, hc, hxy, hrep⟩ := posCut_of_herm F hF
  refine ⟨ι, hι, c, x, y, hc.trans ?_, hxy, hrep⟩
  calc ∏ i, nuclearNorm (F i) ≤ ∏ _i : Fin (k + 1), K :=
        Finset.prod_le_prod₀ (fun i _ => nuclearNorm_nonneg _) fun i _ => hFK i
    _ = K ^ (k + 1) := by simp

end BlockBand.SourceProcess.ContractingWords
