module

public import BlockBand.SourceProcess.FullSourceStops.WordBounds
public import BlockBand.SourceProcess.FullSourceStops.Tail
public import BlockBand.Transmission.Bridge.PencilAE
public import BlockBand.Transmission.SourceMixing.Conductance

/-!
# Word values along the path: measurability and the bound by a polynomial load

* `measurable_wordValue`: every word value `ω ↦ Tr(A₁B₁⋯A_rB_r)` at length `j` is measurable
  (the path scattering matrix, current, tags and interval sources are measurable in `ω`).
* `ae_norm_wordValue_le`: almost surely, for every length `j`, tag births `k` and every ordinary
  word `w` (separators `I`, `P`, at least one letter), `|Tr w| ≤ L_j^{|w|}` with the load
  `L_j = 1 + 2g_j + Σ_a Tr Q_{a,j}` (`wordLoad`). As in the paper, this never uses `Tr|J|`:
  a one-letter word is `Tr J = 0`, `Tr JP = -g`, or `|Tr(QB)| ≤ Tr Q`; a longer word is at most
  the product of the Hilbert–Schmidt norms of its letters, `‖J‖₂ = (2g)^{1/2}`, `‖Q‖₂ ≤ Tr Q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.Bridge BlockBand.Transmission.SourceMixing

variable {W : ℕ}

/-!
## Measurability
-/

theorem measurable_matrix_sub {α m n : Type*} [MeasurableSpace α] {f g : α → Matrix m n ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a - g a :=
  Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix.sub hg.eval_matrix

theorem measurable_matrix_smul {α m n : Type*} [MeasurableSpace α] {f : α → Matrix m n ℂ}
    (c : ℂ) (hf : Measurable f) : Measurable fun a => c • f a :=
  Measurable.of_eval_matrix _ fun _ _ => measurable_const.mul hf.eval_matrix

theorem measurable_matrix_sum {α ι m n : Type*} [MeasurableSpace α] (s : Finset ι)
    {f : ι → α → Matrix m n ℂ} (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a => ∑ i ∈ s, f i a := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [Matrix.sum_apply]
  exact Finset.measurable_sum _ fun i hi => (hf i hi).eval_matrix

theorem measurable_fullInverse (b E : ℝ) (n : ℕ) :
    Measurable (fullInverse b E W n) := by
  have e : fullInverse b E W n =
      fun ω => (fullMat b E (pathOfPast W n (pastCoords W n ω)))⁻¹ := by
    funext ω; rw [fullInverse, fullPathMatrix, pathAt_eq_pathOfPast]; rfl
  rw [e]
  exact measurable_matrix_inv.comp ((measurable_fullMat b E n).comp
    ((measurable_pathOfPast n).comp (measurable_pastCoords W n)))

theorem measurable_scatteringMatrix (b E : ℝ) (n : ℕ) :
    Measurable (scatteringMatrix b E W n) := by
  have hR : Measurable (boundaryResolvent b E W n) :=
    Measurable.of_eval_matrix _ fun _ _ => (measurable_fullInverse b E n).eval_matrix
  exact measurable_matrix_sub measurable_const (measurable_matrix_smul _ hR)

theorem measurable_pathCurrent (b E : ℝ) (n : ℕ) : Measurable (pathCurrent b E W n) := by
  have hS := measurable_scatteringMatrix (W := W) b E n
  exact measurable_matrix_sub (measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_conjTranspose' hS) measurable_const) hS) measurable_const

theorem measurable_tagResponse (b E : ℝ) (j k : ℕ) : Measurable (tagResponse b E W j k) := by
  have hS := (measurable_pastS (W := W) b E j k).comp (measurable_pastCoords W j)
  have e : tagResponse b E W j k = fun ω =>
      (pastS b E W j k (pastCoords W j ω))ᴴ * pastS b E W j k (pastCoords W j ω) :=
    funext (tagResponse_eq_factor b E j k)
  rw [e]
  exact measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS

theorem measurable_letterMatrix (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (j : ℕ) (ℓ : TraceLetter nT nI) :
    Measurable fun ω : GrowthPath W => letterMatrix b E k q W j ω ℓ := by
  cases ℓ with
  | current => exact measurable_pathCurrent b E j
  | tag a => exact measurable_matrix_smul _ (measurable_tagResponse b E j (k a))
  | interval a =>
    simp only [letterMatrix, intervalSource]
    exact measurable_matrix_sum _ fun i _ => measurable_matrix_smul _ (measurable_tagResponse b E j i)

theorem measurable_separatorMatrix (b E : ℝ) (j : ℕ) (s : Separator) :
    Measurable fun ω : GrowthPath W => separatorMatrix b E W j ω s := by
  have hS := measurable_scatteringMatrix (W := W) b E j
  have hS' := measurable_matrix_conjTranspose' hS
  cases s with
  | id => exact measurable_const
  | proj => exact measurable_const
  | projS => exact measurable_matrix_mul' measurable_const hS
  | sStarProj => exact measurable_matrix_mul' hS' measurable_const
  | projSProj =>
    exact measurable_matrix_mul' (measurable_matrix_mul' measurable_const hS) measurable_const
  | projSStarProj =>
    exact measurable_matrix_mul' (measurable_matrix_mul' measurable_const hS') measurable_const

theorem measurable_list_prod {α n : Type*} [MeasurableSpace α] [Fintype n] [DecidableEq n]
    (L : List (α → Matrix n n ℂ)) (hL : ∀ f ∈ L, Measurable f) :
    Measurable fun a => (L.map fun f => f a).prod := by
  induction L with
  | nil => exact measurable_const
  | cons f L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact measurable_matrix_mul' (hL f List.mem_cons_self)
      (ih fun g hg => hL g (List.mem_cons_of_mem _ hg))

theorem measurable_trace {α n : Type*} [MeasurableSpace α] [Fintype n] {M : α → Matrix n n ℂ}
    (hM : Measurable M) : Measurable fun a => (M a).trace :=
  Finset.measurable_sum _ fun _ _ => hM.eval_matrix

/-- **Every word value is measurable.** -/
theorem measurable_wordValue (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (j : ℕ) (w : TraceWord nT nI) :
    Measurable fun ω : GrowthPath W => wordValue b E k q W j ω w := by
  have h := measurable_list_prod (w.map fun x (ω : GrowthPath W) =>
    letterMatrix b E k q W j ω x.1 * separatorMatrix b E W j ω x.2) (by
      intro f hf
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hf
      exact measurable_matrix_mul' (measurable_letterMatrix b E k q j x.1)
        (measurable_separatorMatrix b E j x.2))
  simp only [List.map_map] at h
  exact measurable_trace h

/-!
## Almost-sure unitarity and the letter bounds
-/

theorem ae_scattering_unitary {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ n, scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1 ∧
      pathConductance b E W n ω = ((pathCurrent b E W n ω) ^ 2).trace.re / 2 := by
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [ae_growth_isHermitian W b, ae_isUnit_pathPencil_growth hb hW E] with ω hA hF n
  refine ⟨?_, pathConductance_eq_half_trace_sq b E n ω hA hη (hF n)⟩
  rw [scatteringMatrix_eq b E n ω (hF n)]
  exact (twoPortScattering_unitary b E _ (pathSchur_isHermitian E n ω hA) hη).2

/-- The load `L_j = 1 + 2g_j + Σ_a Tr Q_{a,j}` that bounds every ordinary word letter by letter. -/
def wordLoad (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) : ℝ :=
  1 + 2 * pathConductance b E W j ω + ∑ a, sourceTrace b E k q W j ω a

theorem nearProjection_eq_diagonal :
    nearProjection W = Matrix.diagonal fun x : Fin 2 × Fin W => if x.1 = 0 then 1 else 0 := rfl

theorem hsNorm_mul_nearProjection_le {m : Type*} [Fintype m]
    (T : Matrix m (Fin 2 × Fin W) ℂ) : hsNorm (T * nearProjection W) ≤ hsNorm T :=
  hsNorm_mul_diagonal_le T _ fun y => by split_ifs <;> simp

theorem hsNorm_mul_ordSep_le {m : Type*} [Fintype m] (b E : ℝ) (j : ℕ) (ω : GrowthPath W)
    (s : Separator) (hs : s = .id ∨ s = .proj) (T : Matrix m (Fin 2 × Fin W) ℂ) :
    hsNorm (T * separatorMatrix b E W j ω s) ≤ hsNorm T := by
  rcases hs with rfl | rfl
  · simp [separatorMatrix]
  · exact hsNorm_mul_nearProjection_le T

/-- A source letter is a positive Gram combination of the factors `P_i𝒰_j`. -/
theorem sourceLetter_gram (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) (a : Fin nT ⊕ Fin nI) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ), (∀ i ∈ s, 0 ≤ c i) ∧
      letterMatrix b E k q W j ω (sourceLetter a) = ∑ i ∈ s, ((c i : ℝ) : ℂ) •
        ((pastS b E W j i (pastCoords W j ω))ᴴ * pastS b E W j i (pastCoords W j ω)) := by
  rcases a with a | a
  · refine ⟨{k a}, fun _ => (W : ℝ)⁻¹, fun _ _ => by positivity, ?_⟩
    simp only [sourceLetter, Sum.elim_inl, letterMatrix, Finset.sum_singleton,
      tagResponse_eq_factor]
    push_cast; rfl
  · obtain ⟨s, T, hsT⟩ := hq a
    refine ⟨Finset.range j, fun i => q a (((i + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2,
      fun i _ => div_nonneg (hsT.1 _) (by positivity), ?_⟩
    simp only [sourceLetter, Sum.elim_inr, letterMatrix, intervalSource, tagResponse_eq_factor]

theorem sourceTrace_nonneg (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) (a : Fin nT ⊕ Fin nI) :
    0 ≤ sourceTrace b E k q W j ω a := by
  obtain ⟨s, c, hc, he⟩ := sourceLetter_gram b E k q hq j ω a
  rw [sourceTrace, he]; exact gram_trace_re_nonneg s c hc _

theorem sourceTrace_le_sum (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) (a : Fin nT ⊕ Fin nI) :
    sourceTrace b E k q W j ω a ≤ ∑ a', sourceTrace b E k q W j ω a' :=
  Finset.single_le_sum (fun a' _ => sourceTrace_nonneg b E k q hq j ω a') (Finset.mem_univ a)

/-- On the unitarity event: every letter has `‖A‖₂ ≤ L_j`, and every one-letter ordinary word
has `|Tr(AB)| ≤ L_j`. -/
theorem letter_bounds (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W)
    (hS : scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1)
    (hg : pathConductance b E W j ω = ((pathCurrent b E W j ω) ^ 2).trace.re / 2)
    (ℓ : TraceLetter nT nI) (s : Separator) (hs : s = .id ∨ s = .proj) :
    hsNorm (letterMatrix b E k q W j ω ℓ) ≤ wordLoad b E k q W j ω ∧
      ‖(letterMatrix b E k q W j ω ℓ * separatorMatrix b E W j ω s).trace‖ ≤
        wordLoad b E k q W j ω := by
  have hsum : 0 ≤ ∑ a, sourceTrace b E k q W j ω a :=
    Finset.sum_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a
  have hP : (nearProjection W)ᴴ = nearProjection W := nearProjection_conjTranspose
  have hPP : nearProjection W * nearProjection W = nearProjection W := nearProjection_mul_self
  have hJdef : pathCurrent b E W j ω = (scatteringMatrix b E W j ω)ᴴ * nearProjection W *
      scatteringMatrix b E W j ω - nearProjection W := rfl
  have hJ2 : hsNorm (pathCurrent b E W j ω) ^ 2 = 2 * pathConductance b E W j ω := by
    have h := current_hsNorm_sq (scatteringMatrix b E W j ω) (nearProjection W) hP
    rw [hg, hJdef, ← h, Complex.ofReal_re]; ring
  cases ℓ with
  | current =>
    have h1 : hsNorm (pathCurrent b E W j ω) ≤ 1 + hsNorm (pathCurrent b E W j ω) ^ 2 := by
      nlinarith [hsNorm_nonneg (pathCurrent b E W j ω)]
    have hg0 : 0 ≤ pathConductance b E W j ω := by nlinarith [hsNorm_nonneg (pathCurrent b E W j ω)]
    refine ⟨?_, ?_⟩
    · simp only [letterMatrix, wordLoad]; linarith
    · have hB : separatorMatrix b E W j ω s = 1 ∨ separatorMatrix b E W j ω s = nearProjection W := by
        rcases hs with rfl | rfl
        · left; rfl
        · right; rfl
      have h := current_trace_mul_le (scatteringMatrix b E W j ω) (nearProjection W) hS hP hPP _ hB
      rw [← hJdef] at h
      simp only [letterMatrix, wordLoad]
      linarith
  | tag a =>
    obtain ⟨t, c, hc, he⟩ := sourceLetter_gram b E k q hq j ω (Sum.inl a)
    have hle := sourceTrace_le_sum b E k q hq j ω (Sum.inl a)
    have hg0 : 0 ≤ pathConductance b E W j ω := by nlinarith [hsNorm_nonneg (pathCurrent b E W j ω)]
    have hst : sourceTrace b E k q W j ω (Sum.inl a) =
        (letterMatrix b E k q W j ω (.tag a)).trace.re := rfl
    simp only [sourceLetter, Sum.elim_inl] at he
    rw [hst, he] at hle
    rw [he]
    refine ⟨?_, ?_⟩
    · have := gram_hsNorm_le t c hc (fun i => pastS b E W j i (pastCoords W j ω))
      simp only [wordLoad]; linarith
    · have := gram_trace_mul_le t c hc (fun i => pastS b E W j i (pastCoords W j ω)) _
        (hsNorm_mul_ordSep_le b E j ω s hs)
      simp only [wordLoad]; linarith
  | interval a =>
    obtain ⟨t, c, hc, he⟩ := sourceLetter_gram b E k q hq j ω (Sum.inr a)
    have hle := sourceTrace_le_sum b E k q hq j ω (Sum.inr a)
    have hg0 : 0 ≤ pathConductance b E W j ω := by nlinarith [hsNorm_nonneg (pathCurrent b E W j ω)]
    have hst : sourceTrace b E k q W j ω (Sum.inr a) =
        (letterMatrix b E k q W j ω (.interval a)).trace.re := rfl
    simp only [sourceLetter, Sum.elim_inr] at he
    rw [hst, he] at hle
    rw [he]
    refine ⟨?_, ?_⟩
    · have := gram_hsNorm_le t c hc (fun i => pastS b E W j i (pastCoords W j ω))
      simp only [wordLoad]; linarith
    · have := gram_trace_mul_le t c hc (fun i => pastS b E W j i (pastCoords W j ω)) _
        (hsNorm_mul_ordSep_le b E j ω s hs)
      simp only [wordLoad]; linarith

theorem one_le_wordLoad (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W)
    (hg : pathConductance b E W j ω = ((pathCurrent b E W j ω) ^ 2).trace.re / 2) :
    1 ≤ wordLoad b E k q W j ω := by
  have hsum : 0 ≤ ∑ a, sourceTrace b E k q W j ω a :=
    Finset.sum_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a
  have hJ2 := current_hsNorm_sq (scatteringMatrix b E W j ω) (nearProjection W)
    nearProjection_conjTranspose
  have hJdef : pathCurrent b E W j ω = (scatteringMatrix b E W j ω)ᴴ * nearProjection W *
      scatteringMatrix b E W j ω - nearProjection W := rfl
  have hg0 : 0 ≤ pathConductance b E W j ω := by
    rw [hg, hJdef, ← hJ2, Complex.ofReal_re]; positivity
  simp only [wordLoad]; linarith

theorem list_prod_le_pow {L : List ℝ} {M : ℝ} (h0 : ∀ x ∈ L, 0 ≤ x) (hM : ∀ x ∈ L, x ≤ M) :
    L.prod ≤ M ^ L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.prod_cons, List.length_cons, pow_succ']
    have hx0 := h0 x List.mem_cons_self
    have hxM := hM x List.mem_cons_self
    have ih' := ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy))
      (fun y hy => hM y (List.mem_cons_of_mem _ hy))
    have hP : 0 ≤ L.prod := List.prod_nonneg fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    exact mul_le_mul hxM ih' hP (hx0.trans hxM)

/-- **Ordinary words are bounded by the load**, almost surely, at every length. -/
theorem ae_norm_wordValue_le {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {nT nI : ℕ} (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ) (w : TraceWord nT nI),
      IsOrdinaryWord w → ‖wordValue b E k q W j ω w‖ ≤ wordLoad b E k q W j ω ^ w.length := by
  filter_upwards [ae_scattering_unitary hb hE1 hE2 hW] with ω hω j k w hw
  obtain ⟨hS, hg⟩ := hω j
  have hb := letter_bounds b E k q hq j ω hS hg
  rcases w with _ | ⟨x, w⟩
  · exact absurd rfl hw.1
  rcases w with _ | ⟨y, w⟩
  · simp only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.mul_one, List.length_singleton, pow_one]
    exact (hb x.1 x.2 (hw.2 x List.mem_cons_self)).2
  · rw [wordValue]
    refine (norm_trace_list_prod_le _ (by simp)).trans ?_
    rw [List.map_map]
    have hlen : (x :: y :: w).length =
        ((x :: y :: w).map (hsNorm ∘ fun x => letterMatrix b E k q W j ω x.1 *
          separatorMatrix b E W j ω x.2)).length := by simp
    rw [hlen]
    refine list_prod_le_pow (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hz; exact hsNorm_nonneg _
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
      have hus := hw.2 u hu
      exact (hsNorm_mul_ordSep_le b E j ω u.2 hus _).trans (hb u.1 u.2 hus).1

end BlockBand.SourceProcess.FullSourceStops
