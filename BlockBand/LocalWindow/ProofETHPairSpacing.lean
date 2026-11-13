module

public import BlockBand.LocalWindow.ProofETHPairCentre
public import BlockBand.LocalWindow.ProofETHInputs

/-!
# A typical spacing of size `O(1/N)` on the window

On a root rectangle, a typical spacing of the branch can be chosen of size `O(1/N)` on the
window, for part (ii) of the physical local-window lemma.

## Main results

* `dysonRoot_im_sq_le`: `s (Im m)² ≤ 1` at every root (`Im z ≥ 0`).
* `exists_small_spacing`: a typical spacing with `η_f(x) ≤ π/(N v₀)` on the window.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open MeasureTheory Matrix Set Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section Root

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem frob_one : frob (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  unfold frob
  have : ∀ a : ι, ∑ b, ‖(1 : Matrix ι ι ℂ) a b‖ ^ 2 = 1 := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb])
      (by simp)]
    simp
  simp [this]

/-- `s (Im m)² ≤ 1` at a Dyson root (`Im z ≥ 0`, `s > 0`, Hermitian `F`). -/
theorem dysonRoot_im_sq_le [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (hroot : IsDysonRoot F s z m) :
    s * m.im ^ 2 ≤ 1 := by
  have hm := hroot.1
  set w := z + (s : ℂ) * m
  have hw : 0 < w.im := dysonRoot_w_im_pos hs hz hm
  have hwge : s * m.im ≤ w.im := dysonRoot_w_im hz
  have heq := dysonRoot_im_eq hF hs hz hroot
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hfrob : frob (F - w • (1 : Matrix ι ι ℂ))⁻¹ ≤ (|w.im|⁻¹) ^ 2 * Fintype.card ι := by
    have h := frob_mul_left_le (sqNorm_resolvent_le hF hw.ne') (1 : Matrix ι ι ℂ)
    rwa [Matrix.mul_one, frob_one] at h
  rw [abs_of_pos hw] at hfrob
  -- `Im m · N = Im w · frob ≤ N / Im w`
  have h1 : m.im * w.im ≤ 1 := by
    have h2 : m.im * Fintype.card ι ≤ w.im * ((w.im⁻¹) ^ 2 * Fintype.card ι) := by
      rw [heq]; exact mul_le_mul_of_nonneg_left hfrob hw.le
    have h3 : w.im * ((w.im⁻¹) ^ 2 * Fintype.card ι) = w.im⁻¹ * Fintype.card ι := by
      field_simp
    rw [h3] at h2
    have h4 : m.im ≤ w.im⁻¹ := le_of_mul_le_mul_right h2 hN
    calc m.im * w.im ≤ w.im⁻¹ * w.im := mul_le_mul_of_nonneg_right h4 hw.le
      _ = 1 := inv_mul_cancel₀ hw.ne'
  nlinarith [mul_le_mul_of_nonneg_left hwge hm.le]

end Root

variable {p : Parameters} {i : ZMod p.n}

/-- The spacing function `g(E, η) = N η ρ(E + iη)` of a branch. -/
def spacingFn {s : ℝ} {F : CEH.SourceHermitian (2 * p.W)} (M : CEH.MDEBranch (Real.sqrt s) F)
    (E η : ℝ) : ℝ :=
  ((2 * p.W : ℕ) : ℝ) * η * CEH.sourceDensity (M.matrix ((E : ℂ) + (η : ℂ) * Complex.I))

theorem continuousOn_spacingFn {s : ℝ} {F : CEH.SourceHermitian (2 * p.W)}
    (M : CEH.MDEBranch (Real.sqrt s) F) {η₁ : ℝ} (hη₁ : 0 < η₁) (I : Set ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => spacingFn M q.1 q.2) (I ×ˢ Ici η₁) := by
  unfold spacingFn CEH.sourceDensity CEH.normalizedTrace
  have hz : Continuous fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by fun_prop
  have hM : ContinuousOn (fun q : ℝ × ℝ => M.matrix ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))
      (I ×ˢ Ici η₁) := by
    refine M.continuous_off_real.comp hz.continuousOn fun q hq => ?_
    have : ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I).im = q.2 := by simp
    show ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I).im ≠ 0
    rw [this]
    exact (hη₁.trans_le hq.2).ne'
  have htr : Continuous fun A : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ => A.trace :=
    continuous_id.matrix_trace
  refine ContinuousOn.mul (by fun_prop) ?_
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.abs ?_
  refine Complex.continuous_im.comp_continuousOn ?_
  refine ContinuousOn.mul continuousOn_const ?_
  exact htr.comp_continuousOn hM

/-- **A typical spacing of size `O(1/N)` on the window** (for the external ETH theorem).
Under `MDEBranchIdentification` (and the contract, for the values off the window): for
`s > 0`, Hermitian pair `K`, a branch `M` of `K` (reindexed) at `√s`, `2W ≥ 4`, a root
rectangle `Im m ≥ v₀ > 0` at every `x + iη`, `|x - E₀| ≤ r`, `0 < η ≤ 1`, and `N v₀ > π`
(`N = 2W`), some typical spacing of `M` satisfies `η_f(x) ≤ π/(N v₀)` for `|x - E₀| ≤ r`. -/
theorem exists_small_spacing (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) {s : ℝ} (hs : 0 < s) {K : PairMatrix p i}
    (hK : K.IsHermitian) (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK))
    (hN4 : 4 ≤ 2 * p.W) {E₀ r v₀ : ℝ} (hv₀ : 0 < v₀)
    (hrect : ∀ x : ℝ, |x - E₀| ≤ r → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ m : ℂ, IsDysonRoot K s ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im)
    (hNv : Real.pi < ((2 * p.W : ℕ) : ℝ) * v₀) :
    ∃ spacing : CEH.TypicalSpacing M,
      ∀ x : ℝ, |x - E₀| ≤ r → spacing.eta x ≤ Real.pi / (((2 * p.W : ℕ) : ℝ) * v₀) := by
  classical
  have hNpos : 0 < 2 * p.W := Nat.mul_pos two_pos p.W_pos
  have hNr : (0 : ℝ) < ((2 * p.W : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hpi := Real.pi_pos
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  obtain ⟨native⟩ := exists_typicalSpacing inputs hAd hN4 (Real.sqrt_pos.mpr hs) M
  set N : ℝ := ((2 * p.W : ℕ) : ℝ) with hNdef
  set I : Set ℝ := Icc (E₀ - r) (E₀ + r) with hIdef
  have hmemI : ∀ x, x ∈ I ↔ |x - E₀| ≤ r := by
    intro x; rw [hIdef, mem_Icc, abs_le]; constructor <;> intro h <;> constructor <;> linarith
  set g := fun E η : ℝ => spacingFn M E η with hg
  -- the density at a root
  have hdens : ∀ x : ℝ, x ∈ I → ∀ η : ℝ, 0 < η → η ≤ 1 →
      v₀ / Real.pi ≤ CEH.sourceDensity (M.matrix ((x : ℂ) + (η : ℂ) * Complex.I)) ∧
      CEH.sourceDensity (M.matrix ((x : ℂ) + (η : ℂ) * Complex.I)) ≤
        (Real.sqrt s)⁻¹ / Real.pi := by
    intro x hx η hη hη1
    obtain ⟨m, hroot, hv⟩ := hrect x ((hmemI x).mp hx) η hη hη1
    have hz : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
    have hrootF := (isDysonRoot_reindex (pairEquiv p i) K s _ m).mpr hroot
    obtain ⟨hm, heq⟩ := (isDysonRoot_iff _ s _ m).mp hrootF
    obtain ⟨-, htr⟩ := BlockBand.LocalWindow.ProofCertificate.branch_eq_of_root hMDE hNpos hs
      (toSourceHermitian K hK) M hz hm heq
    unfold CEH.sourceDensity
    rw [htr, abs_of_pos hm]
    refine ⟨div_le_div_of_nonneg_right hv hpi.le, div_le_div_of_nonneg_right ?_ hpi.le⟩
    have hsq := dysonRoot_im_sq_le hK hs hz.le hroot
    have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hy2 : (m.im * Real.sqrt s) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hs.le]; linarith [hsq]
    have hy : m.im * Real.sqrt s ≤ 1 := by nlinarith [hy2, mul_pos hm hsqrt]
    calc m.im = m.im * Real.sqrt s * (Real.sqrt s)⁻¹ := by field_simp
      _ ≤ 1 * (Real.sqrt s)⁻¹ := mul_le_mul_of_nonneg_right hy (by positivity)
      _ = _ := one_mul _
  -- the lower height `η₁`
  set η₁ := min 1 (Real.pi * Real.sqrt s / (2 * N)) with hη₁def
  have hη₁ : 0 < η₁ := lt_min one_pos (by positivity)
  have hη₁1 : η₁ ≤ 1 := min_le_left _ _
  have hlow : ∀ x ∈ I, g x η₁ ≤ 1 / 2 := by
    intro x hx
    have h := (hdens x hx η₁ hη₁ hη₁1).2
    simp only [hg, spacingFn]
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    calc N * η₁ * CEH.sourceDensity (M.matrix ((x : ℂ) + (η₁ : ℂ) * Complex.I))
        ≤ N * (Real.pi * Real.sqrt s / (2 * N)) * ((Real.sqrt s)⁻¹ / Real.pi) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (min_le_right _ _) hNr.le) h
            (CEH.sourceDensity_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp
  have hhigh : ∀ x ∈ I, 1 < g x 1 := by
    intro x hx
    have h := (hdens x hx 1 one_pos le_rfl).1
    simp only [hg, spacingFn]
    calc 1 < N * 1 * (v₀ / Real.pi) := by rw [mul_one, mul_div_assoc', lt_div_iff₀ hpi]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  -- continuity in `η` and jointly
  have hcont2 : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) (I ×ˢ Ici η₁) :=
    continuousOn_spacingFn M hη₁ I
  have hcont1 : ∀ x ∈ I, ContinuousOn (g x) (Icc η₁ 1) := by
    intro x hx
    have h := hcont2.comp (Continuous.continuousOn (f := fun η : ℝ => (x, η)) (by fun_prop))
      (fun η (hη : η ∈ Icc η₁ 1) => (⟨hx, hη.1⟩ : (x, η) ∈ I ×ˢ Ici η₁))
    exact h
  -- the least solution
  set S : ℝ → Set ℝ := fun x => {η | η ∈ Icc η₁ 1 ∧ 1 ≤ g x η} with hSdef
  set ηs : ℝ → ℝ := fun x => sInf (S x) with hηsdef
  have hSclosed : ∀ x ∈ I, IsClosed (S x) := by
    intro x hx
    exact (hcont1 x hx).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : ∀ x ∈ I, (S x).Nonempty := fun x hx => ⟨1, ⟨hη₁1, le_rfl⟩, (hhigh x hx).le⟩
  have hSbdd : ∀ x, BddBelow (S x) := fun x => ⟨η₁, fun η hη => hη.1.1⟩
  have hηs_mem : ∀ x ∈ I, ηs x ∈ S x := fun x hx =>
    (hSclosed x hx).csInf_mem (hSne x hx) (hSbdd x)
  have hηs_eq : ∀ x ∈ I, g x (ηs x) = 1 := by
    intro x hx
    have hm := hηs_mem x hx
    refine le_antisymm ?_ hm.2
    by_contra hlt
    push Not at hlt
    have hab : η₁ ≤ ηs x := hm.1.1
    have hc : ContinuousOn (g x) (Icc η₁ (ηs x)) :=
      (hcont1 x hx).mono (Icc_subset_Icc le_rfl hm.1.2)
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc hab hc
      ⟨(hlow x hx).trans (by norm_num), hlt.le⟩
    have hcS : c ∈ S x := ⟨⟨hc1.1, hc1.2.trans hm.1.2⟩, hc2.ge⟩
    have hle : ηs x ≤ c := csInf_le (hSbdd x) hcS
    have hceq : c = ηs x := le_antisymm hc1.2 hle
    rw [hceq] at hc2
    linarith
  have hηs_pos : ∀ x ∈ I, 0 < ηs x := fun x hx => hη₁.trans_le (hηs_mem x hx).1.1
  -- the spacing
  set eta : ℝ → ℝ := fun x => if x ∈ I then ηs x else native.eta x with hetadef
  have hmeas : Measurable eta := by
    refine measurable_of_Iic fun t => ?_
    have hset : eta ⁻¹' Iic t = (Prod.fst '' ({q : ℝ × ℝ | q ∈ I ×ˢ Icc η₁ 1 ∧ 1 ≤ g q.1 q.2} ∩
        (univ ×ˢ Iic t))) ∪ (Iᶜ ∩ native.eta ⁻¹' Iic t) := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_union, mem_image, mem_inter_iff, mem_prod,
        mem_univ, true_and, Prod.exists, exists_and_right, exists_eq_right, mem_compl_iff]
      by_cases hx : x ∈ I
      · simp only [hetadef, hx, ↓reduceIte, not_true_eq_false, false_and, or_false]
        constructor
        · intro h
          exact ⟨ηs x, ⟨⟨hx, (hηs_mem x hx).1⟩, (hηs_mem x hx).2⟩, h⟩
        · rintro ⟨η, ⟨⟨-, hη⟩, hg1⟩, hηt⟩
          exact (csInf_le (hSbdd x) ⟨hη, hg1⟩).trans hηt
      · simp only [hetadef, hx, ↓reduceIte, not_false_eq_true, true_and]
        constructor
        · intro h; exact Or.inr h
        · rintro (⟨η, ⟨⟨hxI, -⟩, -⟩, -⟩ | h)
          · exact absurd hxI hx
          · exact h
    rw [hset]
    refine MeasurableSet.union ?_ ((measurableSet_Icc.compl).inter
      (native.measurable_eta measurableSet_Iic))
    refine IsClosed.measurableSet (IsCompact.isClosed ?_)
    refine IsCompact.image ?_ continuous_fst
    refine IsCompact.inter_right ?_ (isClosed_univ.prod isClosed_Iic)
    have hK2 : IsCompact (I ×ˢ Icc η₁ 1) := isCompact_Icc.prod isCompact_Icc
    refine hK2.of_isClosed_subset ?_ (fun q hq => hq.1)
    have hc : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) (I ×ˢ Icc η₁ 1) :=
      hcont2.mono (prod_mono le_rfl Icc_subset_Ici_self)
    exact hc.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Ici
  refine ⟨⟨eta, fun x => ?_, hmeas, fun x => ?_⟩, fun x hx => ?_⟩
  · by_cases hx : x ∈ I
    · simp only [hetadef, hx, ↓reduceIte]; exact hηs_pos x hx
    · simp only [hetadef, hx, ↓reduceIte]; exact native.positive x
  · by_cases hx : x ∈ I
    · simp only [hetadef, hx, ↓reduceIte]
      have := hηs_eq x hx
      simpa [hg, spacingFn] using this
    · simp only [hetadef, hx, ↓reduceIte]; exact native.equation x
  · have hxI : x ∈ I := (hmemI x).mpr hx
    simp only [hetadef, hxI, ↓reduceIte]
    have hm := hηs_mem x hxI
    have h1 := hηs_eq x hxI
    have hd := (hdens x hxI (ηs x) (hηs_pos x hxI) hm.1.2).1
    simp only [hg, spacingFn] at h1
    have h3 : 0 ≤ N * ηs x := mul_nonneg hNr.le (hηs_pos x hxI).le
    have h4 : N * ηs x * (v₀ / Real.pi) ≤ 1 := by
      rw [← h1]; exact mul_le_mul_of_nonneg_left hd h3
    rw [le_div_iff₀ (mul_pos hNr hv₀)]
    have h5 : N * ηs x * v₀ ≤ Real.pi := by
      rw [mul_div_assoc', div_le_one hpi] at h4; exact h4
    nlinarith

end BlockBand.LocalWindow.ProofETH
