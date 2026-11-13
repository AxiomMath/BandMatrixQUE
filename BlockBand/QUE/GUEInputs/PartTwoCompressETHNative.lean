module

public import BlockBand.LocalWindow.ProofPartTwoCompressETHNative
public import BlockBand.QUE.GUEInputs.Fields

/-!
# A typical spacing in dimension `N` (GUE inputs)

`nat_exists_small_spacing`: the typical spacing bound `η_f(x) ≤ π/(N v₀)` on the window for a
Hermitian deformation of dimension `N ≥ 4`.

The hypotheses are `SpacingExists` and `MDEBranchIdentification`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo.GUEInputs

open MeasureTheory Matrix Set Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section

variable {N : ℕ}

/-- **A typical spacing of size `O(1/N)` on the window, dimension `N`** (from the eigenstate
thermalization (ETH) input; the analogue of `exists_small_spacing`). Under
`MDEBranchIdentification` and `SpacingExists`: for `s > 0`, a Hermitian deformation `F` of dimension
`N ≥ 4`, a branch `M` of `F` at `√s`, a root rectangle `Im m ≥ v₀ > 0` at every `x + iη`,
`|x - E₀| ≤ r`, `0 < η ≤ 1`, and `N v₀ > π`, some typical spacing of `M` satisfies
`η_f(x) ≤ π/(N v₀)` for `|x - E₀| ≤ r`. -/
theorem nat_exists_small_spacing (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) {s : ℝ} (hs : 0 < s) {F : CEH.SourceHermitian N}
    (M : CEH.MDEBranch (Real.sqrt s) F) (hN4 : 4 ≤ N) {E₀ r v₀ : ℝ} (hv₀ : 0 < v₀)
    (hrect : ∀ x : ℝ, |x - E₀| ≤ r → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ m : ℂ, IsDysonRoot F.1 s ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im)
    (hNv : Real.pi < (N : ℝ) * v₀) :
    ∃ spacing : CEH.TypicalSpacing M,
      ∀ x : ℝ, |x - E₀| ≤ r → spacing.eta x ≤ Real.pi / ((N : ℝ) * v₀) := by
  classical
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hpi := Real.pi_pos
  have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  obtain ⟨native⟩ := hSp hN4 (Real.sqrt_pos.mpr hs) M
  set Nr : ℝ := (N : ℝ) with hNdef
  set I : Set ℝ := Icc (E₀ - r) (E₀ + r) with hIdef
  have hmemI : ∀ x, x ∈ I ↔ |x - E₀| ≤ r := by
    intro x; rw [hIdef, mem_Icc, abs_le]; constructor <;> intro h <;> constructor <;> linarith
  set g := fun E η : ℝ => natSpacingFn M E η with hg
  -- the density at a root
  have hdens : ∀ x : ℝ, x ∈ I → ∀ η : ℝ, 0 < η → η ≤ 1 →
      v₀ / Real.pi ≤ CEH.sourceDensity (M.matrix ((x : ℂ) + (η : ℂ) * Complex.I)) ∧
      CEH.sourceDensity (M.matrix ((x : ℂ) + (η : ℂ) * Complex.I)) ≤
        (Real.sqrt s)⁻¹ / Real.pi := by
    intro x hx η hη hη1
    obtain ⟨m, hroot, hv⟩ := hrect x ((hmemI x).mp hx) η hη hη1
    have hz : 0 < ((x : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
    obtain ⟨hm, heq⟩ := (isDysonRoot_iff _ s _ m).mp hroot
    obtain ⟨-, htr⟩ := BlockBand.LocalWindow.ProofCertificate.branch_eq_of_root hMDE hNpos hs
      F M hz hm heq
    unfold CEH.sourceDensity
    rw [htr, abs_of_pos hm]
    refine ⟨div_le_div_of_nonneg_right hv hpi.le, div_le_div_of_nonneg_right ?_ hpi.le⟩
    have hsq := dysonRoot_im_sq_le F.2 hs hz.le hroot
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hy2 : (m.im * Real.sqrt s) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hs.le]; linarith [hsq]
    have hy : m.im * Real.sqrt s ≤ 1 := by nlinarith [hy2, mul_pos hm hsqrt]
    calc m.im = m.im * Real.sqrt s * (Real.sqrt s)⁻¹ := by field_simp
      _ ≤ 1 * (Real.sqrt s)⁻¹ := mul_le_mul_of_nonneg_right hy (by positivity)
      _ = _ := one_mul _
  -- the lower height `η₁`
  set η₁ := min 1 (Real.pi * Real.sqrt s / (2 * Nr)) with hη₁def
  have hη₁ : 0 < η₁ := lt_min one_pos (by positivity)
  have hη₁1 : η₁ ≤ 1 := min_le_left _ _
  have hlow : ∀ x ∈ I, g x η₁ ≤ 1 / 2 := by
    intro x hx
    have h := (hdens x hx η₁ hη₁ hη₁1).2
    simp only [hg, natSpacingFn]
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    calc Nr * η₁ * CEH.sourceDensity (M.matrix ((x : ℂ) + (η₁ : ℂ) * Complex.I))
        ≤ Nr * (Real.pi * Real.sqrt s / (2 * Nr)) * ((Real.sqrt s)⁻¹ / Real.pi) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (min_le_right _ _) hNr.le) h
            (CEH.sourceDensity_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp
  have hhigh : ∀ x ∈ I, 1 < g x 1 := by
    intro x hx
    have h := (hdens x hx 1 one_pos le_rfl).1
    simp only [hg, natSpacingFn]
    calc 1 < Nr * 1 * (v₀ / Real.pi) := by
          rw [mul_one, mul_div_assoc', lt_div_iff₀ hpi]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  -- continuity in `η` and jointly
  have hcont2 : ContinuousOn (fun q : ℝ × ℝ => g q.1 q.2) (I ×ˢ Ici η₁) :=
    continuousOn_natSpacingFn M hη₁ I
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
      simpa [hg, natSpacingFn] using this
    · simp only [hetadef, hx, ↓reduceIte]; exact native.equation x
  · have hxI : x ∈ I := (hmemI x).mpr hx
    simp only [hetadef, hxI, ↓reduceIte]
    have hm := hηs_mem x hxI
    have h1 := hηs_eq x hxI
    have hd := (hdens x hxI (ηs x) (hηs_pos x hxI) hm.1.2).1
    simp only [hg, natSpacingFn] at h1
    have h3 : 0 ≤ Nr * ηs x := mul_nonneg hNr.le (hηs_pos x hxI).le
    have h4 : Nr * ηs x * (v₀ / Real.pi) ≤ 1 := by
      rw [← h1]; exact mul_le_mul_of_nonneg_left hd h3
    rw [le_div_iff₀ (mul_pos hNr hv₀)]
    have h5 : Nr * ηs x * v₀ ≤ Real.pi := by
      rw [mul_div_assoc', div_le_one hpi] at h4; exact h4
    nlinarith

end

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
