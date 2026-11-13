module

public import BlockBand.LocalWindow.ProofETHPairSpacing

/-!
# The native-`N` spacing and centre move

`ProofETH.exists_small_spacing` and `ProofETH.ethCentre_close` are stated for a pair deformation
(dimension `2W`, reindexed by `toSourceHermitian`). This file proves the same statements for a
deformation `F : CEH.SourceHermitian N` of any dimension `N`, with the same proofs.

## Main results

* `natSpacingFn`, `continuousOn_natSpacingFn`: `g(E, η) = N η ρ(E + iη)`.
* **`nat_exists_small_spacing`**: on a root rectangle (`Im m ≥ v₀` up to height `1`) with
  `N ≥ 4`, `N v₀ > π`, a typical spacing with `η_f(x) ≤ π/(N v₀)` on the window.
* `natEthCentre` (the ETH centre `⟨Γ(x + iN^ξ η_f(x)) J⟩` of `ethBadEvent`), `nativeCentre`
  (the real-axis centre `N⁻¹ Tr(J s RR*)`, `R = (F - x - s m(x))⁻¹`, `m = freshDyson`).
* **`nat_ethCentre_close`**: `|natEthCentre - nativeCentre(x₀)| ≤ Im z/(s Im m) +
  2|w - w₀|/(s Im m₀)`.
* **`nat_ethCentre_sub_nativeCentre_le`**: at `x₀ = x` on a root rectangle,
  `≤ Im z (3 + 1/(s v₀²))/(s v₀)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
## The typical spacing
-/

/-- The spacing function `g(E, η) = N η ρ(E + iη)` of a branch of dimension `N`. -/
def natSpacingFn {s : ℝ} {F : CEH.SourceHermitian N} (M : CEH.MDEBranch (Real.sqrt s) F)
    (E η : ℝ) : ℝ :=
  (N : ℝ) * η * CEH.sourceDensity (M.matrix ((E : ℂ) + (η : ℂ) * Complex.I))

theorem continuousOn_natSpacingFn {s : ℝ} {F : CEH.SourceHermitian N}
    (M : CEH.MDEBranch (Real.sqrt s) F) {η₁ : ℝ} (hη₁ : 0 < η₁) (I : Set ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => natSpacingFn M q.1 q.2) (I ×ˢ Ici η₁) := by
  unfold natSpacingFn CEH.sourceDensity CEH.normalizedTrace
  have hz : Continuous fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by fun_prop
  have hM : ContinuousOn (fun q : ℝ × ℝ => M.matrix ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))
      (I ×ˢ Ici η₁) := by
    refine M.continuous_off_real.comp hz.continuousOn fun q hq => ?_
    have : ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I).im = q.2 := by simp
    show ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I).im ≠ 0
    rw [this]
    exact (hη₁.trans_le hq.2).ne'
  have htr : Continuous fun A : Matrix (Fin N) (Fin N) ℂ => A.trace :=
    continuous_id.matrix_trace
  refine ContinuousOn.mul (by fun_prop) ?_
  refine ContinuousOn.div_const ?_ _
  refine ContinuousOn.abs ?_
  refine Complex.continuous_im.comp_continuousOn ?_
  refine ContinuousOn.mul continuousOn_const ?_
  exact htr.comp_continuousOn hM

/-- **A typical spacing of size `O(1/N)` on the window, dimension `N`**
(for the external ETH theorem; the analogue of `ProofETH.exists_small_spacing`). Under `MDEBranchIdentification` (and the contract, for
the values off the window): for `s > 0`, a Hermitian deformation `F` of dimension
`N ≥ 4`, a branch `M` of `F` at `√s`, a root rectangle `Im m ≥ v₀ > 0` at every `x + iη`,
`|x - E₀| ≤ r`, `0 < η ≤ 1`, and `N v₀ > π`, some typical spacing of `M` satisfies
`η_f(x) ≤ π/(N v₀)` for `|x - E₀| ≤ r`. -/
theorem nat_exists_small_spacing (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
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
  obtain ⟨native⟩ := exists_typicalSpacing inputs hAd hN4 (Real.sqrt_pos.mpr hs) M
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

/-!
## The centres
-/

/-- The ETH centre `⟨Γ(x + i N^ξ η_f(x)) J⟩` of the external ETH theorem for a
observable `J` (the centre inside `Inputs.ethBadEvent`). -/
def natEthCentre {s : ℝ} {F : CEH.SourceHermitian N} (M : CEH.MDEBranch (Real.sqrt s) F)
    (spacing : CEH.TypicalSpacing M) (ξ : ℝ) (J : CEH.SourceMatrix N) (x : ℝ) : ℂ :=
  CEH.normalizedTrace (CEH.gammaMatrix (M.matrix (CEH.inflatedSpectralPoint spacing ξ x)) * J)

/-- The real-axis window centre `N⁻¹ Tr(J Γ(x))`, `Γ = s RR*`,
`R = (F - x - s m(x))⁻¹`, `m(x) = freshDyson F s x` (`j_B(E, λ)` in dimension
`N`; at `N = 2W - 1` it is `ProofPartTwo.compressCentre`). -/
def nativeCentre (J F : Matrix (Fin N) (Fin N) ℂ) (s x : ℝ) : ℂ :=
  ((N : ℕ) : ℂ)⁻¹ * (J * ((s : ℂ) •
    ((F - ((x : ℂ) + (s : ℂ) * freshDyson F s x) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *
      ((F - ((x : ℂ) + (s : ℂ) * freshDyson F s x) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᴴ))).trace

theorem nat_inflatedSpectralPoint_im {s : ℝ} {F : CEH.SourceHermitian N}
    {M : CEH.MDEBranch (Real.sqrt s) F} (spacing : CEH.TypicalSpacing M) (ξ x : ℝ) :
    (CEH.inflatedSpectralPoint spacing ξ x).im = (N : ℝ) ^ ξ * spacing.eta x := by
  unfold CEH.inflatedSpectralPoint
  simp

theorem nat_inflatedSpectralPoint_im_pos {s : ℝ} {F : CEH.SourceHermitian N}
    {M : CEH.MDEBranch (Real.sqrt s) F} (hN : 0 < N) (spacing : CEH.TypicalSpacing M)
    (ξ x : ℝ) : 0 < (CEH.inflatedSpectralPoint spacing ξ x).im := by
  rw [nat_inflatedSpectralPoint_im]
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact mul_pos (Real.rpow_pos_of_pos hN' _) (spacing.positive x)

/-- **ETH centre versus the real-axis centre, dimension `N`** (the
centre of the external ETH theorem and `j_B`; the analogue of `ProofETH.ethCentre_close`). Under `MDEBranchIdentification`, for `N > 0`, `s > 0`, a native
Hermitian `F`, any branch `M` of `F` at `λ = √s`, a typical spacing, a contraction `J`
(`‖J‖ ≤ 1`), a Dyson root `m` of `F` at `z = x + i N^ξ η_f(x)` and a root `m₀` of `F` at the
real `x₀`: `|⟨Γ(z) J⟩ - nativeCentre J F s x₀| ≤ Im z/(s Im m) + 2|w - w₀|/(s Im m₀)`,
`w = z + s m`, `w₀ = x₀ + s m₀`. -/
theorem nat_ethCentre_close (hMDE : MDEBranchIdentification) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    {F : CEH.SourceHermitian N} (M : CEH.MDEBranch (Real.sqrt s) F)
    (spacing : CEH.TypicalSpacing M) (ξ : ℝ) {J : CEH.SourceMatrix N} (hJ : ‖J‖ ≤ 1)
    {x x₀ : ℝ} {m m₀ : ℂ}
    (hroot : IsDysonRoot F.1 s (CEH.inflatedSpectralPoint spacing ξ x) m)
    (hroot₀ : IsDysonRoot F.1 s (x₀ : ℂ) m₀) :
    ‖natEthCentre M spacing ξ J x - nativeCentre J F.1 s x₀‖ ≤
      (CEH.inflatedSpectralPoint spacing ξ x).im / (s * m.im) +
        2 * ‖(CEH.inflatedSpectralPoint spacing ξ x + (s : ℂ) * m) - ((x₀ : ℂ) + (s : ℂ) * m₀)‖ /
          (s * m₀.im) := by
  have : NeZero N := ⟨hN.ne'⟩
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set z := CEH.inflatedSpectralPoint spacing ξ x with hzdef
  have hz : 0 < z.im := nat_inflatedSpectralPoint_im_pos hN spacing ξ x
  obtain ⟨hm, heq⟩ := (isDysonRoot_iff _ s z m).mp hroot
  obtain ⟨hMz, htr⟩ := BlockBand.LocalWindow.ProofCertificate.branch_eq_of_root hMDE hN hs
    F M hz hm heq
  set w := z + (s : ℂ) * m with hw
  have hwim : 0 < w.im := dysonRoot_w_im_pos hs hz.le hm
  have htr' : CEH.normalizedTrace (F.1 - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = m := by
    rw [← hMz]; exact htr
  have hΓ := gammaMatrix_eq F.2 hwim.ne' htr'
  set R := (F.1 - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ with hR
  have hcentre : natEthCentre M spacing ξ J x =
      ((N : ℕ) : ℂ)⁻¹ * (((w.im / m.im : ℝ) : ℂ) * (R * Rᴴ * J).trace) := by
    unfold natEthCentre
    rw [hMz, hΓ, smul_mul_assoc]
    unfold CEH.normalizedTrace
    rw [trace_smul, smul_eq_mul]
  have hfd : freshDyson F.1 s x₀ = m₀ := freshDyson_eq_of_isDysonRoot F.2 hs (by simp) hroot₀
  set R₀ := (F.1 - ((x₀ : ℂ) + (s : ℂ) * m₀) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ with hR₀
  have hwin : nativeCentre J F.1 s x₀ = ((N : ℕ) : ℂ)⁻¹ * ((s : ℂ) * (R₀ * R₀ᴴ * J).trace) := by
    unfold nativeCentre
    rw [hfd, mul_smul_comm, trace_smul, smul_eq_mul, trace_mul_comm J]
  have hJ' : ∀ v : Fin N → ℂ, sqNorm (Jᴴ *ᵥ v) ≤ 1 ^ 2 * sqNorm v := fun v =>
    sqNorm_mulVec_le_of_opNorm_le (by rw [Matrix.l2_opNorm_conjTranspose]; exact hJ) v
  have hcc := centre_close F.2 hs (x₀ := x₀) hz.le hroot hroot₀ hJ'
  rw [Fintype.card_fin] at hcc
  rw [hcentre, hwin, ← mul_sub, norm_mul]
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnorm : ‖((N : ℕ) : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnorm]
  calc (N : ℝ)⁻¹ * ‖((w.im / m.im : ℝ) : ℂ) * (R * Rᴴ * J).trace -
        (s : ℂ) * (R₀ * R₀ᴴ * J).trace‖
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) * (z.im / (s * m.im) +
          2 * ‖w - ((x₀ : ℂ) + (s : ℂ) * m₀)‖ / (s * m₀.im))) :=
        mul_le_mul_of_nonneg_left hcc (inv_nonneg.mpr hN0.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul]

/-- The centre move of `nat_ethCentre_close` at `x₀ = x` on a root rectangle:
`‖natEthCentre - nativeCentre‖ ≤ Im z (3 + 1/(s v₀²))/(s v₀)`, `z = x + iN^ξ η_f(x)`
(the analogue of `ProofPartTwo.ethCentre_sub_pairCentre_le`). -/
theorem nat_ethCentre_sub_nativeCentre_le (hMDE : MDEBranchIdentification) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {F : CEH.SourceHermitian N} (M : CEH.MDEBranch (Real.sqrt s) F)
    (spacing : CEH.TypicalSpacing M) (ξ : ℝ) {J : CEH.SourceMatrix N} (hJ : ‖J‖ ≤ 1)
    {x : ℝ} {m m₀ : ℂ} {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hroot : IsDysonRoot F.1 s (CEH.inflatedSpectralPoint spacing ξ x) m) (hm : v₀ ≤ m.im)
    (hroot₀ : IsDysonRoot F.1 s (x : ℂ) m₀) (hm₀ : v₀ ≤ m₀.im) :
    ‖natEthCentre M spacing ξ J x - nativeCentre J F.1 s x‖ ≤
      (CEH.inflatedSpectralPoint spacing ξ x).im * ((3 + 1 / (s * v₀ ^ 2)) / (s * v₀)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set z := CEH.inflatedSpectralPoint spacing ξ x with hz
  have hzim : 0 < z.im := nat_inflatedSpectralPoint_im_pos hN spacing ξ x
  have hc := nat_ethCentre_close hMDE hN hs M spacing ξ hJ hroot hroot₀
  have hzx : z - (x : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
    rw [hz]; unfold CEH.inflatedSpectralPoint; simp
  have hzx' : ‖z - (x : ℂ)‖ = z.im := by
    rw [hzx, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hzim]
  have hlip := root_lipschitz F.2 hs hzim.le (by simp) hroot hroot₀ hv₀ hm hm₀
  rw [hzx'] at hlip
  have hw : ‖(z + (s : ℂ) * m) - ((x : ℂ) + (s : ℂ) * m₀)‖ ≤ z.im * (1 + s * rootLip s v₀) := by
    have e : (z + (s : ℂ) * m) - ((x : ℂ) + (s : ℂ) * m₀) = (z - (x : ℂ)) + (s : ℂ) * (m - m₀) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [hzx', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    nlinarith
  have hsr : s * rootLip s v₀ = 1 / (2 * (s * v₀ ^ 2)) := by
    unfold rootLip; field_simp
  have hsv : 0 < s * v₀ := mul_pos hs hv₀
  have h1 : z.im / (s * m.im) ≤ z.im / (s * v₀) :=
    div_le_div_of_nonneg_left hzim.le hsv (mul_le_mul_of_nonneg_left hm hs.le)
  have h2 : 2 * ‖(z + (s : ℂ) * m) - ((x : ℂ) + (s : ℂ) * m₀)‖ / (s * m₀.im) ≤
      2 * (z.im * (1 + s * rootLip s v₀)) / (s * v₀) := by
    have hrl := mul_nonneg hs.le (rootLip_nonneg s v₀)
    refine div_le_div₀ (mul_nonneg zero_le_two (mul_nonneg hzim.le (by linarith)))
      (by linarith) hsv
      (mul_le_mul_of_nonneg_left hm₀ hs.le)
  calc _ ≤ _ := hc
    _ ≤ z.im / (s * v₀) + 2 * (z.im * (1 + s * rootLip s v₀)) / (s * v₀) := add_le_add h1 h2
    _ = z.im * ((3 + 1 / (s * v₀ ^ 2)) / (s * v₀)) := by
        rw [hsr]; field_simp; ring

end BlockBand.LocalWindow.ProofPartTwo
