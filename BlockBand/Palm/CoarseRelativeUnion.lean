module

public import BlockBand.Palm.CoarseRelativeMesh

/-!
# Coarse relative local law: polynomial mesh and union bound

* `coarse_mesh`: a finite mesh of the coarse domain with spacing `ρ` and at most
  `(2r₀/ρ + 1)(2/ρ + 1)` points.
* `gueMeasure_not_hermitian`: the GUE law charges no non-Hermitian matrix.
* `coarseRelative_of_pointwise`: `CoarseRelativeContract` follows from the fixed-point estimate:
  if, for each fixed `z` in the coarse domain, the trace failure and each directional failure
  with constant `N^{-1/3}/2` have probability `≤ N^{-D'}` for every `D'`, then the coarse
  relative local law holds. Outer measure is used throughout, so no measurability of the events
  is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.CoarseRelative

open MeasureTheory Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm
open scoped ComplexConjugate ENNReal

variable {N : ℕ}

/-- A finite `ρ`-net of an interval, with at most `(b - a)/ρ + 1` points. -/
theorem interval_mesh {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) :
    ∃ S : Finset ℝ, (∀ y ∈ S, a ≤ y ∧ y ≤ b) ∧ (S.card : ℝ) ≤ (b - a) / ρ + 1 ∧
      ∀ x : ℝ, a ≤ x → x ≤ b → ∃ y ∈ S, |x - y| ≤ ρ := by
  set n := ⌊(b - a) / ρ⌋₊ with hn
  have hba : 0 ≤ (b - a) / ρ := div_nonneg (by linarith) hρ.le
  have hnle : (n : ℝ) ≤ (b - a) / ρ := Nat.floor_le hba
  refine ⟨(Finset.range (n + 1)).image (fun k : ℕ => a + k * ρ), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkρ : (k : ℝ) * ρ ≤ b - a := by
      calc (k : ℝ) * ρ ≤ n * ρ := mul_le_mul_of_nonneg_right hk' hρ.le
        _ ≤ (b - a) / ρ * ρ := mul_le_mul_of_nonneg_right hnle hρ.le
        _ = b - a := by field_simp
    constructor
    · have : 0 ≤ (k : ℝ) * ρ := by positivity
      linarith
    · linarith
  · have h1 := Finset.card_image_le (s := Finset.range (n + 1)) (f := fun k : ℕ => a + k * ρ)
    rw [Finset.card_range] at h1
    have h2 : ((((Finset.range (n + 1)).image (fun k : ℕ => a + k * ρ)).card : ℕ) : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  · intro x hax hxb
    set k := ⌊(x - a) / ρ⌋₊ with hk
    have hxa : 0 ≤ (x - a) / ρ := div_nonneg (by linarith) hρ.le
    have hkn : k ≤ n := Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hρ.le)
    refine ⟨a + k * ρ, Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hkn),
      rfl⟩, ?_⟩
    have h1 : (k : ℝ) ≤ (x - a) / ρ := Nat.floor_le hxa
    have h2 : (x - a) / ρ < k + 1 := Nat.lt_floor_add_one _
    have h1' : (k : ℝ) * ρ ≤ x - a := by
      have := mul_le_mul_of_nonneg_right h1 hρ.le
      rwa [div_mul_cancel₀ _ hρ.ne'] at this
    have h2' : x - a < (k + 1) * ρ := by
      have := mul_lt_mul_of_pos_right h2 hρ
      rwa [div_mul_cancel₀ _ hρ.ne'] at this
    rw [abs_le]
    constructor <;> nlinarith

/-- A finite `ρ`-mesh of the coarse domain. -/
theorem coarse_mesh (hN : 0 < N) {E r₀ ρ : ℝ} (hr₀ : 0 < r₀) (hρ : 0 < ρ) :
    ∃ Z : Finset ℂ, (∀ z' ∈ Z, CoarseDomain N E r₀ z') ∧
      (Z.card : ℝ) ≤ (2 * r₀ / ρ + 1) * (2 / ρ + 1) ∧
      ∀ z : ℂ, CoarseDomain N E r₀ z → ∃ z' ∈ Z, ‖z - z'‖ ≤ ρ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hh
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hh0 : 0 < h := Real.rpow_pos_of_pos (by linarith) _
  have hρ2 : 0 < ρ / 2 := by linarith
  obtain ⟨Sx, hSx, hcx, hcovx⟩ := interval_mesh (a := E - r₀ / 2) (b := E + r₀ / 2)
    (by linarith) hρ2
  obtain ⟨Sy, hSy, hcy, hcovy⟩ := interval_mesh hh1 hρ2
  refine ⟨(Sx ×ˢ Sy).image (fun p => (⟨p.1, p.2⟩ : ℂ)), ?_, ?_, ?_⟩
  · intro z' hz'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz'
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hx1, hx2⟩ := hSx p.1 hp1
    obtain ⟨hy1, hy2⟩ := hSy p.2 hp2
    refine ⟨?_, hy1, hy2⟩
    show |p.1 - E| ≤ r₀ / 2
    rw [abs_le]
    constructor <;> linarith
  · have h1 := Finset.card_image_le (s := Sx ×ˢ Sy) (f := fun p => (⟨p.1, p.2⟩ : ℂ))
    rw [Finset.card_product] at h1
    have h2 : (((Sx ×ˢ Sy).image (fun p => (⟨p.1, p.2⟩ : ℂ))).card : ℝ) ≤
        (Sx.card : ℝ) * Sy.card := by exact_mod_cast h1
    have hx' : (Sx.card : ℝ) ≤ 2 * r₀ / ρ + 1 := by
      have : (E + r₀ / 2 - (E - r₀ / 2)) / (ρ / 2) = 2 * r₀ / ρ := by field_simp; ring
      linarith
    have hy' : (Sy.card : ℝ) ≤ 2 / ρ + 1 := by
      have : (1 - h) / (ρ / 2) ≤ 2 / ρ := by
        rw [div_le_div_iff₀ hρ2 hρ]
        nlinarith
      linarith
    calc _ ≤ (Sx.card : ℝ) * Sy.card := h2
      _ ≤ (2 * r₀ / ρ + 1) * (2 / ρ + 1) :=
          mul_le_mul hx' hy' (Nat.cast_nonneg _) (by positivity)
  · intro z hz
    obtain ⟨hx, hη0, hη1⟩ := hz
    obtain ⟨x', hx'S, hx'⟩ := hcovx z.re (by linarith [(abs_le.mp hx).1])
      (by linarith [(abs_le.mp hx).2])
    obtain ⟨y', hy'S, hy'⟩ := hcovy z.im hη0 hη1
    refine ⟨⟨x', y'⟩, Finset.mem_image.mpr ⟨(x', y'), Finset.mem_product.mpr ⟨hx'S, hy'S⟩, rfl⟩,
      ?_⟩
    have := Complex.norm_le_abs_re_add_abs_im (z - ⟨x', y'⟩)
    simp only [Complex.sub_re, Complex.sub_im] at this
    linarith

/-- The GUE sample map produces Hermitian matrices. -/
theorem gueSample_isHermitian {ι : Type*} [Fintype ι] (t : NNReal) (X : ι × ι → ℂ) :
    (gueSample t X).IsHermitian := by
  ext a b
  simp only [gueSample, conjTranspose_apply, of_apply, star_mul', star_add, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- `GUE` charges no non-Hermitian matrix. -/
theorem gueMeasure_not_hermitian (ι : Type*) [Fintype ι] (t : NNReal) :
    gueMeasure ι t {A | ¬ A.IsHermitian} = 0 := by
  have hclosed : IsClosed {A : Matrix ι ι ℂ | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hmeas : MeasurableSet {A : Matrix ι ι ℂ | ¬ A.IsHermitian} :=
    hclosed.measurableSet.compl
  have hcont : Continuous (gueSample (ι := ι) t) := by
    unfold gueSample
    fun_prop
  unfold gueMeasure
  rw [Measure.map_apply hcont.measurable hmeas]
  have : gueSample t ⁻¹' {A : Matrix ι ι ℂ | ¬ A.IsHermitian} = ∅ := by
    ext X
    simp [gueSample_isHermitian t X]
  rw [this, measure_empty]

/-- The failure event of the coarse relative local law is covered by the mesh failure events and
the non-Hermitian set. -/
theorem coarse_event_subset {A c₀ r₀ s₀ v₀ : ℝ} {N₁ : ℕ}
    (hint : ∀ N : ℕ, N₁ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ G : Matrix (Fin N) (Fin N) ℂ, G.IsHermitian →
      ∀ z z' : ℂ, CoarseDomain N E r₀ z → CoarseDomain N E r₀ z' →
        ‖z - z'‖ ≤ (N : ℝ) ^ (-meshExp A) →
        (traceErr F G s z' ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 →
            traceErr F G s z ≤ (N : ℝ) ^ (-(1 / 3 : ℝ))) ∧
        ∀ q : Fin N → ℂ, (quadErr F G s z' q ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z' q →
            quadErr F G s z q ≤ (N : ℝ) ^ (-(1 / 3 : ℝ)) * quadIm F s z q))
    {N : ℕ} (hN : N₁ ≤ N) {F : Matrix (Fin N) (Fin N) ℂ} {E : ℝ}
    (hC : FreshClass F A c₀ E r₀ s₀ v₀) {s : ℝ} (hs : s ∈ Set.Icc (c₀ - s₀) c₀)
    (Q : Finset (Fin N → ℂ)) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, CoarseDomain N E r₀ z → ∃ z' ∈ Z, CoarseDomain N E r₀ z' ∧
      ‖z - z'‖ ≤ (N : ℝ) ^ (-meshExp A)) :
    {G : Matrix (Fin N) (Fin N) ℂ | ∃ x η : ℝ, |x - E| ≤ r₀ / 2 ∧
        (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η ∧ η ≤ 1 ∧
        let z : ℂ := ⟨x, η⟩
        let R := (F + (Real.sqrt s : ℂ) • G - z • 1)⁻¹
        (N : ℝ) ^ (-(1 / 3 : ℝ)) < ‖(N : ℂ)⁻¹ * R.trace - freshDyson F s z‖ ∨
          ∃ q ∈ Q, (N : ℝ) ^ (-(1 / 3 : ℝ)) * (star q ⬝ᵥ (freshM F s z *ᵥ q)).im <
            ‖star q ⬝ᵥ ((R - freshM F s z) *ᵥ q)‖} ⊆
      {G | ¬ G.IsHermitian} ∪ ⋃ z' ∈ Z,
        ({G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 < traceErr F G s z'} ∪
          ⋃ q ∈ Q, {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z' q < quadErr F G s z' q}) := by
  intro G hG
  obtain ⟨x, η, hx, hη0, hη1, hfail⟩ := hG
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_not, not_exists,
    not_lt] at hcon
  obtain ⟨hherm, hgood⟩ := hcon
  have hz : CoarseDomain N E r₀ ⟨x, η⟩ := ⟨hx, hη0, hη1⟩
  obtain ⟨z', hz'Z, hz'D, hzz⟩ := hZ ⟨x, η⟩ hz
  obtain ⟨ht, hq⟩ := hint N hN F E hC s hs G hherm ⟨x, η⟩ z' hz hz'D hzz
  obtain ⟨hgt, hgq⟩ := hgood z' hz'Z
  have hT := ht hgt
  have hQ : ∀ q ∈ Q, quadErr F G s ⟨x, η⟩ q ≤
      (N : ℝ) ^ (-(1 / 3 : ℝ)) * quadIm F s ⟨x, η⟩ q :=
    fun q hqQ => hq q (hgq q hqQ)
  rcases hfail with hf | ⟨q, hqQ, hf⟩
  · exact absurd hT (not_le.mpr hf)
  · exact absurd (hQ q hqQ) (not_le.mpr hf)

/-- The coarse relative local law follows from the fixed-point estimate, by the mesh and a union
bound. -/
theorem coarseRelative_of_pointwise
    (hpt : ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ D' : ℝ, ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
        FreshClass F A c₀ E r₀ s₀ v₀ → ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ z : ℂ,
        CoarseDomain N E r₀ z →
          gueMeasure (Fin N) (Real.toNNReal (1 / N))
              {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 < traceErr F G s z} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D')) ∧
          ∀ q : Fin N → ℂ, gueMeasure (Fin N) (Real.toNNReal (1 / N))
              {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z q < quadErr F G s z q} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D'))) :
    CoarseRelativeContract := by
  intro A c₀ r₀ s₀ v₀ hK a D
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨N₁, hN₁, hint⟩ := coarse_interpolation (A := A) hK
  set K := meshExp A with hKdef
  set a' := max a 0 with ha'
  set D' := D + 2 * K + a' + 1 with hD'
  obtain ⟨N₀, hpt'⟩ := hpt A c₀ r₀ s₀ v₀ hK D'
  set C₀ := 6 * (2 * r₀ + 1) with hC₀
  refine ⟨max (max N₀ N₁) (⌈C₀⌉₊ + 1), ?_⟩
  intro N hN F E hC s hs Q hQ
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1' : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNC : ⌈C₀⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.succ_pos _) hNC
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNbig : C₀ ≤ N := by
    have h1 := Nat.le_ceil C₀
    have h2 : ((⌈C₀⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNC
    push_cast at h2
    linarith
  set ρ := (N : ℝ) ^ (-K) with hρdef
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hNr _
  obtain ⟨Z, hZD, hZcard, hZcov⟩ := coarse_mesh (E := E) hNpos hr₀ hρ
  have hZ : ∀ z : ℂ, CoarseDomain N E r₀ z → ∃ z' ∈ Z, CoarseDomain N E r₀ z' ∧
      ‖z - z'‖ ≤ (N : ℝ) ^ (-meshExp A) := by
    intro z hz
    obtain ⟨z', hz'Z, hzz⟩ := hZcov z hz
    exact ⟨z', hz'Z, hZD z' hz'Z, hzz⟩
  have hsub := coarse_event_subset hint hN1' hC hs Q Z hZ
  set μ := gueMeasure (Fin N) (Real.toNNReal (1 / N))
  set β := ENNReal.ofReal ((N : ℝ) ^ (-D'))
  have hbound : μ ({G | ¬ G.IsHermitian} ∪ ⋃ z' ∈ Z,
        ({G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 < traceErr F G s z'} ∪
          ⋃ q ∈ Q, {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z' q < quadErr F G s z' q})) ≤
      (Z.card : ℝ≥0∞) * (β + (Q.card : ℝ≥0∞) * β) := by
    refine (measure_union_le _ _).trans ?_
    rw [gueMeasure_not_hermitian, zero_add]
    refine (measure_biUnion_finset_le Z _).trans ?_
    have hpoint : ∀ z' ∈ Z, μ ({G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 < traceErr F G s z'} ∪
          ⋃ q ∈ Q, {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z' q <
            quadErr F G s z' q}) ≤ β + (Q.card : ℝ≥0∞) * β := by
      intro z' hz'
      obtain ⟨hpt1, hpt2⟩ := hpt' N hN0 F E hC s hs z' (hZD z' hz')
      refine (measure_union_le _ _).trans (add_le_add hpt1 ?_)
      refine (measure_biUnion_finset_le Q _).trans ?_
      calc ∑ q ∈ Q, μ {G | (N : ℝ) ^ (-(1 / 3 : ℝ)) / 2 * quadIm F s z' q < quadErr F G s z' q}
          ≤ ∑ _q ∈ Q, β := Finset.sum_le_sum (fun q _ => hpt2 q)
        _ = (Q.card : ℝ≥0∞) * β := by rw [Finset.sum_const, nsmul_eq_mul]
    calc _ ≤ ∑ _z' ∈ Z, (β + (Q.card : ℝ≥0∞) * β) := Finset.sum_le_sum hpoint
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine (measure_mono hsub).trans (hbound.trans ?_)
  -- real arithmetic
  have hx0 : 0 ≤ (N : ℝ) ^ (-D') := (Real.rpow_pos_of_pos hNr _).le
  have hconv : (Z.card : ℝ≥0∞) * (β + (Q.card : ℝ≥0∞) * β) =
      ENNReal.ofReal ((Z.card : ℝ) * ((1 + Q.card) * (N : ℝ) ^ (-D'))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg _),
      ENNReal.ofReal_one, ENNReal.ofReal_natCast, add_mul, one_mul]
  rw [hconv]
  apply ENNReal.ofReal_le_ofReal
  have hK0 : 0 ≤ K := by
    rw [hKdef, meshExp]
    have := le_max_right A 1
    linarith
  set P := (N : ℝ) ^ K with hPdef
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1 hK0
  have hρinv : ρ⁻¹ = P := by rw [hρdef, Real.rpow_neg hNr.le, inv_inv]
  have hZc : (Z.card : ℝ) ≤ 3 * (2 * r₀ + 1) * (P * P) := by
    have h1 : 2 * r₀ / ρ + 1 ≤ (2 * r₀ + 1) * P := by
      rw [div_eq_mul_inv, hρinv]; nlinarith
    have h2 : 2 / ρ + 1 ≤ 3 * P := by
      rw [div_eq_mul_inv, hρinv]; linarith
    calc (Z.card : ℝ) ≤ (2 * r₀ / ρ + 1) * (2 / ρ + 1) := hZcard
      _ ≤ (2 * r₀ + 1) * P * (3 * P) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 3 * (2 * r₀ + 1) * (P * P) := by ring
  set Pa := (N : ℝ) ^ a' with hPa
  have hPa1 : 1 ≤ Pa := Real.one_le_rpow hN1 (le_max_right _ _)
  have hQc : (1 + (Q.card : ℝ)) ≤ 2 * Pa := by
    have : (N : ℝ) ^ a ≤ Pa := Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
    linarith
  have hexp : P * P * Pa * (N : ℝ) ^ (-D') = (N : ℝ) ^ (-D) * (N : ℝ)⁻¹ := by
    rw [hPdef, hPa, ← Real.rpow_add hNr, ← Real.rpow_add hNr, ← Real.rpow_add hNr,
      ← Real.rpow_neg_one, ← Real.rpow_add hNr, hD']
    congr 1
    ring
  have hND : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNr _
  have hfin : C₀ * (N : ℝ)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hNr, one_mul]
    exact hNbig
  calc (Z.card : ℝ) * ((1 + Q.card) * (N : ℝ) ^ (-D'))
      ≤ (3 * (2 * r₀ + 1) * (P * P)) * ((2 * Pa) * (N : ℝ) ^ (-D')) :=
        mul_le_mul hZc (mul_le_mul_of_nonneg_right hQc hx0) (by positivity) (by positivity)
    _ = C₀ * (P * P * Pa * (N : ℝ) ^ (-D')) := by rw [hC₀]; ring
    _ = (N : ℝ) ^ (-D) * (C₀ * (N : ℝ)⁻¹) := by rw [hexp]; ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := mul_le_mul_of_nonneg_left hfin hND.le
    _ = (N : ℝ) ^ (-D) := mul_one _

end BlockBand.Palm.CoarseRelative
