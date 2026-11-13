module

public import BlockBand.Internal.Contracts.Layers
public import BlockBand.Counting.NativeCountTransport

/-!
# Eigenvalue count and gap of the absorbed matrix

Let `D = A - E - X`, where `A = diag(A_1, …, A_k)` has independent `GUE_W(c/W)` blocks, `X` is a
deterministic Hermitian matrix and `E` is real, and let `δ ≤ 1` be the truncated absolute value of
the `(⌊W/8⌋+1)`-th eigenvalue of `D` nearest zero. From the conditional block-GUE count
(`hcount : ConditionalBlockGUECount`, a hypothesis of every probabilistic theorem below) this file
proves `P(δ < t) ≤ (C_b' t)^{⌊W/8⌋+1}` and `‖δ⁻¹‖_{L^q} ≤ C_b` for `q ≤ W/16`, the count step of
the Gaussian absorption lemma.

* **Law bridge** (`blockNoise_hasLaw`). Under `blockLaw k W c`, the matrix `(√c)⁻¹ · diag(A_j)`,
  reindexed by `Σ _ : Fin k, Fin W ≃ Fin k × Fin W`, has exactly the PSSS normalized block-GUE law.
  The proof realizes `gueMeasure` on i.i.d. standard real coordinates and checks every field of
  `PSSS.BlockGUE.Law` (`noiseLaw`), using a grouping lemma for functions of disjoint coordinate
  sets (`iIndepFun_pi_of_local`).
* **Count** (`absorbedCount_factorialMoment`, `absorbedCount_tail`). `hcount` with
  `Ω = (Fin k → Matrix)`, `G = diag(A)` reindexed, `D = -E - X` (deterministic, hence independent
  of `G`), `t = c`: `E[(N)_r] ≤ (C/√c · kW · (b-a))^r` and `P(N ≥ r) ≤ (C/√c · kW · (b-a))^r/r!`
  for `N = #(Spec D ∩ [a,b])`, every `r ≥ 1`, uniformly in Hermitian `X` and real `E`.
* **Gap** (`gapFloor`, `absorbedGap_tail`, `absorbedGap_inv_moment`, `absorbedGap_inv_eLpNorm`).
  `δ_m(H) = sup {s ∈ [0,1] : #{|λ| < s} ≤ m} = min(1, |λ|_{(m+1)})`; `#{|λ| < δ} ≤ m`
  (`smallCount_gapFloor_le`, the input of `finrank_lowSubspace_le`), and for `t ≤ 1`,
  `δ < t ↔ #{|λ| < t} ≥ m + 1`. With `m = ⌊W/8⌋`:
  `P(δ < t) ≤ (16e·C·k/√c · t)^{⌊W/8⌋+1}` for `0 < t ≤ 1`, and for `1 ≤ q ≤ W/16`
  (`ε₂ = 1/16`): `E[δ^{-q}] ≤ C_b^q`, `‖δ⁻¹‖_{L^q} ≤ C_b`, `C_b = 4^{⌈16e·C·k/√c⌉₊ + 2}`, depending
  only on `k`, `c` and the PSSS constant `C`.

Representation choices (no hypothesis added). `D` is formed from the Hermitian parts
`(A_j + A_jᴴ)/2` (`absorbedMatrix`), so that it is Hermitian for every sample; every `gueMeasure`
sample is Hermitian (`ae_blocks_isHermitian`), and then `absorbedMatrix = diag(A) - E - X`
(`absorbedMatrix_val`). Counts are `PSSS.eigenCount` (multiplicity, increasing enumeration),
equal to Mathlib's `IsHermitian.eigenvalues` counts (`eigenCount_eq_card_eigenvalues`). `δ⁻¹`
uses Lean's `0⁻¹ = 0` on the event `δ = 0`, which is null by `absorbedGap_tail` (`t ↓ 0`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate Matrix
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure gueSample)
open BlockBand.SourceProcess (commonCircularIncrementLaw circularBrownianCoordinates)

/-!
## 1. Real coordinates of `gueMeasure`
-/

/-- The real coordinates `((a,b), s)` of one `W × W` circular matrix (`s = 0` real part, `s = 1`
imaginary part, before the `1/√2` of `circularBrownianCoordinates`). -/
abbrev GaussCoord (W : ℕ) := (Fin W × Fin W) × Fin 2

/-- I.i.d. standard real Gaussian coordinates indexed by a finite type. -/
def stdGaussCoordLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance stdGaussCoordLaw_isProbability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (stdGaussCoordLaw ι) := by
  unfold stdGaussCoordLaw; infer_instance

/-- The `GUE_W(t)` sample `√(t/2)(X + Xᴴ)` of the circular matrix with real coordinates `r`. -/
def gueOfCoords (W : ℕ) (t : ℝ≥0) (r : GaussCoord W → ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  gueSample t (circularBrownianCoordinates r)

theorem measurable_gueOfCoords (W : ℕ) (t : ℝ≥0) : Measurable (gueOfCoords W t) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [gueOfCoords, gueSample, circularBrownianCoordinates, Matrix.of_apply]
  have hc : Measurable (fun z : ℂ => conj z) := Complex.continuous_conj.measurable
  fun_prop

/-- `CoareaPalm.gueMeasure (Fin W) t` is the image of i.i.d. standard real coordinates. -/
theorem gueMeasure_eq_map (W : ℕ) (t : ℝ≥0) :
    gueMeasure (Fin W) t = (stdGaussCoordLaw (GaussCoord W)).map (gueOfCoords W t) := by
  have hm : Measurable (circularBrownianCoordinates (ι := Fin W)) := by
    apply Measurable.of_eval
    intro u
    unfold circularBrownianCoordinates
    fun_prop
  have hg : Measurable (gueSample (ι := Fin W) t) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
    simp only [gueSample, Matrix.of_apply]
    have hc : Measurable (fun z : ℂ => conj z) := Complex.continuous_conj.measurable
    fun_prop
  rw [gueMeasure, commonCircularIncrementLaw, Measure.map_map hg hm]
  rfl

/-- `Re A_ab = √(t/2)/√2 · (r_{ab0} + r_{ba0})`. -/
theorem gueOfCoords_re (W : ℕ) (t : ℝ≥0) (r : GaussCoord W → ℝ) (a b : Fin W) :
    (gueOfCoords W t r a b).re =
      Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 * (r ((a, b), 0) + r ((b, a), 0)) := by
  simp [gueOfCoords, gueSample, circularBrownianCoordinates, Complex.div_ofReal_re]
  ring

/-- `Im A_ab = √(t/2)/√2 · (r_{ab1} - r_{ba1})`. -/
theorem gueOfCoords_im (W : ℕ) (t : ℝ≥0) (r : GaussCoord W → ℝ) (a b : Fin W) :
    (gueOfCoords W t r a b).im =
      Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2 * (r ((a, b), 1) - r ((b, a), 1)) := by
  simp [gueOfCoords, gueSample, circularBrownianCoordinates, Complex.div_ofReal_im]
  ring

theorem gueOfCoords_star (W : ℕ) (t : ℝ≥0) (r : GaussCoord W → ℝ) (a b : Fin W) :
    star (gueOfCoords W t r b a) = gueOfCoords W t r a b := by
  simp only [gueOfCoords, gueSample, Matrix.of_apply, star_mul', Complex.star_def,
    Complex.conj_ofReal, map_add, Complex.conj_conj]
  ring

/-!
## 2. The PSSS block-GUE law of the normalized block noise
-/

open BlockBand.External BlockBand.External.PSSS.BlockGUE

/-- Constant block sizes. -/
abbrev uniformBlockSizes (k W : ℕ) : Fin k → ℕ := fun _ => W

/-- The PSSS index for `k` blocks of size `W`. -/
abbrev UniformBlockIndex (k W : ℕ) := PSSS.BlockGUE.Index (uniformBlockSizes k W)

/-- Flat real Gaussian coordinates of `k` blocks. -/
abbrev FlatGaussCoord (k W : ℕ) := Fin k × GaussCoord W

/-- The block coordinates of a flat sample. -/
def flatCoordBlocks {k W : ℕ} (ω : FlatGaussCoord k W → ℝ) : Fin k → GaussCoord W → ℝ :=
  fun j u => ω (j, u)

/-- The normalized block noise on the PSSS index. -/
def noiseMatrix {k W : ℕ} (c : ℝ) (ω : FlatGaussCoord k W → ℝ) :
    Matrix (UniformBlockIndex k W) (UniformBlockIndex k W) ℂ :=
  fun x y => if x.1 = y.1 then ((Real.sqrt c)⁻¹ : ℂ) *
    gueOfCoords W (Real.toNNReal (c / W)) (flatCoordBlocks ω x.1) x.2 y.2 else 0

/-- The scale of the noise coordinates. -/
def noiseScale (c : ℝ) (W : ℕ) : ℝ :=
  (Real.sqrt c)⁻¹ * (Real.sqrt ((Real.toNNReal (c / W) : ℝ) / 2) / Real.sqrt 2)

/-- `σ² = 1/(4W)`. -/
theorem noiseScale_sq {c : ℝ} (hc : 0 < c) (W : ℕ) (hW : 0 < W) :
    noiseScale c W ^ 2 = 1 / (4 * W) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ((Real.toNNReal (c / W)) : ℝ) = c / W := Real.coe_toNNReal _ (by positivity)
  rw [noiseScale, h1, mul_pow, div_pow, inv_pow, Real.sq_sqrt hc.le, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by norm_num)]
  field_simp
  ring

theorem noiseMatrix_same {k W : ℕ} (c : ℝ) (ω : FlatGaussCoord k W → ℝ) (j : Fin k) (a b : Fin W) :
    noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩ = ((Real.sqrt c)⁻¹ : ℂ) *
      gueOfCoords W (Real.toNNReal (c / W)) (flatCoordBlocks ω j) a b := by
  simp [noiseMatrix]

theorem noiseMatrix_re {k W : ℕ} (c : ℝ) (ω : FlatGaussCoord k W → ℝ) (j : Fin k) (a b : Fin W) :
    (noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩).re =
      noiseScale c W * (ω (j, ((a, b), 0)) + ω (j, ((b, a), 0))) := by
  rw [noiseMatrix_same, ← Complex.ofReal_inv, Complex.re_ofReal_mul, gueOfCoords_re, noiseScale]
  simp [flatCoordBlocks]
  ring

theorem noiseMatrix_im {k W : ℕ} (c : ℝ) (ω : FlatGaussCoord k W → ℝ) (j : Fin k) (a b : Fin W) :
    (noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩).im =
      noiseScale c W * (ω (j, ((a, b), 1)) - ω (j, ((b, a), 1))) := by
  rw [noiseMatrix_same, ← Complex.ofReal_inv, Complex.im_ofReal_mul, gueOfCoords_im, noiseScale]
  simp [flatCoordBlocks]
  ring

theorem noiseMatrix_isHermitian {k W : ℕ} (c : ℝ) (ω : FlatGaussCoord k W → ℝ) :
    (noiseMatrix c ω).IsHermitian := by
  ext ⟨j, a⟩ ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply]
  by_cases h : j = j'
  · subst h
    rw [noiseMatrix_same, noiseMatrix_same, star_mul', gueOfCoords_star]
    simp [← Complex.ofReal_inv]
  · have h' : j' ≠ j := Ne.symm h
    simp [noiseMatrix, h, h']

theorem measurable_noiseMatrix_entry {k W : ℕ} (c : ℝ) (x y : UniformBlockIndex k W) :
    Measurable (fun ω : FlatGaussCoord k W → ℝ => noiseMatrix c ω x y) := by
  unfold noiseMatrix
  split_ifs
  · have hb : Measurable (fun ω : FlatGaussCoord k W → ℝ => flatCoordBlocks ω x.1) :=
      measurable_pi_iff.mpr fun u => measurable_pi_apply _
    exact ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_gueOfCoords W _).comp hb))).const_mul _
  · exact measurable_const

/-- **Grouping lemma.** Under a finite product of real probability laws, functions `f t` each
depending only on the coordinates of the fibre `g⁻¹{t}` are jointly independent. -/
theorem iIndepFun_pi_of_local {I T : Type*} [Fintype I] [Fintype T]
    (μ : I → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (g : I → T)
    {γ : T → Type*} [∀ t, MeasurableSpace (γ t)] (f : ∀ t, (I → ℝ) → γ t)
    (hf : ∀ t, Measurable (f t))
    (hloc : ∀ t (ω ω' : I → ℝ), (∀ i, g i = t → ω i = ω' i) → f t ω = f t ω') :
    iIndepFun f (Measure.pi μ) := by
  classical
  let ext : ∀ t, ({i // g i = t} → ℝ) → (I → ℝ) :=
    fun t ψ i => if h : g i = t then ψ ⟨i, h⟩ else 0
  have hext : ∀ t, Measurable (ext t) := by
    intro t
    refine measurable_pi_iff.mpr fun i => ?_
    by_cases h : g i = t
    · simp only [ext, h, dite_true]; exact measurable_pi_apply _
    · simp only [ext, h, dite_false]; exact measurable_const
  let h : ∀ t, ({i // g i = t} → ℝ) → γ t := fun t ψ => f t (ext t ψ)
  have hh : ∀ t, Measurable (h t) := fun t => (hf t).comp (hext t)
  let Φ : (I → ℝ) → (∀ t, {i // g i = t} → ℝ) := fun ω t i => ω i.1
  have hΦ : Measurable Φ := by
    refine measurable_pi_iff.mpr fun t => measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hfΦ : ∀ t ω, f t ω = h t (Φ ω t) := by
    intro t ω
    apply hloc
    intro i hi
    simp [ext, Φ, hi]
  let ν : ∀ t, Measure ({i // g i = t} → ℝ) := fun t => Measure.pi fun i => μ i.1
  have hmap : (Measure.pi μ).map Φ = Measure.pi ν := by
    have hinj : Function.Injective (fun p : (t : T) × {i // g i = t} => p.2.1) := by
      rintro ⟨t, i, hi⟩ ⟨t', i', hi'⟩ heq
      simp only at heq
      subst heq
      have : t = t' := hi.symm.trans hi'
      subst this
      rfl
    have h1 := Measure.map_infinitePi_infinitePi_of_inj (P := μ) hinj
    have h2 := Measure.infinitePi_map_piCurry
      (X := fun (t : T) (_ : {i // g i = t}) => ℝ) (fun t i => μ i.1)
    have hcomp : Φ = (MeasurableEquiv.piCurry (fun (t : T) (_ : {i // g i = t}) => ℝ)) ∘
        (fun ω (p : (t : T) × {i // g i = t}) => ω p.2.1) := by
      funext ω t i; rfl
    rw [← Measure.infinitePi_eq_pi, hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2]
    simp only [ν, Measure.infinitePi_eq_pi]
  have hind : iIndepFun (fun t (ψ : ∀ t, {i // g i = t} → ℝ) => h t (ψ t)) (Measure.pi ν) :=
    iIndepFun_pi (fun t => (hh t).aemeasurable)
  have hfeq : f = fun t ω => h t (Φ ω t) := by funext t ω; exact hfΦ t ω
  rw [hfeq]
  have hm1 : ∀ t, Measurable (fun ω => h t (Φ ω t)) :=
    fun t => (hh t).comp ((measurable_pi_apply t).comp hΦ)
  have hm2 : ∀ t, Measurable (fun ψ : (∀ t, {i // g i = t} → ℝ) => h t (ψ t)) :=
    fun t => (hh t).comp (measurable_pi_apply t)
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun t ω => h t (Φ ω t))
    (fun t => (hm1 t).aemeasurable)).mpr ?_
  have hind' := (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun t (ψ : ∀ t, {i // g i = t} → ℝ) => h t (ψ t))
    (fun t => (hm2 t).aemeasurable)).mp hind
  have e1 : (fun ω t => h t (Φ ω t)) = (fun ψ t => h t (ψ t)) ∘ Φ := rfl
  rw [e1, ← Measure.map_map (measurable_pi_iff.mpr hm2) hΦ, hmap, hind']
  congr 1
  funext t
  have e2 : (fun ω => h t (Φ ω t)) = (fun ψ => h t (ψ t)) ∘ Φ := rfl
  rw [e2, ← Measure.map_map (hm2 t) hΦ, hmap]

instance upperPairFintypeAbsorber {k : ℕ} (d : Fin k → ℕ) : Fintype (UpperPair d) := by
  unfold UpperPair; infer_instance

/-- The upper pair of two indices, sorted by `indexLE`. -/
def upperSortPair {k : ℕ} {d : Fin k → ℕ} (x y : Index d) : UpperPair d :=
  ⟨if indexLE d x y then (x, y) else (y, x), by
    split_ifs with h
    · exact h
    · unfold indexLE at h ⊢; exact Nat.le_of_lt (lt_of_not_ge h)⟩

theorem upperSortPair_of_le {k : ℕ} {d : Fin k → ℕ} {x y : Index d} (h : indexLE d x y) :
    upperSortPair x y = ⟨(x, y), h⟩ :=
  Subtype.ext (by simp [upperSortPair, h])

theorem upperSortPair_swap_of_le {k : ℕ} {d : Fin k → ℕ} {x y : Index d} (h : indexLE d x y) :
    upperSortPair y x = ⟨(x, y), h⟩ := by
  by_cases h' : indexLE d y x
  · have hxy : x = y := by
      apply (Fintype.equivFin (Index d)).injective
      exact Fin.ext (Nat.le_antisymm h h')
    subst hxy
    exact Subtype.ext (by simp [upperSortPair])
  · exact Subtype.ext (by simp [upperSortPair, h'])

/-- The upper pair owning a flat Gaussian coordinate. -/
def coordPair {k W : ℕ} (i : FlatGaussCoord k W) : UpperPair (uniformBlockSizes k W) :=
  upperSortPair (d := uniformBlockSizes k W) ⟨i.1, i.2.1.1⟩ ⟨i.1, i.2.1.2⟩

/-- The upper entries of the noise are jointly independent (PSSS field `upper_independent`). -/
theorem noiseMatrix_upper_iIndep {k W : ℕ} (c : ℝ) :
    iIndepFun (fun (q : UpperPair (uniformBlockSizes k W)) (ω : FlatGaussCoord k W → ℝ) =>
      noiseMatrix c ω q.1.1 q.1.2) (stdGaussCoordLaw (FlatGaussCoord k W)) := by
  apply iIndepFun_pi_of_local (fun _ => gaussianReal 0 1) coordPair
  · intro q; exact measurable_noiseMatrix_entry c _ _
  · rintro ⟨⟨⟨j, a⟩, ⟨j', b⟩⟩, hq⟩ ω ω' hloc
    simp only
    by_cases hj : j = j'
    · subst hj
      have e : ∀ s : Fin 2, ω (j, ((a, b), s)) = ω' (j, ((a, b), s)) ∧
          ω (j, ((b, a), s)) = ω' (j, ((b, a), s)) := by
        intro s
        exact ⟨hloc _ (upperSortPair_of_le hq), hloc _ (upperSortPair_swap_of_le hq)⟩
      rw [noiseMatrix_same, noiseMatrix_same]
      congr 1
      apply Complex.ext
      · rw [gueOfCoords_re, gueOfCoords_re]
        simp [flatCoordBlocks, (e 0).1, (e 0).2]
      · rw [gueOfCoords_im, gueOfCoords_im]
        simp [flatCoordBlocks, (e 1).1, (e 1).2]
    · simp [noiseMatrix, hj]

/-- The real/imaginary split of one entry is independent (`s = 0` versus `s = 1`). -/
theorem noiseMatrix_re_im_indep {k W : ℕ} (c : ℝ) (j : Fin k) (a b : Fin W) :
    IndepFun (fun ω : FlatGaussCoord k W → ℝ => (noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩).re)
      (fun ω => (noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩).im) (stdGaussCoordLaw (FlatGaussCoord k W)) := by
  have h := iIndepFun_pi_of_local (γ := fun _ : Fin 2 => ℝ) (fun _ => gaussianReal 0 1)
    (fun i : FlatGaussCoord k W => i.2.2)
    (fun s ω => if s = 0 then (noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩).re
      else (noiseMatrix c ω ⟨j, a⟩ ⟨j, b⟩).im) ?_ ?_
  · have := h.indepFun (show (0 : Fin 2) ≠ 1 by decide)
    simpa [stdGaussCoordLaw] using this
  · intro s
    have h1 := Complex.measurable_re.comp (measurable_noiseMatrix_entry (k := k) (W := W) c
      ⟨j, a⟩ ⟨j, b⟩)
    have h2 := Complex.measurable_im.comp (measurable_noiseMatrix_entry (k := k) (W := W) c
      ⟨j, a⟩ ⟨j, b⟩)
    split_ifs
    · exact h1
    · exact h2
  · intro s ω ω' hloc
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      rw [noiseMatrix_re, noiseMatrix_re, hloc (j, ((a, b), 0)) rfl, hloc (j, ((b, a), 0)) rfl]
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [noiseMatrix_im, noiseMatrix_im, hloc (j, ((a, b), 1)) rfl, hloc (j, ((b, a), 1)) rfl]

/-- A coordinate of `stdGaussCoordLaw` is standard Gaussian. -/
theorem hasLaw_stdGaussCoord {I : Type*} [Fintype I] (i : I) :
    HasLaw (fun ω : I → ℝ => ω i) (gaussianReal 0 1) (stdGaussCoordLaw I) :=
  (measurePreserving_eval (fun _ : I => gaussianReal 0 1) i).hasLaw

/-- Distinct coordinates are independent. -/
theorem indep_stdGaussCoord {I : Type*} [Fintype I] {i₁ i₂ : I} (h : i₁ ≠ i₂) :
    IndepFun (fun ω : I → ℝ => ω i₁) (fun ω => ω i₂) (stdGaussCoordLaw I) :=
  (iIndepFun_pi (μ := fun _ : I => gaussianReal 0 1) (X := fun _ => id)
    (fun _ => aemeasurable_id)).indepFun h

/-- `σ(ω_{i₁} + ω_{i₂}) ~ N(0, 2σ²)` for `i₁ ≠ i₂`. -/
theorem hasLaw_stdGauss_scaled_add {I : Type*} [Fintype I] {i₁ i₂ : I} (h : i₁ ≠ i₂) (σ : ℝ) :
    HasLaw (fun ω : I → ℝ => σ * (ω i₁ + ω i₂))
      (gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ) * 2)) (stdGaussCoordLaw I) := by
  have hs : HasLaw (fun ω : I → ℝ => ω i₁ + ω i₂) (gaussianReal 0 2) (stdGaussCoordLaw I) := by
    refine ⟨by fun_prop, ?_⟩
    have := gaussianReal_add_gaussianReal_of_indepFun (indep_stdGaussCoord h)
      (hasLaw_stdGaussCoord i₁)
      (hasLaw_stdGaussCoord i₂)
    rw [show (fun ω : I → ℝ => ω i₁ + ω i₂) = (fun ω => ω i₁) + (fun ω => ω i₂) from rfl, this]
    norm_num
  have := gaussianReal_const_mul hs σ
  rw [mul_zero] at this
  exact this

/-- `σ(ω_{i₁} - ω_{i₂}) ~ N(0, 2σ²)` for `i₁ ≠ i₂`. -/
theorem hasLaw_stdGauss_scaled_sub {I : Type*} [Fintype I] {i₁ i₂ : I} (h : i₁ ≠ i₂) (σ : ℝ) :
    HasLaw (fun ω : I → ℝ => σ * (ω i₁ - ω i₂))
      (gaussianReal 0 (NNReal.mk (σ ^ 2) (sq_nonneg σ) * 2)) (stdGaussCoordLaw I) := by
  have hn : HasLaw (fun ω : I → ℝ => -ω i₂) (gaussianReal 0 1) (stdGaussCoordLaw I) := by
    have := gaussianReal_neg (hasLaw_stdGaussCoord (I := I) i₂)
    simp only [neg_zero] at this
    exact this
  have hi : IndepFun (fun ω : I → ℝ => ω i₁) (fun ω => -ω i₂) (stdGaussCoordLaw I) :=
    (indep_stdGaussCoord h).comp (φ := id) (ψ := fun x : ℝ => -x) measurable_id measurable_neg
  have hs : HasLaw (fun ω : I → ℝ => ω i₁ - ω i₂) (gaussianReal 0 2) (stdGaussCoordLaw I) := by
    refine ⟨by fun_prop, ?_⟩
    have := gaussianReal_add_gaussianReal_of_indepFun hi (hasLaw_stdGaussCoord i₁) hn
    rw [show (fun ω : I → ℝ => ω i₁ - ω i₂) = (fun ω => ω i₁) + (fun ω => -ω i₂) by
      funext ω; simp [sub_eq_add_neg], this]
    norm_num
  have := gaussianReal_const_mul hs σ
  rw [mul_zero] at this
  exact this

theorem entryVariance_uniformBlockSizes {k W : ℕ} (j : Fin k) (a b : Fin W) :
    entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, b⟩ = 1 / (W : ℝ) := by
  simp [entryVariance]

/-- The concrete normalized block noise is a PSSS `BlockGUE.Law`. -/
def noiseLaw (k W : ℕ) (hW : 0 < W) (c : ℝ) (hc : 0 < c) :
    Law (uniformBlockSizes k W) (fun _ => hW) where
  Ω := FlatGaussCoord k W → ℝ
  mΩ := inferInstance
  P := stdGaussCoordLaw (FlatGaussCoord k W)
  probability := inferInstance
  G := noiseMatrix c
  hermitian := noiseMatrix_isHermitian c
  measurable_entry := measurable_noiseMatrix_entry c
  block_diagonal := fun x y hxy => Filter.Eventually.of_forall fun ω => by
    simp [noiseMatrix, hxy]
  upper_independent := noiseMatrix_upper_iIndep c
  diagonal_im_zero := by
    rintro ⟨j, a⟩
    exact Filter.Eventually.of_forall fun ω => by rw [noiseMatrix_im]; ring
  diagonal_re_law := by
    rintro ⟨j, a⟩
    have h := gaussianReal_const_mul
      (hasLaw_stdGaussCoord (I := FlatGaussCoord k W) (j, ((a, a), 0)))
      (2 * noiseScale c W)
    rw [mul_zero] at h
    have hv : (⟨entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, a⟩,
        entryVariance_nonneg (fun _ => hW) _ _⟩ : ℝ≥0) =
        (⟨(2 * noiseScale c W) ^ 2, sq_nonneg _⟩ : ℝ≥0) * 1 := by
      apply NNReal.eq
      change entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, a⟩ = (2 * noiseScale c W) ^ 2 * 1
      rw [mul_one, entryVariance_uniformBlockSizes, mul_pow, noiseScale_sq hc W hW]
      have hW' : (0 : ℝ) < W := by exact_mod_cast hW
      field_simp
      norm_num
    rw [hv]
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only; rw [noiseMatrix_re]; ring)
  offdiag_components_independent := by
    rintro ⟨j, a⟩ ⟨j', b⟩ _ _ hb
    simp only at hb
    subst hb
    exact noiseMatrix_re_im_indep c j a b
  offdiag_re_law := by
    rintro ⟨j, a⟩ ⟨j', b⟩ _ hne hb
    simp only at hb
    subst hb
    have hab : a ≠ b := fun h => hne (by rw [h])
    have hi : ((j, ((a, b), 0)) : FlatGaussCoord k W) ≠ (j, ((b, a), 0)) := by
      intro h; apply hab; simp only [Prod.mk.injEq] at h; exact h.2.1.1
    have h := hasLaw_stdGauss_scaled_add hi (noiseScale c W)
    have hv : (⟨entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2,
        div_nonneg (entryVariance_nonneg (fun _ => hW) _ _) (by norm_num)⟩ : ℝ≥0) =
        (⟨noiseScale c W ^ 2, sq_nonneg _⟩ : ℝ≥0) * 2 := by
      apply NNReal.eq
      change entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2 = noiseScale c W ^ 2 * 2
      rw [entryVariance_uniformBlockSizes, noiseScale_sq hc W hW]
      have hW' : (0 : ℝ) < W := by exact_mod_cast hW
      field_simp
      norm_num
    rw [hv]
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only; rw [noiseMatrix_re])
  offdiag_im_law := by
    rintro ⟨j, a⟩ ⟨j', b⟩ _ hne hb
    simp only at hb
    subst hb
    have hab : a ≠ b := fun h => hne (by rw [h])
    have hi : ((j, ((a, b), 1)) : FlatGaussCoord k W) ≠ (j, ((b, a), 1)) := by
      intro h; apply hab; simp only [Prod.mk.injEq] at h; exact h.2.1.1
    have h := hasLaw_stdGauss_scaled_sub hi (noiseScale c W)
    have hv : (⟨entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2,
        div_nonneg (entryVariance_nonneg (fun _ => hW) _ _) (by norm_num)⟩ : ℝ≥0) =
        (⟨noiseScale c W ^ 2, sq_nonneg _⟩ : ℝ≥0) * 2 := by
      apply NNReal.eq
      change entryVariance (uniformBlockSizes k W) ⟨j, a⟩ ⟨j, b⟩ / 2 = noiseScale c W ^ 2 * 2
      rw [entryVariance_uniformBlockSizes, noiseScale_sq hc W hW]
      have hW' : (0 : ℝ) < W := by exact_mod_cast hW
      field_simp
      norm_num
    rw [hv]
    exact h.congr (Filter.Eventually.of_forall fun ω => by
      simp only; rw [noiseMatrix_im])

open BlockBand.Internal.Contracts.Layers (blockDiag)

/-- The reindexing `Σ _ : Fin k, Fin W ≃ Fin k × Fin W`. -/
def uniformBlockEquiv (k W : ℕ) : UniformBlockIndex k W ≃ Fin k × Fin W :=
  Equiv.sigmaEquivProd (Fin k) (Fin W)

/-- The GUE blocks of a flat sample. -/
def flatBlocks {k W : ℕ} (t : ℝ≥0) (ω : FlatGaussCoord k W → ℝ) :
    Fin k → Matrix (Fin W) (Fin W) ℂ :=
  fun j => gueOfCoords W t (flatCoordBlocks ω j)

theorem measurable_flatBlocks {k W : ℕ} (t : ℝ≥0) :
    Measurable (flatBlocks (k := k) (W := W) t) := by
  refine measurable_pi_iff.mpr fun j => (measurable_gueOfCoords W t).comp ?_
  exact measurable_pi_iff.mpr fun u => measurable_pi_apply _

theorem map_flatBlocks (k W : ℕ) (t : ℝ≥0) :
    (stdGaussCoordLaw (FlatGaussCoord k W)).map (flatBlocks t) =
      Measure.pi fun _ : Fin k => gueMeasure (Fin W) t := by
  have hcur : flatBlocks (k := k) (W := W) t =
      (fun ψ : Fin k → GaussCoord W → ℝ => fun j => gueOfCoords W t (ψ j)) ∘
        (MeasurableEquiv.curry (Fin k) (GaussCoord W) ℝ) := by
    funext ω j; rfl
  have h1 := Measure.infinitePi_map_curry (X := ℝ)
    (fun (_ : Fin k) (_ : GaussCoord W) => gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at h1
  have hm : Measurable (fun ψ : Fin k → GaussCoord W → ℝ => fun j => gueOfCoords W t (ψ j)) :=
    measurable_pi_iff.mpr fun j => (measurable_gueOfCoords W t).comp (measurable_pi_apply j)
  rw [hcur, ← Measure.map_map hm (MeasurableEquiv.measurable _), stdGaussCoordLaw, h1,
    Measure.pi_map_pi (fun _ => (measurable_gueOfCoords W t).aemeasurable)]
  simp only [gueMeasure_eq_map, stdGaussCoordLaw]

/-- The normalized block noise `(√c)⁻¹ · diag(A_j)`, reindexed to the PSSS index. -/
def blockNoise {k W : ℕ} (c : ℝ) (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (UniformBlockIndex k W) (UniformBlockIndex k W) ℂ :=
  ((Real.sqrt c)⁻¹ : ℂ) • (blockDiag A).submatrix (uniformBlockEquiv k W) (uniformBlockEquiv k W)

theorem measurable_blockNoise {k W : ℕ} (c : ℝ) :
    Measurable (blockNoise (k := k) (W := W) c) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [blockNoise, Matrix.smul_apply, Matrix.submatrix_apply, blockDiag, smul_eq_mul]
  refine Measurable.const_mul ?_ _
  split_ifs
  · fun_prop
  · exact measurable_const

theorem blockNoise_flatBlocks {k W : ℕ} (c : ℝ) (ω : FlatGaussCoord k W → ℝ) :
    blockNoise c (flatBlocks (Real.toNNReal (c / W)) ω) = noiseMatrix c ω := by
  ext x y
  simp only [blockNoise, Matrix.smul_apply, Matrix.submatrix_apply, blockDiag, smul_eq_mul,
    noiseMatrix, flatBlocks, uniformBlockEquiv, mul_ite, mul_zero]
  rfl

/-- **Law bridge.** Under `k` independent `GUE_W(c/W)` blocks (`CoareaPalm.gueMeasure`),
`(√c)⁻¹ · diag(A_1, …, A_k)`, reindexed to `Σ _ : Fin k, Fin W`, has exactly the PSSS
normalized block-GUE law `(canonicalMatrixMeasure d hd).map Subtype.val`, `d ≡ W`. -/
theorem blockNoise_hasLaw (k W : ℕ) (hW : 0 < W) (c : ℝ) (hc : 0 < c) :
    HasLaw (blockNoise (k := k) (W := W) c)
      ((canonicalMatrixMeasure (uniformBlockSizes k W) (fun _ => hW)).map Subtype.val)
      (Measure.pi fun _ : Fin k => gueMeasure (Fin W) (Real.toNNReal (c / W))) := by
  have hL := (noiseLaw k W hW c hc).hasLaw_matrix_canonical
  have hV : HasLaw (fun ω => noiseMatrix (k := k) (W := W) c ω)
      ((canonicalMatrixMeasure (uniformBlockSizes k W) (fun _ => hW)).map Subtype.val)
      (stdGaussCoordLaw (FlatGaussCoord k W)) :=
    (hasLaw_map measurable_subtype_coe.aemeasurable).comp hL
  have hB : HasLaw (flatBlocks (k := k) (W := W) (Real.toNNReal (c / W)))
      (Measure.pi fun _ : Fin k => gueMeasure (Fin W) (Real.toNNReal (c / W)))
      (stdGaussCoordLaw (FlatGaussCoord k W)) :=
    ⟨(measurable_flatBlocks _).aemeasurable, map_flatBlocks k W _⟩
  have h := HasLaw.comp_of_hasLaw_comp (f := blockNoise (k := k) (W := W) c)
    (measurable_blockNoise c).aemeasurable hB HasLaw.id
    (by simpa only [blockNoise_flatBlocks] using hV)
  exact h

instance gueMeasure_isProbability (W : ℕ) (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure (Fin W) t) := by
  rw [gueMeasure_eq_map]
  infer_instance

/-!
## 3. Hermitian parts and the absorbed matrix
-/

/-- The Hermitian part `(M + Mᴴ)/2`; it fixes every Hermitian matrix (every GUE sample). -/
def hermPart {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (M + Mᴴ)

theorem hermPart_isHermitian {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) :
    (hermPart M).IsHermitian := by
  ext a b
  simp only [hermPart, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, star_mul', star_add, star_star]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this]; ring

theorem hermPart_of_isHermitian {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) : hermPart M = M := by
  rw [hermPart, hM.eq, ← two_smul ℂ M, smul_smul]
  norm_num

theorem measurable_hermPart (W : ℕ) :
    Measurable (hermPart (ι := Fin W)) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [hermPart, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    smul_eq_mul]
  have hc : Measurable (fun z : ℂ => star z) := Complex.continuous_conj.measurable
  fun_prop

theorem gueOfCoords_isHermitian (W : ℕ) (t : ℝ≥0) (r : GaussCoord W → ℝ) :
    (gueOfCoords W t r).IsHermitian := by
  ext a b
  exact gueOfCoords_star W t r a b

/-- Blockwise Hermitian parts. -/
def hermBlocks {k W : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) :
    Fin k → Matrix (Fin W) (Fin W) ℂ :=
  fun j => hermPart (A j)

theorem blockDiag_isHermitian {k W : ℕ} {A : Fin k → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ j, (A j).IsHermitian) : (blockDiag A).IsHermitian := by
  ext ⟨j, a⟩ ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply, blockDiag]
  by_cases h : j = j'
  · subst h
    simp only [ite_true]
    exact (hA j).apply a b
  · simp [h, Ne.symm h]

/-- The total Hermitian matrix `D = diag(herm A_j) - E - X`. For GUE blocks (Hermitian a.s.,
in fact for every sample of `gueSample`) it is `diag(A_j) - E - X`. -/
def absorbedMatrix {k W : ℕ} (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W))
    (A : Fin k → Matrix (Fin W) (Fin W) ℂ) : PSSS.HermitianMatrix (Fin k × Fin W) :=
  ⟨blockDiag (hermBlocks A) - (E : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) - X.1, by
    refine ((blockDiag_isHermitian fun j => hermPart_isHermitian (A j)).sub ?_).sub X.2
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]⟩

theorem absorbedMatrix_val {k W : ℕ} (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W))
    {A : Fin k → Matrix (Fin W) (Fin W) ℂ} (hA : ∀ j, (A j).IsHermitian) :
    (absorbedMatrix E X A).1 = blockDiag A - (E : ℂ) • 1 - X.1 := by
  have : hermBlocks A = A := funext fun j => hermPart_of_isHermitian (hA j)
  simp only [absorbedMatrix, this]

theorem measurable_absorbedMatrix {k W : ℕ} (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) :
    Measurable (absorbedMatrix (k := k) (W := W) E X) := by
  apply Measurable.subtype_mk
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  simp only [Matrix.sub_apply, blockDiag, hermBlocks]
  refine Measurable.sub (Measurable.sub ?_ measurable_const) measurable_const
  split_ifs
  · have h1 : Measurable (fun A : Fin k → Matrix (Fin W) (Fin W) ℂ => hermPart (A x.1)) :=
      (measurable_hermPart W).comp (measurable_pi_apply _)
    fun_prop
  · exact measurable_const

/-- Every block sample of `Measure.pi (gueMeasure)` is a.s. a family of Hermitian blocks. -/
theorem ae_blocks_isHermitian (k W : ℕ) (t : ℝ≥0) :
    ∀ᵐ A ∂(Measure.pi fun _ : Fin k => gueMeasure (Fin W) t), ∀ j, (A j).IsHermitian := by
  rw [← map_flatBlocks k W t]
  have hS : MeasurableSet {A : Fin k → Matrix (Fin W) (Fin W) ℂ | ∀ j, hermPart (A j) = A j} := by
    have : {A : Fin k → Matrix (Fin W) (Fin W) ℂ | ∀ j, hermPart (A j) = A j} =
        ⋂ j, ⋂ a, ⋂ b, {A | hermPart (A j) a b = A j a b} := by
      ext A; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h j a b => by rw [h j], fun h j => by ext a b; exact h j a b⟩
    rw [this]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun a =>
      MeasurableSet.iInter fun b => measurableSet_eq_fun ?_ ?_
    · have h1 : Measurable (fun A : Fin k → Matrix (Fin W) (Fin W) ℂ => hermPart (A j)) :=
        (measurable_hermPart W).comp (measurable_pi_apply _)
      fun_prop
    · fun_prop
  have hS' : MeasurableSet {A : Fin k → Matrix (Fin W) (Fin W) ℂ | ∀ j, (A j).IsHermitian} := by
    have e : {A : Fin k → Matrix (Fin W) (Fin W) ℂ | ∀ j, (A j).IsHermitian} =
        {A | ∀ j, hermPart (A j) = A j} := by
      ext A
      exact ⟨fun h j => hermPart_of_isHermitian (h j),
        fun h j => by rw [← h j]; exact hermPart_isHermitian _⟩
    rw [e]; exact hS
  rw [ae_map_iff (measurable_flatBlocks t).aemeasurable hS']
  filter_upwards with ω j
  exact gueOfCoords_isHermitian W t _

/-!
## 4. The count step
-/

open BlockBand.Counting (hermitianReindex nativeEigenCount_hermitianReindex
  measurable_nativeEigenCount measurable_hermitianReindex)
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)

/-- The law of `k` independent `GUE_W(c/W)` blocks (the block factor of `layerLaw`). -/
abbrev blockLaw (k W : ℕ) (c : ℝ) : Measure (Fin k → Matrix (Fin W) (Fin W) ℂ) :=
  Measure.pi fun _ : Fin k => gueMeasure (Fin W) (Real.toNNReal (c / W))

/-- `layerLaw` is `blockLaw` (with `c = 1 - 2b`) times the bond law. -/
theorem layerLaw_eq_blockLaw_prod (W : ℕ) (b : ℝ)
    (σ : BlockBand.Internal.Contracts.Layers.LayerShape) :
    BlockBand.Internal.Contracts.Layers.layerLaw W b σ =
      (blockLaw σ.blocks W (1 - 2 * b)).prod
        (Measure.pi fun _ : Fin σ.blocks => Measure.pi fun _ : Fin σ.ports =>
          BlockBand.Internal.Contracts.Layers.ginibreMeasure (Fin W) (Fin W)
            (Real.toNNReal (b / W))) :=
  rfl

/-- The eigenvalue count of the absorbed matrix in `J`, with multiplicity. -/
def absorbedCount {k W : ℕ} (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) (J : Set ℝ)
    (A : Fin k → Matrix (Fin W) (Fin W) ℂ) : ℕ :=
  PSSS.eigenCount (absorbedMatrix E X A) J

theorem measurable_absorbedCount {k W : ℕ} (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W))
    {J : Set ℝ} (hJ : MeasurableSet J) : Measurable (absorbedCount E X J) :=
  (measurable_nativeEigenCount J hJ).comp (measurable_absorbedMatrix E X)

theorem measurable_hermBlocks (k W : ℕ) : Measurable (hermBlocks (k := k) (W := W)) :=
  measurable_pi_iff.mpr fun j => (measurable_hermPart W).comp (measurable_pi_apply j)

theorem hasLaw_hermBlocks (k W : ℕ) (t : ℝ≥0) :
    HasLaw (hermBlocks (k := k) (W := W)) (Measure.pi fun _ : Fin k => gueMeasure (Fin W) t)
      (Measure.pi fun _ : Fin k => gueMeasure (Fin W) t) := by
  have hB : HasLaw (flatBlocks (k := k) (W := W) t)
      (Measure.pi fun _ : Fin k => gueMeasure (Fin W) t) (stdGaussCoordLaw (FlatGaussCoord k W)) :=
    ⟨(measurable_flatBlocks _).aemeasurable, map_flatBlocks k W _⟩
  have hfix : ∀ ω, hermBlocks (flatBlocks (k := k) (W := W) t ω) = flatBlocks t ω := fun ω =>
    funext fun j => hermPart_of_isHermitian (gueOfCoords_isHermitian W t _)
  exact HasLaw.comp_of_hasLaw_comp (f := hermBlocks) (measurable_hermBlocks k W).aemeasurable hB
    HasLaw.id (by simpa only [hfix] using hB)

/-- **Factorial moments of the count** (the external count theorem after scaling by `√c`). With
`C` the PSSS constant: for all `k`, `W ≥ 1`, `c > 0`, real `E`, Hermitian `X`, `a ≤ b`, `r ≥ 1`,
under `blockLaw k W c` the falling factorial `N(N-1)⋯(N-r+1)` of
`N = #{λ ∈ Spec(D) ∩ [a,b]}`, `D = diag(A_j) - E - X`, is integrable with mean
`≤ (C/√c · kW · (b-a))^r`. Uniform in `E, X`. -/
theorem absorbedCount_factorialMoment (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ c : ℝ, 0 < c →
      ∀ (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) (a b : ℝ), a ≤ b →
      ∀ r : ℕ, 1 ≤ r →
        Integrable (PSSS.factorialCount (absorbedCount E X (Set.Icc a b)) r) (blockLaw k W c) ∧
        (∫ A, PSSS.factorialCount (absorbedCount E X (Set.Icc a b)) r A ∂(blockLaw k W c)) ≤
          (C / Real.sqrt c * ((k : ℝ) * W) * (b - a)) ^ r := by
  obtain ⟨C, hC, h⟩ := hcount
  refine ⟨C, hC, fun k W hW c hc E X a b hab r hr => ?_⟩
  let e : Fin k × Fin W ≃ UniformBlockIndex k W := (uniformBlockEquiv k W).symm
  let G : (Fin k → Matrix (Fin W) (Fin W) ℂ) → PSSS.HermitianMatrix (UniformBlockIndex k W) :=
    fun A => hermitianReindex e ⟨blockDiag (hermBlocks A),
      blockDiag_isHermitian fun j => hermPart_isHermitian (A j)⟩
  have hXE : (-((E : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)) - X.1).IsHermitian := by
    refine IsSelfAdjoint.sub (IsSelfAdjoint.neg ?_) X.2
    unfold IsSelfAdjoint
    rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  let D : (Fin k → Matrix (Fin W) (Fin W) ℂ) → PSSS.HermitianMatrix (UniformBlockIndex k W) :=
    fun _ => hermitianReindex e ⟨_, hXE⟩
  have hGm : Measurable G := by
    refine (measurable_hermitianReindex e).comp (Measurable.subtype_mk ?_)
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    simp only [blockDiag]
    split_ifs
    · have h1 : Measurable (fun A : Fin k → Matrix (Fin W) (Fin W) ℂ => hermBlocks A x.1) :=
        (measurable_pi_apply _).comp (measurable_hermBlocks k W)
      fun_prop
    · exact measurable_const
  have hDm : Measurable D := measurable_const
  have hGeq : (fun A => ((Real.sqrt c)⁻¹ : ℂ) • (G A).1) =
      fun A => blockNoise c (hermBlocks A) := by
    funext A; ext x y; rfl
  have hlaw : HasLaw (fun A => ((Real.sqrt c)⁻¹ : ℂ) • (G A).1)
      ((canonicalMatrixMeasure (uniformBlockSizes k W) (fun _ => hW)).map Subtype.val)
      (blockLaw k W c) := by
    rw [hGeq]
    exact (blockNoise_hasLaw k W hW c hc).comp (hasLaw_hermBlocks k W _)
  have hind : IndepFun D G (blockLaw k W c) := indepFun_const_left _ _
  have hres := h (Fin k → Matrix (Fin W) (Fin W) ℂ) (blockLaw k W c) k (uniformBlockSizes k W)
    (fun _ => hW) c hc G D hGm hDm hlaw hind a b hab r hr
  have hfun : (fun w => PSSS.eigenCount ⟨(D w).1 + (G w).1, (D w).2.add (G w).2⟩
      (Set.Icc a b)) = absorbedCount E X (Set.Icc a b) := by
    funext A
    have hm : (⟨(D A).1 + (G A).1, (D A).2.add (G A).2⟩ :
        PSSS.HermitianMatrix (UniformBlockIndex k W)) =
        hermitianReindex e (absorbedMatrix E X A) := by
      apply Subtype.ext
      ext x y
      simp only [D, G, hermitianReindex, absorbedMatrix, Matrix.reindex_apply,
        Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
      ring
    rw [hm, nativeEigenCount_hermitianReindex]
    rfl
  have hsum : (((∑ j, uniformBlockSizes k W j : ℕ)) : ℝ) = (k : ℝ) * W := by
    simp [uniformBlockSizes]
  rw [hfun, hsum] at hres
  exact hres

/-- `r ≤ N` implies `r! ≤ N(N-1)⋯(N-r+1)`. -/
theorem factorial_le_descFactorial {N r : ℕ} (h : r ≤ N) :
    (r.factorial : ℝ) ≤ (N.descFactorial r : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  have : 1 ≤ N.choose r := Nat.choose_pos h
  exact_mod_cast Nat.le_mul_of_pos_right _ this

/-- **Count tail** (Markov on the factorial moment). With `C` the PSSS constant, for all
`k`, `W ≥ 1`, `c > 0`, real `E`, Hermitian `X`, `a ≤ b` and `r ≥ 1`:
`P(#{λ ∈ Spec(D) ∩ [a,b]} ≥ r) ≤ (C/√c · kW · (b-a))^r / r!` under `blockLaw k W c`.
For `[a,b] = [-t,t]` this is the bound `P(·) ≤ (C_b W t)^{r}/r!` of the Gaussian absorption lemma. -/
theorem absorbedCount_tail (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ c : ℝ, 0 < c →
      ∀ (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) (a b : ℝ), a ≤ b →
      ∀ r : ℕ, 1 ≤ r →
        blockLaw k W c {A | r ≤ absorbedCount E X (Set.Icc a b) A} ≤
          ENNReal.ofReal ((C / Real.sqrt c * ((k : ℝ) * W) * (b - a)) ^ r / r.factorial) := by
  obtain ⟨C, hC, h⟩ := absorbedCount_factorialMoment hcount
  refine ⟨C, hC, fun k W hW c hc E X a b hab r hr => ?_⟩
  obtain ⟨hint, hbd⟩ := h k W hW c hc E X a b hab r hr
  set f := PSSS.factorialCount (absorbedCount E X (Set.Icc a b)) r with hf
  have hnn : 0 ≤ᵐ[blockLaw k W c] f := Filter.Eventually.of_forall fun A => by
    simp only [Pi.zero_apply, hf, PSSS.factorialCount]; positivity
  have hM := mul_meas_ge_le_integral_of_nonneg hnn hint (r.factorial : ℝ)
  have hsub : {A | r ≤ absorbedCount E X (Set.Icc a b) A} ⊆ {A | (r.factorial : ℝ) ≤ f A} :=
    fun A hA => factorial_le_descFactorial hA
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hreal : (blockLaw k W c).real {A | (r.factorial : ℝ) ≤ f A} ≤
      (C / Real.sqrt c * ((k : ℝ) * W) * (b - a)) ^ r / r.factorial := by
    rw [le_div_iff₀ hfac, mul_comm]
    exact hM.trans hbd
  calc blockLaw k W c {A | r ≤ absorbedCount E X (Set.Icc a b) A}
      ≤ blockLaw k W c {A | (r.factorial : ℝ) ≤ f A} := measure_mono hsub
    _ = ENNReal.ofReal ((blockLaw k W c).real {A | (r.factorial : ℝ) ≤ f A}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-!
## 5. The truncated gap `δ` (deterministic)
-/

section Gap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `#{λ ∈ Spec H : |λ| < s}`, with multiplicity. -/
def smallCount (H : PSSS.HermitianMatrix ι) (s : ℝ) : ℕ :=
  PSSS.eigenCount H (Set.Ioo (-s) s)

/-- `δ_m(H) = min(1, |λ|_{(m+1)})`, the truncated absolute value of the `(m+1)`-th eigenvalue
nearest zero, as `sup {s ∈ [0,1] : #{|λ| < s} ≤ m}`. -/
def gapFloor (m : ℕ) (H : PSSS.HermitianMatrix ι) : ℝ :=
  sSup {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ smallCount H s ≤ m}

theorem smallCount_mono (H : PSSS.HermitianMatrix ι) {s s' : ℝ} (h : s ≤ s') :
    smallCount H s ≤ smallCount H s' := by
  classical
  unfold smallCount PSSS.eigenCount
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioo]
  intro hi; constructor <;> linarith [hi.1, hi.2]

theorem smallCount_zero (H : PSSS.HermitianMatrix ι) : smallCount H 0 = 0 := by
  classical
  unfold smallCount PSSS.eigenCount
  simp

theorem gapFloor_set_nonempty (m : ℕ) (H : PSSS.HermitianMatrix ι) :
    {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ smallCount H s ≤ m}.Nonempty :=
  ⟨0, ⟨⟨le_rfl, zero_le_one⟩, by rw [smallCount_zero]; exact Nat.zero_le _⟩⟩

theorem gapFloor_set_bddAbove (m : ℕ) (H : PSSS.HermitianMatrix ι) :
    BddAbove {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ smallCount H s ≤ m} :=
  ⟨1, fun _ hs => hs.1.2⟩

theorem gapFloor_nonneg (m : ℕ) (H : PSSS.HermitianMatrix ι) : 0 ≤ gapFloor m H :=
  le_csSup (gapFloor_set_bddAbove m H)
    ⟨⟨le_rfl, zero_le_one⟩, by rw [smallCount_zero]; exact Nat.zero_le _⟩

theorem gapFloor_le_one (m : ℕ) (H : PSSS.HermitianMatrix ι) : gapFloor m H ≤ 1 :=
  csSup_le (gapFloor_set_nonempty m H) fun _ hs => hs.1.2

/-- At most `m` eigenvalues satisfy `|λ| < δ_m(H)`. -/
theorem smallCount_gapFloor_le (m : ℕ) (H : PSSS.HermitianMatrix ι) :
    smallCount H (gapFloor m H) ≤ m := by
  classical
  by_contra hcon
  replace hcon := not_le.mp hcon
  set δ := gapFloor m H with hδ
  set lam := BlockBand.Foundations.Spectral.increasingEigenvalue H.2
  set F := Finset.univ.filter (fun i => lam i ∈ Set.Ioo (-δ) δ) with hF
  have hFc : smallCount H δ = F.card := by
    unfold smallCount PSSS.eigenCount
    convert rfl
  have hne : F.Nonempty := by
    rw [← Finset.card_pos, ← hFc]; omega
  set s₀ := F.sup' hne (fun i => |lam i|)
  have hs₀ : s₀ < δ := by
    rw [Finset.sup'_lt_iff]
    intro i hi
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioo] at hi
    exact abs_lt.mpr hi
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup (gapFloor_set_nonempty m H) hs₀
  have hle : F.card ≤ smallCount H s := by
    unfold smallCount PSSS.eigenCount
    apply Finset.card_le_card
    intro i hi
    have h1 : |lam i| ≤ s₀ := Finset.le_sup' (fun i => |lam i|) hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ioo]
    exact abs_lt.mp (lt_of_le_of_lt h1 hs)
  have := hsS.2
  omega

/-- For `t ≤ 1`: `δ_m(H) < t ↔ #{|λ| < t} ≥ m + 1`. -/
theorem gapFloor_lt_iff (m : ℕ) (H : PSSS.HermitianMatrix ι) {t : ℝ} (ht : t ≤ 1) :
    gapFloor m H < t ↔ m + 1 ≤ smallCount H t := by
  constructor
  · intro h
    by_contra hcon
    replace hcon := not_le.mp hcon
    have ht0 : 0 ≤ t := (gapFloor_nonneg m H).trans h.le
    have hmem : t ∈ {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ smallCount H s ≤ m} :=
      ⟨⟨ht0, ht⟩, by omega⟩
    exact absurd (le_csSup (gapFloor_set_bddAbove m H) hmem) (not_le.mpr h)
  · intro h
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have := (smallCount_mono H hcon).trans (smallCount_gapFloor_le m H)
    omega

/-- `#{|λ| < t} ≤ #{λ ∈ [-t,t]}`. -/
theorem smallCount_le_Icc (H : PSSS.HermitianMatrix ι) (t : ℝ) :
    smallCount H t ≤ PSSS.eigenCount H (Set.Icc (-t) t) := by
  classical
  unfold smallCount PSSS.eigenCount
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun h => Set.Ioo_subset_Icc_self h

end Gap

/-!
## 6. Inverse moments from a polynomial tail (dyadic decomposition)
-/

/-- Pointwise dyadic majorant: `δ^{-q} ≤ 2^q + Σ_m 2^{(m+2)q} 1{δ < 2^{-m}}` (and `0⁻¹ = 0`). -/
theorem inv_rpow_le_dyadic {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 0 < q) :
    ENNReal.ofReal (δ⁻¹ ^ q) ≤ ENNReal.ofReal ((2 : ℝ) ^ q) +
      ∑' m : ℕ, (if δ < ((2 : ℝ) ^ m)⁻¹ then ENNReal.ofReal (((2 : ℝ) ^ (m + 2)) ^ q) else 0) := by
  rcases hδ.eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, Real.zero_rpow hq.ne', ENNReal.ofReal_zero]; exact bot_le
  have hi0 : 0 < δ⁻¹ := inv_pos.mpr hpos
  by_cases h2 : δ⁻¹ < 2
  · refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
    exact Real.rpow_le_rpow hi0.le h2.le hq.le
  · have h2' : (2 : ℝ) ≤ δ⁻¹ := not_lt.mp h2
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ δ⁻¹)
      (by norm_num : (1 : ℝ) < 2)
    rcases m with _ | m
    · simp at hm2; linarith
    · refine le_add_left (le_trans ?_ (ENNReal.le_tsum m))
      have hlt : δ < ((2 : ℝ) ^ m)⁻¹ := by
        have : (2 : ℝ) ^ m < δ⁻¹ := lt_of_lt_of_le
          (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self m)) hm1
        calc δ = (δ⁻¹)⁻¹ := (inv_inv δ).symm
          _ < ((2 : ℝ) ^ m)⁻¹ := inv_strictAnti₀ (by positivity) this
      simp only [hlt, ↓reduceIte]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hi0.le hm2.le hq.le)

/-- Termwise bound, `β = ⌈b⌉₊`, `1 ≤ q ≤ n - 1`:
`2^{(m+2)q} min(1, (b 2^{-m})^n) ≤ 2^{(β+2)q} 2^β 2^{-m}`. -/
theorem dyadic_term_le {b q : ℝ} (hb : 0 ≤ b) {n : ℕ} (hq1 : 1 ≤ q) (hqn : q + 1 ≤ n) (m : ℕ) :
    ((2 : ℝ) ^ (m + 2)) ^ q * min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n) ≤
      ((2 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q * 2 ^ ⌈b⌉₊ * (2⁻¹ : ℝ) ^ m := by
  set β := ⌈b⌉₊ with hβ
  have hq0 : 0 ≤ q := by linarith
  by_cases hm : m ≤ β
  · have h1 : ((2 : ℝ) ^ (m + 2)) ^ q ≤ ((2 : ℝ) ^ (β + 2)) ^ q :=
      Real.rpow_le_rpow (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega)) hq0
    have h2 : (1 : ℝ) ≤ 2 ^ β * (2⁻¹ : ℝ) ^ m := by
      rw [inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hm
    calc ((2 : ℝ) ^ (m + 2)) ^ q * min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n)
        ≤ ((2 : ℝ) ^ (β + 2)) ^ q * 1 :=
          mul_le_mul h1 (min_le_left _ _) (by positivity) (by positivity)
      _ ≤ ((2 : ℝ) ^ (β + 2)) ^ q * (2 ^ β * (2⁻¹ : ℝ) ^ m) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · have hm' : β < m := not_le.mp hm
    obtain ⟨d, rfl⟩ : ∃ d, m = β + d := ⟨m - β, by omega⟩
    have hd : 1 ≤ d := by omega
    set Y : ℝ := 2 ^ d with hY
    have hY1 : 1 ≤ Y := one_le_pow₀ (by norm_num)
    have hYpos : 0 < Y := by positivity
    have hbβ : b ≤ 2 ^ β := (Nat.le_ceil b).trans (by exact_mod_cast (Nat.lt_two_pow_self).le)
    have hbase : b * ((2 : ℝ) ^ (β + d))⁻¹ ≤ Y⁻¹ := by
      rw [pow_add, mul_inv, ← mul_assoc]
      calc b * ((2 : ℝ) ^ β)⁻¹ * Y⁻¹ ≤ 1 * Y⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact hbβ
        _ = Y⁻¹ := one_mul _
    have hpow : (b * ((2 : ℝ) ^ (β + d))⁻¹) ^ n ≤ Y⁻¹ ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by
      have : (1 : ℝ) ≤ n := by linarith
      have : 1 ≤ n := by exact_mod_cast this
      omega⟩
    have hqn' : q ≤ (n' : ℝ) := by push_cast at hqn; linarith
    have hYq : Y ^ q ≤ Y ^ n' := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hY1 hqn'
    have hsplit : ((2 : ℝ) ^ (β + d + 2)) ^ q = ((2 : ℝ) ^ (β + 2)) ^ q * Y ^ q := by
      rw [show β + d + 2 = (β + 2) + d by ring, pow_add, Real.mul_rpow (by positivity)
        (by positivity)]
    have hkey : Y ^ q * Y⁻¹ ^ (n' + 1) ≤ Y⁻¹ := by
      calc Y ^ q * Y⁻¹ ^ (n' + 1) ≤ Y ^ n' * Y⁻¹ ^ (n' + 1) :=
            mul_le_mul_of_nonneg_right hYq (by positivity)
        _ = Y⁻¹ := by
            rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hYpos.ne', one_pow, one_mul]
    have hrhs : ((2 : ℝ) ^ (β + 2)) ^ q * 2 ^ β * (2⁻¹ : ℝ) ^ (β + d) =
        ((2 : ℝ) ^ (β + 2)) ^ q * Y⁻¹ := by
      have e : (2 : ℝ) ^ β * (2⁻¹ : ℝ) ^ (β + d) = Y⁻¹ := by
        rw [hY, inv_pow, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      rw [mul_assoc _ ((2 : ℝ) ^ β), e]
    rw [hrhs, hsplit]
    calc ((2 : ℝ) ^ (β + 2)) ^ q * Y ^ q * min 1 ((b * ((2 : ℝ) ^ (β + d))⁻¹) ^ (n' + 1))
        ≤ ((2 : ℝ) ^ (β + 2)) ^ q * Y ^ q * Y⁻¹ ^ (n' + 1) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hpow) (by positivity)
      _ = ((2 : ℝ) ^ (β + 2)) ^ q * (Y ^ q * Y⁻¹ ^ (n' + 1)) := by ring
      _ ≤ ((2 : ℝ) ^ (β + 2)) ^ q * Y⁻¹ := mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Final constant: `2^q + 2 · 2^{(β+2)q} 2^β ≤ (4^{β+2})^q` for `q ≥ 1`. -/
theorem dyadic_final_le {b q : ℝ} (hq1 : 1 ≤ q) :
    (2 : ℝ) ^ q + ((2 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q * 2 ^ ⌈b⌉₊ * 2 ≤ ((4 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q := by
  set β := ⌈b⌉₊
  have hq0 : 0 ≤ q := by linarith
  set Z := ((2 : ℝ) ^ (β + 2)) ^ q with hZ
  have h4 : ((4 : ℝ) ^ (β + 2)) ^ q = Z * Z := by
    rw [hZ, ← Real.mul_rpow (by positivity) (by positivity), ← mul_pow]; norm_num
  have hP1 : (1 : ℝ) ≤ 2 ^ β := one_le_pow₀ (by norm_num)
  have hP : (2 : ℝ) ^ (β + 2) = 4 * 2 ^ β := by rw [pow_add]; ring
  have hZ1 : (2 : ℝ) ^ (β + 2) ≤ Z := by
    have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ) ^ (β + 2))
      (one_le_pow₀ (by norm_num)) hq1
    rwa [Real.rpow_one] at this
  have h2q : (2 : ℝ) ^ q ≤ Z :=
    Real.rpow_le_rpow (by norm_num) (by rw [hP]; nlinarith) hq0
  rw [h4]
  nlinarith

/-- **Inverse moments from a tail.** If `0 ≤ δ` is measurable and
`P(δ < 2^{-m}) ≤ (b 2^{-m})^n` for all `m`, then for `1 ≤ q ≤ n - 1`:
`E[δ^{-q}] ≤ (4^{⌈b⌉₊+2})^q`. Any probability space. -/
theorem lintegral_inv_rpow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (δ : Ω → ℝ) (hδm : Measurable δ) (hδ0 : ∀ ω, 0 ≤ δ ω)
    {b q : ℝ} (hb : 0 ≤ b) {n : ℕ} (hq1 : 1 ≤ q) (hqn : q + 1 ≤ n)
    (htail : ∀ m : ℕ, μ {ω | δ ω < ((2 : ℝ) ^ m)⁻¹} ≤
      ENNReal.ofReal ((b * ((2 : ℝ) ^ m)⁻¹) ^ n)) :
    ∫⁻ ω, ENNReal.ofReal ((δ ω)⁻¹ ^ q) ∂μ ≤ ENNReal.ofReal (((4 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q) := by
  set β := ⌈b⌉₊
  set K : ℝ := ((2 : ℝ) ^ (β + 2)) ^ q * 2 ^ β with hK
  have hK0 : 0 ≤ K := by positivity
  have hq0 : 0 < q := by linarith
  let S : ℕ → Set Ω := fun m => {ω | δ ω < ((2 : ℝ) ^ m)⁻¹}
  have hS : ∀ m, MeasurableSet (S m) := fun m => measurableSet_lt hδm measurable_const
  let w : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (((2 : ℝ) ^ (m + 2)) ^ q)
  have hpt : ∀ ω, ENNReal.ofReal ((δ ω)⁻¹ ^ q) ≤
      ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m, (S m).indicator (fun _ => w m) ω := by
    intro ω
    exact (inv_rpow_le_dyadic (hδ0 ω) hq0).trans (le_of_eq rfl)
  have hterm : ∀ m, w m * μ (S m) ≤ ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) := by
    intro m
    have hμ : μ (S m) ≤ ENNReal.ofReal (min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n)) := by
      rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
      exact le_min prob_le_one (htail m)
    calc w m * μ (S m) ≤ w m * ENNReal.ofReal (min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n)) :=
          by gcongr
      _ = ENNReal.ofReal (((2 : ℝ) ^ (m + 2)) ^ q * min 1 ((b * ((2 : ℝ) ^ m)⁻¹) ^ n)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) :=
          ENNReal.ofReal_le_ofReal (dyadic_term_le hb hq1 hqn m)
  have hgeom : ∑' m : ℕ, ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) = ENNReal.ofReal K * 2 := by
    have e : ∀ m : ℕ, ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) = ENNReal.ofReal K * 2⁻¹ ^ m := by
      intro m
      rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    simp only [e, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
      inv_inv]
  calc ∫⁻ ω, ENNReal.ofReal ((δ ω)⁻¹ ^ q) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m, (S m).indicator (fun _ => w m) ω) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m, w m * μ (S m) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum (fun m => (measurable_const.indicator (hS m)).aemeasurable)]
        congr 1
        exact tsum_congr fun m => lintegral_indicator_const (hS m) (w m)
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ q) + ∑' m : ℕ, ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ m) :=
        by gcongr with m; exact hterm m
    _ = ENNReal.ofReal ((2 : ℝ) ^ q + K * 2) := by
        rw [hgeom, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul hK0, ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (((4 : ℝ) ^ (⌈b⌉₊ + 2)) ^ q) :=
        ENNReal.ofReal_le_ofReal (dyadic_final_le hq1)

/-!
## 7. Mathlib eigenvalue form of the counts
-/

/-- `PSSS.eigenCount` is the multiplicity count of Mathlib's `IsHermitian.eigenvalues`. -/
theorem eigenCount_eq_card_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : PSSS.HermitianMatrix ι) (J : Set ℝ) :
    PSSS.eigenCount H J = Nat.card {j : ι // H.2.eigenvalues j ∈ J} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold PSSS.eigenCount
  refine Finset.card_equiv BlockBand.Foundations.Spectral.increasingIndex fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]

/-- `#{|λ| < τ}` as a cardinality, the form of `finrank_lowSubspace_le`
(`Nat.card_eq_fintype_card`). -/
theorem smallCount_eq_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : PSSS.HermitianMatrix ι) (τ : ℝ) :
    smallCount H τ = Nat.card {j : ι // |H.2.eigenvalues j| < τ} := by
  rw [smallCount, eigenCount_eq_card_eigenvalues]
  congr 2
  ext j
  simp only [Set.mem_Ioo, abs_lt]

/-!
## 8. The gap of the absorbed matrix: tail and inverse moments
-/

/-- `δ = min(1, |λ|_{(m+1)})` for `D = diag(A_j) - E - X`. -/
def absorbedGap {k W : ℕ} (m : ℕ) (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W))
    (A : Fin k → Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  gapFloor m (absorbedMatrix E X A)

theorem absorbedGap_nonneg {k W : ℕ} (m : ℕ) (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W))
    (A : Fin k → Matrix (Fin W) (Fin W) ℂ) : 0 ≤ absorbedGap m E X A :=
  gapFloor_nonneg m _

theorem absorbedGap_le_one {k W : ℕ} (m : ℕ) (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W))
    (A : Fin k → Matrix (Fin W) (Fin W) ℂ) : absorbedGap m E X A ≤ 1 :=
  gapFloor_le_one m _

theorem measurable_absorbedGap {k W : ℕ} (m : ℕ) (E : ℝ)
    (X : PSSS.HermitianMatrix (Fin k × Fin W)) :
    Measurable (absorbedGap (k := k) (W := W) m E X) := by
  apply measurable_of_Iio
  intro t
  by_cases ht : t ≤ 1
  · have e : absorbedGap (k := k) (W := W) m E X ⁻¹' Set.Iio t =
        absorbedCount E X (Set.Ioo (-t) t) ⁻¹' Set.Ici (m + 1) := by
      ext A
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ici, absorbedGap,
        gapFloor_lt_iff m _ ht]
      rfl
    rw [e]
    exact measurable_absorbedCount E X measurableSet_Ioo measurableSet_Ici
  · have e : absorbedGap (k := k) (W := W) m E X ⁻¹' Set.Iio t = Set.univ := by
      ext A
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_univ, iff_true]
      exact lt_of_le_of_lt (absorbedGap_le_one m E X A) (not_le.mp ht)
    rw [e]
    exact MeasurableSet.univ

/-- `(xW)^n/n! ≤ (8e·x)^n` for `n = ⌊W/8⌋ + 1` (`n! ≥ (n/e)^n`, `W < 8n`). -/
theorem factorial_count_bound_le {x : ℝ} (hx : 0 ≤ x) (W : ℕ) :
    (x * W) ^ (W / 8 + 1) / ((W / 8 + 1).factorial : ℝ) ≤ (8 * Real.exp 1 * x) ^ (W / 8 + 1) := by
  set n := W / 8 + 1 with hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hWn : (W : ℝ) ≤ 8 * n := by
    have : W ≤ 8 * n := by omega
    exact_mod_cast this
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hexp := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hn0.le n
  have e1 : (x * W) ^ n / (n.factorial : ℝ) = (x * W / n) ^ n * ((n : ℝ) ^ n / n.factorial) := by
    rw [div_pow]; field_simp
  rw [e1]
  calc (x * W / n) ^ n * ((n : ℝ) ^ n / n.factorial)
      ≤ (x * W / n) ^ n * Real.exp n :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (x * W / n * Real.exp 1) ^ n := by rw [mul_pow, Real.exp_one_pow]
    _ ≤ (8 * Real.exp 1 * x) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        have : x * W / n ≤ 8 * x := by
          rw [div_le_iff₀ hn0]; nlinarith
        nlinarith [Real.exp_pos 1]

/-- The tail constant `C_b' = 16 e C k / √c` (`C` the PSSS constant). -/
def gapTailConstant (C : ℝ) (k : ℕ) (c : ℝ) : ℝ :=
  16 * Real.exp 1 * C * k / Real.sqrt c

/-- **Gap tail**. With `C` the PSSS constant, for
all `k`, `W ≥ 1`, `c > 0`, real `E`, Hermitian `X` and `0 < t ≤ 1`, under `blockLaw k W c`:
`P(δ < t) ≤ (C_b' t)^{⌊W/8⌋+1}`, `δ = min(1, |λ|_{(⌊W/8⌋+1)}(D))`, `C_b' = gapTailConstant C k c`.
Uniform in `W, E, X`. (In particular `P(δ = 0) = 0`.) -/
theorem absorbedGap_tail (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ c : ℝ, 0 < c →
      ∀ (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) (t : ℝ), 0 < t → t ≤ 1 →
        blockLaw k W c {A | absorbedGap (W / 8) E X A < t} ≤
          ENNReal.ofReal ((gapTailConstant C k c * t) ^ (W / 8 + 1)) := by
  obtain ⟨C, hC, h⟩ := absorbedCount_tail hcount
  refine ⟨C, hC, fun k W hW c hc E X t ht ht1 => ?_⟩
  have hsub : {A | absorbedGap (W / 8) E X A < t} ⊆
      {A | W / 8 + 1 ≤ absorbedCount E X (Set.Icc (-t) t) A} := by
    intro A hA
    exact ((gapFloor_lt_iff (W / 8) _ ht1).mp hA).trans (smallCount_le_Icc _ t)
  refine (measure_mono hsub).trans ((h k W hW c hc E X (-t) t (by linarith) (W / 8 + 1)
    (by omega)).trans (ENNReal.ofReal_le_ofReal ?_))
  have hx : 0 ≤ C / Real.sqrt c * k * (2 * t) := by positivity
  have e1 : C / Real.sqrt c * ((k : ℝ) * W) * (t - -t) = C / Real.sqrt c * k * (2 * t) * W := by
    ring
  have e2 : gapTailConstant C k c * t = 8 * Real.exp 1 * (C / Real.sqrt c * k * (2 * t)) := by
    unfold gapTailConstant; ring
  rw [e1, e2]
  exact factorial_count_bound_le hx W

/-- The moment constant `C_b = 4^{⌈C_b'⌉₊ + 2}`, depending only on `C, k, c`. -/
def gapMomentConstant (C : ℝ) (k : ℕ) (c : ℝ) : ℝ :=
  4 ^ (⌈gapTailConstant C k c⌉₊ + 2)

theorem gapMomentConstant_pos (C : ℝ) (k : ℕ) (c : ℝ) : 0 < gapMomentConstant C k c := by
  unfold gapMomentConstant; positivity

/-- `1 ≤ q ≤ W/16` implies `q + 1 ≤ ⌊W/8⌋ + 1`. -/
theorem q_add_one_le_of_le_div {q : ℝ} {W : ℕ} (hq1 : 1 ≤ q) (hqW : q ≤ (W : ℝ) / 16) :
    q + 1 ≤ ((W / 8 + 1 : ℕ) : ℝ) := by
  have h8 : W ≤ 8 * (W / 8) + 7 := by omega
  have h8' : (W : ℝ) ≤ 8 * ((W / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast h8
  push_cast
  linarith

/-- **Inverse moments of the gap** (`‖δ⁻¹‖_{L^q} ≤ C_b` for `q ≤ ε₂ W`). With `C` the PSSS constant and `ε₂ = 1/16`: for all `k`, `W ≥ 1`, `c > 0`, real `E`,
Hermitian `X` and real `q` with `1 ≤ q ≤ W/16`,
`E[δ^{-q}] ≤ C_b^q` under `blockLaw k W c`, `C_b = gapMomentConstant C k c` (depending only on
`C, k, c`; uniform in `W, E, X, q`). -/
theorem absorbedGap_inv_moment (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ c : ℝ, 0 < c →
      ∀ (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) (q : ℝ), 1 ≤ q → q ≤ (W : ℝ) / 16 →
        ∫⁻ A, ENNReal.ofReal ((absorbedGap (W / 8) E X A)⁻¹ ^ q) ∂(blockLaw k W c) ≤
          ENNReal.ofReal (gapMomentConstant C k c ^ q) := by
  obtain ⟨C, hC, h⟩ := absorbedGap_tail hcount
  refine ⟨C, hC, fun k W hW c hc E X q hq1 hqW => ?_⟩
  have hb : 0 ≤ gapTailConstant C k c := by unfold gapTailConstant; positivity
  refine lintegral_inv_rpow_le_of_tail (blockLaw k W c) (absorbedGap (W / 8) E X)
    (measurable_absorbedGap _ E X) (absorbedGap_nonneg _ E X) hb hq1
    (q_add_one_le_of_le_div hq1 hqW) fun m => ?_
  exact h k W hW c hc E X _ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))

/-- **`L^q` form**: `‖δ⁻¹‖_{L^q(blockLaw)} ≤ C_b` for `1 ≤ q ≤ W/16`, and `δ⁻¹ ∈ L^q`. -/
theorem absorbedGap_inv_eLpNorm (hcount : ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ c : ℝ, 0 < c →
      ∀ (E : ℝ) (X : PSSS.HermitianMatrix (Fin k × Fin W)) (q : ℝ), 1 ≤ q → q ≤ (W : ℝ) / 16 →
        eLpNorm (fun A => (absorbedGap (W / 8) E X A)⁻¹) (ENNReal.ofReal q) (blockLaw k W c) ≤
            ENNReal.ofReal (gapMomentConstant C k c) ∧
          MemLp (fun A => (absorbedGap (W / 8) E X A)⁻¹) (ENNReal.ofReal q) (blockLaw k W c) := by
  obtain ⟨C, hC, h⟩ := absorbedGap_inv_moment hcount
  refine ⟨C, hC, fun k W hW c hc E X q hq1 hqW => ?_⟩
  have hq0 : 0 < q := by linarith
  have hmeas : AEStronglyMeasurable (fun A => (absorbedGap (W / 8) E X A)⁻¹) (blockLaw k W c) :=
    (measurable_absorbedGap _ E X).inv.aestronglyMeasurable
  have hCb := gapMomentConstant_pos C k c
  have hbound : eLpNorm (fun A => (absorbedGap (W / 8) E X A)⁻¹) (ENNReal.ofReal q)
      (blockLaw k W c) ≤ ENNReal.ofReal (gapMomentConstant C k c) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top hmeas,
      ENNReal.toReal_ofReal hq0.le]
    have hint : ∫⁻ A, ‖(absorbedGap (W / 8) E X A)⁻¹‖ₑ ^ q ∂(blockLaw k W c) =
        ∫⁻ A, ENNReal.ofReal ((absorbedGap (W / 8) E X A)⁻¹ ^ q) ∂(blockLaw k W c) := by
      refine lintegral_congr fun A => ?_
      have h0 : 0 ≤ (absorbedGap (W / 8) E X A)⁻¹ := inv_nonneg.mpr (absorbedGap_nonneg _ E X A)
      rw [Real.enorm_eq_ofReal h0, ENNReal.ofReal_rpow_of_nonneg h0 hq0.le]
    rw [hint]
    calc (∫⁻ A, ENNReal.ofReal ((absorbedGap (W / 8) E X A)⁻¹ ^ q) ∂(blockLaw k W c)) ^ (1 / q)
        ≤ (ENNReal.ofReal (gapMomentConstant C k c ^ q)) ^ (1 / q) :=
          ENNReal.rpow_le_rpow (h k W hW c hc E X q hq1 hqW) (by positivity)
      _ = ENNReal.ofReal (gapMomentConstant C k c) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
            Real.rpow_rpow_inv hCb.le hq0.ne']
  exact ⟨hbound, memLp_iff.mpr (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)⟩

end BlockBand.Layers
