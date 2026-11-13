module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GenChain
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.Brackets
public import BlockBand.SourceProcess.Stochastic.GramChar.Bilinear
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.GramCharacteristics
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The source generator of a function of the Gram pair depends only on the Gram pair

For a `C²` function `f` of the Gram pair `(M, B)` and a constrained frame `V`
(`IsNearProjection P Naux`, `TwoProjection P 𝖣 V`), the generator of the finite source equation
applied to `W ↦ f(gramPair P W)` at `V` equals
`Df(G)[(0, -(D₀/2) g B)] + ½ ∑_a D²f(G)[ν_a, ν_a]` with `ν_a = gramNoise` (`sdeGenerator_comp_gramPair`),
and the second-order sum is determined by the Gram covariance
(the sesquilinear brackets reduce to the bilinear ones because `ν_a` is a pair of
Hermitian matrices). Hence (`gram_generator_congr`) two constrained realizations — in any ambient
dimensions, ranks `Naux`, near projections — with the same Gram pair have the same generator
value. This removes the `Naux`-dependence of the drift `-(D₀Naux/4)PV` (it cancels against the
Itô term `dA P dAᴴ = (D₀(Naux - g)/2)P dt`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramChar

section Generic
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {X : Type*} [Fintype X]

/-- `genSplit` depends on the noise family only through its complex brackets. -/
theorem genSplit_congr_of_brackets (f : F → ℝ) (G d : F) (coord : X → F → ℂ) (u v : X → F)
    (hdec : ∀ x, x = ∑ e, ((coord e x).re • u e + (coord e x).im • v e))
    {κ κ' : Type*} [Fintype κ] [Fintype κ'] (ν : κ → F) (ν' : κ' → F)
    (h1 : ∀ e e', ∑ a, coord e (ν a) * coord e' (ν a) = ∑ b, coord e (ν' b) * coord e' (ν' b))
    (h2 : ∀ e e', ∑ a, coord e (ν a) * star (coord e' (ν a)) =
      ∑ b, coord e (ν' b) * star (coord e' (ν' b))) :
    genSplit f G d ν = genSplit f G d ν' := by
  unfold genSplit
  have := sum_bilin_eq_of_brackets
    (ContinuousLinearMap.toLinearMap₁₂ (fderiv ℝ (fderiv ℝ f) G)) coord u v hdec ν ν' h1 h2
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at this
  rw [this]

end Generic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Complex coordinate unit of the Gram coordinate `e`. -/
def gramUnit (e : Fin 2 × c × c) : Matrix c c ℂ × Matrix c c ℂ :=
  if e.1 = 0 then (Matrix.single e.2.1 e.2.2 1, 0) else (0, Matrix.single e.2.1 e.2.2 1)

theorem sum_gramEntry_smul_gramUnit (x : Matrix c c ℂ × Matrix c c ℂ) :
    ∑ e, gramEntry e x • gramUnit e = x := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [gramEntry, gramUnit, Fin.isValue, ↓reduceIte, one_ne_zero, Prod.smul_mk,
    smul_zero, Fintype.sum_prod_type]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, add_zero, Finset.sum_const_zero, smul_single,
      smul_eq_mul, mul_one]
    exact (matrix_eq_sum_single x.1).symm
  · simp only [Prod.snd_add, Prod.snd_sum, zero_add, Finset.sum_const_zero, smul_single,
      smul_eq_mul, mul_one]
    exact (matrix_eq_sum_single x.2).symm

/-- Real decomposition of a Gram pair along `gramUnit e` and `i • gramUnit e`. -/
theorem gram_decomp (x : Matrix c c ℂ × Matrix c c ℂ) :
    x = ∑ e, ((gramEntry e x).re • gramUnit e + (gramEntry e x).im • (Complex.I • gramUnit e)) := by
  conv_lhs => rw [← sum_gramEntry_smul_gramUnit x]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
    ← add_smul]
  congr 1
  exact (Complex.re_add_im _).symm

/-- The target Gram drift as a function of the Gram pair. -/
def gramDriftG (D0 : ℝ) (D : Matrix c c ℂ) (G : Matrix c c ℂ × Matrix c c ℂ) :
    Matrix c c ℂ × Matrix c c ℂ :=
  (0, (-(((D0 / 2 : ℝ) : ℂ) * gramScalar D G.1)) • G.2)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(V, W) ↦ (Vᴴ W, Vᴴ P W)` as a continuous real-bilinear map, elaborated with the Frobenius
topology of this file (same map as `GramChar.gramPairBil`). -/
def gramBil (P : Matrix ι ι ℂ) :=
  toCLM₂ (F₁ := Matrix ι c ℂ) (F₂ := Matrix ι c ℂ) (F₃ := Matrix c c ℂ × Matrix c c ℂ)
    (LinearMap.mk₂ ℝ (fun V W => (Vᴴ * W, Vᴴ * P * W))
    (fun _ _ _ => by simp only [conjTranspose_add, Matrix.add_mul, Prod.mk_add_mk])
    (fun _ _ _ => by
      simp only [conjTranspose_smul, star_trivial, Matrix.smul_mul, Prod.smul_mk])
    (fun _ _ _ => by simp only [Matrix.mul_add, Prod.mk_add_mk])
    (fun _ _ _ => by simp only [Matrix.mul_smul, Prod.smul_mk]))

omit [DecidableEq c] [DecidableEq ι] in
theorem gramBil_apply (P : Matrix ι ι ℂ) (V W : Matrix ι c ℂ) :
    gramBil P V W = (Vᴴ * W, Vᴴ * P * W) := rfl

omit [DecidableEq c] in
theorem gramBil_drift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) :
    gramBil P V (sourceDrift D0 Naux P V) + gramBil P (sourceDrift D0 Naux P V) V +
        ∑ a, gramBil P (sourceDiffusion D0 P D a V) (sourceDiffusion D0 P D a V) =
      gramDrift D0 Naux P D V := by
  ext : 1
  · simp only [Prod.fst_add, Prod.fst_sum, gramBil_apply, gramDrift, quadDrift,
      quadVariation, Matrix.mul_one]
    abel
  · simp only [Prod.snd_add, Prod.snd_sum, gramBil_apply, gramDrift, quadDrift,
      quadVariation]
    abel

omit [DecidableEq c] in
/-- **Generator of a function of the Gram pair** (every frame). -/
theorem sdeGenerator_comp_gramPair {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (fun W => f (gramPair P W)) V =
      genSplit f (gramPair P V) (gramDrift D0 Naux P D V) (fun a => gramNoise D0 P D a V) := by
  have h := sdeGenerator_comp_bilin (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) hf
    (gramBil (c := c) P) V
  rw [gramBil_drift] at h
  exact h

omit [DecidableEq c] in
theorem gramNoise_herm (D0 : ℝ) {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (D : Matrix c c ℂ)
    (a : SourceNoise ι) (V : Matrix ι c ℂ) :
    (gramNoise D0 P D a V).1ᴴ = (gramNoise D0 P D a V).1 ∧
      (gramNoise D0 P D a V).2ᴴ = (gramNoise D0 P D a V).2 := by
  constructor
  · simp only [gramNoise, gramVariation, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose]
    exact add_comm _ _
  · simp only [gramNoise, nearVariation, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hPH, Matrix.mul_assoc]
    exact add_comm _ _

omit [Fintype c] [DecidableEq c] in
theorem star_gramEntry_of_herm {x : Matrix c c ℂ × Matrix c c ℂ} (h1 : x.1ᴴ = x.1)
    (h2 : x.2ᴴ = x.2) (e : Fin 2 × c × c) :
    star (gramEntry e x) = gramEntry (e.1, e.2.2, e.2.1) x := by
  obtain ⟨r, i, j⟩ := e
  by_cases hr : r = 0
  · simp only [gramEntry, hr, ↓reduceIte]
    conv_rhs => rw [← h1]
    rw [conjTranspose_apply]
  · simp only [gramEntry, hr, ↓reduceIte]
    conv_rhs => rw [← h2]
    rw [conjTranspose_apply]

/-- **The generator of a function of the Gram pair depends only on the Gram pair.** -/
theorem gram_generator_congr {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {D0 : ℝ} (hD0 : 0 ≤ D0)
    {Naux Naux' : ℕ} {P : Matrix ι ι ℂ} {P' : Matrix ι' ι' ℂ} {D : Matrix c c ℂ}
    {V : Matrix ι c ℂ} {V' : Matrix ι' c ℂ} (hP : IsNearProjection P Naux)
    (hP' : IsNearProjection P' Naux') (hD : IsSignature D) (hV : TwoProjection P D V)
    (hV' : TwoProjection P' D V') (hG : gramPair P V = gramPair P' V')
    {f : Matrix c c ℂ × Matrix c c ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) (fun W => f (gramPair P W)) V =
      sdeGenerator (sourceDrift D0 Naux' P') (sourceDiffusion D0 P' D)
        (fun W => f (gramPair P' W)) V' := by
  rw [sdeGenerator_comp_gramPair hf, sdeGenerator_comp_gramPair hf]
  have hdr : gramDrift D0 Naux P D V = gramDriftG D0 D (gramPair P V) := by
    rw [gramDrift_eq hD0 hP hV]; rfl
  have hdr' : gramDrift D0 Naux' P' D V' = gramDriftG D0 D (gramPair P' V') := by
    rw [gramDrift_eq hD0 hP' hV']; rfl
  rw [hdr, hdr', hG]
  have h1 : ∀ e e', ∑ a, gramEntry e (gramNoise D0 P D a V) * gramEntry e' (gramNoise D0 P D a V) =
      ∑ b, gramEntry e (gramNoise D0 P' D b V') * gramEntry e' (gramNoise D0 P' D b V') :=
    fun e e' => by
      rw [gramNoise_cov_entry hD0 hP hD hV, gramNoise_cov_entry hD0 hP' hD hV', hG]
  have h2 : ∀ e e', ∑ a, gramEntry e (gramNoise D0 P D a V) *
        star (gramEntry e' (gramNoise D0 P D a V)) =
      ∑ b, gramEntry e (gramNoise D0 P' D b V') * star (gramEntry e' (gramNoise D0 P' D b V')) :=
    fun e e' => by
      simp only [fun a => star_gramEntry_of_herm (gramNoise_herm D0 hP.1 D a V).1
        (gramNoise_herm D0 hP.1 D a V).2 e',
        fun b => star_gramEntry_of_herm (gramNoise_herm D0 hP'.1 D b V').1
        (gramNoise_herm D0 hP'.1 D b V').2 e']
      exact h1 e _
  exact genSplit_congr_of_brackets f _ _ gramEntry gramUnit (fun e => Complex.I • gramUnit e)
    gram_decomp _ _ h1 h2

end BlockBand.SourceProcess.Stochastic.GramUniqueness
