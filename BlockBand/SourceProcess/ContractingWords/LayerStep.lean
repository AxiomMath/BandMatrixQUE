module

public import BlockBand.SourceProcess.ContractingWords.LayerCore
public import BlockBand.SourceProcess.ContractingWords.LayerInj

/-!
# One fresh layer, a product of words: mean and centered part

`layer_step`: on a probability space `ν` (one fresh layer), random `N, D, S` with `‖S_σ‖ ≤ 1` a.s.,
`T_σ = NS_σN*` with integrable entries, `‖ET_σ‖ ≤ μ`, centered bilinear bound `β` at exponent
`(d+2)r`, targets `B'_σ` (`‖B'_σ‖ ≤ 1`, `‖ET_σ - B'_σ‖ ≤ e`) and the moment
`‖G^{2(d+1)²}‖_r ≤ G_m`, `G = 1 + ‖N‖ + ‖D‖`. For an admitted product of degree `≤ d`, with
deterministic Hermitian letters (`Tr|A_ℓ| ≤ K`) and injections `|c_ℓ| ≤ c₀/W²`, the new value
`Z = newProd A c N D S Zs` satisfies, with `Γ = max(1,K)^d`, `B = dβ`:
* `|EZ - coreProd A B' Zs| ≤ Γ(2^d(1+μ)^d B²(1+B^d) + d e(2+e)^d) + C_inj G_m/W`;
* `‖Z - EZ‖_r ≤ 2Γ 2^d(1+μ)^d B(1+B^d) + 2C_inj G_m/W`,
`C_inj = d²(3+d)^d(3(1+K+c₀))^{(d+1)²}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

theorem HasCutRep.mono {n S : Type} [Fintype n] [DecidableEq n] {F : (S → Matrix n n ℂ) → ℂ}
    {d d' : ℕ} {Γ Γ' : ℝ} (h : HasCutRep F d Γ) (hd : d ≤ d') (hΓ : Γ ≤ Γ') : HasCutRep F d' Γ' := by
  obtain ⟨P, hP, σ, ι, hι, c, x, y, h1, h2, h3, h4⟩ := h
  exact ⟨P, hP, σ, ι, hι, c, x, y, h1.trans hd, h2.trans hΓ, h3, h4⟩

/-- The cut representation of `coreProd A · Zs`. -/
theorem coreProd_rep (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {K : ℝ}
    (hA : ∀ ℓ, (A ℓ).IsHermitian) (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K)
    {Zs : List (TraceWord nT nI)} (hZ : IsAdmittedProduct Zs) {d : ℕ} (hd : productDegree Zs ≤ d) :
    HasCutRep (fun T => coreProd A T Zs) d (max 1 K ^ d) := by
  have h := product_rep (Zs.map (letWord A))
    (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      simpa [letWord] using hZ v hv)
    (fun w hw x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact hA y.1)
  have hdeg : ((Zs.map (letWord A)).map List.length).sum = productDegree Zs := by
    simp [productDegree, letWord, Function.comp_def]
  have hΓ : ((Zs.map (letWord A)).map wordNuc).prod ≤ max 1 K ^ d := by
    have hw : ∀ w : TraceWord nT nI, wordNuc (letWord A w) ≤ max 1 K ^ w.length := fun w => by
      simp only [wordNuc, letWord, List.map_map]
      refine (list_prod_le_pow_length w _ (fun _ _ => nuclearNorm_nonneg _) fun x _ =>
        ?_).trans_eq rfl
      exact (hAK x.1).trans (le_max_right _ _)
    have h1 : ((Zs.map (letWord A)).map wordNuc).prod ≤ max 1 K ^ productDegree Zs := by
      clear h hdeg hd
      induction Zs with
      | nil => simp [productDegree]
      | cons w Zs ih =>
        simp only [List.map_cons, List.prod_cons, productDegree, List.sum_cons, pow_add] at ih ⊢
        exact mul_le_mul (hw w) (ih fun v hv => hZ v (List.mem_cons_of_mem _ hv))
          (List.prod_nonneg fun x hx => by
            obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact wordNuc_nonneg _) (by positivity)
    exact h1.trans (pow_le_pow_right₀ (le_max_left _ _) hd)
  have e : (fun T => coreProd A T Zs) = fun T => ((Zs.map (letWord A)).map (matWord T)).prod := by
    funext T; simp [coreProd, List.map_map, Function.comp_def]
  rw [e]
  exact h.mono (hdeg.le.trans hd) hΓ

theorem inj_alg (d : ℕ) (a G W : ℝ) :
    (d : ℝ) * d / W * (a * G ^ 2) ^ (d + 1) * ((3 + d) * (a * G ^ 2) ^ (d + 1)) ^ d =
      (d * d * (3 + d) ^ d * a ^ ((d + 1) ^ 2)) / W * G ^ (2 * (d + 1) ^ 2) := by
  have h1 : ∀ X : ℝ, X ^ (d + 1) * ((3 + d) * X ^ (d + 1)) ^ d = (3 + d) ^ d * X ^ ((d + 1) ^ 2) :=
    fun X => by
      rw [mul_pow, ← pow_mul, show (d + 1) ^ 2 = (d + 1) + (d + 1) * d by ring, pow_add]; ring
  have h2 : (a * G ^ 2) ^ ((d + 1) ^ 2) = a ^ ((d + 1) ^ 2) * G ^ (2 * (d + 1) ^ 2) := by
    rw [mul_pow, ← pow_mul]
  calc (d : ℝ) * d / W * (a * G ^ 2) ^ (d + 1) * ((3 + d) * (a * G ^ 2) ^ (d + 1)) ^ d =
      d * d / W * ((a * G ^ 2) ^ (d + 1) * ((3 + d) * (a * G ^ 2) ^ (d + 1)) ^ d) := by ring
    _ = d * d / W * ((3 + d) ^ d * (a * G ^ 2) ^ ((d + 1) ^ 2)) := by rw [h1]
    _ = _ := by rw [h2]; ring

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

theorem norm_integral_le_of_eLpNorm {f : Ω → ℂ} (hf : AEStronglyMeasurable f ν) {r C : ℝ}
    (hr : 1 ≤ r) (hC : 0 ≤ C) (h : eLpNorm f (ENNReal.ofReal r) ν ≤ ENNReal.ofReal C) :
    ‖∫ ω, f ω ∂ν‖ ≤ C := by
  have h1 : eLpNorm f 1 ν ≤ ENNReal.ofReal C :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by simpa using hr)).trans h
  rw [eLpNorm_one_eq_lintegral_enorm hf] at h1
  refine (norm_integral_le_lintegral_norm _).trans ?_
  have e : ∫⁻ ω, ENNReal.ofReal ‖f ω‖ ∂ν = ∫⁻ ω, ‖f ω‖ₑ ∂ν :=
    lintegral_congr fun ω => ofReal_norm (f ω)
  rw [e]
  exact ENNReal.toReal_le_of_le_ofReal hC h1

theorem eLpNorm_const_le' (c : ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun _ : Ω => c) p ν ≤ ENNReal.ofReal ‖c‖ := by
  refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const (C := ‖c‖)
    (Filter.Eventually.of_forall fun _ => le_rfl)).trans ?_
  simp

/-- **One fresh layer, a product of words.** -/
theorem layer_step (hW : 1 ≤ W)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c : TraceLetter nT nI → ℝ)
    {K c₀ : ℝ} (hK : 0 ≤ K) (hc₀ : 0 ≤ c₀) (hA : ∀ ℓ, (A ℓ).IsHermitian)
    (hAK : ∀ ℓ, nuclearNorm (A ℓ) ≤ K) (hc : ∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2)
    (N : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (D : Ω → Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (S : Ω → Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hS : ∀ᵐ y ∂ν, ∀ σ, ‖S y σ‖ ≤ 1)
    (hTi : ∀ σ i j, Integrable (fun y => (N y * S y σ * (N y)ᴴ) i j) ν)
    {d : ℕ} {μ r β e Gm : ℝ} (hμ : 0 ≤ μ) (hr : 1 ≤ r) (hβ : 0 ≤ β) (he : 0 ≤ e) (hGm0 : 0 ≤ Gm)
    (hM : ∀ σ, ‖matrixExpect ν (fun y => N y * S y σ * (N y)ᴴ)‖ ≤ μ)
    (hB : ∀ σ u v, eLpNorm (fun y => bilinear u (N y * S y σ * (N y)ᴴ -
        matrixExpect ν (fun y => N y * S y σ * (N y)ᴴ)) v) (ENNReal.ofReal ((d + 2) * r)) ν ≤
      ENNReal.ofReal (β * vecNorm u * vecNorm v))
    (Bt : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hBt : ∀ σ, ‖Bt σ‖ ≤ 1)
    (hMB : ∀ σ, ‖matrixExpect ν (fun y => N y * S y σ * (N y)ᴴ) - Bt σ‖ ≤ e)
    (hGm : eLpNorm (fun y => (1 + ‖N y‖ + ‖D y‖) ^ (2 * (d + 1) ^ 2)) (ENNReal.ofReal r) ν ≤
      ENNReal.ofReal Gm)
    (Zs : List (TraceWord nT nI)) (hZ : IsAdmittedProduct Zs) (hd : productDegree Zs ≤ d)
    (hZm : AEStronglyMeasurable (fun y => newProd A c (N y) (D y) (S y) Zs) ν) :
    Integrable (fun y => newProd A c (N y) (D y) (S y) Zs) ν ∧
      ‖∫ y, newProd A c (N y) (D y) (S y) Zs ∂ν - coreProd A Bt Zs‖ ≤
        max 1 K ^ d * (2 ^ d * (1 + μ) ^ d * (d * β) ^ 2 * (1 + (d * β) ^ d) +
          d * e * (1 + 1 + e) ^ d) +
        d * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) * Gm / W ∧
      eLpNorm (fun y => newProd A c (N y) (D y) (S y) Zs -
          ∫ y, newProd A c (N y) (D y) (S y) Zs ∂ν) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal (2 * (max 1 K ^ d * (2 ^ d * (1 + μ) ^ d * (d * β) * (1 + (d * β) ^ d))) +
          2 * (d * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2) * Gm / W)) := by
  set T : Separator → Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    fun σ y => N y * S y σ * (N y)ᴴ
  set M : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun σ => matrixExpect ν (T σ)
  set Z : Ω → ℂ := fun y => newProd A c (N y) (D y) (S y) Zs
  set FT : Ω → ℂ := fun y => coreProd A (fun σ => T σ y) Zs
  set Γ := max 1 K ^ d
  set Cinj := (d : ℝ) * d * (3 + d) ^ d * (3 * (1 + K + c₀)) ^ ((d + 1) ^ 2)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hΓ : 0 ≤ Γ := by positivity
  have hC0 : 0 ≤ Cinj := by positivity
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by simpa using hr
  have hrep := coreProd_rep A hA hAK hZ hd
  obtain ⟨hFi, hFmean, hFlp⟩ := cutRep_layer hrep T hTi hμ hr hβ hM hB
  have hcomp := cutRep_compare hrep M Bt zero_le_one he hBt hMB
  set bf := Γ * (2 ^ d * (1 + μ) ^ d * (d * β) * (1 + (d * β) ^ d))
  have hbf : 0 ≤ bf := by positivity
  -- the injection
  have hpt : ∀ᵐ y ∂ν, ‖Z y - FT y‖ ≤ Cinj / W * (1 + ‖N y‖ + ‖D y‖) ^ (2 * (d + 1) ^ 2) := by
    filter_upwards [hS] with y hy
    have h := newProd_sub_core_le hW A c (N y) (D y) (S y) hK hc₀ hA hAK hc hy Zs hZ hd
    rw [inj_alg] at h
    exact h
  have hZFm : AEStronglyMeasurable (fun y => Z y - FT y) ν := hZm.sub hFi.1
  have hinj : eLpNorm (fun y => Z y - FT y) (ENNReal.ofReal r) ν ≤ ENNReal.ofReal (Cinj * Gm / W) := by
    refine (eLpNorm_mono_ae_real hZFm hpt).trans ?_
    have heq : (fun y => Cinj / W * (1 + ‖N y‖ + ‖D y‖) ^ (2 * (d + 1) ^ 2)) =
        (Cinj / W) • fun y => (1 + ‖N y‖ + ‖D y‖) ^ (2 * (d + 1) ^ 2) := by
      funext y; simp [smul_eq_mul]
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    calc ENNReal.ofReal (Cinj / W) * eLpNorm (fun y => (1 + ‖N y‖ + ‖D y‖) ^ (2 * (d + 1) ^ 2))
          (ENNReal.ofReal r) ν ≤ ENNReal.ofReal (Cinj / W) * ENNReal.ofReal Gm := by gcongr
      _ = ENNReal.ofReal (Cinj * Gm / W) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hZFi : Integrable (fun y => Z y - FT y) ν :=
    MemLp.integrable hr1 (hinj.trans_lt ENNReal.ofReal_lt_top)
  have hZi : Integrable Z ν := by
    have : Z = fun y => (Z y - FT y) + FT y := by funext y; ring
    rw [this]; exact hZFi.add hFi
  have hinjm : ‖∫ y, (Z y - FT y) ∂ν‖ ≤ Cinj * Gm / W :=
    norm_integral_le_of_eLpNorm hZFm hr (by positivity) hinj
  have hIZ : ∫ y, Z y ∂ν = ∫ y, (Z y - FT y) ∂ν + ∫ y, FT y ∂ν := by
    rw [← integral_add hZFi hFi]; congr 1; funext y; ring
  refine ⟨hZi, ?_, ?_⟩
  · change ‖∫ y, Z y ∂ν - coreProd A Bt Zs‖ ≤ _
    have heq : ∫ y, Z y ∂ν - coreProd A Bt Zs = ∫ y, (Z y - FT y) ∂ν +
        (∫ y, FT y ∂ν - coreProd A M Zs) + (coreProd A M Zs - coreProd A Bt Zs) := by
      rw [hIZ]; ring
    rw [heq]
    have h0 := norm_add₃_le (a := ∫ y, (Z y - FT y) ∂ν) (b := ∫ y, FT y ∂ν - coreProd A M Zs)
      (c := coreProd A M Zs - coreProd A Bt Zs)
    have h2 : ‖∫ y, FT y ∂ν - coreProd A M Zs‖ ≤
        Γ * (2 ^ d * (1 + μ) ^ d * (d * β) ^ 2 * (1 + (d * β) ^ d)) := hFmean
    have h3 : ‖coreProd A M Zs - coreProd A Bt Zs‖ ≤ Γ * (d * e * (1 + 1 + e) ^ d) := hcomp
    refine h0.trans ((add_le_add (add_le_add hinjm h2) h3).trans (le_of_eq ?_))
    ring
  · change eLpNorm (fun y => Z y - ∫ y, Z y ∂ν) (ENNReal.ofReal r) ν ≤ _
    have hFl : eLpNorm (fun y => FT y - coreProd A M Zs) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal bf := hFlp
    have hFm' : ‖∫ y, (FT y - coreProd A M Zs) ∂ν‖ ≤ bf :=
      norm_integral_le_of_eLpNorm (hFi.1.sub aestronglyMeasurable_const) hr hbf hFl
    have hFm'' : ‖coreProd A M Zs - ∫ y, FT y ∂ν‖ ≤ bf := by
      rw [integral_sub hFi (integrable_const _), integral_const, probReal_univ, one_smul] at hFm'
      rwa [norm_sub_rev]
    set k : ℂ := coreProd A M Zs - ∫ y, FT y ∂ν - ∫ y, (Z y - FT y) ∂ν
    have hk : ‖k‖ ≤ bf + Cinj * Gm / W := (norm_sub_le _ _).trans (add_le_add hFm'' hinjm)
    have heq : (fun y => Z y - ∫ y, Z y ∂ν) =
        (fun y => Z y - FT y) + ((fun y => FT y - coreProd A M Zs) + fun _ => k) := by
      funext y; simp only [Pi.add_apply, k, hIZ]; ring
    rw [heq]
    refine (eLpNorm_add_le hr1).trans ?_
    refine (add_le_add le_rfl (eLpNorm_add_le hr1)).trans ?_
    refine (add_le_add hinj (add_le_add hFl ((eLpNorm_const_le' k _).trans
      (ENNReal.ofReal_le_ofReal hk)))).trans ?_
    rw [← ENNReal.ofReal_add hbf (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

end Prob

end BlockBand.SourceProcess.ContractingWords
