module

public import BlockBand.LocalWindow.ProofPartTwoLargeRhoActual
public import BlockBand.LocalWindow.ProofPartTwoStability
public import BlockBand.LocalWindow.ProofPartTwoCompressRoot

/-!
# The centre comparison of the large-`ρ` branch

The compressed window estimate at a grid energy `e` and window centre `μ` is centred at
`nativeCentre J_c (compRegM e) s' λ'` (`λ'` a compressed eigenvalue in the window,
`s' = s(1 - 1/(2W))`), while part (ii) is centred at `pairCentre J (K₀(E)) s λ` of the exact
energy `E` and the exact eigenvalue `λ`. The chain is

`nativeCentre J_c (U*M_e U) s' λ'` →(Lipschitz in `(λ, F)`)→ `nativeCentre J_c (U*M_E U) s' λ`
→(linear in the observable)→ `nativeCentre (U*JU) (U*M_E U) s' λ` →(`pairCentre_compress_close`)→
`pairCentre J (M_E + ρ(E)ww*) s λ = pairCentre J (K₀(E)) s λ`,

with `M_x = F_reg(x) - x` (`regF`) and `U = poleIsometry sel j₀ ω`.

## Main results

* `rootCentre J F s x m` (generic finite type): the centre `|ι|⁻¹ Tr(J s RR*)`,
  `R = (F - x - sm)⁻¹`, at a given root `m`; `nativeCentre_eq_rootCentre`,
  `pairCentre_eq_rootCentre`, `compressCentre_eq_nativeCentre`.
* **`rootCentre_sub_le`**: `‖c(J, F₁, x, m₁) - c(J, F₂, y, m₂)‖ ≤ (2 resLip(s, v₀)/v₀)(|x - y| +
  ‖F₁ - F₂‖)` for a contraction `J` (op-norm proof, no `√|ι|` loss).
* **`rootCentre_obs_sub_le`**: `‖c(J₁, …) - c(J₂, …)‖ ≤ ‖J₁ - J₂‖/(s v₀²)`.
* **`largeRho_centre_close`**: the full chain at one exterior point, from Dyson roots of
  `K₀(E)` (variance `s`, at `λ`), of `U*M_E U` (variance `s'`, at `λ`) and of `compRegM e`
  (variance `s'`, at `λ'`), all with `Im ≥ v₀`.
* **`largeRho_hcen`**: the hypothesis `hcen` of `largeRho_actual_transfer` (for the compressed
  observable `J_c`), from root rectangles, with
  `η = (2 resLip(s', v₀)/v₀)(3h/2 + (‖C‖²/ε² + 1)|E - e|) + ‖U*JU - J_c‖/(s'v₀²) + Δ_ρ`,
  `Δ_ρ` the bound of `pairCentre_compress_close`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped Matrix.Norms.L2Operator

/-!
## The centre at a given root, on a finite type
-/

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized trace is bounded by the operator norm: `‖|ι|⁻¹ Tr X‖ ≤ ‖X‖`. -/
theorem norm_inv_card_mul_trace_le (X : Matrix ι ι ℂ) :
    ‖((Fintype.card ι : ℂ))⁻¹ * X.trace‖ ≤ ‖X‖ := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0, Nat.cast_zero, _root_.inv_zero, zero_mul, norm_zero]; exact norm_nonneg _
  · have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hpos
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h := compress_norm_trace_le X
    calc (Fintype.card ι : ℝ)⁻¹ * ‖X.trace‖ ≤ (Fintype.card ι : ℝ)⁻¹ *
          (Fintype.card ι * ‖X‖) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ‖X‖ := by field_simp

/-- The window centre at a given root `m`: `|ι|⁻¹ Tr(J s RR*)`, `R = (F - x - sm)⁻¹`. -/
def rootCentre (J F : Matrix ι ι ℂ) (s x : ℝ) (m : ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * (J * ((s : ℂ) •
    ((F - ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ *
      ((F - ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹)ᴴ))).trace

/-- **Lipschitz bound of the centre in `(x, F)`**: for Hermitian `F₁, F₂`, Dyson roots `m₁` of
`F₁` at `x` and `m₂` of `F₂` at `y` (variance `s > 0`, `Im m_j ≥ v₀ > 0`) and a contraction `J`,
`‖c(J, F₁, x, m₁) - c(J, F₂, y, m₂)‖ ≤ (2 resLip(s, v₀)/v₀)(|x - y| + ‖F₁ - F₂‖)`. -/
theorem rootCentre_sub_le [Nonempty ι] {F₁ F₂ J : Matrix ι ι ℂ} (hF₁ : F₁.IsHermitian)
    (hF₂ : F₂.IsHermitian) (hJ : ‖J‖ ≤ 1) {s v₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) {x y : ℝ}
    {m₁ m₂ : ℂ} (hm₁ : IsDysonRoot F₁ s (x : ℂ) m₁) (hm₂ : IsDysonRoot F₂ s (y : ℂ) m₂)
    (hv₁ : v₀ ≤ m₁.im) (hv₂ : v₀ ≤ m₂.im) :
    ‖rootCentre J F₁ s x m₁ - rootCentre J F₂ s y m₂‖ ≤
      2 * resLip s v₀ / v₀ * (|x - y| + ‖F₁ - F₂‖) := by
  set R₁ := (F₁ - ((x : ℂ) + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ with hR₁
  set R₂ := (F₂ - ((y : ℂ) + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹ with hR₂
  have hn₁ : ‖R₁‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hF₁ hs (by simp) hv₀ hv₁
  have hn₂ : ‖R₂‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hF₂ hs (by simp) hv₀ hv₂
  set Δ := |x - y| + ‖F₁ - F₂‖ with hΔ
  have hlip : ‖R₁ - R₂‖ ≤ resLip s v₀ * Δ := by
    have h := resolvent_lipschitz_two hF₁ hF₂ hs (by simp) (by simp) hm₁ hm₂ hv₀ hv₁ hv₂
    rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  have hL0 : 0 ≤ resLip s v₀ * Δ := (norm_nonneg _).trans hlip
  have hdiff : rootCentre J F₁ s x m₁ - rootCentre J F₂ s y m₂ =
      (Fintype.card ι : ℂ)⁻¹ * (J * ((s : ℂ) • ((R₁ - R₂) * R₁ᴴ + R₂ * (R₁ - R₂)ᴴ))).trace := by
    unfold rootCentre
    rw [← hR₁, ← hR₂, ← mul_sub, ← trace_sub, ← Matrix.mul_sub, ← smul_sub]
    congr 4
    rw [conjTranspose_sub]
    noncomm_ring
  rw [hdiff]
  refine (norm_inv_card_mul_trace_le _).trans ?_
  have hs' : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hX : ‖(R₁ - R₂) * R₁ᴴ + R₂ * (R₁ - R₂)ᴴ‖ ≤ 2 * (resLip s v₀ * Δ * (s * v₀)⁻¹) := by
    refine (norm_add_le _ _).trans ?_
    have a1 : ‖(R₁ - R₂) * R₁ᴴ‖ ≤ resLip s v₀ * Δ * (s * v₀)⁻¹ := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]
      exact mul_le_mul hlip hn₁ (norm_nonneg _) hL0
    have a2 : ‖R₂ * (R₁ - R₂)ᴴ‖ ≤ resLip s v₀ * Δ * (s * v₀)⁻¹ := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose, mul_comm]
      exact mul_le_mul hlip hn₂ (norm_nonneg _) hL0
    linarith
  calc ‖J * ((s : ℂ) • ((R₁ - R₂) * R₁ᴴ + R₂ * (R₁ - R₂)ᴴ))‖
      ≤ ‖J‖ * (s * ‖(R₁ - R₂) * R₁ᴴ + R₂ * (R₁ - R₂)ᴴ‖) := by
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [norm_smul, hs']
    _ ≤ 1 * (s * (2 * (resLip s v₀ * Δ * (s * v₀)⁻¹))) := by
        gcongr
    _ = 2 * resLip s v₀ / v₀ * Δ := by
        field_simp

/-- **The centre is linear in the observable**: at one root `m` of `F` (variance `s > 0`,
`Im m ≥ v₀ > 0`), `‖c(J₁, F, x, m) - c(J₂, F, x, m)‖ ≤ ‖J₁ - J₂‖/(s v₀²)`. -/
theorem rootCentre_obs_sub_le {F J₁ J₂ : Matrix ι ι ℂ} (hF : F.IsHermitian) {s v₀ : ℝ}
    (hs : 0 < s) (hv₀ : 0 < v₀) {x : ℝ} {m : ℂ} (hv : v₀ ≤ m.im) :
    ‖rootCentre J₁ F s x m - rootCentre J₂ F s x m‖ ≤ ‖J₁ - J₂‖ / (s * v₀ ^ 2) := by
  set R := (F - ((x : ℂ) + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ with hR
  have hn : ‖R‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hF hs (by simp) hv₀ hv
  have hdiff : rootCentre J₁ F s x m - rootCentre J₂ F s x m =
      (Fintype.card ι : ℂ)⁻¹ * ((J₁ - J₂) * ((s : ℂ) • (R * Rᴴ))).trace := by
    unfold rootCentre
    rw [← hR, ← mul_sub, ← trace_sub, ← Matrix.sub_mul]
  rw [hdiff]
  refine (norm_inv_card_mul_trace_le _).trans ?_
  have hs' : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hRR : ‖R * Rᴴ‖ ≤ (s * v₀)⁻¹ * (s * v₀)⁻¹ := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    exact mul_le_mul hn hn (norm_nonneg _) (by positivity)
  calc ‖(J₁ - J₂) * ((s : ℂ) • (R * Rᴴ))‖ ≤ ‖J₁ - J₂‖ * (s * ‖R * Rᴴ‖) := by
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [norm_smul, hs']
    _ ≤ ‖J₁ - J₂‖ * (s * ((s * v₀)⁻¹ * (s * v₀)⁻¹)) := by gcongr
    _ = ‖J₁ - J₂‖ / (s * v₀ ^ 2) := by field_simp

end Generic

/-!
## Identification of the centres
-/

section Ident

theorem nativeCentre_eq_rootCentre {N : ℕ} [NeZero N] {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) (J : Matrix (Fin N) (Fin N) ℂ) {x : ℝ} {m : ℂ}
    (hm : IsDysonRoot F s (x : ℂ) m) : nativeCentre J F s x = rootCentre J F s x m := by
  unfold nativeCentre rootCentre
  rw [freshDyson_eq_of_isDysonRoot hF hs (by simp) hm, Fintype.card_fin]

variable {p : Parameters} {i : ZMod p.n}

theorem compressCentre_eq_nativeCentre (J' B : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ)
    (s' x : ℝ) : compressCentre p J' B s' x = nativeCentre J' B s' x := rfl

theorem pairCentre_eq_rootCentre {K : PairMatrix p i} (hK : K.IsHermitian) {s : ℝ} (hs : 0 < s)
    (J : PairMatrix p i) {x : ℝ} {m : ℂ} (hm : IsDysonRoot K s (x : ℂ) m) :
    pairCentre J K s x = rootCentre J K s x m := by
  have hpd : BlockBand.LocalWindow.pairDyson p i K s x = m :=
    pairDyson_eq_of_isDysonRoot p i hK hs (by simp) hm
  unfold pairCentre rootCentre
  rw [windowGamma_eq, hpd, card_pairSite_cc]
  push_cast
  rfl

end Ident

/-!
## The centre chain at one exterior point
-/

section Chain

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-- The bound `Δ_ρ` of `pairCentre_compress_close` for `M`, `ρ`, `x` (`s' = s(1 - 1/(2W))`). -/
def compressCentreErr (p : Parameters) (s v₀ nM ρ x : ℝ) : ℝ :=
  2 * s / (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀) *
    (1 + 4 / (v₀ ^ 2 * (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀) ^ 2)) *
    ((1 + nM / (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀)) ^ 3 / (|ρ| - (|x| + 1 / v₀)))

/-- **The centre comparison of the large-`ρ` branch**. At one
exterior point (`H_R, V` Hermitian), a simple pole label `j₀` separated at radius `ε > 0` from the
exact energy `E` (not a pole) and from the grid energy `e`, `U = poleIsometry sel j₀ ω`,
`M_E = F_reg(E) - E`, `ρ = ρ(E)`, `s > 0`, `s' = s(1 - 1/(2W))`. Given Dyson roots `m` of `K₀(E)`
(variance `s`, at `λ`), `m_c` of `U*M_E U` (variance `s'`, at `λ`) and `m_e` of `compRegM e`
(variance `s'`, at `λ'`), all with `Im ≥ v₀ > 0`, `|λ| + 1/v₀ < |ρ|` and the two smallness
conditions of `pairCentre_compress_close`, for pair and compressed contractions `J`, `J_c`:
`‖nativeCentre J_c (compRegM e) s' λ' - pairCentre J K₀(E) s λ‖ ≤
(2 resLip(s', v₀)/v₀)(|λ' - λ| + (‖C‖²/ε² + 1)|E - e|) + ‖J_c - U*JU‖/(s'v₀²) + Δ_ρ`. -/
theorem largeRho_centre_close (sel : CEH.EigenpairSelection (2 * p.W)) {ε : ℝ} (hε : 0 < ε)
    {om : SplitState p i} (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian)
    {j₀ : ExteriorSite p i} (hs : PoleSimple hH j₀) {E e : ℝ} (hsepE : PoleSeparated ε hH j₀ E)
    (hsepe : PoleSeparated ε hH j₀ e) (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0) {s v₀ : ℝ}
    (hs0 : 0 < s) (hv₀ : 0 < v₀) {lam lam' : ℝ} {m mc me : ℂ}
    (hm : IsDysonRoot (schurK0 p i om E) s (lam : ℂ) m) (hmv : v₀ ≤ m.im)
    (hmc : IsDysonRoot ((poleIsometry sel j₀ om)ᴴ *
      (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1) * poleIsometry sel j₀ om)
      (s * (1 - 1 / (2 * (p.W : ℝ)))) (lam : ℂ) mc) (hmcv : v₀ ≤ mc.im)
    (hme : IsDysonRoot (compRegM sel ε j₀ e om) (s * (1 - 1 / (2 * (p.W : ℝ)))) (lam' : ℂ) me)
    (hmev : v₀ ≤ me.im)
    (hρ : |lam| + 1 / v₀ < |poleRho hH j₀ om.2.1 E|)
    (hδ₁ : 4 * ((1 + ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ /
      (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀)) ^ 3 /
      (|poleRho hH j₀ om.2.1 E| - (|lam| + 1 / v₀))) ≤ v₀)
    (hδ₂ : 2 * ((1 + ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ /
      (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀)) ^ 3 /
      (|poleRho hH j₀ om.2.1 E| - (|lam| + 1 / v₀))) ≤
        s * (1 - 1 / (2 * (p.W : ℝ))) * v₀ ^ 3)
    {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1)
    {Jc : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ} (hJc : ‖Jc‖ ≤ 1) :
    ‖nativeCentre Jc (compRegM sel ε j₀ e om) (s * (1 - 1 / (2 * (p.W : ℝ)))) lam' -
        pairCentre J (schurK0 p i om E) s lam‖ ≤
      2 * resLip (s * (1 - 1 / (2 * (p.W : ℝ)))) v₀ / v₀ *
          (|lam' - lam| + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) +
        ‖Jc - (poleIsometry sel j₀ om)ᴴ * J * poleIsometry sel j₀ om‖ /
          (s * (1 - 1 / (2 * (p.W : ℝ))) * v₀ ^ 2) +
        compressCentreErr p s v₀ ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖
          (poleRho hH j₀ om.2.1 E) lam := by
  have : NeZero (2 * p.W - 1) := ⟨by have := p.W_pos; omega⟩
  have : Nonempty (Fin (2 * p.W - 1)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  set U := poleIsometry sel j₀ om with hUdef
  set w := poleDir hH j₀ om.2.1 with hwdef
  set ρ := poleRho hH j₀ om.2.1 E with hρdef
  set ME := regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i) with hME
  set Me := regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) with hMe
  set s' := s * (1 - 1 / (2 * (p.W : ℝ))) with hs'
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hs'0 : 0 < s' := by
    have h2 : 1 / (2 * (p.W : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    exact mul_pos hs0 (by linarith)
  obtain ⟨hUU, hUw, hcompl⟩ := poleIsometry_spec sel hH hs
  have hMEh : ME.IsHermitian := isHermitian_regK om hH hV j₀ E
  have hCE : (Uᴴ * ME * U).IsHermitian := isHermitian_compress hMEh U
  have hCe : (compRegM sel ε j₀ e om).IsHermitian := isHermitian_compRegM sel ε j₀ e om
  have hceq : compRegM sel ε j₀ e om = Uᴴ * Me * U := compRegM_eq sel ε hH hV hs hsepe
  -- step 1: Lipschitz in `(λ, F)` on the compressed block
  have h1 := rootCentre_sub_le hCe hCE hJc hs'0 hv₀ hme hmc hmev hmcv
  have hFd : ‖compRegM sel ε j₀ e om - Uᴴ * ME * U‖ ≤
      (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| := by
    rw [hceq, ← Matrix.sub_mul, ← Matrix.mul_sub]
    refine (opNorm_compress_le hUU _).trans ?_
    rw [abs_sub_comm]
    exact opNorm_regK_sub_le hε om hH j₀ hsepe hsepE
  -- step 2: the observable
  have h2 := rootCentre_obs_sub_le (J₁ := Jc) (J₂ := Uᴴ * J * U) hCE hs'0 hv₀ (x := lam) hmcv
  -- step 3: compression
  have hww : vecMulVec w (star w) = 1 - U * Uᴴ := eq_sub_of_add_eq' hcompl
  have hK : schurK0 p i om E = ME + (ρ : ℂ) • (1 - U * Uᴴ) := by
    rw [schurK0_pole_decomp om hH j₀ hdet, ← hww]
  rw [hK] at hm
  have h3 := pairCentre_compress_close hMEh hUU hs0 hv₀ hm hmv hmc hmcv hρ hδ₁ hδ₂ hJ
  rw [compressCentre_eq_nativeCentre, nativeCentre_eq_rootCentre hCE hs'0 _ hmc] at h3
  rw [nativeCentre_eq_rootCentre hCe hs'0 _ hme, hK]
  have hL0 : 0 ≤ 2 * resLip s' v₀ / v₀ := by
    have := rootLip_nonneg s' v₀
    unfold resLip
    positivity
  have h1' : ‖rootCentre Jc (compRegM sel ε j₀ e om) s' lam' me -
      rootCentre Jc (Uᴴ * ME * U) s' lam mc‖ ≤
      2 * resLip s' v₀ / v₀ * (|lam' - lam| + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) hL0)
  have t := norm_sub_le_norm_sub_add_norm_sub
    (rootCentre Jc (compRegM sel ε j₀ e om) s' lam' me) (rootCentre Jc (Uᴴ * ME * U) s' lam mc)
    (pairCentre J (ME + (ρ : ℂ) • (1 - U * Uᴴ)) s lam)
  have t' := norm_sub_le_norm_sub_add_norm_sub
    (rootCentre Jc (Uᴴ * ME * U) s' lam mc) (rootCentre (Uᴴ * J * U) (Uᴴ * ME * U) s' lam mc)
    (pairCentre J (ME + (ρ : ℂ) • (1 - U * Uᴴ)) s lam)
  rw [norm_sub_rev (rootCentre (Uᴴ * J * U) (Uᴴ * ME * U) s' lam mc)] at t'
  unfold compressCentreErr
  linarith

/-- **The hypothesis `hcen` of `largeRho_actual_transfer`**, from
root rectangles: `compRegM e` on `[-r, r]` (variance `s'`), `K₀(E)` (variance `s`) and `U*M_E U`
(variance `s'`) at `λ`, `|λ| ≤ r`, `|μ| + h ≤ r`, `|λ - μ| ≤ h/2` (`h = compressRadius p β`), and
a compressed contraction `J_c` with `‖J_c - U*JU‖ ≤ δ_J`. Then for every `λ'` in the window
`[μ - h, μ + h]`, `‖nativeCentre J_c (compRegM e) s' λ' - pairCentre J K₀(E) s λ‖ ≤
(2 resLip(s', v₀)/v₀)(3h/2 + (‖C‖²/ε² + 1)|E - e|) + δ_J/(s'v₀²) + Δ_ρ`. -/
theorem largeRho_hcen (sel : CEH.EigenpairSelection (2 * p.W)) {ε : ℝ} (hε : 0 < ε)
    {om : SplitState p i} (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian)
    {j₀ : ExteriorSite p i} (hs : PoleSimple hH j₀) {E e : ℝ} (hsepE : PoleSeparated ε hH j₀ E)
    (hsepe : PoleSeparated ε hH j₀ e) (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0) {s v₀ r : ℝ}
    (hs0 : 0 < s) (hv₀ : 0 < v₀)
    (hRK : PairRootRectangle (schurK0 p i om E) s 0 r v₀)
    (hRc : RootRectangle ((poleIsometry sel j₀ om)ᴴ *
      (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1) * poleIsometry sel j₀ om) (compressVar p s) 0 r v₀)
    (hRe : RootRectangle (compRegM sel ε j₀ e om) (compressVar p s) 0 r v₀)
    {lam μ β : ℝ} (hlam : |lam| ≤ r) (hμ : |μ| + compressRadius p β ≤ r)
    (hlamμ : |lam - μ| ≤ compressRadius p β / 2)
    (hρ : |lam| + 1 / v₀ < |poleRho hH j₀ om.2.1 E|)
    (hδ₁ : 4 * ((1 + ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ / (compressVar p s * v₀)) ^ 3 /
      (|poleRho hH j₀ om.2.1 E| - (|lam| + 1 / v₀))) ≤ v₀)
    (hδ₂ : 2 * ((1 + ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ / (compressVar p s * v₀)) ^ 3 /
      (|poleRho hH j₀ om.2.1 E| - (|lam| + 1 / v₀))) ≤ compressVar p s * v₀ ^ 3)
    {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1)
    {Jc : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ} (hJc : ‖Jc‖ ≤ 1) {δJ : ℝ}
    (hδJ : ‖Jc - (poleIsometry sel j₀ om)ᴴ * J * poleIsometry sel j₀ om‖ ≤ δJ) :
    ∀ lam' ∈ Icc (μ - compressRadius p β) (μ + compressRadius p β),
      ‖nativeCentre Jc (compRegM sel ε j₀ e om) (compressVar p s) lam' -
          pairCentre J (schurK0 p i om E) s lam‖ ≤
        2 * resLip (compressVar p s) v₀ / v₀ *
            (3 * compressRadius p β / 2 + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) +
          δJ / (compressVar p s * v₀ ^ 2) +
          compressCentreErr p s v₀ ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖
            (poleRho hH j₀ om.2.1 E) lam := by
  intro lam' hlam'
  have : NeZero (2 * p.W - 1) := ⟨by have := p.W_pos; omega⟩
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hs'0 : 0 < compressVar p s := by
    have h2 : 1 / (2 * (p.W : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    exact mul_pos hs0 (by linarith)
  obtain ⟨hUU, -, -⟩ := poleIsometry_spec sel hH hs
  have hCE := isHermitian_compress (isHermitian_regK om hH hV j₀ E) (poleIsometry sel j₀ om)
  have hCe := isHermitian_compRegM sel ε j₀ e om
  have hl' : |lam' - 0| ≤ r := by
    rw [sub_zero]
    obtain ⟨a, b⟩ := hlam'
    rw [abs_le]
    have h1 := neg_abs_le μ
    have h2 := le_abs_self μ
    constructor <;> linarith
  have hl : |lam - 0| ≤ r := by rwa [sub_zero]
  obtain ⟨hme, hmev⟩ := realRoot_spec hCe hs'0 hRe hl'
  obtain ⟨hmc, hmcv⟩ := realRoot_spec hCE hs'0 hRc hl
  obtain ⟨m, hm, hmv⟩ := hRK lam hl 0 le_rfl zero_le_one
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hm
  have h := largeRho_centre_close sel hε hH hV hs hsepE hsepe hdet hs0 hv₀ hm hmv hmc hmcv hme
    hmev hρ hδ₁ hδ₂ hJ hJc
  have hL0 : 0 ≤ 2 * resLip (compressVar p s) v₀ / v₀ := by
    have := rootLip_nonneg (compressVar p s) v₀
    unfold resLip
    positivity
  have hd : |lam' - lam| ≤ 3 * compressRadius p β / 2 := by
    obtain ⟨a, b⟩ := hlam'
    rw [abs_le] at hlamμ ⊢
    constructor <;> linarith
  have hJd : ‖Jc - (poleIsometry sel j₀ om)ᴴ * J * poleIsometry sel j₀ om‖ /
      (compressVar p s * v₀ ^ 2) ≤ δJ / (compressVar p s * v₀ ^ 2) :=
    div_le_div_of_nonneg_right hδJ (by positivity)
  have hm1 : 2 * resLip (compressVar p s) v₀ / v₀ *
      (|lam' - lam| + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) ≤
      2 * resLip (compressVar p s) v₀ / v₀ *
        (3 * compressRadius p β / 2 + (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) :=
    mul_le_mul_of_nonneg_left (by linarith) hL0
  exact h.trans (by unfold compressVar at hJd hm1 ⊢; linarith)

/-- The size of the centre: `‖c(J, F, x, m)‖ ≤ ‖J‖/(s v₀²)`. -/
theorem norm_rootCentre_le {ι : Type} [Fintype ι] [DecidableEq ι] {F J : Matrix ι ι ℂ}
    (hF : F.IsHermitian) {s v₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) {x : ℝ} {m : ℂ}
    (hv : v₀ ≤ m.im) : ‖rootCentre J F s x m‖ ≤ ‖J‖ / (s * v₀ ^ 2) := by
  have h := rootCentre_obs_sub_le (J₁ := J) (J₂ := 0) hF hs hv₀ (x := x) hv
  have h0 : rootCentre (0 : Matrix ι ι ℂ) F s x m = 0 := by
    unfold rootCentre; rw [Matrix.zero_mul, trace_zero, mul_zero]
  rwa [h0, sub_zero, sub_zero] at h

/-- **The size of the target centre**: on a root rectangle of `K` at `x`, a pair contraction `J`
has `‖pairCentre J K s x‖ ≤ 1/(s v₀²)`. -/
theorem norm_pairCentre_le_rect {K J : PairMatrix p i} (hK : K.IsHermitian) (hJ : ‖J‖ ≤ 1)
    {s v₀ E₀ r : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) (hR : PairRootRectangle K s E₀ r v₀) {x : ℝ}
    (hx : |x - E₀| ≤ r) : ‖pairCentre J K s x‖ ≤ 1 / (s * v₀ ^ 2) := by
  obtain ⟨m, hm, hmv⟩ := hR x hx 0 le_rfl zero_le_one
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hm
  rw [pairCentre_eq_rootCentre hK hs J hm]
  exact (norm_rootCentre_le hK hs hv₀ hmv).trans
    (div_le_div_of_nonneg_right hJ (by positivity))

end Chain

end BlockBand.LocalWindow.ProofPartTwo
