module

public import BlockBand.LocalWindow.ProofPartTwoPoint
public import BlockBand.LocalWindow.ProofPartOneGrid

/-!
# The eigenvalue count in the ETH window

The number of eigenvalues of the deformed pair matrix in the ETH window is `O(W^β)` with high
probability, for part (ii) of the physical local-window lemma.

## Main results

* `sum_eq_sum_of_eigenfamilies`: two orthonormal eigenbases of a Hermitian matrix have the same
  eigenvalues with multiplicity: `Σ_k f(μ_k) = Σ_j f(λ_j)` for every `f`.
* `isOrthonormalFamily_eigenvectorBasis`, `mulVec_eigenvectorBasis_complex`: Mathlib's eigenbasis.
* **`sum_pairEigval_sub_eq_spectralSum`**: `Σ_k f(μ_k - c) = Window.Count.spectralSum f (X - c)`
  for the selected eigenvalues `μ_k = pairEigval sel X k`; **`sum_pairEigval_eq_spectralSum`**:
  `Σ_k f(μ_k) = Inputs.spectralSum X f` (the selection eigenvalues are the eigenvalues with
  multiplicity).
* `card_window_le_two_mul_poisson`: `#{k : μ_k ∈ [E₀ - h, E₀ + h]} ≤ 2 Σ_k P_h(μ_k - E₀)`.
* **`hasRegularRoot_of_pairRootRectangle`**: a root rectangle `Im m ≥ v₀` gives the regular root
  `v ≤ Im m ≤ v⁻¹` of `ProofPartOne.HasRegularRoot` for every `0 < v ≤ min(v₀, √s)` (the upper
  bound `Im m ≤ s^{-1/2}` holds at every Dyson root, `dysonRoot_im_sq_le`).
* **`gue_windowCount_le`**: fixed `A, C, sLo, Λ, r, v₀`; then `0 < β ≤ 1`, `D > 0`; then
  `N₀, C_c`; uniformly in `p, i` with `2W ≥ N₀`, `s ≥ sLo`, Hermitian `K` with
  `s^{-1/2}‖K‖ ≤ C (2W)^A`, `|E₀| ≤ Λ` with `PairRootRectangle K s E₀ r v₀`, eigenpair selections:
  `GUE_{2W}(s/2W){G : ¬(G Hermitian ∧ #{k : μ_k(K + G) ∈ [E₀ ± h]} ≤ C_c (2W)^β)} ≤ 2 (2W)^{-D}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofPartOne
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sqNorm_eq_one_of_orthonormal {e : ι → ι → ℂ} (he : IsOrthonormalFamily e) (k : ι) :
    sqNorm (e k) = 1 := by
  have h := he k k
  simp only [↓reduceIte] at h
  rw [star_dotProduct_self] at h
  exact_mod_cast h

/-- **Eigenvalues with multiplicity do not depend on the eigenbasis**: for a Hermitian `X` with
two orthonormal eigenfamilies `(e_k, μ_k)` and `(v_j, λ_j)` indexed by `ι`, and any `f`,
`Σ_k f(μ_k) = Σ_j f(λ_j)` (expand `1 = Σ_j |⟨e_k, v_j⟩|² = Σ_k |⟨e_k, v_j⟩|²`; the overlap
vanishes unless `μ_k = λ_j`). -/
theorem sum_eq_sum_of_eigenfamilies {X : Matrix ι ι ℂ} (hX : X.IsHermitian) {e v : ι → ι → ℂ}
    (he : IsOrthonormalFamily e) (hv : IsOrthonormalFamily v) {μ lam : ι → ℝ}
    (heig : ∀ k, X *ᵥ e k = (μ k : ℂ) • e k) (hveig : ∀ j, X *ᵥ v j = (lam j : ℂ) • v j)
    (f : ℝ → ℝ) : ∑ k, f (μ k) = ∑ j, f (lam j) := by
  set q : ι → ι → ℂ := fun k j => star (e k) ⬝ᵥ v j with hq
  have hswap : ∀ k j, f (μ k) * ‖q k j‖ ^ 2 = f (lam j) * ‖q k j‖ ^ 2 := by
    intro k j
    have h1 := coeff_mulVec hX (heig k) (v j)
    rw [hveig j, dotProduct_smul, smul_eq_mul] at h1
    by_cases h0 : q k j = 0
    · rw [h0, norm_zero]; ring
    · have : (lam j : ℂ) = (μ k : ℂ) := mul_right_cancel₀ h0 h1
      rw [Complex.ofReal_injective this]
  have hrow : ∀ k, ∑ j, ‖q k j‖ ^ 2 = 1 := by
    intro k
    rw [← sqNorm_eq_one_of_orthonormal he k, sqNorm_eq_sum_coeff hv (e k)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : star (v j) ⬝ᵥ e k = star (q k j) := by
      simp only [hq, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [this, norm_star]
  have hcol : ∀ j, ∑ k, ‖q k j‖ ^ 2 = 1 := by
    intro j
    rw [← sqNorm_eq_one_of_orthonormal hv j, sqNorm_eq_sum_coeff he (v j)]
  calc ∑ k, f (μ k) = ∑ k, ∑ j, f (μ k) * ‖q k j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, hrow k, mul_one]
    _ = ∑ k, ∑ j, f (lam j) * ‖q k j‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hswap k j
    _ = ∑ j, ∑ k, f (lam j) * ‖q k j‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, f (lam j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, hcol j, mul_one]

/-- Mathlib's eigenbasis of a Hermitian matrix is an orthonormal family. -/
theorem isOrthonormalFamily_eigenvectorBasis {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    IsOrthonormalFamily (fun j => ⇑(hX.eigenvectorBasis j)) := by
  intro k l
  have h := orthonormal_iff_ite.mp hX.eigenvectorBasis.orthonormal k l
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  exact h

/-- The eigen equation of Mathlib's eigenbasis, with a complex scalar. -/
theorem mulVec_eigenvectorBasis_complex {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (j : ι) :
    X *ᵥ ⇑(hX.eigenvectorBasis j) = ((hX.eigenvalues j : ℝ) : ℂ) • ⇑(hX.eigenvectorBasis j) := by
  rw [hX.mulVec_eigenvectorBasis j]
  ext x
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- `#{k : μ_k ∈ [E₀ - h, E₀ + h]} ≤ 2 Σ_k P_h(μ_k - E₀)` (`h > 0`; `P_h ≥ 1/2` on the window). -/
theorem card_window_le_two_mul_poisson (μ : ι → ℝ) {E₀ h : ℝ} (hh : 0 < h) :
    ((Finset.univ.filter fun k => μ k ∈ Icc (E₀ - h) (E₀ + h)).card : ℝ) ≤
      2 * ∑ k, poissonWeight h (μ k - E₀) := by
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs with hk
  · rw [mem_Icc] at hk
    have hx : (μ k - E₀) ^ 2 ≤ h ^ 2 := by
      rw [← sq_abs, ← sq_abs h]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self h)) 2
    unfold poissonWeight
    have hd : 0 < (μ k - E₀) ^ 2 + h ^ 2 := by positivity
    rw [Nat.cast_one, mul_div_assoc', le_div_iff₀ hd]
    nlinarith
  · rw [Nat.cast_zero]
    exact mul_nonneg zero_le_two (poissonWeight_nonneg _ _)

end Generic

variable {p : Parameters} {i : ZMod p.n}

/-- **Selected eigenvalues are the eigenvalues with multiplicity** (shifted form): for Hermitian
`X`, every eigenpair selection, real `c` and `f`,
`Σ_k f(pairEigval sel X k - c) = Window.Count.spectralSum f (X - c)`. -/
theorem sum_pairEigval_sub_eq_spectralSum (sel : CEH.EigenpairSelection (2 * p.W))
    {X : PairMatrix p i} (hX : X.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    ∑ k, f (pairEigval sel X hX k - c) =
      BlockBand.Window.Count.spectralSum f (X - (c : ℂ) • (1 : PairMatrix p i)) := by
  have hc : ((c : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hA : (X - (c : ℂ) • (1 : PairMatrix p i)).IsHermitian := hX.sub hc
  unfold BlockBand.Window.Count.spectralSum
  rw [dite_eq_left_of_eq_true (eq_true hA)]
  refine sum_eq_sum_of_eigenfamilies hA (isOrthonormalFamily_pairEigvec sel X hX)
    (isOrthonormalFamily_eigenvectorBasis hA) (fun k => ?_)
    (mulVec_eigenvectorBasis_complex hA) f
  rw [sub_mulVec, mulVec_pairEigvec, smul_mulVec, one_mulVec, Complex.ofReal_sub, sub_smul]

/-- **Selected eigenvalues are the eigenvalues with multiplicity**: for Hermitian `X`, every
eigenpair selection and `f`, `Σ_k f(pairEigval sel X k) = Inputs.spectralSum X f`. -/
theorem sum_pairEigval_eq_spectralSum (sel : CEH.EigenpairSelection (2 * p.W))
    {X : PairMatrix p i} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    ∑ k, f (pairEigval sel X hX k) = BlockBand.Internal.Contracts.Inputs.spectralSum X f := by
  rw [spectralSum_eq_sum hX]
  exact sum_eq_sum_of_eigenfamilies hX (isOrthonormalFamily_pairEigvec sel X hX)
    (isOrthonormalFamily_eigenvectorBasis hX) (mulVec_pairEigvec sel X hX)
    (mulVec_eigenvectorBasis_complex hX) f

/-- **Root rectangle → regular root** (the link to `ProofPartOne.HasRegularRoot`): on a
root rectangle of `K` (`Im m ≥ v₀`), at `|e - E₀| ≤ r`, `0 ≤ η ≤ 1`, the root satisfies
`v ≤ Im m ≤ v⁻¹` for every `0 < v ≤ min(v₀, √s)`. The upper bound needs no certificate: every
Dyson root has `s (Im m)² ≤ 1`. -/
theorem hasRegularRoot_of_pairRootRectangle {K : PairMatrix p i} (hK : K.IsHermitian)
    {s E₀ r v₀ : ℝ} (hs : 0 < s) (hR : PairRootRectangle K s E₀ r v₀) {v : ℝ} (hv : 0 < v)
    (hvv₀ : v ≤ v₀) (hvs : v ≤ Real.sqrt s) {e η : ℝ} (he : |e - E₀| ≤ r) (hη : 0 ≤ η)
    (hη1 : η ≤ 1) : HasRegularRoot K s v e η := by
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  obtain ⟨m, hm, hmv⟩ := hR e he η hη hη1
  have hzim : 0 ≤ ((e : ℂ) + (η : ℂ) * Complex.I).im := by simpa using hη
  have hsq := dysonRoot_im_sq_le hK hs hzim hm
  have hm' := (isDysonRoot_iff K s _ m).mp hm
  refine ⟨m, ?_, hvv₀.trans hmv, ?_⟩
  · have h2 := hm'.2
    rw [mul_comm (η : ℂ) Complex.I] at h2
    exact h2
  · have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hmi : 0 < m.im := hm'.1
    have h1 : Real.sqrt s * m.im ≤ 1 := by
      have h2 : (Real.sqrt s * m.im) ^ 2 ≤ 1 := by
        rw [mul_pow, Real.sq_sqrt hs.le]; exact hsq
      nlinarith [mul_pos hss hmi]
    have h3 : m.im ≤ (Real.sqrt s)⁻¹ := by
      rw [le_inv_comm₀ hmi hss]
      rw [inv_eq_one_div, le_div_iff₀ hmi]; linarith
    exact h3.trans (inv_anti₀ hv hvs)

/-- **The rank of the ETH window projection** (`rank P ≤ CW^β`; the external averaged
local law at one height through `ProofPartOne.gue_poissonBad_le`). Fixed `A, C`,
`sLo > 0`, `Λ`, rectangle radius `r > 0` and `v₀ > 0` first; then `0 < β ≤ 1` and `D > 0`; then
`N₀` and `C_c > 0`. Uniformly in `p, i` with `2W ≥ N₀`, `s ≥ sLo`, Hermitian `K` with
`s^{-1/2}‖K‖ ≤ C (2W)^A`, `|E₀| ≤ Λ` with `PairRootRectangle K s E₀ r v₀` and eigenpair
selections: under `G ~ GUE_{2W}(s/2W)`, outside probability `2 (2W)^{-D}`, `G` is Hermitian and
at most `C_c (2W)^β` selected eigenvalues of `K + G` lie in `[E₀ - h, E₀ + h]`,
`h = (2W)^{-1+β}`. -/
theorem gue_windowCount_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (A C sLo Λ r v₀ : ℝ) (hsLo : 0 < sLo) (hr : 0 < r)
    (hv₀ : 0 < v₀) :
    ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ (N₀ : ℕ) (Cc : ℝ), 0 < Cc ∧ ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W →
        ∀ s : ℝ, sLo ≤ s → ∀ (K : PairMatrix p i) (hK : K.IsHermitian),
          (Real.sqrt s)⁻¹ * ‖K‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
        ∀ E₀ : ℝ, |E₀| ≤ Λ → PairRootRectangle K s E₀ r v₀ →
        ∀ sel : CEH.EigenpairSelection (2 * p.W),
          gueMeasure (PairSite p i) (pairTime p s)
              {G | ¬ ∃ hG : G.IsHermitian,
                ((Finset.univ.filter fun k => pairEigval sel (K + G) (hK.add hG) k ∈
                    Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))
                      (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card : ℝ) ≤
                  Cc * ((2 * p.W : ℕ) : ℝ) ^ β} ≤
            2 * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  intro β hβ hβ1 D hD
  set v : ℝ := min v₀ (Real.sqrt sLo) with hvdef
  have hsLo' : 0 < Real.sqrt sLo := Real.sqrt_pos.mpr hsLo
  have hv : 0 < v := lt_min hv₀ hsLo'
  set εl : ℝ := min (β / 2) (1 / (|A| + 1)) with hεl
  have hεl0 : 0 < εl := lt_min (half_pos hβ) (by positivity)
  have hεlβ : εl < β := (min_le_left _ _).trans_lt (half_lt_self hβ)
  have hexp : 1 ≤ A + 1 / εl := by
    have h1 : εl ≤ 1 / (|A| + 1) := min_le_right _ _
    have h2 : |A| + 1 ≤ 1 / εl := by
      rw [le_div_iff₀ hεl0]
      calc (|A| + 1) * εl ≤ (|A| + 1) * (1 / (|A| + 1)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 := by field_simp
    have := neg_abs_le A
    linarith
  obtain ⟨N₁, -, hN₁⟩ := gue_poissonBad_le hBridge hELG hMDE A C εl β D hεl0 hβ hD
  -- eventual size conditions on `d = 2W`
  have e2 := eventually_const_mul_rpow_le (Real.pi / v) (εl - β) (by linarith)
  have e3 : ∀ᶠ n : ℕ in atTop, (Λ + 1) / Real.sqrt sLo ≤ ((n : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop N₁).and
    ((eventually_ge_atTop 1).and (e2.and e3)))
  refine ⟨N₀, 2 * (1 / v + 1), by positivity, fun p i hN s hs K hK hKn E₀ hE₀ hR sel => ?_⟩
  obtain ⟨h1, hd1, hdom, hnorm⟩ := hN₀ (2 * p.W) hN
  have hs0 : 0 < s := hsLo.trans_le hs
  set d : ℝ := ((2 * p.W : ℕ) : ℝ) with hd
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast (Nat.mul_pos two_pos p.W_pos)
  have hd1' : (1 : ℝ) ≤ d := by rw [hd]; exact_mod_cast hd1
  set h := d ^ (-1 + β) with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos hd0 _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd1' (by linarith)
  have hdh : d * h = d ^ β := by
    rw [hh, ← Real.rpow_one_add' hd0.le (by linarith)]; ring_nf
  have hvs : v ≤ Real.sqrt s := (min_le_right _ _).trans (Real.sqrt_le_sqrt hs)
  have hreg := hasRegularRoot_of_pairRootRectangle hK hs0 hR hv (min_le_left _ _) hvs
    (e := E₀) (by simpa using hr.le) hh0.le hh1
  have hreg' : HasRegularRoot K s v E₀ (1 * h) := by rw [one_mul]; exact hreg
  -- domain condition
  have hdom' : d ^ εl ≤ d * h * (v / Real.pi) := by
    rw [hdh]
    have e : d ^ εl = (Real.pi / v * d ^ (εl - β)) * (d ^ β * (v / Real.pi)) := by
      rw [show d ^ (εl - β) = d ^ εl / d ^ β from Real.rpow_sub hd0 _ _]
      have := Real.pi_pos
      have : 0 < d ^ β := Real.rpow_pos_of_pos hd0 _
      field_simp
    rw [e]
    have : 0 ≤ d ^ β * (v / Real.pi) := by have := Real.pi_pos; positivity
    calc (Real.pi / v * d ^ (εl - β)) * (d ^ β * (v / Real.pi))
        ≤ 1 * (d ^ β * (v / Real.pi)) := mul_le_mul_of_nonneg_right hdom this
      _ = _ := one_mul _
  -- norm condition
  have hz : ‖(E₀ : ℂ) + Complex.I * (h : ℂ)‖ ≤ Real.sqrt s * d ^ (A + 1 / εl) := by
    have e1 : ‖(E₀ : ℂ) + Complex.I * (h : ℂ)‖ ≤ Λ + 1 := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh0]
      linarith
    have e2' : d ≤ d ^ (A + 1 / εl) := by
      calc d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
        _ ≤ d ^ (A + 1 / εl) := Real.rpow_le_rpow_of_exponent_le hd1' hexp
    have e3' : Λ + 1 ≤ Real.sqrt sLo * d := by
      rw [div_le_iff₀ hsLo'] at hnorm; linarith
    calc _ ≤ Λ + 1 := e1
      _ ≤ Real.sqrt sLo * d := e3'
      _ ≤ Real.sqrt s * d ^ (A + 1 / εl) :=
          mul_le_mul (Real.sqrt_le_sqrt hs) e2' hd0.le (Real.sqrt_nonneg _)
  have hz' : ‖(E₀ : ℂ) + Complex.I * ((1 * h : ℝ) : ℂ)‖ ≤ Real.sqrt s * d ^ (A + 1 / εl) := by
    rw [one_mul]; exact hz
  have hbad := hN₁ p i h1 s hs0 K hK hKn E₀ h 1 v hh0 le_rfl hv hreg hreg' hdom' hz hz'
  set μ := gueMeasure (PairSite p i) (pairTime p s)
  have hnull : μ {G | ¬ G.IsHermitian} = 0 := by
    have := BlockBand.Angular.PairCoareaBridge.ae_gueMeasure_isHermitian (PairSite p i)
      (pairTime p s)
    rwa [ae_iff] at this
  have hsub : {G : PairMatrix p i | ¬ ∃ hG : G.IsHermitian,
      ((Finset.univ.filter fun k => pairEigval sel (K + G) (hK.add hG) k ∈
          Icc (E₀ - h) (E₀ + h)).card : ℝ) ≤ 2 * (1 / v + 1) * d ^ β} ⊆
      {G | PoissonBad d β v h 1 (K + G - (E₀ : ℂ) • 1)} ∪ {G | ¬ G.IsHermitian} := by
    intro G hG
    by_cases hGh : G.IsHermitian
    · left
      simp only [Set.mem_ofPred_eq] at hG ⊢
      by_contra hP
      apply hG
      refine ⟨hGh, ?_⟩
      unfold PoissonBad at hP
      push Not at hP
      have hsum := sum_pairEigval_sub_eq_spectralSum sel (hK.add hGh) E₀ (poissonWeight h)
      have hc := card_window_le_two_mul_poisson (pairEigval sel (K + G) (hK.add hGh))
        (E₀ := E₀) hh0
      rw [hsum] at hc
      have hup := hP.2.1
      have hdv : d * h / v = d ^ β * (1 / v) := by rw [hdh]; ring
      calc _ ≤ _ := hc
        _ ≤ 2 * (d * h / v + d ^ β) := by linarith
        _ = 2 * (1 / v + 1) * d ^ β := by rw [hdv]; ring
    · right; exact hGh
  calc μ {G | ¬ ∃ hG : G.IsHermitian,
        ((Finset.univ.filter fun k => pairEigval sel (K + G) (hK.add hG) k ∈
            Icc (E₀ - h) (E₀ + h)).card : ℝ) ≤ 2 * (1 / v + 1) * d ^ β}
      ≤ μ ({G | PoissonBad d β v h 1 (K + G - (E₀ : ℂ) • 1)} ∪ {G | ¬ G.IsHermitian}) :=
        measure_mono hsub
    _ ≤ μ {G | PoissonBad d β v h 1 (K + G - (E₀ : ℂ) • 1)} + μ {G | ¬ G.IsHermitian} :=
        measure_union_le _ _
    _ ≤ 2 * ENNReal.ofReal (d ^ (-D)) + 0 := by rw [hnull]; exact add_le_add hbad le_rfl
    _ = 2 * ENNReal.ofReal (d ^ (-D)) := add_zero _

/-- From the real bound of `gue_windowCount_le` to the integer bound `N_c = ⌊C_c (2W)^β⌋₊` of
the hypothesis `hcount` of `pairWindow_transfer`. -/
theorem card_le_floor_of_le {S : Finset (PairSite p i)} {x : ℝ} (h : (S.card : ℝ) ≤ x) :
    S.card ≤ ⌊x⌋₊ :=
  Nat.le_floor h

end BlockBand.LocalWindow.ProofPartTwo
