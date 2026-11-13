module

public import BlockBand.LocalWindow.ProofPartTwoPoint

/-!
# From one grid point to the eigenvectors of a nearby deformation

The window bound at a grid deformation transfers to every unit eigenvector of a nearby
deformation, for part (ii) of the physical local-window lemma.

## Main results

* `sqNorm_mulVec_le_opNorm`: `‖X v‖² ≤ ‖X‖² ‖v‖²` (`L²` operator norm).
* `sqNorm_eq_one_of_l2Norm`: `l2Norm u = 1 → sqNorm u = 1`.
* **`pairWindow_transfer`**: let `K_g` be a Hermitian grid deformation and `G` Hermitian with
  `PairWindowGood K_g sel s E₀ β ε J G` (the output of `gue_not_pairWindowGood_le`), at most `N_c`
  eigenvalues of `K_g + G` in the window `[E₀ - h, E₀ + h]`, `h = (2W)^{-1+β}`, and the centre
  closeness `‖pairCentre J K_g s μ - c₀‖ ≤ ε'` on the window. If `(K + G) u = λ u`, `‖u‖ = 1`,
  `|λ - E₀| ≤ h/2` and `‖K - K_g‖ ≤ r`, then with `τ = 2r/h`:
  `‖u* J u - c₀‖ ≤ N_c · 2(2W)^ε(2W)^{-1/2} + ε' + 2τ + (1 + ‖c₀‖) τ²`
  (`ProofETH.window_transfer` with the window of radius `h/2` around `λ`; no gap is assumed).
* `pairWindow_transfer_re`: the same bound for `|Re(u* J u) - Re c₀|`.
* `frob_le_card_mul_opNorm_sq`, `sqrt_frob_le`: `frob X ≤ |ι| ‖X‖²`.
* **`pairCentre_lipschitz`**: on a root rectangle, `x ↦ pairCentre J K s x` is
  `2 resLip(s, v₀)/v₀`-Lipschitz ("variation of the deterministic center across the window costs
  `O(W^{-1+β})`").
* **`pairWindow_transfer_grid`**: `pairWindow_transfer_re` centred at
  `windowCenter p i J K_g s λ`, the window variation paid by `pairCentre_lipschitz`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `‖X v‖² ≤ ‖X‖² ‖v‖²` for the `L²` operator norm. -/
theorem sqNorm_mulVec_le_opNorm (X : Matrix ι ι ℂ) (v : ι → ℂ) :
    sqNorm (X *ᵥ v) ≤ ‖X‖ ^ 2 * sqNorm v := by
  have hnorm : ∀ x : ι → ℂ, ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (sqNorm x) := by
    intro x; rw [EuclideanSpace.norm_eq]; rfl
  have h := Matrix.l2_opNorm_mulVec X (WithLp.toLp 2 v)
  have h' : Real.sqrt (sqNorm (X *ᵥ v)) ≤ ‖X‖ * Real.sqrt (sqNorm v) := by
    rw [← hnorm, ← hnorm]; exact h
  have h0 : 0 ≤ Real.sqrt (sqNorm (X *ᵥ v)) := Real.sqrt_nonneg _
  calc sqNorm (X *ᵥ v) = Real.sqrt (sqNorm (X *ᵥ v)) ^ 2 := (Real.sq_sqrt (sqNorm_nonneg _)).symm
    _ ≤ (‖X‖ * Real.sqrt (sqNorm v)) ^ 2 := pow_le_pow_left₀ h0 h' 2
    _ = ‖X‖ ^ 2 * sqNorm v := by rw [mul_pow, Real.sq_sqrt (sqNorm_nonneg _)]

theorem sqNorm_eq_one_of_l2Norm {u : ι → ℂ} (hu : l2Norm u = 1) : sqNorm u = 1 := by
  unfold l2Norm at hu
  exact Real.sqrt_eq_one.mp hu

/-- `frob X ≤ |ι| ‖X‖²`. -/
theorem frob_le_card_mul_opNorm_sq (X : Matrix ι ι ℂ) :
    frob X ≤ Fintype.card ι * ‖X‖ ^ 2 := by
  have h := frob_mul_left_le (A := X) (L := ‖X‖) (fun v => sqNorm_mulVec_le_opNorm X v) 1
  rw [mul_one, frob_one] at h
  linarith

/-- `√(frob X) ≤ √|ι| ‖X‖`. -/
theorem sqrt_frob_le (X : Matrix ι ι ℂ) :
    Real.sqrt (frob X) ≤ Real.sqrt (Fintype.card ι) * ‖X‖ := by
  calc Real.sqrt (frob X) ≤ Real.sqrt (Fintype.card ι * ‖X‖ ^ 2) :=
        Real.sqrt_le_sqrt (frob_le_card_mul_opNorm_sq X)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end Generic

variable {p : Parameters} {i : ZMod p.n}

/-- **Window transfer at one grid point**. Let `K_g` (the grid deformation) and
`G` be Hermitian with `PairWindowGood K_g sel s E₀ β ε J G`, at most `N_c` eigenvalues of
`K_g + G` in `[E₀ - h, E₀ + h]`, `h = (2W)^{-1+β}`, and `‖pairCentre J K_g s μ - c₀‖ ≤ ε'` for
`|μ - E₀| ≤ h`. Then every unit `u` with `(K + G) u = λ u`, `|λ - E₀| ≤ h/2`, `‖K - K_g‖ ≤ r`
satisfies `‖u* J u - c₀‖ ≤ N_c · 2(2W)^ε(2W)^{-1/2} + ε' + 2τ + (1 + ‖c₀‖) τ²`, `τ = r/(h/2)`. -/
theorem pairWindow_transfer {K Kg G : PairMatrix p i} (hKg : Kg.IsHermitian)
    (hG : G.IsHermitian) (sel : CEH.EigenpairSelection (2 * p.W)) {s E₀ β ε : ℝ}
    {J : PairMatrix p i} (hJn : ‖J‖ ≤ 1) (hgood : PairWindowGood Kg hKg sel s E₀ β ε J G)
    {Nc : ℕ}
    (hcount : (Finset.univ.filter fun k => pairEigval sel (Kg + G) (hKg.add hG) k ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card ≤ Nc)
    {u : PairSite p i → ℂ} (hu : l2Norm u = 1) {lam : ℝ} (hAu : (K + G) *ᵥ u = (lam : ℂ) • u)
    (hlam : |lam - E₀| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2) {r : ℝ} (hr : 0 ≤ r)
    (hKr : ‖K - Kg‖ ≤ r) {c₀ : ℂ} {ε' : ℝ} (hε' : 0 ≤ ε')
    (hcen : ∀ μ : ℝ, |μ - E₀| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) →
      ‖pairCentre J Kg s μ - c₀‖ ≤ ε') :
    ‖star u ⬝ᵥ (J *ᵥ u) - c₀‖ ≤
      Nc * (2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))) + ε' +
        2 * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) +
        (1 + ‖c₀‖) * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) ^ 2 := by
  obtain ⟨hG', hpair⟩ := hgood
  set h := ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) with hh
  set B := ((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) with hB
  have hNpos : (0 : ℝ) < ((2 * p.W : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos two_pos p.W_pos)
  have hh0 : 0 < h := Real.rpow_pos_of_pos hNpos _
  have hB0 : 0 ≤ B := by positivity
  set hA := hKg.add hG
  set e := pairEigvec sel (Kg + G) hA
  set μ := pairEigval sel (Kg + G) hA
  set S := Finset.univ.filter fun k => μ k ∈ Icc (E₀ - h) (E₀ + h) with hS
  have hSout : ∀ k ∉ S, h / 2 ≤ |μ k - lam| := by
    intro k hk
    have hk' : μ k ∉ Icc (E₀ - h) (E₀ + h) := fun h' => hk (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h'⟩)
    rw [mem_Icc, not_and_or, not_le, not_le] at hk'
    rw [abs_le] at hlam
    rcases hk' with hk' | hk'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hpert : sqNorm ((K + G - (Kg + G)) *ᵥ u) ≤ r ^ 2 := by
    have e1 : K + G - (Kg + G) = K - Kg := by abel
    rw [e1]
    refine (sqNorm_mulVec_le_opNorm _ u).trans ?_
    rw [sqNorm_eq_one_of_l2Norm hu, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) hKr 2
  have hwt := window_transfer hA (isOrthonormalFamily_pairEigvec sel (Kg + G) hA)
    (mulVec_pairEigvec sel (Kg + G) hA) (bilinear_le_of_opNorm_le hJn)
    (sqNorm_eq_one_of_l2Norm hu) hAu hr (half_pos hh0) hpert hSout
    (c := fun k => pairCentre J Kg s (μ k)) (c₀ := c₀) (ε := 2 * B) (ε' := ε')
    (by positivity) hε'
    (fun k hk l hl => hpair k l (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2)
    (fun k hk => by
      have hk' := (Finset.mem_filter.mp hk).2
      rw [mem_Icc] at hk'
      exact hcen (μ k) (by rw [abs_le]; constructor <;> linarith [hk'.1, hk'.2]))
  refine hwt.trans ?_
  have hc : (S.card : ℝ) ≤ Nc := by exact_mod_cast hcount
  have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 2 * B)
  linarith

/-- `pairWindow_transfer` for the real parts: `|Re(u* J u) - Re c₀|` obeys the same bound. -/
theorem pairWindow_transfer_re {K Kg G : PairMatrix p i} (hKg : Kg.IsHermitian)
    (hG : G.IsHermitian) (sel : CEH.EigenpairSelection (2 * p.W)) {s E₀ β ε : ℝ}
    {J : PairMatrix p i} (hJn : ‖J‖ ≤ 1) (hgood : PairWindowGood Kg hKg sel s E₀ β ε J G)
    {Nc : ℕ}
    (hcount : (Finset.univ.filter fun k => pairEigval sel (Kg + G) (hKg.add hG) k ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card ≤ Nc)
    {u : PairSite p i → ℂ} (hu : l2Norm u = 1) {lam : ℝ} (hAu : (K + G) *ᵥ u = (lam : ℂ) • u)
    (hlam : |lam - E₀| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2) {r : ℝ} (hr : 0 ≤ r)
    (hKr : ‖K - Kg‖ ≤ r) {c₀ : ℂ} {ε' : ℝ} (hε' : 0 ≤ ε')
    (hcen : ∀ μ : ℝ, |μ - E₀| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) →
      ‖pairCentre J Kg s μ - c₀‖ ≤ ε') :
    |(star u ⬝ᵥ (J *ᵥ u)).re - c₀.re| ≤
      Nc * (2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))) + ε' +
        2 * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) +
        (1 + ‖c₀‖) * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) ^ 2 := by
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans
    (pairWindow_transfer hKg hG sel hJn hgood hcount hu hAu hlam hr hKr hε' hcen)

/-- **Lipschitz bound of the real-axis centre across the window** (the variation
of the deterministic centre across the window costs `O(W^{-1+β})`): on a root rectangle,
`‖pairCentre J K s x - pairCentre J K s y‖ ≤ (2 resLip(s, v₀)/v₀) |x - y|` for a pair contraction
`J`. -/
theorem pairCentre_lipschitz {K J : PairMatrix p i} (hK : K.IsHermitian) (hJn : ‖J‖ ≤ 1)
    {s E₀ r v₀ : ℝ} (hs : 0 < s) (hv₀ : 0 < v₀) (hR : PairRootRectangle K s E₀ r v₀) {x y : ℝ}
    (hx : |x - E₀| ≤ r) (hy : |y - E₀| ≤ r) :
    ‖pairCentre J K s x - pairCentre J K s y‖ ≤ 2 * resLip s v₀ / v₀ * |x - y| := by
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  obtain ⟨mx, hmx, hvx⟩ := hR x hx 0 le_rfl zero_le_one
  obtain ⟨my, hmy, hvy⟩ := hR y hy 0 le_rfl zero_le_one
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hmx hmy
  have hpx : BlockBand.LocalWindow.pairDyson p i K s x = mx :=
    pairDyson_eq_of_isDysonRoot p i hK hs (by simp) hmx
  have hpy : BlockBand.LocalWindow.pairDyson p i K s y = my :=
    pairDyson_eq_of_isDysonRoot p i hK hs (by simp) hmy
  set Rx := (K - ((x : ℂ) + (s : ℂ) * mx) • (1 : PairMatrix p i))⁻¹ with hRx
  set Ry := (K - ((y : ℂ) + (s : ℂ) * my) • (1 : PairMatrix p i))⁻¹ with hRy
  have hgx : BlockBand.LocalWindow.windowGamma p i K s x = (s : ℂ) • (Rx * Rxᴴ) := by
    rw [windowGamma_eq, hpx]
  have hgy : BlockBand.LocalWindow.windowGamma p i K s y = (s : ℂ) • (Ry * Ryᴴ) := by
    rw [windowGamma_eq, hpy]
  set c : ℂ := (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) with hc
  have key : (J * (Rx * Rxᴴ)).trace - (J * (Ry * Ryᴴ)).trace =
      ((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace := by
    rw [trace_mul_comm J (Rx * Rxᴴ), trace_mul_comm J (Ry * Ryᴴ), ← trace_sub, ← trace_add]
    congr 1
    rw [conjTranspose_sub]
    noncomm_ring
  have hdiff : pairCentre J K s x - pairCentre J K s y =
      c * (s : ℂ) * (((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace) := by
    unfold pairCentre
    rw [hgx, hgy, mul_smul_comm, mul_smul_comm, trace_smul, trace_smul, smul_eq_mul,
      smul_eq_mul, ← hc, mul_assoc, mul_assoc, ← mul_sub, ← mul_sub, key]
    simp only [Matrix.mul_assoc]
  have hJ' : ∀ v : PairSite p i → ℂ, sqNorm (Jᴴ *ᵥ v) ≤ 1 ^ 2 * sqNorm v := fun v =>
    sqNorm_mulVec_le_of_opNorm_le (by rw [Matrix.l2_opNorm_conjTranspose]; exact hJn) v
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * (p.W : ℝ) := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have hW2 : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  have hsq : Real.sqrt (Fintype.card (PairSite p i) : ℝ) * Real.sqrt (Fintype.card (PairSite p i))
      = 2 * (p.W : ℝ) := by
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _), hcard]
  have hnx : ‖Rx‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hK hs (by simp) hv₀ hvx
  have hny : ‖Ry‖ ≤ (s * v₀)⁻¹ := opNorm_root_resolvent_le hK hs (by simp) hv₀ hvy
  have hlip : ‖Rx - Ry‖ ≤ resLip s v₀ * |x - y| := by
    have h := resolvent_lipschitz hK hs (by simp) (by simp) hmx hmy hv₀ hvx hvy
    rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  set q := Real.sqrt (Fintype.card (PairSite p i) : ℝ)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have ht1 : ‖((Rx - Ry) * Rxᴴ * J).trace‖ ≤ (q * ‖Rx - Ry‖) * (q * ‖Rx‖) :=
    (norm_trace_mul_mul_le hJ' _ _).trans
      (mul_le_mul (sqrt_frob_le _) (sqrt_frob_le _) (Real.sqrt_nonneg _) (by positivity))
  have ht2 : ‖(Ry * (Rx - Ry)ᴴ * J).trace‖ ≤ (q * ‖Ry‖) * (q * ‖Rx - Ry‖) :=
    (norm_trace_mul_mul_le hJ' _ _).trans
      (mul_le_mul (sqrt_frob_le _) (sqrt_frob_le _) (Real.sqrt_nonneg _) (by positivity))
  have hnc : ‖c * (s : ℂ)‖ = (2 * (p.W : ℝ))⁻¹ * s := by
    rw [norm_mul, hc, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hW2), abs_of_pos hs]
  have hL0 : 0 ≤ resLip s v₀ * |x - y| := (norm_nonneg _).trans hlip
  have hsum : ‖((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace‖ ≤
      2 * (p.W : ℝ) * (2 * ((resLip s v₀ * |x - y|) * (s * v₀)⁻¹)) := by
    refine (norm_add_le _ _).trans ?_
    have e1 : (q * ‖Rx - Ry‖) * (q * ‖Rx‖) = (q * q) * (‖Rx - Ry‖ * ‖Rx‖) := by ring
    have e2 : (q * ‖Ry‖) * (q * ‖Rx - Ry‖) = (q * q) * (‖Rx - Ry‖ * ‖Ry‖) := by ring
    rw [e1, hsq] at ht1
    rw [e2, hsq] at ht2
    have b1 : ‖Rx - Ry‖ * ‖Rx‖ ≤ (resLip s v₀ * |x - y|) * (s * v₀)⁻¹ :=
      mul_le_mul hlip hnx (norm_nonneg _) hL0
    have b2 : ‖Rx - Ry‖ * ‖Ry‖ ≤ (resLip s v₀ * |x - y|) * (s * v₀)⁻¹ :=
      mul_le_mul hlip hny (norm_nonneg _) hL0
    nlinarith [mul_le_mul_of_nonneg_left b1 hW2.le, mul_le_mul_of_nonneg_left b2 hW2.le]
  rw [hdiff, norm_mul, hnc]
  calc (2 * (p.W : ℝ))⁻¹ * s *
        ‖((Rx - Ry) * Rxᴴ * J).trace + (Ry * (Rx - Ry)ᴴ * J).trace‖
      ≤ (2 * (p.W : ℝ))⁻¹ * s * (2 * (p.W : ℝ) * (2 * ((resLip s v₀ * |x - y|) * (s * v₀)⁻¹))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * resLip s v₀ / v₀ * |x - y| := by
        have hWne : (p.W : ℝ) ≠ 0 := by have := p.W_pos; positivity
        field_simp

/-- **Window transfer at one grid point, real-axis centre at the eigenvalue**:
`pairWindow_transfer_re` with `c₀ = pairCentre J K_g s λ` and the centre variation across the
window paid by `pairCentre_lipschitz` (`|μ - λ| ≤ 3h/2`; the root rectangle of `K_g` has radius
`r₀ ≥ h`). The conclusion is centred at `windowCenter p i J K_g s λ`. -/
theorem pairWindow_transfer_grid {K Kg G : PairMatrix p i} (hKg : Kg.IsHermitian)
    (hG : G.IsHermitian) (sel : CEH.EigenpairSelection (2 * p.W)) {s E₀ β ε r₀ v₀ : ℝ}
    (hs : 0 < s) (hv₀ : 0 < v₀) (hR : PairRootRectangle Kg s E₀ r₀ v₀)
    (hhr : ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) ≤ r₀)
    {J : PairMatrix p i} (hJn : ‖J‖ ≤ 1) (hgood : PairWindowGood Kg hKg sel s E₀ β ε J G)
    {Nc : ℕ}
    (hcount : (Finset.univ.filter fun k => pairEigval sel (Kg + G) (hKg.add hG) k ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card ≤ Nc)
    {u : PairSite p i → ℂ} (hu : l2Norm u = 1) {lam : ℝ} (hAu : (K + G) *ᵥ u = (lam : ℂ) • u)
    (hlam : |lam - E₀| ≤ ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2) {r : ℝ} (hr : 0 ≤ r)
    (hKr : ‖K - Kg‖ ≤ r) :
    |(star u ⬝ᵥ (J *ᵥ u)).re - BlockBand.LocalWindow.windowCenter p i J Kg s lam| ≤
      Nc * (2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))) +
        2 * resLip s v₀ / v₀ * (3 / 2 * ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) +
        2 * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) +
        (1 + ‖pairCentre J Kg s lam‖) * (r / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2)) ^ 2 := by
  set h := ((2 * p.W : ℕ) : ℝ) ^ (-1 + β) with hh
  have hh0 : 0 < h := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.mul_pos two_pos p.W_pos)) _
  have hL0 : 0 ≤ 2 * resLip s v₀ / v₀ := by
    have : 0 ≤ resLip s v₀ := by
      unfold resLip
      have := rootLip_nonneg s v₀
      have : 0 ≤ 1 + s * rootLip s v₀ := by nlinarith
      positivity
    positivity
  have hlam' : |lam - E₀| ≤ r₀ := hlam.trans (by linarith)
  have hcen : ∀ μ : ℝ, |μ - E₀| ≤ h →
      ‖pairCentre J Kg s μ - pairCentre J Kg s lam‖ ≤ 2 * resLip s v₀ / v₀ * (3 / 2 * h) := by
    intro μ hμ
    refine (pairCentre_lipschitz hKg hJn hs hv₀ hR (hμ.trans hhr) hlam').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hL0
    have : |μ - lam| ≤ |μ - E₀| + |lam - E₀| := by
      rw [show μ - lam = (μ - E₀) - (lam - E₀) by ring]; exact abs_sub _ _
    linarith
  rw [← re_pairCentre]
  exact pairWindow_transfer_re hKg hG sel hJn hgood hcount hu hAu hlam hr hKr
    (by positivity) hcen

end BlockBand.LocalWindow.ProofPartTwo
