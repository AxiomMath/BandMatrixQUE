module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalBox
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalCE

/-!
# The generic step, pathwise

* `im_diag_b3ClosedGramAt`, `im_diag_jSet`, **`sum_dlt_diag`**: the diagonal `M`-entries are
  real, so `Σ_k δ_{(0,k,k)} = Re Tr` increment (the hypothesis of the Taylor data);
* `Dh j`: the tested increment with the discrete jumps,
  `F(ẑ(t_{j+1})) − F(ẑ(t_j)) − ∫_{(t_j, t_{j+1}]} Λ`;
* **`genStep_pt`**: at a cell `p < j < q` without a birth, `Dh j` differs from the
  conditional-error form `Σ_c a₁_c (δ_c − W⁻¹ b_c) + Σ_{c,c'} a₂_{cc'} (δ_c δ_{c'} − W⁻¹ Γ_{cc'})`
  by at most `C (η³ + η⁴) + W⁻² |Γ| + W⁻¹ ε`, where `ε` controls `Λ` within the cell.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ComplexConjugate

variable {K np : ℕ}

/-!
## Real diagonals
-/

theorem im_diag_sourceGram {ι c : Type*} [Fintype ι] (V : Matrix ι c ℂ) (k : c) :
    (((V : Matrix ι c ℂ)ᴴ * V) k k).im = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.ofReal_im _

theorem im_diag_b3ClosedGramAt (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (k : SrcCol K (Fin np)) : ((b3ClosedGramAt b E s h τ m W n V y).1 k k).im = 0 :=
  im_diag_sourceGram _ k

theorem im_diag_jSet {b : ℝ} {m : Fin np → ℝ} {J : GSt K np} (hJ : J ∈ jSet b m)
    (k : SrcCol K (Fin np)) : (J.1 k k).im = 0 := by
  obtain ⟨x, rfl⟩ := hJ
  simp only [jSel, Prod.fst_sum, Matrix.sum_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs
  · simp [Matrix.single_apply]; split_ifs <;> simp
  · simp

/-- **The diagonal increment is the real trace increment.** -/
theorem sum_dlt_diag {H H' J J' : GSt K np} (hH : ∀ k, (H.1 k k).im = 0)
    (hH' : ∀ k, (H'.1 k k).im = 0) (hJ : ∀ k, (J.1 k k).im = 0) (hJ' : ∀ k, (J'.1 k k).im = 0) :
    ∑ k, dlt (H - J) (H' - J') (0, k, k) = ((trRe (H' - J') - trRe (H - J) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [dlt, gramEntry, trRe, Matrix.trace, Complex.re_sum, Finset.sum_sub_distrib]
  · simp [dlt, gramEntry, Complex.im_sum, hH, hH', hJ, hJ']

/-!
## The tested increment with the discrete jumps
-/

section Step

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} {a t : ℝ≥0}

/-- The correction `F(Z(u)) − F(Ẑ(u))` (nonzero only at grid points `τ_i − s` with `Wτ_i ∈ ℕ`). -/
def corrF (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (F : ZSt K np → ℂ) (u : ℝ≥0)
    (y : ProbedPath W np × ℝ) : ℂ :=
  F (stZ χ b E s τ m (pG b E s h τ m W V) u y) - F (zHat χ b E s h τ m W V u y)

/-- **The tested increment of the cell `j` with the discrete jumps.** -/
def Dh (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (F : ZSt K np → ℂ)
    (Λ : GSt K np × ZSt K np → ℂ) (a t : ℝ≥0) (j : ℕ) (y : ProbedPath W np × ℝ) : ℂ :=
  (pM χ b E s h τ m W V F Λ (cellT s W a t (j + 1)) y -
      pM χ b E s h τ m W V F Λ (cellT s W a t j) y) -
    (corrF χ b E s h τ m W V F (cellT s W a t (j + 1)) y -
      corrF χ b E s h τ m W V F (cellT s W a t j) y)

theorem Dh_eq (hV : Measurable V) (hχ : Continuous χ) (hΛ : Continuous Λ) (j : ℕ)
    (y : ProbedPath W np × ℝ) :
    Dh χ b E s h τ m W V F Λ a t j y = F (zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y) -
      F (zHat χ b E s h τ m W V (cellT s W a t j) y) -
      ∫ r in Ioc (cellT s W a t j : ℝ) (cellT s W a t (j + 1)), lInt χ b E s h τ m W V Λ y r := by
  rw [Dh, pM_sub hV hχ hΛ y (cellT_mono s W a t (Nat.le_succ j))]
  simp only [corrF]
  ring

/-- **The generic step, pathwise.** -/
theorem genStep_pt (td : TaylorData χ b E F Λ) (hV : Measurable V) (hχ : Continuous χ)
    (hΛ : Continuous Λ) (hs : 0 ≤ s) (hτ : ∀ i, s < τ i) (hW : 1 ≤ W) {j : ℕ}
    (hpj : limLenAll s W a < j) (hjq : j + 1 ≤ limLenAll s W t) (hnb : ¬ IsBirthStep τ W j)
    (y : ProbedPath W np × ℝ) {B C ε : ℝ}
    (hC : ∀ (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ),
      0 ≤ ℓ → (∀ e, ‖z.2.1 e‖ ≤ B) → (∀ e, ‖lamA χ b E e (J, z.1)‖ ≤ B) →
      ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ) →
      ‖F (nextZ χ b E J y' ℓ z) - F z - (td.a0 (J, z, ℓ) + ip1 (td.a1 (J, z, ℓ)) (dlt z.1 y') +
          ip2 (td.a2 (J, z, ℓ)) (sq2 (dlt z.1 y')))‖ ≤
        C * ((∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 3 + (∑ c, ‖dlt z.1 y' c‖ + ℓ * B) ^ 4))
    (hx : ∀ e, ‖(zHat χ b E s h τ m W V (cellT s W a t j) y).2.1 e‖ ≤ B)
    (hla : ∀ e, ‖lamA χ b E e (b3JumpAt b s τ m W j, yHat b E s h τ m W j V y)‖ ≤ B)
    (hUC : ∀ ξ : GIdx K np → ℂ, (∀ e, ‖ξ e‖ ≤ (W : ℝ)⁻¹ * B) →
      ‖Λ (b3JumpAt b s τ m W j, ((zHat χ b E s h τ m W V (cellT s W a t j) y).1,
          fun e => (zHat χ b E s h τ m W V (cellT s W a t j) y).2.1 e - ξ e,
          (zHat χ b E s h τ m W V (cellT s W a t j) y).2.2)) -
        Λ (b3JumpAt b s τ m W j, zHat χ b E s h τ m W V (cellT s W a t j) y)‖ ≤ ε) :
    ‖Dh χ b E s h τ m W V F Λ a t j y -
        (∑ c, td.a1 (b3JumpAt b s τ m W j, zHat χ b E s h τ m W V (cellT s W a t j) y,
            (W : ℝ)⁻¹) c * (b3dX b E s h τ m W j V (Sum.inl c) y -
              (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)) +
          ∑ c, ∑ c', td.a2 (b3JumpAt b s τ m W j, zHat χ b E s h τ m W V (cellT s W a t j) y,
            (W : ℝ)⁻¹) c c' * (b3dX b E s h τ m W j V (Sum.inl c) y *
              b3dX b E s h τ m W j V (Sum.inl c') y - (W : ℂ)⁻¹ *
                cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y)))‖ ≤
      C * ((∑ c, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ + (W : ℝ)⁻¹ * B) ^ 3 +
          (∑ c, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ + (W : ℝ)⁻¹ * B) ^ 4) +
        ‖((W : ℝ)⁻¹ : ℂ) ^ 2 * td.Γ (b3JumpAt b s τ m W j,
          zHat χ b E s h τ m W V (cellT s W a t j) y)‖ + (W : ℝ)⁻¹ * ε := by
  set J := b3JumpAt (K := K) b s τ m W j
  set z := zHat χ b E s h τ m W V (cellT s W a t j) y
  set w : ℝ := (W : ℝ)⁻¹
  set y' := yHat b E s h τ m W (j + 1) V y
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hw0 : 0 ≤ w := by positivity
  have hwc : ((w : ℝ) : ℂ) = (W : ℂ)⁻¹ := by simp [w]
  have hLj : limLenAll s W (cellT s W a t j) = j := limLenAll_cellT hs hW hpj.le (by omega)
  have hLj1 : limLenAll s W (cellT s W a t (j + 1)) = j + 1 :=
    limLenAll_cellT hs hW (by omega) hjq
  have hcj : closeLen s W ≤ j :=
    (closeLen_le_limLenAll (s := s) (W := W) a).trans hpj.le
  have hJ1 : b3JumpAt (K := K) b s τ m W (j + 1) = J := by
    rw [b3JumpAt_succ b s τ m hcj, b3BirthAt_eq_zero b hnb, add_zero]
  have hz1 : z.1 = yHat b E s h τ m W j V y := by simp only [z, zHat, hLj]
  have hℓ : ((cellT s W a t (j + 1) : ℝ) - cellT s W a t j) = w := by
    rw [cellT_succ_sub_eq hs hW hpj hjq, one_div]
  -- the next state
  have hnext : zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y = nextZ χ b E J y' w z := by
    have hA : ∀ e, genA χ b E s τ m (pG b E s h τ m W V) e (cellT s W a t (j + 1)) y =
        genA χ b E s τ m (pG b E s h τ m W V) e (cellT s W a t j) y +
          (w : ℂ) * lamA χ b E e (J, yHat b E s h τ m W j V y) := fun e => by
      have := genA_cell (b := b) (E := E) (h := h) (m := m) hV hχ hs hτ hW hpj.le (by omega) hnb
        e y (cellT_mono s W a t (Nat.le_succ j)) le_rfl
      rw [hℓ] at this
      rw [← this]; ring
    simp only [zHat, nextZ, z, hLj, hLj1, y', dlt, hA]
    refine Prod.ext rfl (Prod.ext (funext fun e => ?_) rfl)
    simp only
    ring
  -- the increments
  have hδ : ∀ c, dlt z.1 y' c = b3dX b E s h τ m W j V (Sum.inl c) y := fun c => by
    rw [hz1]
    simp only [dlt, y', yHat, hJ1, gramEntry_sub', b3dX, b3X, cEntry]
    ring
  have hδf : dlt z.1 y' = fun c => b3dX b E s h τ m W j V (Sum.inl c) y := funext hδ
  have hh : ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ) := by
    rw [hz1]
    have := sum_dlt_diag (H := b3ClosedGramAt b E s h τ m W j V y)
      (H' := b3ClosedGramAt b E s h τ m W (j + 1) V y) (J := J) (J' := b3JumpAt b s τ m W (j + 1))
      (im_diag_b3ClosedGramAt b E s h τ m W j V y) (im_diag_b3ClosedGramAt b E s h τ m W _ V y)
      (im_diag_jSet (b3JumpAt_mem_jSet b s τ m W j))
      (im_diag_jSet (b3JumpAt_mem_jSet b s τ m W (j + 1)))
    exact this
  have hrest := hC J y' z w hw0 hx (fun e => by rw [hz1]; exact hla e) hh
  rw [← hnext, hδf] at hrest
  -- the generator identity
  have hzJ : z.1 + J = b3ClosedGramAt b E s h τ m W j V y := by
    rw [hz1]; simp only [yHat, J, sub_add_cancel]
  have hgen := td.gen J z w
  rw [hzJ] at hgen
  -- the generator integral over the cell
  have hint : ‖(∫ r in Ioc (cellT s W a t j : ℝ) (cellT s W a t (j + 1)),
      lInt χ b E s h τ m W V Λ y r) - (w : ℂ) * Λ (J, z)‖ ≤ w * ε := by
    rw [integral_Ioc_eq_integral_Ioo]
    have hvol : volume.real (Ioo (cellT s W a t j : ℝ) (cellT s W a t (j + 1))) = w := by
      rw [Real.volume_real_Ioo, hℓ, max_eq_left hw0]
    have hfin : volume (Ioo (cellT s W a t j : ℝ) (cellT s W a t (j + 1))) < ⊤ := measure_Ioo_lt_top
    have hi1 : IntegrableOn (lInt χ b E s h τ m W V Λ y)
        (Ioo (cellT s W a t j : ℝ) (cellT s W a t (j + 1))) :=
      (integrableOn_lInt hV hχ hΛ y (cellT s W a t (j + 1))).mono_set
        (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc_left (cellT s W a t j).2))
    have hi2 : IntegrableOn (fun _ : ℝ => Λ (J, z))
        (Ioo (cellT s W a t j : ℝ) (cellT s W a t (j + 1))) := integrableOn_const hfin.ne
    have e1 : (∫ r in Ioo (cellT s W a t j : ℝ) (cellT s W a t (j + 1)),
        lInt χ b E s h τ m W V Λ y r) - (w : ℂ) * Λ (J, z) =
        ∫ r in Ioo (cellT s W a t j : ℝ) (cellT s W a t (j + 1)),
          (lInt χ b E s h τ m W V Λ y r - Λ (J, z)) := by
      rw [integral_sub hi1 hi2, setIntegral_const, hvol, Complex.real_smul]
    rw [e1]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (C := ε) hfin
      (f := fun r => lInt χ b E s h τ m W V Λ y r - Λ (J, z)) fun r hr => by
        have hr0 : 0 < r := lt_of_le_of_lt (cellT s W a t j).2 hr.1
        have hcr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0.le
        have hl1 : cellT s W a t j ≤ r.toNNReal := by
          rw [← NNReal.coe_le_coe, hcr]; exact hr.1.le
        have hl2 : r.toNNReal < cellT s W a t (j + 1) := by
          rw [← NNReal.coe_lt_coe, hcr]; exact hr.2
        have hL := limLenAll_of_cell hs hW hpj.le (by omega) hl1 hl2
        have hnb' : ¬ IsBirthStep τ W (limLenAll s W r.toNNReal) := hL ▸ hnb
        have hgJ := gramJ_eq_b3JumpAt (K := K) (b := b) (m := m) hτ hW hnb'
        have hZ := stZ_eq_zHat (χ := χ) (b := b) (E := E) (h := h) (m := m) (V := V) hτ hW hnb' y
        have hA : ∀ e, genA χ b E s τ m (pG b E s h τ m W V) e r.toNNReal y =
            genA χ b E s τ m (pG b E s h τ m W V) e (cellT s W a t j) y +
              (((r : ℝ) - cellT s W a t j : ℝ) : ℂ) *
                lamA χ b E e (J, yHat b E s h τ m W j V y) := fun e => by
          have := genA_cell (b := b) (E := E) (h := h) (m := m) hV hχ hs hτ hW hpj.le
            (by omega) hnb e y hl1 hl2.le
          rw [hcr] at this
          rw [← this]; ring
        have hz' : zHat χ b E s h τ m W V r.toNNReal y = (z.1, fun e => z.2.1 e -
            (((r : ℝ) - cellT s W a t j : ℝ) : ℂ) * lamA χ b E e (J, z.1), z.2.2) := by
          rw [hz1]
          simp only [zHat, z, hL, hLj, hA]
          refine Prod.ext rfl (Prod.ext (funext fun e => ?_) rfl)
          simp only
          ring
        simp only [lInt, hgJ, hZ, hL, hz']
        refine hUC _ fun e => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.2 hr.1.le)]
        have h1 : (r : ℝ) - cellT s W a t j ≤ w := by
          rw [← hℓ]; linarith [hr.2]
        rw [hz1]
        exact mul_le_mul h1 (hla e) (norm_nonneg _) hw0
    rw [hvol] at this
    linarith
  -- assembly
  obtain ⟨S1, hS1⟩ : ∃ S, ∑ c, td.a1 (J, z, w) c * b3dX b E s h τ m W j V (Sum.inl c) y = S :=
    ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S, ∑ c, td.a1 (J, z, w) c *
      ((W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)) = S := ⟨_, rfl⟩
  obtain ⟨S3, hS3⟩ : ∃ S, ∑ c, ∑ c', td.a2 (J, z, w) c c' *
      (b3dX b E s h τ m W j V (Sum.inl c) y * b3dX b E s h τ m W j V (Sum.inl c') y) = S :=
    ⟨_, rfl⟩
  obtain ⟨S4, hS4⟩ : ∃ S, ∑ c, ∑ c', td.a2 (J, z, w) c c' * ((W : ℂ)⁻¹ *
      cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y)) = S := ⟨_, rfl⟩
  have hm : (∑ c, td.a1 (J, z, w) c * (b3dX b E s h τ m W j V (Sum.inl c) y -
          (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)) +
        ∑ c, ∑ c', td.a2 (J, z, w) c c' * (b3dX b E s h τ m W j V (Sum.inl c) y *
          b3dX b E s h τ m W j V (Sum.inl c') y - (W : ℂ)⁻¹ *
            cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y))) =
      (S1 - S2) + (S3 - S4) := by
    rw [← hS1, ← hS2, ← hS3, ← hS4]
    simp only [mul_sub, Finset.sum_sub_distrib]
  have h1 : ip1 (td.a1 (J, z, w))
      (fun c => (w : ℂ) * drE b E c (b3ClosedGramAt b E s h τ m W j V y)) = S2 := by
    rw [← hS2]; simp only [ip1, hwc]; rfl
  have h2 : ip2 (td.a2 (J, z, w))
      (fun c c' => (w : ℂ) * cvE b E c c' (b3ClosedGramAt b E s h τ m W j V y)) = S4 := by
    rw [← hS4]; simp only [ip2, hwc]; rfl
  have h3 : ip1 (td.a1 (J, z, w)) (fun c => b3dX b E s h τ m W j V (Sum.inl c) y) = S1 := hS1
  have h4 : ip2 (td.a2 (J, z, w)) (sq2 fun c => b3dX b E s h τ m W j V (Sum.inl c) y) = S3 :=
    hS3
  rw [h3, h4] at hrest
  rw [h1, h2] at hgen
  obtain ⟨Iv, hIv⟩ : ∃ I, (∫ r in Ioc (cellT s W a t j : ℝ) (cellT s W a t (j + 1)),
      lInt χ b E s h τ m W V Λ y r) = I := ⟨_, rfl⟩
  rw [hIv] at hint
  obtain ⟨Fn, hFn⟩ : ∃ X, F (zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y) = X :=
    ⟨_, rfl⟩
  rw [hFn] at hrest
  have key : (Fn - F z - Iv) - ((S1 - S2) + (S3 - S4)) =
      (Fn - F z - (td.a0 (J, z, w) + S1 + S3)) +
        (td.a0 (J, z, w) + S2 + S4 - (w : ℂ) * Λ (J, z)) - (Iv - (w : ℂ) * Λ (J, z)) := by ring
  rw [Dh_eq hV hχ hΛ, hFn, hIv, hm]
  change ‖(Fn - F z - Iv) - ((S1 - S2) + (S3 - S4))‖ ≤ _
  rw [key, hgen]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) hint).trans ?_
  refine add_le_add (add_le_add hrest (le_of_eq ?_)) le_rfl
  simp only [w, Complex.ofReal_inv]

end Step

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
