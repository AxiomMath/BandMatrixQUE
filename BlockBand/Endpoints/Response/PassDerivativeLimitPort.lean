module

public import BlockBand.Endpoints.Response.PassDerivative

/-!
# Port-wise ratios and zero-source derivatives; additivity; path reversal

* `portRatio … κ i ω = F_{x,y}(T_i(κ))` (`portRatioSum = portRatio 0 + portRatio 1`);
* `portDeriv … q i ω = Re DF_{x,y}(T_i(0))[Ṫ_i]` (`portRatioDeriv = portDeriv 0 + portDeriv 1`).

Deterministic facts:
* `portRatio_bounds`, `portDeriv_abs_le`: the port-wise form of the pointwise bounds of clause 1
  (`portRatio_pointwise`);
* `portDeriv_add`: additivity in the nonnegative source (`B_{q+r} = B_q + B_r`);
* `portDeriv_congr_grid`, `portRatio_congr_grid`: only the grid values `q((n-i)/W)` matter;
* `portDeriv_one_revPath`: the far-port derivative of a sample is the near-port derivative of the
  reversed sample `revPath n ω` (blocks and bonds in reverse order, internal bonds adjointed, the
  two port bonds swapped), with the reversed grid profile.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open scoped Matrix.Norms.L2Operator

/-!
### Definitions
-/

/-- `F_{x,y}(T_i(κ))`, the ratio of port `i` (`0`: near, `1`: far). -/
def portRatio (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) (κ : ℝ) (i : Fin 2) (ω : GrowthPath W) : ℝ :=
  ratioDet x y (portDefect (absorbedScattering b E W n κ q ω) i)

/-- `Re DF_{x,y}(T_i(0))[Ṫ_i]`, the zero-source derivative of port `i`. -/
def portDeriv (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) (i : Fin 2) (ω : GrowthPath W) : ℝ :=
  (ratioDetDeriv x y
    (pencilPortDefect (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)
      (sourceRoot W n q) (portInclusion W i) 0)
    (pencilPortDefectDeriv (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)
      (sourceRoot W n q) (portInclusion W i))).re

variable {b E x y : ℝ} {W n : ℕ} {q : ℝ → ℝ}

theorem portRatioSum_eq_add (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) (κ : ℝ) (ω : GrowthPath W) :
    portRatioSum b E x y W n q κ ω = portRatio b E x y W n q κ 0 ω + portRatio b E x y W n q κ 1 ω :=
  rfl

theorem portRatioDeriv_eq_add (b E x y : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    portRatioDeriv b E x y W n q ω = portDeriv b E x y W n q 0 ω + portDeriv b E x y W n q 1 ω := by
  simp [portRatioDeriv, portDeriv, Fin.sum_univ_two]

theorem portRatio_eq (hq : ∀ t, 0 ≤ q t) (κ : ℝ) (i : Fin 2) (ω : GrowthPath W) :
    portRatio b E x y W n q κ i ω = ratioDet x y
      (pencilPortDefect (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)
        (sourceRoot W n q) (portInclusion W i) κ) := by
  simp only [portRatio, absorbedScattering_eq hq, portDefect_eq, pencilPortDefect]

/-!
### Pointwise bounds (port-wise form of clause 1)
-/

theorem portRatio_bounds (hb : b ≤ 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hq : ∀ t, 0 ≤ q t) (i : Fin 2)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) :
    (∀ κ : ℝ, 0 ≤ κ → |portRatio b E x y W n q κ i ω| ≤ 1) ∧
    (IsUnit (fullPathMatrix b E W n ω).det →
      (∀ κ : ℝ, 0 ≤ κ → |portRatio b E x y W n q κ i ω - portRatio b E x y W n q 0 i ω -
          κ * portDeriv b E x y W n q i ω| ≤
        κ * (4 * ratioC1 x y * etaZ b E *
          (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
            (leadInclusion W n)).trace.re *
          min 2 (κ * ‖sourceKernel (fullPathMatrix b E W n ω) (sourceRoot W n q)‖) +
          κ * (36 * ratioC1 x y + 576 * ratioC2 x y) * etaZ b E ^ 2 *
            (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
              (leadInclusion W n)).trace.re ^ 2)) ∧
      |portDeriv b E x y W n q i ω| ≤ ratioC1 x y * (4 * etaZ b E *
        (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
          (leadInclusion W n)).trace.re)) := by
  have hη := etaZ_nonneg hb hE1 hE2
  have hW := fullPathMatrix_ward (b := b) (E := E) (n := n) hH
  have hJ := portInclusion_norm_le (W := W) i
  refine ⟨fun κ hκ => ?_, fun hM => ⟨fun κ hκ => ?_, ?_⟩⟩
  · rw [portRatio_eq hq]
    exact (Complex.abs_re_le_norm _).trans (norm_ratioDetC_le_one hx hy0 hy1
      (pencilPortDefect_band (R := sourceRoot W n q) hη hκ hW hJ))
  · rw [portRatio_eq hq, portRatio_eq hq, portDeriv]
    have h0 := pencilRatio_pass_bound (R := sourceRoot W n q) hη hκ hx hy0 hy1 hM hW hJ
    refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans h0)
    simp [ratioDet, Complex.sub_re]
  · rw [portDeriv]
    refine (Complex.abs_re_le_norm _).trans ?_
    exact norm_ratioDetDeriv_le hx hy0 hy1
      (pencilPortDefect_band (R := sourceRoot W n q) hη le_rfl hW hJ)
      (pencilPortDefectDeriv_traceBound hη hW hJ)

/-- `|D_i| ≤ c₁ · 4η Tr B_q` for Hermitian blocks (no invertibility needed). -/
theorem portDeriv_abs_le (hb : b ≤ 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (i : Fin 2)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) :
    |portDeriv b E x y W n q i ω| ≤ ratioC1 x y * (4 * etaZ b E *
        (pencilSourceGram (fullPathMatrix b E W n ω) (sourceRoot W n q)
          (leadInclusion W n)).trace.re) := by
  have hη := etaZ_nonneg hb hE1 hE2
  have hW := fullPathMatrix_ward (b := b) (E := E) (n := n) hH
  have hJ := portInclusion_norm_le (W := W) i
  rw [portDeriv]
  refine (Complex.abs_re_le_norm _).trans ?_
  exact norm_ratioDetDeriv_le hx hy0 hy1
    (pencilPortDefect_band (R := sourceRoot W n q) hη le_rfl hW hJ)
    (pencilPortDefectDeriv_traceBound hη hW hJ)

/-!
### Measurability
-/

theorem measurable_portRatio (hq : ∀ t, 0 ≤ q t) (κ : ℝ) (i : Fin 2) :
    Measurable (fun ω => portRatio b E x y W n q κ i ω) := by
  have hG : Measurable (fun ω => (absorbedPencil (fullPathMatrix b E W n ω)
      (sourceRoot W n q) κ)⁻¹) :=
    passDeriv_measurable_inv.comp ((measurable_fullPathMatrix b E W n).add_const _)
  have hA : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) G) (portInclusion W i)) := by
    unfold portDefectOf scatFromInv; fun_prop
  have hT := (measurable_ratioDet (w := Fin W) x y).comp hA.measurable
  have e : (fun ω => portRatio b E x y W n q κ i ω) = fun ω =>
      ratioDet x y (portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n)
        (absorbedPencil (fullPathMatrix b E W n ω) (sourceRoot W n q) κ)⁻¹)
          (portInclusion W i)) := by
    funext ω
    rw [portRatio_eq hq]
    rfl
  rw [e]
  exact hT.comp hG

theorem measurable_portDeriv (i : Fin 2) :
    Measurable (fun ω => portDeriv b E x y W n q i ω) := by
  have hG : Measurable (fun ω => (fullPathMatrix b E W n ω)⁻¹) :=
    passDeriv_measurable_inv.comp (measurable_fullPathMatrix b E W n)
  have hA : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) G) (portInclusion W i)) := by
    unfold portDefectOf scatFromInv; fun_prop
  have hB : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      defectDerivFromInv (etaZ b E) (leadInclusion W n) (sourceRoot W n q)
        (portInclusion W i) G) := by
    unfold defectDerivFromInv scatFromInv; fun_prop
  have h1 := (measurable_ratioDetDeriv (w := Fin W) x y).comp
    (hA.measurable.prodMk hB.measurable)
  have h2 := Complex.measurable_re.comp h1
  have e : (fun ω => portDeriv b E x y W n q i ω) = fun ω =>
      (ratioDetDeriv x y
        (portDefectOf (scatFromInv (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω)⁻¹)
          (portInclusion W i))
        (defectDerivFromInv (etaZ b E) (leadInclusion W n) (sourceRoot W n q)
          (portInclusion W i) (fullPathMatrix b E W n ω)⁻¹)).re := by
    funext ω
    simp only [portDeriv, pencilPortDefect, absorbedPencil_zero]
    rfl
  rw [e]
  exact h2.comp hG

/-!
### Additivity in the source
-/

/-- The diagonal `R*R = Q_q/W²` of the source root. -/
def sourceDiag (W n : ℕ) (q : ℝ → ℝ) : Matrix (FullSite W n) (FullSite W n) ℂ :=
  Matrix.diagonal (Sum.elim
    (fun s => ((q (((n - s.1.val : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ)) fun _ => 0)

theorem sourceRoot_conjTranspose_mul (hq : ∀ t, 0 ≤ q t) :
    (sourceRoot W n q)ᴴ * sourceRoot W n q = sourceDiag W n q := by
  rw [sourceRoot, diagonal_conjTranspose, diagonal_mul_diagonal, sourceDiag]
  congr 1
  funext x
  rcases x with s | a
  · simp only [Pi.star_apply, Sum.elim_inl]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [div_mul_div_comm, Real.mul_self_sqrt (hq _), sq]
  · simp

theorem pencilSourceGram_sourceRoot (hq : ∀ t, 0 ≤ q t)
    (M : Matrix (FullSite W n) (FullSite W n) ℂ) :
    pencilSourceGram M (sourceRoot W n q) (leadInclusion W n) =
      (M⁻¹ * leadInclusion W n)ᴴ * sourceDiag W n q * (M⁻¹ * leadInclusion W n) := by
  rw [pencilSourceGram, sourceFrame, ← sourceRoot_conjTranspose_mul hq]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem sourceDiag_add (q r : ℝ → ℝ) :
    sourceDiag W n (fun t => q t + r t) = sourceDiag W n q + sourceDiag W n r := by
  rw [sourceDiag, sourceDiag, sourceDiag, diagonal_add]
  congr 1
  funext x
  rcases x with s | a
  · simp only [Sum.elim_inl]; push_cast; ring
  · simp

theorem pencilSourceGram_add {q r : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (hr : ∀ t, 0 ≤ r t)
    (M : Matrix (FullSite W n) (FullSite W n) ℂ) :
    pencilSourceGram M (sourceRoot W n (fun t => q t + r t)) (leadInclusion W n) =
      pencilSourceGram M (sourceRoot W n q) (leadInclusion W n) +
        pencilSourceGram M (sourceRoot W n r) (leadInclusion W n) := by
  rw [pencilSourceGram_sourceRoot (fun t => add_nonneg (hq t) (hr t)),
    pencilSourceGram_sourceRoot hq, pencilSourceGram_sourceRoot hr, sourceDiag_add,
    Matrix.mul_add, Matrix.add_mul]

theorem portDeriv_add {q r : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (hr : ∀ t, 0 ≤ r t) (i : Fin 2)
    (ω : GrowthPath W) :
    portDeriv b E x y W n (fun t => q t + r t) i ω =
      portDeriv b E x y W n q i ω + portDeriv b E x y W n r i ω := by
  have hT : ∀ q' : ℝ → ℝ, pencilPortDefect (etaZ b E) (leadInclusion W n)
      (fullPathMatrix b E W n ω) (sourceRoot W n q') (portInclusion W i) 0 =
      portDefectOf (pencilScattering (etaZ b E) (leadInclusion W n) (fullPathMatrix b E W n ω))
        (portInclusion W i) := fun q' => by
    simp [pencilPortDefect, absorbedPencil_zero]
  simp only [portDeriv, hT]
  rw [← Complex.add_re, ← ratioDetDeriv_add]
  congr 2
  simp only [pencilPortDefectDeriv, pencilSourceGram_add hq hr, Matrix.mul_add, smul_add,
    Matrix.add_mul, conjTranspose_add]
  abel

/-!
### Grid congruence
-/

theorem sourceRoot_congr_grid {q r : ℝ → ℝ}
    (h : ∀ i : Fin n, q (((n - i.val : ℕ) : ℝ) / W) = r (((n - i.val : ℕ) : ℝ) / W)) :
    sourceRoot W n q = sourceRoot W n r := by
  rw [sourceRoot, sourceRoot]
  congr 1
  funext x
  rcases x with ⟨j, c⟩ | a
  · simp only [Sum.elim_inl, h j]
  · rfl

theorem portDeriv_congr_grid {q r : ℝ → ℝ}
    (h : ∀ i : Fin n, q (((n - i.val : ℕ) : ℝ) / W) = r (((n - i.val : ℕ) : ℝ) / W))
    (i : Fin 2) (ω : GrowthPath W) :
    portDeriv b E x y W n q i ω = portDeriv b E x y W n r i ω := by
  simp only [portDeriv, sourceRoot_congr_grid h]

theorem portRatio_congr_grid {q r : ℝ → ℝ}
    (h : ∀ i : Fin n, q (((n - i.val : ℕ) : ℝ) / W) = r (((n - i.val : ℕ) : ℝ) / W))
    (κ : ℝ) (i : Fin 2) (ω : GrowthPath W) :
    portRatio b E x y W n q κ i ω = portRatio b E x y W n r κ i ω := by
  have : absorbedFullMatrix b E W n κ q ω = absorbedFullMatrix b E W n κ r ω := by
    simp only [absorbedFullMatrix]
    congr 3
    funext j
    simp only [layerAbsorption, h j]
  simp only [portRatio, absorbedScattering, this]

/-!
### Path reversal
-/

/-- Block index reversal on the first `n` birth indices. -/
def revIdx (n k : ℕ) : ℕ := if k < n then n - 1 - k else k

/-- The reversed sample at length `n`: block `k < n` is `A_{n-1-k}`; internal bond `0 < k < n` is
`B_{n-k}*`; the port bonds `B_0, B_n` are swapped; all other coordinates are unchanged. -/
def revPath (n : ℕ) {W : ℕ} (ω : GrowthPath W) : GrowthPath W :=
  (fun k => ω.1 (revIdx n k),
    fun k => if k = 0 then ω.2 n else if k < n then (ω.2 (n - k))ᴴ else if k = n then ω.2 0
      else ω.2 k)

/-- Site reversal of the full path: position `i ↦ n-1-i`, port `p ↦ 1-p`. -/
def fullRev (W n : ℕ) : FullSite W n ≃ FullSite W n :=
  Equiv.sumCongr (Equiv.prodCongr Fin.revPerm (Equiv.refl _))
    (Equiv.prodCongr Fin.revPerm (Equiv.refl _))

/-- Port swap `p ↦ 1-p`. -/
def portRev (W : ℕ) : Fin 2 × Fin W ≃ Fin 2 × Fin W :=
  Equiv.prodCongr Fin.revPerm (Equiv.refl _)

theorem ite_pos' {α : Type*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem dite_pos' {α : Type*} {c : Prop} [Decidable c] (h : c) (f : c → α) (g : ¬c → α) :
    dite c f g = f h := by simp [h]

theorem dite_neg' {α : Type*} {c : Prop} [Decidable c] (h : ¬c) (f : c → α) (g : ¬c → α) :
    dite c f g = g h := by simp [h]

theorem revPath_fst_lt (ω : GrowthPath W) {k : ℕ} (hk : k < n) :
    (revPath n ω).1 k = ω.1 (n - 1 - k) := by
  simp only [revPath, revIdx, ite_pos' hk]

theorem revPath_snd_mid (ω : GrowthPath W) {k : ℕ} (h0 : k ≠ 0) (hk : k < n) :
    (revPath n ω).2 k = (ω.2 (n - k))ᴴ := by
  simp only [revPath, ite_neg' h0, ite_pos' hk]

theorem revPath_snd_zero (ω : GrowthPath W) : (revPath n ω).2 0 = ω.2 n := by
  simp [revPath]

theorem revPath_snd_n (ω : GrowthPath W) (hn : n ≠ 0) : (revPath n ω).2 n = ω.2 0 := by
  simp [revPath, hn]

theorem val_rev' {k : Fin n} : (Fin.rev k).val = n - 1 - k.val := by
  rw [Fin.val_rev]; omega

theorem pathMatrix_revPath (ω : GrowthPath W) (i j : Fin n) (a c : Fin W) :
    pathMatrix (pathAt W n (revPath n ω)) (i, a) (j, c) =
      pathMatrix (pathAt W n ω) (Fin.rev i, a) (Fin.rev j, c) := by
  have hi := i.isLt
  have hj := j.isLt
  have hri : (Fin.rev i).val = n - 1 - i.val := val_rev'
  have hrj : (Fin.rev j).val = n - 1 - j.val := val_rev'
  unfold pathMatrix
  by_cases hij : i = j
  · subst hij
    rw [ite_pos' rfl, ite_pos' rfl]
    show (revPath n ω).1 (n - 1 - i.val) a c = ω.1 (n - 1 - (Fin.rev i).val) a c
    rw [revPath_fst_lt _ (by omega), hri]
  · have hij' : Fin.rev i ≠ Fin.rev j := fun h => hij (Fin.rev_injective h)
    rw [ite_neg' hij, ite_neg' hij']
    by_cases h1 : i.val + 1 = j.val
    · have h1' : ¬ (Fin.rev i).val + 1 = (Fin.rev j).val := by omega
      have h2' : (Fin.rev j).val + 1 = (Fin.rev i).val := by omega
      rw [dite_pos' h1, dite_neg' h1', dite_pos' h2']
      show ((revPath n ω).2 (n - 1 - i.val))ᴴ a c =
        star (((ω.2 (n - 1 - (Fin.rev j).val))ᴴ) c a)
      have e : n - (n - 1 - i.val) = n - 1 - (Fin.rev j).val := by omega
      rw [revPath_snd_mid _ (by omega) (by omega), conjTranspose_apply, conjTranspose_apply,
        conjTranspose_apply, star_star, e]
      try rw [star_star]
    · by_cases h2 : j.val + 1 = i.val
      · have h1' : (Fin.rev i).val + 1 = (Fin.rev j).val := by omega
        rw [dite_neg' h1, dite_pos' h2, dite_pos' h1']
        show star (((revPath n ω).2 (n - 1 - j.val))ᴴ c a) =
          ((ω.2 (n - 1 - (Fin.rev i).val))ᴴ) a c
        have e : n - (n - 1 - j.val) = n - 1 - (Fin.rev i).val := by omega
        rw [revPath_snd_mid _ (by omega) (by omega), conjTranspose_apply, conjTranspose_apply,
          conjTranspose_apply, star_star, e]
        try rw [star_star]
      try rw [star_star]
      · have h1' : ¬ (Fin.rev i).val + 1 = (Fin.rev j).val := by omega
        have h2' : ¬ (Fin.rev j).val + 1 = (Fin.rev i).val := by omega
        rw [dite_neg' h1, dite_neg' h2, dite_neg' h1', dite_neg' h2']

theorem pathPortCoupling_revPath (ω : GrowthPath W) (i : Fin n) (a : Fin W) (p : Fin 2)
    (c : Fin W) :
    pathPortCoupling (pathAt W n (revPath n ω)) (i, a) (p, c) =
      pathPortCoupling (pathAt W n ω) (Fin.rev i, a) (Fin.rev p, c) := by
  have hi := i.isLt
  have hn : n ≠ 0 := by omega
  have hri : (Fin.rev i).val = n - 1 - i.val := val_rev'
  unfold pathPortCoupling
  fin_cases p
  · by_cases h0 : i.val = 0
    · have h1 : (Fin.rev i).val + 1 = n := by omega
      simp only [Fin.zero_eta, Fin.isValue, show Fin.rev (0 : Fin 2) = 1 from rfl, h0, h1,
        and_self, true_or, or_true, ite_true]
      show (revPath n ω).2 n a c = ω.2 0 a c
      rw [revPath_snd_n _ hn]
    · have h2 : ¬ (n - (i.val + 1) + 1 = n) := by omega
      simp [show Fin.rev (0 : Fin 2) = 1 from rfl, h0, h2]
  · by_cases h0 : i.val + 1 = n
    · have h1 : (Fin.rev i).val = 0 := by omega
      simp only [Fin.mk_one, Fin.isValue, show Fin.rev (1 : Fin 2) = 0 from rfl, h0, h1,
        and_self, true_or, or_true, ite_true]
      show (revPath n ω).2 0 a c = ω.2 n a c
      rw [revPath_snd_zero]
    · have h2 : ¬ (n - (i.val + 1) = 0) := by omega
      simp [show Fin.rev (1 : Fin 2) = 0 from rfl, h0, h2]

theorem fullPathMatrix_revPath (b E : ℝ) (ω : GrowthPath W) :
    fullPathMatrix b E W n (revPath n ω) =
      (fullPathMatrix b E W n ω).submatrix (fullRev W n) (fullRev W n) := by
  ext u v
  rcases u with ⟨i, a⟩ | ⟨p, a⟩ <;> rcases v with ⟨j, c⟩ | ⟨p', c⟩
  · simp only [fullPathMatrix, fullRev, submatrix_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Equiv.refl_apply, fromBlocks_apply₁₁,
      Matrix.sub_apply, Matrix.smul_apply, one_apply, Prod.mk.injEq, pathMatrix_revPath,
      Fin.rev_inj]
  · simp only [fullPathMatrix, fullRev, submatrix_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Equiv.refl_apply,
      fromBlocks_apply₁₂, pathPortCoupling_revPath]
  · simp only [fullPathMatrix, fullRev, submatrix_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Equiv.refl_apply,
      fromBlocks_apply₂₁, conjTranspose_apply, pathPortCoupling_revPath]
  · simp only [fullPathMatrix, fullRev, submatrix_apply, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Equiv.refl_apply,
      fromBlocks_apply₂₂, Matrix.smul_apply, one_apply, Prod.mk.injEq, Fin.rev_inj]

theorem leadInclusion_submatrix_rev :
    (leadInclusion W n).submatrix (fullRev W n) (portRev W) = leadInclusion W n := by
  ext u a
  rcases u with s | p
  · simp [leadInclusion, fullRev]
  · simp only [leadInclusion, fullRev, portRev, submatrix_apply, Equiv.sumCongr_apply, Sum.map_inr,
      of_apply, Sum.elim_inr, Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply,
      Equiv.refl_apply, Prod.mk.injEq, Fin.rev_inj]
    simp [Prod.ext_iff]

theorem portInclusion_submatrix_rev :
    (portInclusion W 1).submatrix (portRev W) id = portInclusion W 0 := by
  ext a c
  simp only [portInclusion, portRev, submatrix_apply, of_apply, Equiv.prodCongr_apply, Prod.map,
    Fin.revPerm_apply, Equiv.refl_apply, id]
  have : Fin.rev a.1 = 1 ↔ a.1 = 0 := by
    rw [show (1 : Fin 2) = Fin.rev 0 from rfl, Fin.rev_inj]
  simp only [this]

theorem sourceRoot_rev {q q' : ℝ → ℝ}
    (h : ∀ i : Fin n, q' (((n - i.val : ℕ) : ℝ) / W) =
      q (((n - (Fin.rev i).val : ℕ) : ℝ) / W)) :
    sourceRoot W n q' = (sourceRoot W n q).submatrix (fullRev W n) (fullRev W n) := by
  rw [sourceRoot, sourceRoot, submatrix_diagonal_equiv]
  congr 1
  funext u
  rcases u with ⟨i, a⟩ | p
  · show ((Real.sqrt (q' (((n - i.val : ℕ) : ℝ) / W)) / W : ℝ) : ℂ) =
      ((Real.sqrt (q (((n - (Fin.rev i).val : ℕ) : ℝ) / W)) / W : ℝ) : ℂ)
    rw [h i]
  · rfl

section Transport

variable {ι p w : Type*} [Fintype ι] [DecidableEq ι] [Fintype p] [DecidableEq p] [Fintype w]
  [DecidableEq w]

omit [Fintype p] in
theorem pencilScattering_submatrix (η : ℝ) {V : Matrix ι p ℂ} (σ : ι ≃ ι) (τ : p ≃ p)
    (hV : V.submatrix σ τ = V) (M : Matrix ι ι ℂ) :
    pencilScattering η V (M.submatrix σ σ) = (pencilScattering η V M).submatrix τ τ := by
  have e : Vᴴ * (M.submatrix σ σ)⁻¹ * V = (Vᴴ * M⁻¹ * V).submatrix τ τ := by
    rw [inv_submatrix_equiv]
    conv_lhs => rw [← hV]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  rw [pencilScattering, pencilScattering, e]
  ext i j
  simp [Matrix.sub_apply, one_apply]

omit [Fintype p] [DecidableEq p] in
theorem pencilSourceGram_submatrix {V : Matrix ι p ℂ} (σ : ι ≃ ι) (τ : p ≃ p)
    (hV : V.submatrix σ τ = V) (M R : Matrix ι ι ℂ) :
    pencilSourceGram (M.submatrix σ σ) (R.submatrix σ σ) V =
      (pencilSourceGram M R V).submatrix τ τ := by
  have e : sourceFrame (M.submatrix σ σ) (R.submatrix σ σ) V =
      (sourceFrame M R V).submatrix σ τ := by
    rw [sourceFrame, sourceFrame, inv_submatrix_equiv]
    conv_lhs => rw [← hV]
    rw [submatrix_mul_equiv, submatrix_mul_equiv]
  rw [pencilSourceGram, pencilSourceGram, e, conjTranspose_submatrix, submatrix_mul_equiv]

omit [DecidableEq p] [Fintype w] [DecidableEq w] in
theorem compression_submatrix (S : Matrix p p ℂ) (τ : p ≃ p) {J J' : Matrix p w ℂ}
    (hJ : J.submatrix τ (Equiv.refl w) = J') :
    J'ᴴ * S.submatrix τ τ * J' = Jᴴ * S * J := by
  rw [← hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  rfl

theorem pencil_transport (η : ℝ) {V : Matrix ι p ℂ} (σ : ι ≃ ι) (τ : p ≃ p)
    (hV : V.submatrix σ τ = V) (M R : Matrix ι ι ℂ) {J J' : Matrix p w ℂ}
    (hJ : J.submatrix τ (Equiv.refl w) = J') :
    pencilPortDefect η V (M.submatrix σ σ) (R.submatrix σ σ) J' 0 =
        pencilPortDefect η V M R J 0 ∧
      pencilPortDefectDeriv η V (M.submatrix σ σ) (R.submatrix σ σ) J' =
        pencilPortDefectDeriv η V M R J := by
  have hS := pencilScattering_submatrix η σ τ hV M
  have hB := pencilSourceGram_submatrix σ τ hV M R
  have hSB : pencilScattering η V (M.submatrix σ σ) *
      pencilSourceGram (M.submatrix σ σ) (R.submatrix σ σ) V =
      (pencilScattering η V M * pencilSourceGram M R V).submatrix τ τ := by
    rw [hS, hB, submatrix_mul_equiv]
  constructor
  · simp only [pencilPortDefect, absorbedPencil_zero, portDefectOf, hS,
      compression_submatrix _ τ hJ]
  · simp only [pencilPortDefectDeriv]
    have hsm : ∀ (c : ℂ) (X : Matrix p p ℂ), c • X.submatrix τ τ = (c • X).submatrix τ τ :=
      fun c X => rfl
    rw [hSB, hsm, compression_submatrix _ τ hJ, hS, compression_submatrix _ τ hJ]

end Transport

/-- **Reversal of the far port.** The far-port derivative of `ω` equals the near-port derivative of
the reversed sample, for a profile `q'` with the reversed grid values. -/
theorem portDeriv_one_revPath {q q' : ℝ → ℝ}
    (h : ∀ i : Fin n, q' (((n - i.val : ℕ) : ℝ) / W) =
      q (((n - (Fin.rev i).val : ℕ) : ℝ) / W)) (ω : GrowthPath W) :
    portDeriv b E x y W n q' 0 (revPath n ω) = portDeriv b E x y W n q 1 ω := by
  have ht := pencil_transport (w := Fin W) (etaZ b E) (fullRev W n) (portRev W)
    leadInclusion_submatrix_rev (fullPathMatrix b E W n ω) (sourceRoot W n q)
    (J := portInclusion W 1) (J' := portInclusion W 0) portInclusion_submatrix_rev
  rw [portDeriv, portDeriv, fullPathMatrix_revPath, sourceRoot_rev h, ht.1, ht.2]

end BlockBand.Endpoints
