module

public import BlockBand.DeterminantScore.SelectedResolvent

/-!
# Grid-to-selected-energy transfer of the pole certificate (deterministic)

* `norm_diag_le`, `norm_pairBlockTrace_le`: block traces are bounded by twice the operator bound.
* `toE_resolvent_sub_le`: `‖(K - z)⁻¹ - (K' - z')⁻¹‖ ≤ |Im z|⁻¹ d |Im z'|⁻¹` when
  `‖(K' - z') - (K - z)‖ ≤ d`.
* `norm_matchedA_sub_le`: `a(E) = matchedA E` is `(1/2 + 2/√κ)`-Lipschitz on `bulkInterval κ`.
* `certErrHat_le_grid`: `certErrHat(E) ≤ certErrHat(e) + Λ |E - e|` for `E, e ∈ bulkInterval κ`,
  `‖C‖, ‖C*‖ ≤ c`, with `Λ = 2 h⁻² (c²/ε₀² + 1 + s(1/2 + 2/√κ)) + (1/2 + 2/√κ)`, `h = s√κ/2`.
* `certErr_le_certErrHat`: at a nonpole energy with at most one exterior eigenvalue within `ε₀`,
  `certErr(E) ≤ certErrHat(E) + 2/(W s |Im a|)` (the reverse of `certErrHat_le`).
* `bulkGrid`: a grid of `bulkInterval κ` of spacing `h` with at most `4/h + 2` points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedResolvent

open Matrix Set BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCertificate BlockBand.LocalWindow.ProofCount
open BlockBand.DeterminantScore.MinorTailInverse
open scoped ComplexConjugate

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A diagonal entry is bounded by an operator bound. -/
theorem norm_diag_le {M : Matrix ι ι ℂ} {c : ℝ} (h : ∀ v, ‖T M v‖ ≤ c * ‖v‖) (x : ι) :
    ‖M x x‖ ≤ c := by
  have hv : ‖(EuclideanSpace.single x 1 : EuclideanSpace ℂ ι)‖ = 1 := by simp
  have hMv : (T M (EuclideanSpace.single x 1)) x = M x x := by
    simp [mulVec, dotProduct, Pi.single_apply]
  calc ‖M x x‖ = ‖(T M (EuclideanSpace.single x 1)) x‖ := by rw [hMv]
    _ ≤ ‖T M (EuclideanSpace.single x 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ c * ‖(EuclideanSpace.single x 1 : EuclideanSpace ℂ ι)‖ := h _
    _ = c := by rw [hv, mul_one]

/-- `‖T (z • 1) v‖ = ‖z‖ ‖v‖`. -/
theorem norm_toE_smul_one (z : ℂ) (v : EuclideanSpace ℂ ι) :
    ‖T (z • (1 : Matrix ι ι ℂ)) v‖ = ‖z‖ * ‖v‖ := by
  rw [toE_apply, Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.toLp_smul, WithLp.toLp_ofLp,
    norm_smul]

/-- **Resolvent difference**: for Hermitian `K, K'` and nonreal `z, z'`, if
`(K' - z') - (K - z)` has operator bound `d ≥ 0`, then
`‖(K - z)⁻¹ - (K' - z')⁻¹‖ ≤ |Im z|⁻¹ d |Im z'|⁻¹`. -/
theorem toE_resolvent_sub_le {K K' : Matrix ι ι ℂ} (hK : K.IsHermitian) (hK' : K'.IsHermitian)
    {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : ∀ v, ‖T ((K' - z' • 1) - (K - z • 1)) v‖ ≤ d * ‖v‖) (v : EuclideanSpace ℂ ι) :
    ‖T ((K - z • (1 : Matrix ι ι ℂ))⁻¹ - (K' - z' • (1 : Matrix ι ι ℂ))⁻¹) v‖ ≤
      |z.im|⁻¹ * d * |z'.im|⁻¹ * ‖v‖ := by
  set X := K - z • (1 : Matrix ι ι ℂ)
  set X' := K' - z' • (1 : Matrix ι ι ℂ)
  have hX : IsUnit X.det := isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hK hz)
  have hX' : IsUnit X'.det := isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hK' hz')
  have hid : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX',
      Matrix.mul_one, Matrix.nonsing_inv_mul _ hX, Matrix.one_mul]
  rw [hid, ← toE_toE, ← toE_toE]
  calc ‖T X⁻¹ (T (X' - X) (T X'⁻¹ v))‖ ≤ |z.im|⁻¹ * ‖T (X' - X) (T X'⁻¹ v)‖ :=
        norm_resolvent_le hK hz _
    _ ≤ |z.im|⁻¹ * (d * ‖T X'⁻¹ v‖) := by gcongr; exact hd _
    _ ≤ |z.im|⁻¹ * (d * (|z'.im|⁻¹ * ‖v‖)) := by gcongr; exact norm_resolvent_le hK' hz' _
    _ = _ := by ring

end Operator

section Pair

variable {p : Parameters} {i : ZMod p.n}

/-- Block traces are bounded by twice an operator bound. -/
theorem norm_pairBlockTrace_le {M : PairMatrix p i} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, ‖T M v‖ ≤ c * ‖v‖) (k : ZMod p.n) : ‖pairBlockTrace p i M k‖ ≤ 2 * c := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    exact_mod_cast BlockBand.Angular.FiberAngular.card_pairSite p i
  unfold pairBlockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ x : PairSite p i, (if x.1.1 = k then M x x else 0)‖ ≤ 2 * p.W * c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : PairSite p i, ‖if x.1.1 = k then M x x else 0‖ ≤ ∑ _x : PairSite p i, c := by
          refine Finset.sum_le_sum fun x _ => ?_
          split_ifs
          · exact norm_diag_le h x
          · rw [norm_zero]; exact hc
      _ = 2 * p.W * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  calc (p.W : ℝ)⁻¹ * ‖∑ x : PairSite p i, (if x.1.1 = k then M x x else 0)‖
      ≤ (p.W : ℝ)⁻¹ * (2 * p.W * c) := by gcongr
    _ = 2 * c := by field_simp

theorem pairBlockTrace_sub (M M' : PairMatrix p i) (k : ZMod p.n) :
    pairBlockTrace p i M k - pairBlockTrace p i M' k = pairBlockTrace p i (M - M') k := by
  unfold pairBlockTrace
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

end Pair

/-!
## Lipschitz bound for `a(E)`
-/

/-- `4 - E² ≥ κ` on `bulkInterval κ`. -/
theorem four_sub_sq_ge {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : κ ≤ 4 - E ^ 2 := by
  obtain ⟨h1, h2⟩ := hE
  have hk2 : κ ≤ 2 := by linarith
  nlinarith

/-- **`a(E)` is Lipschitz on the bulk**: `‖a(E) - a(e)‖ ≤ (1/2 + 2/√κ) |E - e|`. -/
theorem norm_matchedA_sub_le {κ E e : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    (he : e ∈ bulkInterval κ) :
    ‖matchedA E - matchedA e‖ ≤ (1 / 2 + 2 / Real.sqrt κ) * |E - e| := by
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hu := four_sub_sq_ge hκ hE
  have hv := four_sub_sq_ge hκ he
  set u := 4 - E ^ 2
  set v := 4 - e ^ 2
  have hsu : Real.sqrt κ ≤ Real.sqrt u := Real.sqrt_le_sqrt hu
  have hsv : Real.sqrt κ ≤ Real.sqrt v := Real.sqrt_le_sqrt hv
  have hE2 : |E| ≤ 2 := by obtain ⟨h1, h2⟩ := hE; rw [abs_le]; constructor <;> linarith
  have he2 : |e| ≤ 2 := by obtain ⟨h1, h2⟩ := he; rw [abs_le]; constructor <;> linarith
  have huv : |u - v| ≤ 4 * |E - e| := by
    have : u - v = -((E - e) * (E + e)) := by simp only [u, v]; ring
    rw [this, abs_neg, abs_mul]
    have : |E + e| ≤ 4 := (abs_add_le _ _).trans (by linarith)
    nlinarith [abs_nonneg (E - e)]
  have hsq : |Real.sqrt u - Real.sqrt v| ≤ 2 * |E - e| / Real.sqrt κ := by
    have hprod : (Real.sqrt u - Real.sqrt v) * (Real.sqrt u + Real.sqrt v) = u - v := by
      have h1 := Real.sq_sqrt (show 0 ≤ u by linarith [hκ])
      have h2 := Real.sq_sqrt (show 0 ≤ v by linarith [hκ])
      nlinarith
    have hpos : 0 < Real.sqrt u + Real.sqrt v := by linarith
    rw [le_div_iff₀ hsk]
    have habs : |Real.sqrt u - Real.sqrt v| * (Real.sqrt u + Real.sqrt v) = |u - v| := by
      rw [← hprod, abs_mul, abs_of_pos hpos]
    have : |Real.sqrt u - Real.sqrt v| * (2 * Real.sqrt κ) ≤ |u - v| := by
      rw [← habs]; gcongr; linarith
    nlinarith [abs_nonneg (Real.sqrt u - Real.sqrt v)]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (matchedA E - matchedA e).re = -(E - e) / 2 := by
    simp only [Complex.sub_re, matchedA]; ring
  have him : (matchedA E - matchedA e).im = -(Real.sqrt u - Real.sqrt v) / 2 := by
    simp only [Complex.sub_im, matchedA, u, v]; ring
  rw [hre, him, abs_div, abs_div, abs_neg, abs_neg, abs_two]
  have : 2 * |E - e| / Real.sqrt κ = 2 / Real.sqrt κ * |E - e| := by ring
  rw [this] at hsq
  have : 0 ≤ 2 / Real.sqrt κ * |E - e| := by positivity
  linarith

/-!
## The grid transfer of `certErrHat`
-/

section Transfer

variable {p : Parameters} {i : ZMod p.n}

/-- The Lipschitz constant of the grid transfer. -/
def gridLip (s κ c ε₀ : ℝ) : ℝ :=
  2 * (s * (Real.sqrt κ / 2))⁻¹ * (s * (Real.sqrt κ / 2))⁻¹ *
      (c ^ 2 / ε₀ ^ 2 + 1 + s * (1 / 2 + 2 / Real.sqrt κ)) + (1 / 2 + 2 / Real.sqrt κ)

/-- **Grid transfer of the truncated certificate**: for Hermitian `V`,
`‖C‖, ‖C*‖ ≤ c`, `E, e ∈ bulkInterval κ`, `s = splitS p > 0`:
`certErrHat(E) ≤ certErrHat(e) + gridLip s κ c ε₀ · |E - e|`. -/
theorem certErrHat_le_grid (om : SplitState p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) {ε₀ c κ : ℝ} (hε₀ : 0 < ε₀) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖)
    (hs : 0 < splitS p) {E e : ℝ} (hE : E ∈ bulkInterval κ) (he : e ∈ bulkInterval κ) :
    certErrHat ε₀ p i om E ≤ certErrHat ε₀ p i om e + gridLip (splitS p) κ c ε₀ * |E - e| := by
  set s := splitS p
  set La := 1 / 2 + 2 / Real.sqrt κ with hLa
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hLa0 : 0 ≤ La := by positivity
  set h := s * (Real.sqrt κ / 2) with hh
  have hh0 : 0 < h := by positivity
  have hEh : ∀ x : ℝ, ((x : ℂ) • (1 : PairMatrix p i)).IsHermitian := fun x => by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  set K : ℝ → PairMatrix p i := fun x => truncF ε₀ om.1 om.2.1 om.2.2 x - (x : ℂ) • 1 with hKdef
  have hK : ∀ x, (K x).IsHermitian := fun x => (isHermitian_truncF ε₀ om.1 om.2.1 hV x).sub (hEh x)
  set z : ℝ → ℂ := fun x => (s : ℂ) * matchedA x with hzdef
  have hzim : ∀ x, x ∈ bulkInterval κ → h ≤ |(z x).im| := by
    intro x hx
    have := sqrt_le_abs_matchedA_im hκ hx
    have hz : (z x).im = s * (matchedA x).im := by simp [z, Complex.mul_im]
    rw [hz, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left this hs.le
  have hzne : ∀ x, x ∈ bulkInterval κ → (z x).im ≠ 0 := fun x hx h0 => by
    have := hzim x hx; rw [h0, abs_zero] at this; linarith
  set d := (c ^ 2 / ε₀ ^ 2 + 1 + s * La) * |E - e| with hd
  have hd0 : 0 ≤ d := by positivity
  have hdiff : ∀ v, ‖T ((K e - z e • 1) - (K E - z E • 1)) v‖ ≤ d * ‖v‖ := by
    intro v
    have heq : (K e - z e • (1 : PairMatrix p i)) - (K E - z E • 1) =
        (truncF ε₀ om.1 om.2.1 om.2.2 e - truncF ε₀ om.1 om.2.1 om.2.2 E) -
          ((e - E : ℝ) : ℂ) • 1 - (z e - z E) • 1 := by
      simp only [K]; rw [Complex.ofReal_sub, sub_smul, sub_smul]; abel
    rw [heq, map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply]
    have h1 := norm_truncF_sub_le hH om.2.1 om.2.2 hε₀ hc hC hC' e E v
    have h2 := norm_toE_smul_one (ι := PairSite p i) ((e - E : ℝ) : ℂ) v
    have h3 := norm_toE_smul_one (ι := PairSite p i) (z e - z E) v
    have hza : ‖z e - z E‖ ≤ s * (La * |E - e|) := by
      have : z e - z E = (s : ℂ) * (matchedA e - matchedA E) := by simp only [z]; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      gcongr
      rw [abs_sub_comm]
      exact norm_matchedA_sub_le hκ he hE
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at h2
    rw [abs_sub_comm] at h1
    calc _ ≤ ‖T (truncF ε₀ om.1 om.2.1 om.2.2 e - truncF ε₀ om.1 om.2.1 om.2.2 E) v‖ +
            ‖T (((e - E : ℝ) : ℂ) • (1 : PairMatrix p i)) v‖ +
            ‖T ((z e - z E) • (1 : PairMatrix p i)) v‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ c ^ 2 * (|E - e| / ε₀ ^ 2) * ‖v‖ + |E - e| * ‖v‖ + s * (La * |E - e|) * ‖v‖ := by
          rw [h2, h3]
          gcongr
      _ = d * ‖v‖ := by rw [hd]; field_simp
  have hres := toE_resolvent_sub_le (hK E) (hK e) (hzne E hE) (hzne e he) hd0 hdiff
  have hres' : ∀ v, ‖T ((K E - z E • (1 : PairMatrix p i))⁻¹ - (K e - z e • 1)⁻¹) v‖ ≤
      (h⁻¹ * d * h⁻¹) * ‖v‖ := by
    intro v
    refine (hres v).trans ?_
    have h1 : |(z E).im|⁻¹ ≤ h⁻¹ := inv_anti₀ hh0 (hzim E hE)
    have h2 : |(z e).im|⁻¹ ≤ h⁻¹ := inv_anti₀ hh0 (hzim e he)
    gcongr
  have hk : ∀ k : ZMod p.n,
      ‖pairBlockTrace p i ((K E - z E • 1)⁻¹) k - matchedA E‖ ≤
        ‖pairBlockTrace p i ((K e - z e • 1)⁻¹) k - matchedA e‖ +
          gridLip s κ c ε₀ * |E - e| := by
    intro k
    have hB := norm_pairBlockTrace_le (by positivity) hres' k
    rw [← pairBlockTrace_sub] at hB
    have ha : ‖matchedA E - matchedA e‖ ≤ La * |E - e| := norm_matchedA_sub_le hκ hE he
    have heq : pairBlockTrace p i ((K E - z E • 1)⁻¹) k - matchedA E =
        (pairBlockTrace p i ((K e - z e • 1)⁻¹) k - matchedA e) +
          (pairBlockTrace p i ((K E - z E • 1)⁻¹) k - pairBlockTrace p i ((K e - z e • 1)⁻¹) k) -
          (matchedA E - matchedA e) := by ring
    rw [heq]
    have hL : 2 * (h⁻¹ * d * h⁻¹) + La * |E - e| = gridLip s κ c ε₀ * |E - e| := by
      unfold gridLip; rw [hd]; ring
    calc _ ≤ ‖pairBlockTrace p i ((K e - z e • 1)⁻¹) k - matchedA e‖ +
            ‖pairBlockTrace p i ((K E - z E • 1)⁻¹) k -
              pairBlockTrace p i ((K e - z e • 1)⁻¹) k‖ + ‖matchedA E - matchedA e‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := by rw [← hL]; linarith
  unfold certErrHat
  refine max_le ((hk i).trans ?_) ((hk (i + 1)).trans ?_)
  · exact add_le_add_left (le_max_left _ _) _
  · exact add_le_add_left (le_max_right _ _) _

/-- **Transfer `F̂ → F`** (the reverse of `certErrHat_le`): at a nonpole energy
`E` with at most one exterior eigenvalue within `ε₀` of `E`, Hermitian `H_R`, `V`,
`Im a(E) ≠ 0` and `s = splitS p > 0`: `certErr(E) ≤ certErrHat(E) + 2/(W s |Im a(E)|)`. -/
theorem certErr_le_certErrHat {ε : ℝ} (om : SplitState p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) {E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    (hnear : (nearSet ε hH E).card ≤ 1) (him : (matchedA E).im ≠ 0) (hs : 0 < splitS p) :
    certErr p i om E ≤
      certErrHat ε p i om E + 2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) := by
  obtain ⟨a, b, hab⟩ := physicalCoareaF_sub_truncF_rankOne hH om.2.1 om.2.2 hdet hnear
  have hEh : ((E : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hK : (pairResidual p i om E).IsHermitian :=
    (isHermitian_physicalCoareaF hH om.2.1 hV E).sub hEh
  have hK' : (truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1).IsHermitian :=
    (isHermitian_truncF ε om.1 om.2.1 hV E).sub hEh
  set z : ℂ := (splitS p : ℂ) * matchedA E
  have hzim : z.im = splitS p * (matchedA E).im := by
    simp [z, Complex.mul_im]
  have hz : z.im ≠ 0 := by rw [hzim]; exact mul_ne_zero hs.ne' him
  have hzabs : |z.im| = splitS p * |(matchedA E).im| := by
    rw [hzim, abs_mul, abs_of_pos hs]
  have hD : pairResidual p i om E - (truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1) =
      vecMulVec a b := by
    rw [← hab]
    unfold pairResidual
    abel
  have hk : ∀ k : ZMod p.n,
      ‖pairBlockTrace p i ((pairResidual p i om E - z • 1)⁻¹) k - matchedA E‖ ≤
        ‖pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 - z • 1)⁻¹) k -
            matchedA E‖ +
          2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) := by
    intro k
    have h := norm_pairBlockTrace_sub_le hK hK' hz a b hD k
    rw [hzabs] at h
    calc _ = ‖(pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 - z • 1)⁻¹) k -
              matchedA E) +
            (pairBlockTrace p i ((pairResidual p i om E - z • 1)⁻¹) k -
              pairBlockTrace p i ((truncF ε om.1 om.2.1 om.2.2 E - (E : ℂ) • 1 - z • 1)⁻¹) k)‖ := by
            congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right h _)
  unfold certErrHat certErr
  refine max_le ((hk i).trans ?_) ((hk (i + 1)).trans ?_)
  · exact add_le_add_left (le_max_left _ _) _
  · exact add_le_add_left (le_max_right _ _) _

end Transfer

/-!
## The bulk grid
-/

/-- Grid of `bulkInterval κ` of spacing `h`: `min(-2 + κ + j h, 2 - κ)`, `0 ≤ j ≤ ⌈(4 - 2κ)/h⌉`. -/
def bulkGrid (κ h : ℝ) : Finset ℝ :=
  (Finset.range (⌈(4 - 2 * κ) / h⌉₊ + 1)).image fun j : ℕ => min (-2 + κ + j * h) (2 - κ)

theorem bulkGrid_mem {κ h : ℝ} (hκ : κ ≤ 2) (hh : 0 ≤ h) {e : ℝ} (he : e ∈ bulkGrid κ h) :
    e ∈ bulkInterval κ := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he
  refine ⟨le_min ?_ (by linarith), min_le_right _ _⟩
  have : (0 : ℝ) ≤ j * h := by positivity
  linarith

theorem bulkGrid_card_le {κ h : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 2) (hh : 0 < h) :
    ((bulkGrid κ h).card : ℝ) ≤ 4 / h + 2 := by
  have h1 : ((bulkGrid κ h).card : ℝ) ≤ ((⌈(4 - 2 * κ) / h⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_image_le).trans (Finset.card_range _).le
  have h2 : ((⌈(4 - 2 * κ) / h⌉₊ : ℕ) : ℝ) < (4 - 2 * κ) / h + 1 :=
    Nat.ceil_lt_add_one (by apply div_nonneg <;> linarith)
  have h3 : (4 - 2 * κ) / h ≤ 4 / h := div_le_div_of_nonneg_right (by linarith) hh.le
  push_cast at h1
  linarith

/-- Every point of `bulkInterval κ` is within `h` of the grid. -/
theorem exists_bulkGrid_near {κ h : ℝ} (hh : 0 < h) {E : ℝ}
    (hE : E ∈ bulkInterval κ) : ∃ e ∈ bulkGrid κ h, |E - e| ≤ h := by
  obtain ⟨h1, h2⟩ := hE
  set j := ⌊(E - (-2 + κ)) / h⌋₊
  have hx : 0 ≤ (E - (-2 + κ)) / h := div_nonneg (by linarith) hh.le
  have hjle : (j : ℝ) ≤ (E - (-2 + κ)) / h := Nat.floor_le hx
  have hjlt : (E - (-2 + κ)) / h < j + 1 := Nat.lt_floor_add_one _
  have hjh : (j : ℝ) * h ≤ E - (-2 + κ) := by rwa [le_div_iff₀ hh] at hjle
  have hjh' : E - (-2 + κ) < (j + 1) * h := by rwa [div_lt_iff₀ hh] at hjlt
  refine ⟨-2 + κ + j * h, Finset.mem_image.mpr ⟨j, ?_, ?_⟩, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hh.le)).trans
      (Nat.floor_le_ceil _)
  · exact min_eq_left (by linarith)
  · rw [abs_le]; constructor <;> nlinarith

end BlockBand.DeterminantScore.SelectedResolvent
