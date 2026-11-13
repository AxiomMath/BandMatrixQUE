module

public import BlockBand.DeterminantScore.SelectedLocalLawGrid

/-!
# Transfer of the complex trace from a grid energy to a selected energy (deterministic)

* `norm_trace_resolvent_sub_rankOne`: `‖Tr (K - z)⁻¹ - Tr (K' - z)⁻¹‖ ≤ 2/|Im z|` if
  `K - K' = a bᵀ` (Hermitian `K, K'`).
* `norm_trace_resolvent_sub_op`: `‖Tr (K - z)⁻¹ - Tr (K' - z)⁻¹‖ ≤ |ι| r/|Im z|²` if
  `‖(K' - z) - (K - z)‖ ≤ r`.
* **`trace_transfer`**: off the crowding event, at a nonpole energy `E` and a grid energy `e`,
  `‖Tr (A(E) - iη)⁻¹ - Tr (K̂_e + G - iη)⁻¹‖ ≤ 2/η + 2W (c²/ε₀² + 1)|E - e|/η²`.
* **`certErrHat_grid_le`**: `certErrHat(e) ≤ certErr(E) + 4/(W s √κ) + gridLip · h`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedLocalLaw

open Matrix BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.DeterminantScore.SelectedResolvent
open scoped ComplexConjugate

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Trace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Rank-one change of the resolvent trace**: for Hermitian `K, K'` with `K - K' = a bᵀ` and
`Im z ≠ 0`, `‖Tr (K - z)⁻¹ - Tr (K' - z)⁻¹‖ ≤ 2/|Im z|`. -/
theorem norm_trace_resolvent_sub_rankOne {K K' : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (hK' : K'.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : ι → ℂ) (hD : K - K' = vecMulVec a b) :
    ‖((K - z • (1 : Matrix ι ι ℂ))⁻¹).trace - ((K' - z • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤
      2 * |z.im|⁻¹ := by
  have h := norm_weightedTrace_resolvent_sub_le hK hK' hz a b hD (fun _ => 1) (fun _ => by simp)
  simp only [one_mul] at h
  rw [← trace_sub]
  exact h

/-- **Operator change of the resolvent trace**: for Hermitian `K, K'`, `Im z ≠ 0` and an operator
bound `r ≥ 0` on `(K' - z) - (K - z)`, `‖Tr (K - z)⁻¹ - Tr (K' - z)⁻¹‖ ≤ |ι| r/|Im z|²`. -/
theorem norm_trace_resolvent_sub_op {K K' : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (hK' : K'.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (hd : ∀ v, ‖T ((K' - z • 1) - (K - z • 1)) v‖ ≤ r * ‖v‖) :
    ‖((K - z • (1 : Matrix ι ι ℂ))⁻¹).trace - ((K' - z • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤
      Fintype.card ι * (|z.im|⁻¹ * r * |z.im|⁻¹) := by
  have hop := toE_resolvent_sub_le hK hK' hz hz hr hd
  rw [← trace_sub]
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖Matrix.diag ((K - z • (1 : Matrix ι ι ℂ))⁻¹ - (K' - z • 1)⁻¹) x‖
      ≤ ∑ _x : ι, |z.im|⁻¹ * r * |z.im|⁻¹ :=
        Finset.sum_le_sum fun x _ => norm_diag_le hop x
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Trace

section Pair

variable {p : Parameters} {i : ZMod p.n}

theorem isHermitian_real_smul_one (x : ℝ) : ((x : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- **Grid-to-selected transfer of the resolvent trace**. Let
`H_R, V, G` be Hermitian, `‖C‖, ‖C*‖ ≤ c`, `ε₀ > 0`, `E` a nonpole energy with at most one
eigenvalue of `H_R` within `ε₀`, `e` any energy and `η > 0`. With `z = iη`:
`‖Tr (A(E) - z)⁻¹ - Tr (K̂_e + G - z)⁻¹‖ ≤ 2/η + 2W ((c²/ε₀² + 1)|E - e|)/η²`. -/
theorem trace_transfer (om : SplitState p i) (G : PairMatrix p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) (hG : G.IsHermitian) {ε₀ c : ℝ} (hε₀ : 0 < ε₀) (hc : 0 ≤ c)
    (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖) {E e η : ℝ}
    (hdet : (om.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0)
    (hnear : (nearSet ε₀ hH E).card ≤ 1) (hη : 0 < η) :
    ‖((schurA p i om G E - (((0 : ℝ) : ℂ) + Complex.I * η) • (1 : PairMatrix p i))⁻¹).trace -
        ((hatK ε₀ om e + G - (((0 : ℝ) : ℂ) + Complex.I * η) • (1 : PairMatrix p i))⁻¹).trace‖ ≤
      2 / η + 2 * p.W * ((c ^ 2 / ε₀ ^ 2 + 1) * |E - e|) / η ^ 2 := by
  set z : ℂ := ((0 : ℝ) : ℂ) + Complex.I * η with hzdef
  have hzim : z.im = η := by simp [z]
  have hz : z.im ≠ 0 := by rw [hzim]; exact hη.ne'
  have hA : (schurA p i om G E).IsHermitian :=
    ((isHermitian_physicalCoareaF hH om.2.1 hV E).sub (isHermitian_real_smul_one E)).add hG
  have hM : (hatK ε₀ om E + G).IsHermitian := (isHermitian_hatK ε₀ om hV E).add hG
  have hM' : (hatK ε₀ om e + G).IsHermitian := (isHermitian_hatK ε₀ om hV e).add hG
  obtain ⟨a, b, hab⟩ := physicalCoareaF_sub_truncF_rankOne hH om.2.1 om.2.2 hdet hnear
  have hD : schurA p i om G E - (hatK ε₀ om E + G) = vecMulVec a b := by
    rw [← hab]; unfold schurA schurK0 hatK; abel
  have h1 := norm_trace_resolvent_sub_rankOne hA hM hz a b hD
  set r := (c ^ 2 / ε₀ ^ 2 + 1) * |E - e| with hr
  have hr0 : 0 ≤ r := by positivity
  have hdiff : ∀ v, ‖T ((hatK ε₀ om e + G - z • 1) - (hatK ε₀ om E + G - z • 1)) v‖ ≤ r * ‖v‖ := by
    intro v
    have heq : (hatK ε₀ om e + G - z • (1 : PairMatrix p i)) - (hatK ε₀ om E + G - z • 1) =
        (truncF ε₀ om.1 om.2.1 om.2.2 e - truncF ε₀ om.1 om.2.1 om.2.2 E) -
          ((e - E : ℝ) : ℂ) • 1 := by
      unfold hatK; rw [Complex.ofReal_sub, sub_smul]; abel
    rw [heq, map_sub, LinearMap.sub_apply]
    have k1 := norm_truncF_sub_le hH om.2.1 om.2.2 hε₀ hc hC hC' e E v
    have k2 := norm_toE_smul_one (ι := PairSite p i) ((e - E : ℝ) : ℂ) v
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at k2
    rw [abs_sub_comm] at k1
    calc _ ≤ ‖T (truncF ε₀ om.1 om.2.1 om.2.2 e - truncF ε₀ om.1 om.2.1 om.2.2 E) v‖ +
            ‖T (((e - E : ℝ) : ℂ) • (1 : PairMatrix p i)) v‖ := norm_sub_le _ _
      _ ≤ c ^ 2 * (|E - e| / ε₀ ^ 2) * ‖v‖ + |E - e| * ‖v‖ := by rw [k2]; gcongr
      _ = r * ‖v‖ := by rw [hr]; field_simp
  have h2 := norm_trace_resolvent_sub_op hM hM' hz hr0 hdiff
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    exact_mod_cast BlockBand.Angular.FiberAngular.card_pairSite p i
  rw [hcard, hzim, abs_of_pos hη] at h2
  rw [hzim, abs_of_pos hη] at h1
  have heq : ((schurA p i om G E - z • 1)⁻¹).trace - ((hatK ε₀ om e + G - z • 1)⁻¹).trace =
      (((schurA p i om G E - z • 1)⁻¹).trace - ((hatK ε₀ om E + G - z • 1)⁻¹).trace) +
        (((hatK ε₀ om E + G - z • 1)⁻¹).trace - ((hatK ε₀ om e + G - z • 1)⁻¹).trace) := by ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  have e1 : 2 * η⁻¹ = 2 / η := by ring
  have e2 : 2 * (p.W : ℝ) * (η⁻¹ * r * η⁻¹) = 2 * p.W * r / η ^ 2 := by field_simp
  linarith

/-- **Certificate at the grid from the certificate at the selected energy** (the
reverse direction of `SelectedResolvent.certErr_le_of_good`): for Hermitian `H_R`, `V`,
`‖C‖, ‖C*‖ ≤ c`, a nonpole `E ∈ bulkInterval κ` with at most one eigenvalue of `H_R` within
`ε₀`, a grid energy `e ∈ bulkInterval κ` with `|E - e| ≤ h`:
`certErrHat(e) ≤ certErr(E) + 4/(W s √κ) + gridLip(s, κ, c, ε₀) h`. -/
theorem certErrHat_grid_le (om : SplitState p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) {ε₀ c κ h : ℝ} (hε₀ : 0 < ε₀) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖)
    (hs : 0 < splitS p) {E e : ℝ} (hE : E ∈ bulkInterval κ) (he : e ∈ bulkInterval κ)
    (hEe : |E - e| ≤ h)
    (hdet : (om.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0)
    (hnear : (nearSet ε₀ hH E).card ≤ 1) :
    certErrHat ε₀ p i om e ≤ certErr p i om E + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) +
      gridLip (splitS p) κ c ε₀ * h := by
  have hgrid := certErrHat_le_grid om hH hV hε₀ hc hκ hC hC' hs he hE
  have him := sqrt_le_abs_matchedA_im hκ hE
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have himne : (matchedA E).im ≠ 0 := by
    intro h0; rw [h0, abs_zero] at him; linarith
  have hrev := certErrHat_le (ε := ε₀) om hH hV hdet hnear himne hs
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hk : 2 / ((p.W : ℝ) * (splitS p * |(matchedA E).im|)) ≤
      4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h' : Real.sqrt κ ≤ 2 * |(matchedA E).im| := by linarith
    have := mul_le_mul_of_nonneg_left h' (mul_pos hW hs).le
    nlinarith
  have hgl : 0 ≤ gridLip (splitS p) κ c ε₀ := by unfold gridLip; positivity
  have hgh : gridLip (splitS p) κ c ε₀ * |e - E| ≤ gridLip (splitS p) κ c ε₀ * h := by
    rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left hEe hgl
  linarith

end Pair

end BlockBand.DeterminantScore.SelectedLocalLaw
