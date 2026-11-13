module

public import BlockBand.SourceProcess.ContractingWords.MatchDrift

/-!
# The second-order sums of the two expansions, matched

`A_J = currentOf 𝕏`, `B = sepOf 𝕏`, ordinary words, `κ₀ ≥ |κ₂|, |κ₃|`:
* `drift_second`: the pair sum of `word_drift_expand`, `Σ_{p<q} Σ_k κ_k pairF(…)` is
  `W⁻¹ Σ_{i<j} pairContraction(D₀/2, P, P + A_J, M_{ij}, N_{ij}) + O(2κ₀ Σ_{Z ∈ contrTwo w}|Tr Z|)`;
* `cov_second`: the cross sum of `word_cov_expand`, `Σ_{p,q} Σ_k κ_k crossF(…)` is
  `W⁻¹ Σ_{i,j} crossContraction(D₀/2, P, P + A_J, M_i, M'_j) + O(2κ₀ Σ_{Z ∈ contrCov w v}|Tr Z|)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.FullSourceGenerator

variable {W nT nI : ℕ}

/-- **The drift pair sum.** -/
theorem drift_second (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hJ : A .current = currentOf b E XX) {w : TraceWord nT nI} (hw : IsOrdinaryWord w)
    {κ₀ : ℝ} (hκ : ‖fscK b E s W 2‖ ≤ κ₀ ∧ ‖fscK b E s W 3‖ ≤ κ₀) :
    ‖∑ p, ∑ q ∈ Finset.Ioi p, ∑ k, fscK b E s W k * pairF (wl A w) (slotSep b E XX w) p q
          (slotSep b E XX w p * fscG b E XX k * slotSep b E XX w q)
          (slotSep b E XX w q * fscH b E XX k * slotSep b E XX w p) -
        (W : ℂ)⁻¹ * ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length,
          pairContraction ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj)
            (sepOf b E XX .proj + A .current) (pairM A (sepOf b E XX) w i j)
            (pairN A (sepOf b E XX) w i j)‖ ≤
      2 * κ₀ * ((contrTwo w).map fun Zs => ‖coreProd A (sepOf b E XX) Zs‖).sum := by
  have hF : ∀ p : Fin w.length, ∀ q ∈ Finset.Ioi p,
      ∑ k, fscK b E s W k * pairF (wl A w) (slotSep b E XX w) p q
          (slotSep b E XX w p * fscG b E XX k * slotSep b E XX w q)
          (slotSep b E XX w q * fscH b E XX k * slotSep b E XX w p) =
        pairVal b E s XX A w p q := fun p q hq => by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show slotSep b E XX w = fun i => sepOf b E XX (w.get i).2 from rfl,
      pairF_word A (sepOf b E XX) w (Finset.mem_Ioi.mp hq)]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl (hF p),
    fin_pair_sum w.length (pairVal b E s XX A w), Finset.mul_sum, ← Finset.sum_sub_distrib,
    contrTwo_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  obtain ⟨hij, hj⟩ := Finset.mem_Ioo.mp hj
  exact pair_one b E s XX A hJ hw hκ hij hj

/-- The value of one cross pair with the four tensors. -/
abbrev crossVal (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w v : TraceWord nT nI)
    (i j : ℕ) : ℂ :=
  ∑ k, fscK b E s W k * (singleM A (sepOf b E XX) w i * fscG b E XX k *
    singleM A (sepOf b E XX) v j * fscH b E XX k).trace

theorem cross_one (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hJ : A .current = currentOf b E XX) {w v : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hv : IsOrdinaryWord v) {κ₀ : ℝ} (hκ : ‖fscK b E s W 2‖ ≤ κ₀ ∧ ‖fscK b E s W 3‖ ≤ κ₀)
    {i j : ℕ} (hi : i < w.length) (hj : j < v.length) :
    ‖crossVal b E s XX A w v i j - (W : ℂ)⁻¹ * crossContraction ((transportD0 b E / 2 : ℝ) : ℂ)
        (sepOf b E XX .proj) (sepOf b E XX .proj + A .current) (singleM A (sepOf b E XX) w i)
        (singleM A (sepOf b E XX) v j)‖ ≤
      2 * κ₀ * sepSum (fun σ σ' => [setLastSep (w.rotate (i + 1)) σ ++
        setLastSep (v.rotate (j + 1)) σ']) fun Zs => ‖coreProd A (sepOf b E XX) Zs‖ := by
  have hP' : sepOf b E XX .proj + A .current =
      (twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX := by
    rw [hJ, currentOf]; simp [sepOf]
  have nw : w.rotate (i + 1) ≠ [] := fun h => hw.1 (List.rotate_eq_nil_iff.mp h)
  have nv : v.rotate (j + 1) ≠ [] := fun h => hv.1 (List.rotate_eq_nil_iff.mp h)
  have ow : ∀ x ∈ w.rotate (i + 1), x.2 = .id ∨ x.2 = .proj := fun x hx =>
    hw.2 x (List.mem_rotate.mp hx)
  have ov : ∀ x ∈ v.rotate (j + 1), x.2 = .id ∨ x.2 = .proj := fun x hx =>
    hv.2 x (List.mem_rotate.mp hx)
  have hk : ∀ k : Fin 4, k = 2 ∨ k = 3 →
      ‖(singleM A (sepOf b E XX) w i * fscG b E XX k * singleM A (sepOf b E XX) v j *
          fscH b E XX k).trace‖ ≤
        sepSum (fun σ σ' => [setLastSep (w.rotate (i + 1)) σ ++ setLastSep (v.rotate (j + 1)) σ'])
          fun Zs => ‖coreProd A (sepOf b E XX) Zs‖ := fun k hk => by
    obtain ⟨σ, hσ, σ', hσ', e⟩ := exists_contr_cross b E XX A nw ow nv ov (sepAt_ord hw hi)
      (sepAt_ord hv hj) hk
    have e' : (singleM A (sepOf b E XX) w i * fscG b E XX k * singleM A (sepOf b E XX) v j *
        fscH b E XX k).trace = wval A (sepOf b E XX) (setLastSep (w.rotate (i + 1)) σ ++
          setLastSep (v.rotate (j + 1)) σ') := e
    rw [e', ← coreProd_one]
    exact le_sepSum (fun σ σ' => [setLastSep (w.rotate (i + 1)) σ ++
      setLastSep (v.rotate (j + 1)) σ']) (fun _ => norm_nonneg _) hσ hσ'
  have e : crossVal b E s XX A w v i j - (W : ℂ)⁻¹ * crossContraction
      ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj) (sepOf b E XX .proj + A .current)
        (singleM A (sepOf b E XX) w i) (singleM A (sepOf b E XX) v j) =
      fscK b E s W 2 * (singleM A (sepOf b E XX) w i * fscG b E XX 2 *
          singleM A (sepOf b E XX) v j * fscH b E XX 2).trace +
        fscK b E s W 3 * (singleM A (sepOf b E XX) w i * fscG b E XX 3 *
          singleM A (sepOf b E XX) v j * fscH b E XX 3).trace := by
    rw [crossVal, Fin.sum_univ_four, hP', crossContraction]
    simp only [fscK, fscG, fscH, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, sepOf]
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul (fscK b E s W 2), norm_mul (fscK b E s W 3)]
  have h2 := hk 2 (Or.inl rfl)
  have h3 := hk 3 (Or.inr rfl)
  have hk0 : 0 ≤ κ₀ := (norm_nonneg _).trans hκ.1
  have := mul_le_mul hκ.1 h2 (norm_nonneg _) hk0
  have := mul_le_mul hκ.2 h3 (norm_nonneg _) hk0
  linarith

/-- **The covariance cross sum.** -/
theorem cov_second (b E : ℝ) (s : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hJ : A .current = currentOf b E XX) {w v : TraceWord nT nI} (hw : IsOrdinaryWord w)
    (hv : IsOrdinaryWord v) {κ₀ : ℝ} (hκ : ‖fscK b E s W 2‖ ≤ κ₀ ∧ ‖fscK b E s W 3‖ ≤ κ₀) :
    ‖∑ p, ∑ q, ∑ k, fscK b E s W k * crossF (wl A w) (slotSep b E XX w) (wl A v)
          (slotSep b E XX v) p q (slotSep b E XX w p * fscG b E XX k * slotSep b E XX v q)
          (slotSep b E XX v q * fscH b E XX k * slotSep b E XX w p) -
        (W : ℂ)⁻¹ * ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length,
          crossContraction ((transportD0 b E / 2 : ℝ) : ℂ) (sepOf b E XX .proj)
            (sepOf b E XX .proj + A .current) (singleM A (sepOf b E XX) w i)
            (singleM A (sepOf b E XX) v j)‖ ≤
      2 * κ₀ * ((contrCov w v).map fun Zs => ‖coreProd A (sepOf b E XX) Zs‖).sum := by
  have hF : ∀ (p : Fin w.length) (q : Fin v.length),
      ∑ k, fscK b E s W k * crossF (wl A w) (slotSep b E XX w) (wl A v)
          (slotSep b E XX v) p q (slotSep b E XX w p * fscG b E XX k * slotSep b E XX v q)
          (slotSep b E XX v q * fscH b E XX k * slotSep b E XX w p) =
        crossVal b E s XX A w v p q := fun p q => by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show slotSep b E XX w = fun i => sepOf b E XX (w.get i).2 from rfl,
      show slotSep b E XX v = fun i => sepOf b E XX (v.get i).2 from rfl, crossF_word]
  simp only [hF]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ q : Fin v.length, crossVal b E s XX A w v i q)]
  rw [Finset.sum_congr rfl fun i _ =>
    Fin.sum_univ_eq_sum_range (fun j => crossVal b E s XX A w v i j) v.length]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, contrCov_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  exact cross_one b E s XX A hJ hw hv hκ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

end BlockBand.SourceProcess.ContractingWords
