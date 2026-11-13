module

public import BlockBand.Native.ErdosRiabov.Psi.Defs

/-!
# Continuity of the control quantities in `(t, H)`

Deterministic; no law.

On `U = [0,1] × {H Hermitian}` (product topology, entrywise topology on matrices), for `N ≥ 1`,
`W ≥ 1`, `Im z > 0` and a stochastic symmetric profile `S` (`Kernel.StochasticSymm`):
* the resolvent slots `(H - z_{j,t})⁻¹` are continuous (`Im z_{j,t} = ±η_t ≠ 0`, Hermitian pencils
  are invertible, `continuousAt_matrix_inv`), hence so are the chains (`continuousOn_gChain`);
* the M-terms `t ↦ Split.chainM t S m A 1 k` are continuous on `[0,1]` for `‖m_i‖ < 1`
  (`continuousOn_chainM`), by strong induction on the recursion length: each stability operator
  `(1 - σ m_j m_k S)⁻¹` is invertible for `σ ∈ [0,1]` (Neumann series, `Kernel`);
* `Υ_t`, `ℓ_tη_t`, the size functions are continuous and positive;
* hence every ratio and `Ψ^iso_{k,t}(H)`, `Ψ^av_{k,t}(H)` are continuous on `U`
  (`continuousOn_bigPsiIso`, `continuousOn_bigPsiAv`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Psi

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl)
open Set
open scoped ComplexConjugate NNReal

variable {N k : ℕ}

/-- The domain `[0,1] × {H Hermitian}`. -/
def hermDomain (N : ℕ) : Set (ℝ × Matrix (Fin N) (Fin N) ℂ) :=
  Icc (0 : ℝ) 1 ×ˢ {H | H.IsHermitian}

/-! ### Generic continuity tools -/

theorem continuousAt_matrix_inv_of_isUnit {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsUnit A.det) :
    ContinuousAt (fun B : Matrix (Fin N) (Fin N) ℂ => B⁻¹) A := by
  apply continuousAt_matrix_inv
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hA.ne_zero

theorem isUnit_det_herm_sub {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) : IsUnit (H - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  have h := (ERNative.BlockBand.isUnit_resolventPencil H hH hw).neg
  rw [neg_sub] at h
  exact (Matrix.isUnit_iff_isUnit_det _).mp h

theorem continuousOn_list_ofFn_prod {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [Monoid M] [ContinuousMul M] {s : Set X} :
    ∀ {k : ℕ} (f : Fin k → X → M), (∀ l, ContinuousOn (f l) s) →
      ContinuousOn (fun q => (List.ofFn fun l => f l q).prod) s
  | 0, _, _ => by simpa using continuousOn_const
  | k + 1, f, hf => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hf 0).mul (continuousOn_list_ofFn_prod (fun l => f l.succ) fun l => hf l.succ)

theorem continuous_patConj (b : Bool) : Continuous (VS.patConj b) := by
  cases b
  · exact continuous_id
  · exact Complex.continuous_conj

theorem continuous_vsTraj (z : ℂ) : Continuous (vsTraj z) := by
  unfold vsTraj
  fun_prop

theorem continuous_patZ (z : ℂ) (σ : Fin k → Bool) (j : Fin k) :
    Continuous fun t => patZ z σ t j :=
  (continuous_patConj (σ j)).comp (continuous_vsTraj z)

theorem patZ_im_ne_zero {z : ℂ} (hz : 0 < z.im) (σ : Fin k → Bool) {t : ℝ} (ht : t ≤ 1)
    (j : Fin k) : (patZ z σ t j).im ≠ 0 := by
  have h := vsHeight_pos hz ht
  unfold patZ
  cases σ j
  · simp only [VS.patConj, Bool.false_eq_true, ite_false, vsTraj_im]
    exact h.ne'
  · simp only [VS.patConj, ite_true, Complex.conj_im, vsTraj_im]
    linarith

/-- **Chains are continuous** on `[0,1] × {H Hermitian}` (`Im z > 0`). -/
theorem continuousOn_gChain {z : ℂ} (hz : 0 < z.im) (σ : Fin k → Bool)
    (B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => gChain (patZ z σ q.1) B q.2)
      (hermDomain N) := by
  unfold gChain Chains.slotProd Chains.slotList
  apply continuousOn_list_ofFn_prod
  intro l
  apply ContinuousOn.mul _ continuousOn_const
  intro _q hq
  have hA := isUnit_det_herm_sub hq.2 (patZ_im_ne_zero hz σ hq.1.2 l)
  have hc : Continuous fun q : ℝ × Matrix (Fin N) (Fin N) ℂ =>
      q.2 - patZ z σ q.1 l • (1 : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_snd.sub (((continuous_patZ z σ l).comp continuous_fst).smul continuous_const)
  exact (ContinuousAt.comp (g := fun B : Matrix (Fin N) (Fin N) ℂ => B⁻¹)
    (f := fun q : ℝ × Matrix (Fin N) (Fin N) ℂ =>
      q.2 - patZ z σ q.1 l • (1 : Matrix (Fin N) (Fin N) ℂ)) (x := _q)
    (continuousAt_matrix_inv_of_isUnit hA) hc.continuousAt).continuousWithinAt

/-! ### Continuity of the M-terms in the profile scale -/

theorem profileC_eq_cMat (S : Matrix (Fin N) (Fin N) ℝ) : Split.profileC S = cMat S := by
  ext a b
  simp [Split.profileC, cMat]

theorem continuousOn_stabOp {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {a : ℂ}
    (ha : ‖a‖ < 1) : ContinuousOn (fun σ : ℝ => Split.stabOp σ S a) (Icc 0 1) := by
  intro σ hσ
  have hσa : ‖(σ : ℂ) * a‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.1]
    calc σ * ‖a‖ ≤ ‖a‖ := mul_le_of_le_one_left (norm_nonneg _) hσ.2
      _ < 1 := ha
  have hU : IsUnit (1 - ((σ : ℂ) * a) • Split.profileC S).det := by
    rw [profileC_eq_cMat]
    exact Matrix.isUnit_det_of_right_inverse (one_sub_smul_mul_neumann hS hσa)
  have hc : Continuous fun s : ℝ => 1 - ((s : ℂ) * a) • Split.profileC S := by fun_prop
  exact (ContinuousAt.comp (g := fun B : Matrix (Fin N) (Fin N) ℂ => B⁻¹)
    (f := fun s : ℝ => 1 - ((s : ℂ) * a) • Split.profileC S) (x := σ)
    (continuousAt_matrix_inv_of_isUnit hU) hc.continuousAt).continuousWithinAt

theorem continuous_mulVec_pair :
    Continuous fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) => Matrix.mulVec p.1 p.2 :=
  continuous_fst.matrix_mulVec continuous_snd

theorem continuousOn_chainTilde_aux {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {m : ℕ → ℂ} (hm : ∀ i, ‖m i‖ < 1) (A : ℕ → Fin N → ℂ) (n : ℕ) :
    ∀ j l, l - j = n →
      ContinuousOn (fun σ : ℝ => Split.chainTilde σ S m A j l) (Icc 0 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn
  have heq : (fun σ : ℝ => Split.chainTilde σ S m A j l) = fun σ =>
      if j < l then
        Matrix.mulVec (Split.stabOp σ S (m j * m l))
          (A j * Split.chainTilde σ S m A (j + 1) l +
            ∑ i ∈ Finset.Ioo j l,
              ((σ : ℂ) * m j * m i) •
                (Split.selfEnergy S (Split.chainTilde σ S m A j i) *
                  Split.chainTilde σ S m A i l))
      else fun _ => 1 := funext fun σ => Split.chainTilde_eq σ S m A j l
  rw [heq]
  by_cases hjl : j < l
  · simp only [hjl, ite_true]
    have hml : ‖m j * m l‖ < 1 := by
      rw [norm_mul]
      calc ‖m j‖ * ‖m l‖ ≤ ‖m l‖ := mul_le_of_le_one_left (norm_nonneg _) (hm j).le
        _ < 1 := hm l
    have h1 := ih (l - (j + 1)) (by omega) (j + 1) l rfl
    have hsum : ContinuousOn (fun σ : ℝ => ∑ i ∈ Finset.Ioo j l,
        ((σ : ℂ) * m j * m i) • (Split.selfEnergy S (Split.chainTilde σ S m A j i) *
          Split.chainTilde σ S m A i l)) (Icc 0 1) := by
      apply continuousOn_finsetSum
      intro i hi
      have hi' := Finset.mem_Ioo.mp hi
      have h2 := ih (i - j) (by omega) j i rfl
      have h3 := ih (l - i) (by omega) i l rfl
      have hself : ContinuousOn (fun σ : ℝ => Split.selfEnergy S (Split.chainTilde σ S m A j i))
          (Icc 0 1) :=
        ((continuous_const.matrix_mulVec continuous_id).comp_continuousOn h2)
      have hc : Continuous fun σ : ℝ => (σ : ℂ) * m j * m i :=
        (Complex.continuous_ofReal.mul continuous_const).mul continuous_const
      exact hc.continuousOn.smul (hself.mul h3)
    have hvec : ContinuousOn (fun σ : ℝ => A j * Split.chainTilde σ S m A (j + 1) l +
        ∑ i ∈ Finset.Ioo j l, ((σ : ℂ) * m j * m i) •
          (Split.selfEnergy S (Split.chainTilde σ S m A j i) * Split.chainTilde σ S m A i l))
        (Icc 0 1) :=
      ((continuousOn_const (c := A j)).mul h1).add hsum
    exact continuous_mulVec_pair.comp_continuousOn ((continuousOn_stabOp hS hml).prodMk hvec)
  · simp only [hjl, ite_false]
    exact continuousOn_const

/-- **M-terms are continuous** in the profile scale `σ ∈ [0,1]` (`‖m_i‖ < 1`, `S` stochastic
symmetric). -/
theorem continuousOn_chainM {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {m : ℕ → ℂ} (hm : ∀ i, ‖m i‖ < 1) (A : ℕ → Fin N → ℂ) (j l : ℕ) :
    ContinuousOn (fun σ : ℝ => Split.chainM σ S m A j l) (Icc 0 1) := by
  unfold Split.chainM
  exact (continuousOn_chainTilde_aux hS hm A (l - j) j l rfl).const_smul
    (∏ i ∈ Finset.Icc j l, m i)

/-! ### Control, scales and size functions -/

theorem continuousOn_loc (N W : ℕ) :
    ContinuousOn (fun η : ℝ => localizationLength N W η) (Ioi 0) := by
  unfold localizationLength
  have h : ContinuousOn (fun η : ℝ => (W : ℝ) / Real.sqrt η) (Ioi 0) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn fun η hη =>
      (Real.sqrt_pos.mpr hη).ne'
  exact continuous_min.comp_continuousOn (h.prodMk continuousOn_const)

theorem continuousOn_polynomialControl {N W : ℕ} (hN : 0 < N) (hW : 0 < W) (D : ℝ)
    (x y : Fin N) :
    ContinuousOn (fun η : ℝ => polynomialControl N W D η x y) (Ioi 0) := by
  unfold polynomialControl
  have hl := continuousOn_loc N W
  have hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < localizationLength N W η := fun η hη =>
    Adapters.ErdosRiabov.loc_pos hN hW hη
  apply ContinuousOn.mul
  · apply (hl.mul continuousOn_id).inv₀
    intro η hη
    exact (mul_pos (hpos η hη) hη).ne'
  · apply ContinuousOn.rpow_const (continuousOn_const.add (continuousOn_const.div hl
      fun η hη => (hpos η hη).ne'))
    intro η hη
    refine Or.inl (ne_of_gt ?_)
    show 0 < 1 + (cyclicDistance N x y : ℝ) / localizationLength N W η
    have := hpos η hη
    have : 0 ≤ (cyclicDistance N x y : ℝ) / localizationLength N W η := by positivity
    linarith

namespace PsiData

variable (P : PsiData N)

theorem vsHeight_mapsTo {z : ℂ} (hz : 0 < z.im) :
    MapsTo (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => vsHeight z q.1) (hermDomain N) (Ioi 0) :=
  fun _ hq => vsHeight_pos hz hq.1.2

theorem continuousOn_ups (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (x y : Fin N) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.ups q.1 x y) (hermDomain N) :=
  (continuousOn_polynomialControl hN hW P.D x y).comp
    ((continuous_vsHeight P.z).comp continuous_fst).continuousOn (vsHeight_mapsTo hz)

theorem continuousOn_lEta (hz : 0 < P.z.im) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.lEta q.1) (hermDomain N) := by
  unfold lEta
  have hη := ((continuous_vsHeight P.z).comp continuous_fst).continuousOn (s := hermDomain N)
  exact ((continuousOn_loc N P.W).comp hη (vsHeight_mapsTo hz)).mul hη

theorem lEta_pos (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t : ℝ} (ht : t ≤ 1) :
    0 < P.lEta t :=
  mul_pos (Adapters.ErdosRiabov.loc_pos hN hW (vsHeight_pos hz ht)) (vsHeight_pos hz ht)

theorem ups_pos (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t : ℝ} (ht : t ≤ 1)
    (x y : Fin N) : 0 < P.ups t x y :=
  Adapters.ErdosRiabov.polynomialControl_pos hN hW P.D (vsHeight_pos hz ht) x y

theorem sIso_pos (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t : ℝ} (ht : t ≤ 1)
    (a b : Fin N) (x : Fin k → Fin N) : 0 < P.sIso a b x t := by
  unfold sIso
  apply mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz ht) _)
  apply Real.sqrt_pos.mpr
  exact Finset.prod_pos fun i _ => P.ups_pos hN hW hz ht _ _

theorem sAv_pos (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t : ℝ} (ht : t ≤ 1)
    (x : Fin k → Fin N) : 0 < P.sAv x t := by
  unfold sAv
  split_ifs
  · exact inv_pos.mpr (P.lEta_pos hN hW hz ht)
  · apply mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz ht) _)
    apply Real.sqrt_pos.mpr
    exact Finset.prod_pos fun i _ => P.ups_pos hN hW hz ht _ _

theorem continuousOn_lEta_rpow (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (r : ℝ) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.lEta q.1 ^ r) (hermDomain N) :=
  (P.continuousOn_lEta hz).rpow_const fun _ hq => Or.inl (P.lEta_pos hN hW hz hq.1.2).ne'

theorem continuousOn_sIso (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (a b : Fin N)
    (x : Fin k → Fin N) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.sIso a b x q.1) (hermDomain N) := by
  unfold sIso
  refine (P.continuousOn_lEta_rpow hN hW hz _).mul ?_
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_finsetProd _ fun i _ => P.continuousOn_ups hN hW hz _ _)

theorem continuousOn_sAv (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (x : Fin k → Fin N) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.sAv x q.1) (hermDomain N) := by
  by_cases hk : k = 1
  · simp only [sAv, hk, ite_true]
    exact (P.continuousOn_lEta hz).inv₀ fun _ hq => (P.lEta_pos hN hW hz hq.1.2).ne'
  · simp only [sAv, hk, ite_false]
    refine (P.continuousOn_lEta_rpow hN hW hz _).mul ?_
    exact Real.continuous_sqrt.comp_continuousOn
      (continuousOn_finsetProd _ fun i _ => P.continuousOn_ups hN hW hz _ _)

theorem continuousOn_mChain (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (x : Fin k → Fin N) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.mChain σ x q.1) (hermDomain N) :=
  (continuousOn_chainM hS (norm_patM_lt_one hz.ne' σ) _ 1 k).comp continuous_fst.continuousOn
    fun _ hq => hq.1

theorem continuousOn_isoErr (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (a b : Fin N) (x : Fin k → Fin N) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.isoErr σ a b x q.1 q.2)
      (hermDomain N) := by
  unfold isoErr
  apply ContinuousOn.sub
  · exact (continuous_apply_apply a b).comp_continuousOn (continuousOn_gChain hz σ _)
  · by_cases hab : a = b
    · simp only [hab, ite_true]
      exact (continuous_apply b).comp_continuousOn (P.continuousOn_mChain hz hS σ x)
    · simp only [hab, ite_false]
      exact continuousOn_const

theorem continuousOn_avErr (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (x : Fin k → Fin N) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.avErr σ x q.1 q.2)
      (hermDomain N) := by
  unfold avErr
  apply ContinuousOn.sub
  · exact (continuous_id.matrix_trace).comp_continuousOn (continuousOn_gChain hz σ _)
  · apply continuousOn_finsetSum
    intro a _
    exact ((continuous_apply a).comp_continuousOn (P.continuousOn_mChain hz hS σ x)).mul
      continuousOn_const

theorem continuousOn_isoRatio (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (i : IsoIdx N k) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.isoRatio i q.1 q.2)
      (hermDomain N) := by
  unfold isoRatio
  refine (continuous_norm.comp_continuousOn (P.continuousOn_isoErr hz hS _ _ _ _)).div
    ((P.continuousOn_lEta_rpow hN hW hz _).mul (P.continuousOn_sIso hN hW hz _ _ _)) ?_
  intro _ hq
  exact (mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz hq.1.2) _)
    (P.sIso_pos hN hW hz hq.1.2 _ _ _)).ne'

theorem continuousOn_avRatio (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (i : AvIdx N k) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.avRatio i q.1 q.2)
      (hermDomain N) := by
  unfold avRatio
  refine (continuous_norm.comp_continuousOn (P.continuousOn_avErr hz hS _ _)).div
    ((P.continuousOn_lEta_rpow hN hW hz _).mul (P.continuousOn_sAv hN hW hz _)) ?_
  intro _ hq
  exact (mul_pos (Real.rpow_pos_of_pos (P.lEta_pos hN hW hz hq.1.2) _)
    (P.sAv_pos hN hW hz hq.1.2 _)).ne'

/-- **Continuity of `Ψ^iso`** in `(t, H)` on `[0,1] × {H Hermitian}` (`N, W ≥ 1`,
`Im z > 0`, `S` stochastic symmetric). -/
theorem continuousOn_bigPsiIso (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (k : ℕ) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.bigPsiIso k q.1 q.2)
      (hermDomain N) := by
  unfold bigPsiIso
  apply NNReal.continuous_coe.comp_continuousOn
  apply ContinuousOn.finset_sup_apply
  intro i _
  exact continuous_real_toNNReal.comp_continuousOn (P.continuousOn_isoRatio hN hW hz hS i)

/-- **Continuity of `Ψ^av`** in `(t, H)` on `[0,1] × {H Hermitian}`. -/
theorem continuousOn_bigPsiAv (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (k : ℕ) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.bigPsiAv k q.1 q.2)
      (hermDomain N) := by
  unfold bigPsiAv
  apply NNReal.continuous_coe.comp_continuousOn
  apply ContinuousOn.finset_sup_apply
  intro i _
  exact continuous_real_toNNReal.comp_continuousOn (P.continuousOn_avRatio hN hW hz hS i)

end PsiData

end BlockBand.Native.ErdosRiabov.Psi
